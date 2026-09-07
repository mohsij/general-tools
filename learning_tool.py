#!/usr/bin/env python3
"""
learning_tool.py - a small Python editor that runs code one line at a time.

Run it with whatever Python you have:

    python3 learning_tool.py

Standard library only (needs tkinter, which ships with most Python installs).

Controls
    Start        run the program and stop on the first line
    Step (F10)   execute the highlighted line, then stop again
    Run to end   finish without stopping (F8)
    Stop         end the run and unlock the editor (Esc)
"""

import builtins
import keyword
import linecache
import queue
import re
import sys
import threading
import traceback
import types
import tkinter as tk
from tkinter import filedialog, font as tkfont, messagebox, simpledialog, ttk

PROGRAM_NAME = "<your program>"
STEP_LIMIT = 5_000_000

# ---------------------------------------------------------------- appearance

BG = "#1c1f2b"
PANEL = "#232734"
EDITOR_BG = "#191c26"
GUTTER_BG = "#191c26"
FG = "#dce0ea"
MUTED = "#767d94"
ACCENT = "#79b8ff"
BORDER = "#2f3446"
SELECT = "#33405e"
CURRENT_LINE = "#3b3a22"
ERROR_LINE = "#4b2530"

SYNTAX = {
    "keyword": "#c39ded",
    "builtin": "#79b8ff",
    "string": "#b4dc8e",
    "comment": "#5f6780",
    "number": "#f2a36b",
    "definition": "#ffd48a",
    "decorator": "#8be0e0",
    "selfarg": "#ef8a8a",
}

KEYWORDS = sorted(set(keyword.kwlist) | set(getattr(keyword, "softkwlist", [])))
BUILTIN_NAMES = sorted(n for n in dir(builtins) if not n.startswith("_"))

TOKENS = re.compile(
    r"(?P<comment>#[^\n]*)"
    r"|(?P<string>(?i:[rbuf]{0,3})(?:'''[\s\S]*?(?:'''|\Z)"
    r"|\"\"\"[\s\S]*?(?:\"\"\"|\Z)"
    r"|'(?:\\.|[^'\\\n])*'"
    r"|\"(?:\\.|[^\"\\\n])*\"))"
    r"|(?P<decorator>@[A-Za-z_]\w*)"
    r"|(?P<definition>\b(?:def|class)\s+[A-Za-z_]\w*)"
    r"|(?P<number>\b(?:0[xXbBoO][0-9a-fA-F_]+|\d[\d_]*(?:\.\d*)?(?:[eE][-+]?\d+)?[jJ]?)\b)"
    r"|(?P<selfarg>\bself\b)"
    r"|(?P<keyword>\b(?:" + "|".join(KEYWORDS) + r")\b)"
    r"|(?P<builtin>\b(?:" + "|".join(BUILTIN_NAMES) + r")\b)"
)

SAMPLE = '''# Press Start, then Step through this one line at a time.
# The arrow shows where you are; the panel on the right shows
# every variable and how it changes.

def add_up(numbers):
    total = 0
    for number in numbers:
        total = total + number
        print("added", number, "so far:", total)
    return total


scores = [4, 8, 15, 16]
result = add_up(scores)
average = result / len(scores)

print("total:", result)
print("average:", average)
'''


class Stopped(BaseException):
    """Raised inside the traced program when the user presses Stop.

    Inherits from BaseException so a stray ``except Exception`` in the
    student's own code cannot swallow it.
    """


class QueueWriter:
    """Stands in for stdout/stderr so printed text reaches the output panel."""

    def __init__(self, q, tag):
        self.q = q
        self.tag = tag

    def write(self, text):
        if text:
            self.q.put(("out", text, self.tag))
        return len(text)

    def flush(self):
        pass

    def isatty(self):
        return False


class CodeText(tk.Text):
    """Text widget that fires <<Change>> whenever content or scroll changes."""

    def __init__(self, master, **kwargs):
        super().__init__(master, **kwargs)
        self._orig = self._w + "_orig"
        self.tk.call("rename", self._w, self._orig)
        self.tk.createcommand(self._w, self._proxy)

    def _proxy(self, *args):
        try:
            result = self.tk.call((self._orig,) + args)
        except tk.TclError:
            return None
        if args[0] in ("insert", "delete", "replace") or args[:3] == (
            "mark",
            "set",
            "insert",
        ) or args[:2] in (
            ("xview", "moveto"),
            ("xview", "scroll"),
            ("yview", "moveto"),
            ("yview", "scroll"),
        ):
            self.event_generate("<<Change>>", when="tail")
        return result


class Gutter(tk.Canvas):
    """Line numbers plus the arrow marking the current line."""

    def __init__(self, master, text, **kwargs):
        super().__init__(master, **kwargs)
        self.text = text
        self.marker = None
        self.error_marker = None

    def redraw(self, *_):
        self.delete("all")
        index = self.text.index("@0,0")
        while True:
            info = self.text.dlineinfo(index)
            if info is None:
                break
            y = info[1]
            line = int(str(index).split(".")[0])
            width = int(self["width"])
            if line == self.marker:
                self.create_text(6, y, anchor="nw", text="\u25b6",
                                 fill="#ffd48a", font=self.number_font)
                colour, weight = "#ffd48a", "bold"
            elif line == self.error_marker:
                self.create_text(6, y, anchor="nw", text="\u2716",
                                 fill="#ef8a8a", font=self.number_font)
                colour, weight = "#ef8a8a", "bold"
            else:
                colour, weight = MUTED, "normal"
            font = (self.number_font[0], self.number_font[1], weight)
            self.create_text(width - 8, y, anchor="ne", text=str(line),
                             fill=colour, font=font)
            index = self.text.index(f"{index}+1line")


class LearningTool(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Python step-through editor")
        self.geometry("1180x740")
        self.minsize(900, 560)
        self.configure(bg=BG)

        self.queue = queue.Queue()
        self.resume = threading.Event()
        self.input_ready = threading.Event()
        self.input_value = ""
        self.worker = None
        self.stop_requested = False
        self.mode = "step"
        self.steps = 0
        self.previous_values = {}
        self._hidden = {"input"}
        self.path = None
        self._highlight_job = None

        self._pick_fonts()
        self._build_ui()

        self.editor.insert("1.0", SAMPLE)
        self.editor.edit_reset()
        self._highlight()
        self.gutter.redraw()
        self._set_state("idle")
        self.after(30, self._poll)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ------------------------------------------------------------------ setup

    def _pick_fonts(self):
        available = set(tkfont.families())
        for name in ("JetBrains Mono", "Menlo", "Consolas", "DejaVu Sans Mono",
                     "Liberation Mono", "Courier New"):
            if name in available:
                mono = name
                break
        else:
            mono = "TkFixedFont"
        for name in ("Inter", "Segoe UI", "Helvetica Neue", "DejaVu Sans"):
            if name in available:
                ui = name
                break
        else:
            ui = "TkDefaultFont"
        self.mono = (mono, 13)
        self.mono_small = (mono, 11)
        self.ui_font = (ui, 11)
        self.ui_bold = (ui, 11, "bold")

    def _build_ui(self):
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure("TFrame", background=BG)
        style.configure("Panel.TFrame", background=PANEL)
        style.configure("TLabel", background=BG, foreground=MUTED,
                        font=self.ui_font)
        style.configure("Head.TLabel", background=PANEL, foreground=MUTED,
                        font=self.ui_bold, padding=(10, 6))
        style.configure("TButton", background=BORDER, foreground=FG,
                        font=self.ui_font, borderwidth=0, focuscolor=BORDER,
                        padding=(12, 6))
        style.map("TButton",
                  background=[("active", "#3d445c"), ("disabled", "#262a38")],
                  foreground=[("disabled", "#555b70")])
        style.configure("Go.TButton", background="#2f6f4f", foreground="#eafff2")
        style.map("Go.TButton", background=[("active", "#3a8a62"),
                                            ("disabled", "#262a38")],
                  foreground=[("disabled", "#555b70")])
        style.configure("TPanedwindow", background=BORDER)
        style.configure("Treeview", background=PANEL, fieldbackground=PANEL,
                        foreground=FG, borderwidth=0, rowheight=24,
                        font=self.mono_small)
        style.configure("Treeview.Heading", background=BORDER, foreground=MUTED,
                        font=self.ui_font, relief="flat", padding=(6, 4))
        style.map("Treeview", background=[("selected", SELECT)],
                  foreground=[("selected", FG)])

        bar = ttk.Frame(self, padding=(10, 8))
        bar.pack(fill="x")
        self.btn_start = ttk.Button(bar, text="Start", style="Go.TButton",
                                    command=self.start)
        self.btn_step = ttk.Button(bar, text="Step  F10", command=self.step)
        self.btn_run = ttk.Button(bar, text="Run to end  F8", command=self.run_to_end)
        self.btn_stop = ttk.Button(bar, text="Stop  Esc", command=self.stop)
        for b in (self.btn_start, self.btn_step, self.btn_run, self.btn_stop):
            b.pack(side="left", padx=(0, 6))
        ttk.Frame(bar, width=24).pack(side="left")
        ttk.Button(bar, text="Open", command=self.open_file).pack(side="left",
                                                                 padx=(0, 6))
        ttk.Button(bar, text="Save", command=self.save_file).pack(side="left")

        panes = ttk.PanedWindow(self, orient="horizontal")
        panes.pack(fill="both", expand=True, padx=10, pady=(0, 6))

        left = ttk.Frame(panes, style="Panel.TFrame")
        panes.add(left, weight=3)
        ttk.Label(left, text="Your program", style="Head.TLabel").pack(
            fill="x", anchor="w")

        wrap = tk.Frame(left, bg=EDITOR_BG, highlightthickness=1,
                        highlightbackground=BORDER)
        wrap.pack(fill="both", expand=True, padx=1, pady=(0, 1))
        yscroll = ttk.Scrollbar(wrap, orient="vertical")
        yscroll.pack(side="right", fill="y")
        self.editor = CodeText(
            wrap, wrap="none", undo=True, font=self.mono, bg=EDITOR_BG, fg=FG,
            insertbackground=ACCENT, selectbackground=SELECT, relief="flat",
            padx=10, pady=6, tabs="1c", yscrollcommand=yscroll.set,
            spacing1=1, spacing3=1,
        )
        self.gutter = Gutter(wrap, self.editor, width=52, bg=GUTTER_BG,
                             highlightthickness=0, bd=0)
        self.gutter.number_font = self.mono_small
        self.gutter.pack(side="left", fill="y")
        self.editor.pack(side="left", fill="both", expand=True)
        yscroll.config(command=self.editor.yview)

        xscroll = ttk.Scrollbar(left, orient="horizontal",
                                command=self.editor.xview)
        xscroll.pack(fill="x")
        self.editor.config(xscrollcommand=xscroll.set)

        for tag, colour in SYNTAX.items():
            self.editor.tag_configure(tag, foreground=colour)
        self.editor.tag_configure("current", background=CURRENT_LINE)
        self.editor.tag_configure("errorline", background=ERROR_LINE)
        self.editor.tag_lower("current")
        self.editor.tag_lower("errorline")

        self.editor.bind("<<Change>>", self._on_change)
        self.editor.bind("<Tab>", self._on_tab)
        self.editor.bind("<Return>", self._on_return)
        self.editor.bind("<MouseWheel>", lambda e: self.after(1, self.gutter.redraw))
        self.editor.bind("<Button-4>", lambda e: self.after(1, self.gutter.redraw))
        self.editor.bind("<Button-5>", lambda e: self.after(1, self.gutter.redraw))

        right = ttk.PanedWindow(panes, orient="vertical")
        panes.add(right, weight=2)

        var_frame = ttk.Frame(right, style="Panel.TFrame")
        right.add(var_frame, weight=3)
        ttk.Label(var_frame, text="Variables", style="Head.TLabel").pack(
            fill="x", anchor="w")
        tree_wrap = tk.Frame(var_frame, bg=PANEL, highlightthickness=1,
                             highlightbackground=BORDER)
        tree_wrap.pack(fill="both", expand=True, padx=1, pady=(0, 1))
        tree_scroll = ttk.Scrollbar(tree_wrap, orient="vertical")
        tree_scroll.pack(side="right", fill="y")
        self.tree = ttk.Treeview(tree_wrap, columns=("type", "value"),
                                 show="tree headings",
                                 yscrollcommand=tree_scroll.set)
        self.tree.heading("#0", text="name", anchor="w")
        self.tree.heading("type", text="type", anchor="w")
        self.tree.heading("value", text="value", anchor="w")
        self.tree.column("#0", width=178, minwidth=110, stretch=False)
        self.tree.column("type", width=80, minwidth=60, stretch=False)
        self.tree.column("value", width=220, minwidth=100)
        self.tree.tag_configure("changed", foreground="#ffd48a",
                                background=CURRENT_LINE)
        self.tree.tag_configure("scope", foreground=MUTED)
        self.tree.pack(side="left", fill="both", expand=True)
        tree_scroll.config(command=self.tree.yview)

        out_frame = ttk.Frame(right, style="Panel.TFrame")
        right.add(out_frame, weight=2)
        ttk.Label(out_frame, text="Output", style="Head.TLabel").pack(
            fill="x", anchor="w")
        out_wrap = tk.Frame(out_frame, bg=EDITOR_BG, highlightthickness=1,
                            highlightbackground=BORDER)
        out_wrap.pack(fill="both", expand=True, padx=1, pady=(0, 1))
        out_scroll = ttk.Scrollbar(out_wrap, orient="vertical")
        out_scroll.pack(side="right", fill="y")
        self.output = tk.Text(out_wrap, wrap="word", font=self.mono_small,
                              bg=EDITOR_BG, fg=FG, relief="flat", padx=8, pady=6,
                              height=8, state="disabled",
                              yscrollcommand=out_scroll.set)
        self.output.pack(side="left", fill="both", expand=True)
        out_scroll.config(command=self.output.yview)
        self.output.tag_configure("out", foreground=FG)
        self.output.tag_configure("err", foreground="#ef8a8a")
        self.output.tag_configure("info", foreground=MUTED)

        self.status = ttk.Label(self, text="", anchor="w", padding=(12, 0, 12, 8))
        self.status.pack(fill="x")

        self.bind("<F10>", lambda e: self.step())
        self.bind("<F8>", lambda e: self.run_to_end())
        self.bind("<F5>", lambda e: self.start())
        self.bind("<Escape>", lambda e: self.stop())

    # --------------------------------------------------------------- editing

    def _on_change(self, _event=None):
        self.gutter.redraw()
        if self._highlight_job:
            self.after_cancel(self._highlight_job)
        self._highlight_job = self.after(120, self._highlight)

    def _on_tab(self, _event):
        self.editor.insert("insert", "    ")
        return "break"

    def _on_return(self, _event):
        line = self.editor.get("insert linestart", "insert")
        indent = re.match(r"[ \t]*", line).group()
        if line.rstrip().endswith(":"):
            indent += "    "
        self.editor.insert("insert", "\n" + indent)
        self.editor.see("insert")
        return "break"

    def _highlight(self):
        self._highlight_job = None
        for tag in SYNTAX:
            self.editor.tag_remove(tag, "1.0", "end")
        source = self.editor.get("1.0", "end-1c")
        for match in TOKENS.finditer(source):
            kind = match.lastgroup
            start, end = match.span()
            if kind == "definition":
                parts = re.match(r"(def|class)(\s+)(\w+)", match.group())
                kw_end = start + len(parts.group(1))
                name_start = kw_end + len(parts.group(2))
                self._tag("keyword", start, kw_end)
                self._tag("definition", name_start, end)
            else:
                self._tag(kind, start, end)

    def _tag(self, tag, start, end):
        self.editor.tag_add(tag, f"1.0+{start}c", f"1.0+{end}c")

    def open_file(self):
        if self.worker and self.worker.is_alive():
            return
        path = filedialog.askopenfilename(
            filetypes=[("Python files", "*.py"), ("All files", "*.*")])
        if not path:
            return
        with open(path, "r", encoding="utf-8") as handle:
            text = handle.read()
        self.editor.config(state="normal")
        self.editor.delete("1.0", "end")
        self.editor.insert("1.0", text)
        self.editor.edit_reset()
        self.path = path
        self.title(f"Python step-through editor - {path}")
        self._highlight()
        self.gutter.redraw()

    def save_file(self):
        path = self.path or filedialog.asksaveasfilename(
            defaultextension=".py",
            filetypes=[("Python files", "*.py"), ("All files", "*.*")])
        if not path:
            return
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(self.editor.get("1.0", "end-1c"))
        self.path = path
        self.title(f"Python step-through editor - {path}")
        self._say(f"Saved to {path}")

    # ------------------------------------------------------------- run control

    def start(self, mode="step"):
        if self.worker and self.worker.is_alive():
            return
        source = self.editor.get("1.0", "end-1c")
        try:
            code = compile(source, PROGRAM_NAME, "exec")
        except SyntaxError as error:
            self._clear_output()
            line = error.lineno or 1
            self._mark_error(line)
            self._write(f"SyntaxError on line {line}: {error.msg}\n", "err")
            self._say(f"Syntax error on line {line} - nothing was run")
            return

        # Let tracebacks show the actual line of code, even though the
        # program was never written to disk.
        linecache.cache[PROGRAM_NAME] = (
            len(source), None, source.splitlines(True), PROGRAM_NAME)

        self._clear_output()
        self._clear_marks()
        self.tree.delete(*self.tree.get_children())
        self.previous_values = {}
        self.stop_requested = False
        self.steps = 0
        self.mode = mode
        self.resume.clear()
        self.input_ready.clear()
        self.editor.config(state="disabled")
        self._set_state("running")
        self._say("Starting...")
        self.worker = threading.Thread(target=self._execute, args=(code,),
                                       daemon=True)
        self.worker.start()

    def step(self):
        if not (self.worker and self.worker.is_alive()):
            self.start()
            return
        self.mode = "step"
        self._set_state("running")
        self.resume.set()

    def run_to_end(self):
        if not (self.worker and self.worker.is_alive()):
            self.start(mode="continue")
            self._say("Running...")
            return
        self.mode = "continue"
        self._set_state("running")
        self._say("Running...")
        self.resume.set()

    def stop(self):
        if self.worker and self.worker.is_alive():
            self.stop_requested = True
            self.input_ready.set()
            self.resume.set()

    # ---------------------------------------------------------- the debugger

    def _execute(self, code):
        namespace = {
            "__name__": "__main__",
            "__builtins__": builtins,
            "input": self._student_input,
        }
        self._hidden = {"input"}
        real_out, real_err = sys.stdout, sys.stderr
        sys.stdout = QueueWriter(self.queue, "out")
        sys.stderr = QueueWriter(self.queue, "err")
        sys.settrace(self._trace)
        problem = None
        try:
            exec(code, namespace)
        except Stopped:
            problem = ("stopped", None)
        except BaseException as error:  # noqa: BLE001 - student code, show it all
            problem = ("error", self._describe(error))
        finally:
            sys.settrace(None)
            sys.stdout, sys.stderr = real_out, real_err
            self.queue.put(("done", problem))

    def _trace(self, frame, event, _arg):
        if self.stop_requested:
            raise Stopped()
        if frame.f_code.co_filename != PROGRAM_NAME:
            return None
        if event == "line":
            if self.mode == "continue":
                self.steps += 1
                if self.steps > STEP_LIMIT:
                    raise RuntimeError(
                        "Stopped after a very large number of steps - "
                        "the program may be stuck in an endless loop.")
                return self._trace
            self._pause(frame)
        return self._trace

    def _pause(self, frame):
        self.queue.put(("pause", frame.f_lineno, self._stack(frame),
                        self._snapshot(frame)))
        self.resume.clear()
        self.resume.wait()
        if self.stop_requested:
            raise Stopped()

    def _stack(self, frame):
        names = []
        current = frame
        while current is not None and current.f_code.co_filename == PROGRAM_NAME:
            name = current.f_code.co_name
            names.append("main program" if name == "<module>" else f"{name}()")
            current = current.f_back
        return list(reversed(names))

    def _snapshot(self, frame):
        scopes = []
        name = frame.f_code.co_name
        if name == "<module>":
            scopes.append(("Variables", self._values(frame.f_locals)))
        else:
            scopes.append((f"Inside {name}()", self._values(frame.f_locals)))
            scopes.append(("Global variables", self._values(frame.f_globals)))
        return scopes

    def _values(self, mapping):
        rows = []
        for key, value in list(mapping.items()):
            if key.startswith("__") or key in self._hidden:
                continue
            if isinstance(value, types.ModuleType):
                continue
            kind = type(value).__name__
            if isinstance(value, types.FunctionType):
                text = f"function {value.__name__}"
                kind = "function"
            elif isinstance(value, type):
                text = f"class {value.__name__}"
                kind = "class"
            else:
                try:
                    text = repr(value)
                except Exception as error:  # noqa: BLE001
                    text = f"<could not show value: {error}>"
            if len(text) > 400:
                text = text[:400] + " ..."
            rows.append((key, kind, text))
        return rows

    def _describe(self, error):
        tb = error.__traceback__
        if tb is not None and tb.tb_next is not None:
            tb = tb.tb_next
        lines = traceback.format_exception(type(error), error, tb)
        line_number = None
        for frame_info in traceback.extract_tb(tb):
            if frame_info.filename == PROGRAM_NAME:
                line_number = frame_info.lineno
        return "".join(lines), line_number

    def _student_input(self, prompt=""):
        self.queue.put(("input", str(prompt)))
        self.input_ready.clear()
        self.input_ready.wait()
        if self.stop_requested:
            raise Stopped()
        self.queue.put(("out", f"{prompt}{self.input_value}\n", "info"))
        return self.input_value

    # ---------------------------------------------------------- gui updating

    def _poll(self):
        try:
            while True:
                message = self.queue.get_nowait()
                kind = message[0]
                if kind == "out":
                    self._write(message[1], message[2])
                elif kind == "pause":
                    self._on_pause(message[1], message[2], message[3])
                elif kind == "input":
                    self._ask_input(message[1])
                elif kind == "done":
                    self._on_done(message[1])
        except queue.Empty:
            pass
        self.after(30, self._poll)

    def _on_pause(self, line, stack, scopes):
        self._mark_current(line)
        self._show_variables(scopes)
        where = " > ".join(stack) if stack else "main program"
        self._say(f"Paused before line {line}   ({where})")
        self._set_state("paused")

    def _on_done(self, problem):
        self.editor.config(state="normal")
        self._set_state("idle")
        self.editor.tag_remove("current", "1.0", "end")
        self.gutter.marker = None
        if problem is None:
            self._say("Finished.")
        elif problem[0] == "stopped":
            self._say("Stopped. You can edit the code again.")
        else:
            text, line = problem[1]
            self._write("\n" + text, "err")
            if line:
                self._mark_error(line)
                self._say(f"The program stopped with an error on line {line}")
            else:
                self._say("The program stopped with an error")
        self.gutter.redraw()

    def _ask_input(self, prompt):
        answer = simpledialog.askstring("input()", prompt or "Enter a value:",
                                        parent=self)
        if answer is None:
            self.stop_requested = True
            self.input_value = ""
        else:
            self.input_value = answer
        self.input_ready.set()

    def _show_variables(self, scopes):
        self.tree.delete(*self.tree.get_children())
        current = {}
        for scope_name, rows in scopes:
            parent = self.tree.insert("", "end", text=scope_name, open=True,
                                      values=("", ""), tags=("scope",))
            if not rows:
                self.tree.insert(parent, "end", text="(none yet)",
                                 values=("", ""), tags=("scope",))
            for name, kind, value in rows:
                key = (scope_name, name)
                current[key] = value
                changed = self.previous_values.get(key) != value
                tags = ("changed",) if changed and self.previous_values else ()
                self.tree.insert(parent, "end", text=name, values=(kind, value),
                                 tags=tags)
        self.previous_values = current

    def _mark_current(self, line):
        self.editor.tag_remove("current", "1.0", "end")
        self.editor.tag_remove("errorline", "1.0", "end")
        self.editor.tag_add("current", f"{line}.0", f"{line}.0 lineend+1c")
        self.gutter.marker = line
        self.gutter.error_marker = None
        self.editor.see(f"{line}.0")
        self.gutter.redraw()

    def _mark_error(self, line):
        self.editor.tag_remove("current", "1.0", "end")
        self.editor.tag_remove("errorline", "1.0", "end")
        self.editor.tag_add("errorline", f"{line}.0", f"{line}.0 lineend+1c")
        self.gutter.marker = None
        self.gutter.error_marker = line
        self.editor.see(f"{line}.0")
        self.gutter.redraw()

    def _clear_marks(self):
        self.editor.tag_remove("current", "1.0", "end")
        self.editor.tag_remove("errorline", "1.0", "end")
        self.gutter.marker = None
        self.gutter.error_marker = None
        self.gutter.redraw()

    def _write(self, text, tag="out"):
        self.output.config(state="normal")
        self.output.insert("end", text, tag)
        self.output.see("end")
        self.output.config(state="disabled")

    def _clear_output(self):
        self.output.config(state="normal")
        self.output.delete("1.0", "end")
        self.output.config(state="disabled")

    def _say(self, text):
        self.status.config(text=text)

    def _set_state(self, state):
        if state == "idle":
            self.btn_start.config(state="normal", text="Start")
            self.btn_step.config(state="normal")
            self.btn_run.config(state="normal")
            self.btn_stop.config(state="disabled")
        elif state == "paused":
            self.btn_start.config(state="disabled", text="Running")
            self.btn_step.config(state="normal")
            self.btn_run.config(state="normal")
            self.btn_stop.config(state="normal")
        else:
            self.btn_start.config(state="disabled", text="Running")
            self.btn_step.config(state="disabled")
            self.btn_run.config(state="disabled")
            self.btn_stop.config(state="normal")

    def _on_close(self):
        self.stop_requested = True
        self.input_ready.set()
        self.resume.set()
        self.destroy()


def main():
    if sys.version_info < (3, 7):
        print("This tool needs Python 3.7 or newer.")
        return
    try:
        app = LearningTool()
    except tk.TclError as error:
        print("Could not open a window:", error)
        print("On Linux you may need to install tkinter, e.g. "
              "sudo apt install python3-tk")
        return
    app.mainloop()


if __name__ == "__main__":
    main()
