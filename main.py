import tkinter as tk
from tkinter import ttk, font
import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import matplotlib.gridspec as gridspec
import random
import math

# ── Palette ──────────────────────────────────────────────────────────────────
BG      = "#0a0e1a"
BG2     = "#111827"
BG3     = "#1a2235"
CARD    = "#141b2d"
BORDER  = "#1e3a5f"
ACCENT  = "#63b3ed"
ACC2    = "#68d391"
ACC3    = "#f6ad55"
ACC4    = "#fc8181"
TEXT    = "#e2e8f0"
TEXT2   = "#94a3b8"
TEXT3   = "#64748b"

PROC_COLORS = ['#7c3aed','#0891b2','#059669','#dc2626','#d97706','#db2777','#2563eb','#0e7490']
PROC_LIGHT  = ['#a78bfa','#67e8f9','#6ee7b7','#fca5a5','#fcd34d','#f9a8d4','#93c5fd','#67e8f9']

ALGO_COLOR  = {'fcfs': '#0891b2', 'sjn': '#059669', 'rr': '#d97706'}
ALGO_LIGHT  = {'fcfs': '#67e8f9', 'sjn': '#6ee7b7', 'rr': '#fcd34d'}
ALGO_LABEL  = {'fcfs': 'First Come First Serve', 'sjn': 'Shortest Job Next', 'rr': 'Round Robin'}

# ── Scheduling Algorithms ─────────────────────────────────────────────────────
def fcfs(procs):
    p = sorted([dict(x, id=i) for i, x in enumerate(procs)], key=lambda x: x['arrival'])
    t = 0; gantt = []
    for proc in p:
        if t < proc['arrival']: t = proc['arrival']
        gantt.append({'pid': proc['id'], 'start': t, 'end': t + proc['burst']})
        proc['start'] = t; t += proc['burst']
        proc['finish'] = t
        proc['waiting'] = proc['start'] - proc['arrival']
        proc['turnaround'] = proc['finish'] - proc['arrival']
    return {'results': p, 'gantt': gantt}

def sjn(procs):
    p = [dict(x, id=i) for i, x in enumerate(procs)]
    done = [False] * len(p); t = 0; completed = 0; gantt = []
    while completed < len(p):
        idx = -1; best = float('inf')
        for i, proc in enumerate(p):
            if not done[i] and proc['arrival'] <= t and proc['burst'] < best:
                best = proc['burst']; idx = i
        if idx == -1: t += 1; continue
        gantt.append({'pid': p[idx]['id'], 'start': t, 'end': t + p[idx]['burst']})
        p[idx]['waiting'] = t - p[idx]['arrival']
        t += p[idx]['burst']
        p[idx]['finish'] = t; p[idx]['turnaround'] = p[idx]['finish'] - p[idx]['arrival']
        done[idx] = True; completed += 1
    return {'results': p, 'gantt': gantt}

def round_robin(procs, quantum):
    p = [dict(x, id=i, rem=x['burst']) for i, x in enumerate(procs)]
    n = len(p); in_q = [False] * n; queue = []; t = 0; completed = 0; gantt = []
    for i, pr in enumerate(p):
        if pr['arrival'] <= 0: queue.append(i); in_q[i] = True
    while completed < n:
        if not queue:
            t += 1
            for i, pr in enumerate(p):
                if not in_q[i] and pr['arrival'] <= t and pr['rem'] > 0:
                    queue.append(i); in_q[i] = True
            continue
        i = queue.pop(0)
        run = min(quantum, p[i]['rem'])
        gantt.append({'pid': p[i]['id'], 'start': t, 'end': t + run})
        p[i]['rem'] -= run; t += run
        for j, pr in enumerate(p):
            if not in_q[j] and pr['arrival'] <= t and pr['rem'] > 0:
                queue.append(j); in_q[j] = True
        if p[i]['rem'] > 0:
            queue.append(i)
        else:
            completed += 1; p[i]['finish'] = t
            p[i]['turnaround'] = t - p[i]['arrival']
            p[i]['waiting'] = p[i]['turnaround'] - p[i]['burst']
    return {'results': p, 'gantt': gantt}

def avg(results, key):
    return sum(r[key] for r in results) / len(results)

def cpu_util(gantt, total):
    busy = sum(g['end'] - g['start'] for g in gantt)
    return (busy / total * 100) if total > 0 else 0

# ── Main Application ──────────────────────────────────────────────────────────
class CPUSchedulerApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("CPU Scheduling Simulator")
        self.geometry("1380x820")
        try:
            self.state("zoomed")
        except:
            try:
                self.attributes("-zoomed", True)
            except:
                pass
        self.minsize(900, 600)
        self.configure(bg=BG)
        self.processes = []
        self.algo = tk.StringVar(value='fcfs')
        self.quantum = tk.IntVar(value=2)
        self._chart_canvas = None
        self._build_ui()
        self.load_example()

    # ── UI Construction ───────────────────────────────────────────────────────
    def _build_ui(self):
        self._build_header()
        self.body = tk.Frame(self, bg=BG)
        self.body.pack(fill='both', expand=True)
        self._build_sidebar(self.body)
        self._build_divider(self.body)
        self._build_content(self.body)

    def _build_divider(self, parent):
        self._sidebar_width = 380
        self._sidebar_collapsed = False
        divider = tk.Frame(parent, bg=BORDER, width=6, cursor='sb_h_double_arrow')
        divider.pack(side='left', fill='y')
        divider.pack_propagate(False)
        self._collapse_btn = tk.Label(divider, text='\u25c4', bg=ACCENT, fg=BG,
                                      font=('Arial', 8, 'bold'), cursor='hand2',
                                      width=1, pady=4)
        self._collapse_btn.place(relx=0.5, rely=0.5, anchor='center')
        self._collapse_btn.bind('<Button-1>', self._toggle_sidebar)
        divider.bind('<Button-1>',        self._drag_start)
        divider.bind('<B1-Motion>',       self._drag_motion)
        divider.bind('<ButtonRelease-1>', self._drag_end)
        self._divider = divider
        self._drag_x = None

    def _drag_start(self, e):
        self._drag_x = e.x_root

    def _drag_motion(self, e):
        if self._drag_x is None: return
        dx = e.x_root - self._drag_x
        self._drag_x = e.x_root
        new_w = max(200, min(600, self.sidebar.winfo_width() + dx))
        self._sidebar_width = new_w
        self.sidebar.config(width=new_w)

    def _drag_end(self, e):
        self._drag_x = None

    def _toggle_sidebar(self, e=None):
        if self._sidebar_collapsed:
            self.sidebar.config(width=self._sidebar_width)
            self.sidebar.pack(side='left', fill='y', before=self._divider)
            self._collapse_btn.config(text='\u25c4')
            self._sidebar_collapsed = False
        else:
            self._sidebar_width = self.sidebar.winfo_width()
            self.sidebar.pack_forget()
            self._collapse_btn.config(text='\u25ba')
            self._sidebar_collapsed = True

    def _build_header(self):
        hdr = tk.Frame(self, bg="#0d1b3e", height=64)
        hdr.pack(fill='x')
        hdr.pack_propagate(False)

        inner = tk.Frame(hdr, bg="#0d1b3e")
        inner.pack(fill='both', expand=True, padx=32, pady=10)

        icon = tk.Label(inner, text="CPU", bg=ACCENT, fg=BG, width=5, height=1,
                        font=("Courier", 13, "bold"), relief='flat')
        icon.pack(side='left', padx=(0, 12))

        title_f = tk.Frame(inner, bg="#0d1b3e")
        title_f.pack(side='left')
        tk.Label(title_f, text="Scheduling Simulator", bg="#0d1b3e", fg=TEXT,
                 font=("Courier", 15, "bold")).pack(anchor='w')
        tk.Label(title_f, text="Process Scheduling Algorithm Visualizer", bg="#0d1b3e", fg=TEXT3,
                 font=("Helvetica", 9)).pack(anchor='w')

        badges = tk.Frame(inner, bg="#0d1b3e")
        badges.pack(side='right')
        for label, color, bg_c in [("FCFS","#67e8f9","#082a36"),("SJN","#6ee7b7","#062820"),("Round Robin","#fcd34d","#2e1f05")]:
            tk.Label(badges, text=label, fg=color, bg=bg_c, font=("Courier", 9, "bold"),
                     padx=10, pady=3, relief='flat').pack(side='left', padx=4)

    def _build_sidebar(self, parent):
        self.sidebar = tk.Frame(parent, bg=CARD, width=380, bd=0,
                                highlightthickness=1, highlightbackground=BORDER)
        self.sidebar.pack(side='left', fill='y')
        self.sidebar.pack_propagate(False)

        canvas = tk.Canvas(self.sidebar, bg=CARD, highlightthickness=0)
        scrollbar = tk.Scrollbar(self.sidebar, orient="vertical", command=canvas.yview)
        self.sb_frame = tk.Frame(canvas, bg=CARD)
        self.sb_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=self.sb_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        canvas.bind_all("<MouseWheel>", lambda e: canvas.yview_scroll(int(-1*(e.delta/120)), "units"))

        self._sidebar_section(self.sb_frame, "PROCESSES")
        self.proc_frame = tk.Frame(self.sb_frame, bg=CARD)
        self.proc_frame.pack(fill='x', padx=14, pady=4)

        btn_row = tk.Frame(self.sb_frame, bg=CARD)
        btn_row.pack(fill='x', padx=14, pady=4)
        self._btn(btn_row, "+ Add", self.add_process, ACCENT).pack(side='left', fill='x', expand=True, padx=(0,4))
        self._btn(btn_row, "− Remove", self.remove_process, ACC4).pack(side='left', fill='x', expand=True)
        self._btn(self.sb_frame, "↺  Load Example", self.load_example, TEXT2).pack(fill='x', padx=14, pady=(2,10))

        self._sidebar_section(self.sb_frame, "ALGORITHM")
        algo_frame = tk.Frame(self.sb_frame, bg=CARD)
        algo_frame.pack(fill='x', padx=14, pady=6)
        self.algo_btns = {}
        cols = [('fcfs','FCFS','#67e8f9','#082a36'), ('sjn','SJN','#6ee7b7','#062820'), ('rr','Round Robin','#fcd34d','#2e1f05')]
        for i,(key,label,fg,bg) in enumerate(cols):
            b = tk.Label(algo_frame, text=label, fg=TEXT2, bg=BG2, font=("Courier",10,"bold"),
                         padx=6, pady=7, cursor='hand2', relief='flat',
                         highlightthickness=1, highlightbackground=BORDER)
            b.grid(row=0, column=i, sticky='ew', padx=2)
            algo_frame.grid_columnconfigure(i, weight=1)
            b.bind("<Button-1>", lambda e, k=key: self.set_algo(k))
            self.algo_btns[key] = (b, fg, bg)

        self.rr_frame = tk.Frame(self.sb_frame, bg=CARD)
        self.rr_frame.pack(fill='x', padx=14, pady=4)
        tk.Label(self.rr_frame, text="Quantum:", bg=CARD, fg=TEXT2, font=("Helvetica",11)).pack(side='left')
        self.q_label = tk.Label(self.rr_frame, text="2", bg=CARD, fg='#fcd34d', font=("Courier",14,"bold"), width=3)
        self.q_label.pack(side='right')
        q_slider = tk.Scale(self.rr_frame, from_=1, to=10, orient='horizontal', variable=self.quantum,
                            bg=CARD, fg='#fcd34d', troughcolor=BG3, highlightthickness=0,
                            showvalue=False, command=lambda v: (self.q_label.config(text=v), self.run()))
        q_slider.pack(side='left', fill='x', expand=True, padx=6)
        self.rr_frame.pack_forget()

        self._sidebar_section(self.sb_frame, "COMPARE ALL")
        self._btn(self.sb_frame, "📊  Compare Algorithms", self.show_compare, ACC2,
                  font=("Helvetica",11,"bold")).pack(fill='x', padx=14, pady=(4,10))

        self.set_algo('fcfs')

    def _sidebar_section(self, parent, title):
        f = tk.Frame(parent, bg=CARD)
        f.pack(fill='x', padx=14, pady=(14, 4))
        tk.Label(f, text=title, fg=TEXT3, bg=CARD, font=("Courier", 9, "bold")).pack(side='left')
        tk.Frame(f, bg=BORDER, height=1).pack(side='left', fill='x', expand=True, padx=(8,0))

    def _btn(self, parent, text, cmd, color=TEXT2, font=("Helvetica",10,"bold")):
        b = tk.Label(parent, text=text, fg=BG if color==ACCENT else color, bg=CARD,
                     font=font, padx=10, pady=7, cursor='hand2', relief='flat',
                     highlightthickness=1, highlightbackground=BORDER)
        if color == ACCENT: b.config(bg=ACCENT, fg=BG)
        elif color == ACC2: b.config(bg='#0d3320', fg=ACC2)
        b.bind("<Button-1>", lambda e: cmd())
        b.bind("<Enter>", lambda e: b.config(highlightbackground=ACCENT))
        b.bind("<Leave>", lambda e: b.config(highlightbackground=BORDER))
        return b

    def _build_content(self, parent):
        self.content = tk.Frame(parent, bg=BG)
        self.content.pack(side='left', fill='both', expand=True)
        self.placeholder = tk.Frame(self.content, bg=BG)
        self.placeholder.place(relx=0.5, rely=0.5, anchor='center')
        tk.Label(self.placeholder, text="⚙", fg=TEXT3, bg=BG, font=("Arial",52)).pack()
        tk.Label(self.placeholder, text="Add processes and run an algorithm", fg=TEXT3, bg=BG, font=("Helvetica",13)).pack()

    # ── Process Management ────────────────────────────────────────────────────
    def render_inputs(self):
        for w in self.proc_frame.winfo_children(): w.destroy()
        for i, p in enumerate(self.processes):
            color = PROC_COLORS[i % 8]; light = PROC_LIGHT[i % 8]
            card = tk.Frame(self.proc_frame, bg=BG2, highlightthickness=1, highlightbackground=BORDER)
            card.pack(fill='x', pady=4)

            hdr = tk.Frame(card, bg=BG2)
            hdr.pack(fill='x', padx=10, pady=(8,4))
            dot = tk.Label(hdr, text=f"P{i+1}", bg=color, fg='white', font=("Courier",10,"bold"),
                           width=3, pady=3)
            dot.pack(side='left')
            tk.Label(hdr, text=f"Process {i+1}", fg=TEXT3, bg=BG2, font=("Helvetica",10)).pack(side='right')

            fields = tk.Frame(card, bg=BG2)
            fields.pack(fill='x', padx=6, pady=(0,10))
            fields.grid_columnconfigure(0, weight=1, uniform="col")
            fields.grid_columnconfigure(1, weight=1, uniform="col")
            for j, (lbl, key) in enumerate([("ARRIVAL TIME","arrival"),("BURST TIME","burst")]):
                f = tk.Frame(fields, bg=BG2)
                f.grid(row=0, column=j, sticky='ew', padx=3)
                tk.Label(f, text=lbl, fg=TEXT3, bg=BG2, font=("Helvetica",8,"bold")).pack(anchor='w')
                var = tk.StringVar(value=str(p[key]))
                entry = tk.Entry(f, textvariable=var, bg=BG3, fg=TEXT, font=("Courier",12),
                                 insertbackground=TEXT, relief='flat', bd=4,
                                 highlightthickness=1, highlightbackground=BORDER)
                entry.pack(fill='x')
                entry.bind("<FocusIn>", lambda e, en=entry: en.config(highlightbackground=ACCENT))
                entry.bind("<FocusOut>", lambda e, en=entry: en.config(highlightbackground=BORDER))
                def on_change(e, idx=i, k=key, v=var):
                    try:
                        val = max(0 if k=='arrival' else 1, int(v.get()))
                        self.processes[idx][k] = val
                        self.run()
                    except: pass
                entry.bind("<KeyRelease>", on_change)

    def add_process(self):
        if len(self.processes) >= 8: return
        self.processes.append({'arrival': 0, 'burst': random.randint(2, 9)})
        self.render_inputs()

    def remove_process(self):
        if len(self.processes) > 1:
            self.processes.pop(); self.render_inputs()

    def load_example(self):
        self.processes = [
            {'arrival': 0, 'burst': 7}, {'arrival': 2, 'burst': 4},
            {'arrival': 4, 'burst': 1}, {'arrival': 6, 'burst': 4},
            {'arrival': 8, 'burst': 2}
        ]
        self.render_inputs()

    def set_algo(self, a):
        self.algo.set(a)
        for key, (btn, fg, bg) in self.algo_btns.items():
            if key == a:
                btn.config(bg=bg, fg=fg, highlightbackground=ALGO_COLOR[a])
            else:
                btn.config(bg=BG2, fg=TEXT2, highlightbackground=BORDER)
        if a == 'rr': self.rr_frame.pack(fill='x', padx=14, pady=4)
        else: self.rr_frame.pack_forget()
        self.run()

    # ── Run Simulation ────────────────────────────────────────────────────────
    def run(self):
        if not self.processes: return
        self.placeholder.place_forget()
        a = self.algo.get()
        q = self.quantum.get()
        if a == 'fcfs':   data = fcfs(self.processes)
        elif a == 'sjn':  data = sjn(self.processes)
        else:             data = round_robin(self.processes, q)
        self._render_single(data, a)

    def _render_single(self, data, a):
        results, gantt = data['results'], data['gantt']
        n_procs = len(results)
        total = max(g['end'] for g in gantt)
        avg_wt  = avg(results, 'waiting')
        avg_tat = avg(results, 'turnaround')
        cpu     = cpu_util(gantt, total)

        if self._chart_canvas:
            self._chart_canvas.get_tk_widget().destroy()
            plt.close('all')

        # ── Dynamic figure height based on number of processes ────────────────
        # Table needs ~0.18 height per process row + header/footer rows
        table_rows = n_procs + 2  # header + data rows + average row
        table_height_ratio = max(1.5, table_rows * 0.22)
        total_height = 3.2 + 2.2 + 2.5 + table_height_ratio  # metric+gantt+bars+table
        fig_height = min(max(total_height, 9), 14)

        fig = plt.figure(figsize=(13, fig_height), facecolor=BG)

        # ── GridSpec with proper ratios so table gets enough room ─────────────
        height_ratios = [1.8, 2.2, 2.5, table_height_ratio]
        gs = gridspec.GridSpec(4, 2, figure=fig,
                               height_ratios=height_ratios,
                               hspace=0.55, wspace=0.35,
                               top=0.95, bottom=0.04,
                               left=0.06, right=0.97)

        # ── Metric strip (top row spanning both cols) ─────────────────────────
        ax_m = fig.add_subplot(gs[0, :])
        ax_m.set_facecolor(BG); ax_m.axis('off')
        metrics = [
            ("AVG WAITING TIME",     f"{avg_wt:.2f}",   "time units", '#a78bfa'),
            ("AVG TURNAROUND TIME",  f"{avg_tat:.2f}",  "time units", ACC2),
            ("CPU UTILIZATION",      f"{cpu:.1f}%",     "of total",   ACCENT),
            ("PROCESSES",            str(n_procs),      "scheduled",  ACC3),
        ]
        for i, (lbl, val, sub, col) in enumerate(metrics):
            x = 0.04 + i * 0.245
            ax_m.text(x+0.025, 0.75, lbl, transform=fig.transFigure,
                      color=TEXT3, fontsize=7.5, fontfamily='monospace', ha='left')
            ax_m.text(x+0.025, 0.65, val, transform=fig.transFigure,
                      color=col, fontsize=22, fontfamily='monospace', fontweight='bold', ha='left')
            ax_m.text(x+0.025, 0.57, sub, transform=fig.transFigure,
                      color=TEXT3, fontsize=8, ha='left')
            rect = plt.Rectangle((x+0.005, 0.535), 0.225, 0.31,
                                  transform=fig.transFigure, color=CARD, zorder=0,
                                  clip_on=False)
            fig.add_artist(rect)
            top_bar = plt.Rectangle((x+0.005, 0.84), 0.225, 0.007,
                                    transform=fig.transFigure, color=col, zorder=1, clip_on=False)
            fig.add_artist(top_bar)

        # ── Gantt Chart ───────────────────────────────────────────────────────
        ax_g = fig.add_subplot(gs[1, :])
        ax_g.set_facecolor(BG2)
        self._draw_gantt(ax_g, gantt, total)
        ax_g.set_title(f"GANTT CHART — {ALGO_LABEL[a].upper()}", color=ALGO_LIGHT[a],
                       fontfamily='monospace', fontsize=9, loc='left', pad=8)

        # ── Waiting Time Bar Chart ────────────────────────────────────────────
        ax_wt = fig.add_subplot(gs[2, 0])
        ax_wt.set_facecolor(BG2)
        sorted_r = sorted(results, key=lambda x: x['id'])
        names = [f"P{r['id']+1}" for r in sorted_r]
        colors = [PROC_COLORS[r['id']%8] for r in sorted_r]
        bars = ax_wt.bar(names, [r['waiting'] for r in sorted_r], color=colors, alpha=0.85,
                         edgecolor='none', width=0.6)
        for bar, r in zip(bars, sorted_r):
            ax_wt.text(bar.get_x()+bar.get_width()/2, bar.get_height()+0.1,
                       str(r['waiting']), ha='center', va='bottom', color=TEXT2,
                       fontsize=9, fontfamily='monospace')
        self._style_ax(ax_wt, "WAITING TIME PER PROCESS")

        # ── Turnaround Time Bar Chart ─────────────────────────────────────────
        ax_tat = fig.add_subplot(gs[2, 1])
        ax_tat.set_facecolor(BG2)
        light_cols = [PROC_LIGHT[r['id']%8] for r in sorted_r]
        bars2 = ax_tat.bar(names, [r['turnaround'] for r in sorted_r], color=light_cols, alpha=0.7,
                           edgecolor='none', width=0.6)
        for bar, r in zip(bars2, sorted_r):
            ax_tat.text(bar.get_x()+bar.get_width()/2, bar.get_height()+0.1,
                        str(r['turnaround']), ha='center', va='bottom', color=TEXT2,
                        fontsize=9, fontfamily='monospace')
        self._style_ax(ax_tat, "TURNAROUND TIME PER PROCESS")

        # ── Results Table ─────────────────────────────────────────────────────
        # Use a dedicated axes with tight bbox so rows never overlap
        ax_t = fig.add_subplot(gs[3, :])
        ax_t.set_facecolor(BG)
        ax_t.axis('off')
        self._draw_table(ax_t, sorted_r)

        self._chart_canvas = FigureCanvasTkAgg(fig, master=self.content)
        self._chart_canvas.draw()
        self._chart_canvas.get_tk_widget().pack(fill='both', expand=True)

    # ── Compare View ──────────────────────────────────────────────────────────
    def show_compare(self):
        if not self.processes: return
        if self._chart_canvas:
            self._chart_canvas.get_tk_widget().destroy()
            plt.close('all')

        q = self.quantum.get()
        all_data = {
            'fcfs': fcfs(self.processes),
            'sjn':  sjn(self.processes),
            'rr':   round_robin(self.processes, q),
        }
        wts  = {k: avg(v['results'],'waiting')    for k,v in all_data.items()}
        tats = {k: avg(v['results'],'turnaround') for k,v in all_data.items()}
        min_wt = min(wts.values())

        fig = plt.figure(figsize=(13, 10), facecolor=BG)
        gs = gridspec.GridSpec(3, 3, figure=fig, hspace=0.55, wspace=0.4,
                               top=0.93, bottom=0.05, left=0.06, right=0.97)

        fig.text(0.5, 0.965, "ALGORITHM COMPARISON", ha='center', color=TEXT2,
                 fontfamily='monospace', fontsize=11, fontweight='bold')

        for ci, (key, label) in enumerate([('fcfs','FCFS'),('sjn','SJN'),('rr','Round Robin')]):
            ax = fig.add_subplot(gs[0, ci])
            ax.set_facecolor(CARD); ax.axis('off')
            col = ALGO_LIGHT[key]
            is_w = abs(wts[key] - min_wt) < 0.001
            ax.text(0.5, 0.88, label + (" ✓ Best" if is_w else ""), ha='center', va='top',
                    color=col, fontsize=11, fontfamily='monospace', fontweight='bold',
                    transform=ax.transAxes)
            for yi, (stat_lbl, val, stat_col) in enumerate([
                ("Avg Waiting",    f"{wts[key]:.2f}",  ACC2 if is_w else ACC4),
                ("Avg Turnaround", f"{tats[key]:.2f}", ACC2 if abs(tats[key]-min(tats.values()))<0.001 else TEXT2),
                ("CPU Util.",      f"{cpu_util(all_data[key]['gantt'], max(g['end'] for g in all_data[key]['gantt'])):.1f}%", TEXT2),
            ]):
                y = 0.62 - yi * 0.22
                ax.text(0.08, y, stat_lbl, ha='left', va='center', color=TEXT3,
                        fontsize=9, transform=ax.transAxes)
                ax.text(0.92, y, val, ha='right', va='center', color=stat_col,
                        fontsize=11, fontfamily='monospace', fontweight='bold', transform=ax.transAxes)
            ax.add_patch(plt.Rectangle((0,0),1,1, transform=ax.transAxes, facecolor=CARD,
                                        edgecolor=ACC2 if is_w else BORDER, linewidth=1.5, zorder=0))
            ax.add_patch(plt.Rectangle((0,0.97),1,0.03, transform=ax.transAxes,
                                        facecolor=ALGO_COLOR[key], zorder=1))

        ax_cmp = fig.add_subplot(gs[1, :])
        ax_cmp.set_facecolor(BG2)
        keys = list(all_data.keys()); labels = ['FCFS','SJN','Round Robin']
        x = range(len(keys)); w = 0.35
        b1 = ax_cmp.bar([i - w/2 for i in x], [wts[k] for k in keys], width=w,
                        color=[ALGO_COLOR[k]+'bb' for k in keys], edgecolor='none', label='Avg Waiting')
        b2 = ax_cmp.bar([i + w/2 for i in x], [tats[k] for k in keys], width=w,
                        color=[ALGO_COLOR[k]+'55' for k in keys], edgecolor=BORDER, linewidth=0.5,
                        label='Avg Turnaround')
        ax_cmp.set_xticks(list(x)); ax_cmp.set_xticklabels(labels)
        legend = ax_cmp.legend(facecolor=BG3, edgecolor=BORDER, labelcolor=TEXT2,
                               prop={'family':'monospace','size':9})
        self._style_ax(ax_cmp, "COMPARISON — WAITING & TURNAROUND TIME")

        ax_pp = fig.add_subplot(gs[2, :])
        ax_pp.set_facecolor(BG2)
        n = len(self.processes); pw = 0.25; xp = range(n)
        for bi, (key, lbl) in enumerate(zip(keys, labels)):
            sorted_r = sorted(all_data[key]['results'], key=lambda x: x['id'])
            offset = (bi - 1) * pw
            ax_pp.bar([i + offset for i in xp], [r['waiting'] for r in sorted_r],
                      width=pw, color=ALGO_COLOR[key]+'cc', edgecolor='none',
                      label=lbl)
        ax_pp.set_xticks(list(xp)); ax_pp.set_xticklabels([f"P{i+1}" for i in range(n)])
        ax_pp.legend(facecolor=BG3, edgecolor=BORDER, labelcolor=TEXT2,
                     prop={'family':'monospace','size':9})
        self._style_ax(ax_pp, "WAITING TIME PER PROCESS — ALL ALGORITHMS")

        self._chart_canvas = FigureCanvasTkAgg(fig, master=self.content)
        self._chart_canvas.draw()
        self._chart_canvas.get_tk_widget().pack(fill='both', expand=True)

    # ── Gantt Drawing ─────────────────────────────────────────────────────────
    def _draw_gantt(self, ax, gantt, total):
        pids = sorted(set(g['pid'] for g in gantt))
        yticks = []; ylabels = []
        for row, pid in enumerate(pids):
            segs = [g for g in gantt if g['pid'] == pid]
            cursor = 0
            for seg in sorted(segs, key=lambda s: s['start']):
                if seg['start'] > cursor:
                    ax.barh(row, seg['start']-cursor, left=cursor, height=0.6,
                            color=BG3, edgecolor='none')
                    cursor = seg['start']
                w = seg['end'] - seg['start']
                ax.barh(row, w, left=seg['start'], height=0.6,
                        color=PROC_COLORS[pid%8], edgecolor='none', alpha=0.88)
                if w / total > 0.04:
                    ax.text(seg['start'] + w/2, row, f"t{seg['start']}",
                            ha='center', va='center', fontsize=7.5,
                            color='white', fontfamily='monospace', fontweight='bold')
                cursor = seg['end']
            if cursor < total:
                ax.barh(row, total-cursor, left=cursor, height=0.6, color=BG3, edgecolor='none')
            yticks.append(row); ylabels.append(f"P{pid+1}")

        ax.set_yticks(yticks); ax.set_yticklabels(ylabels, color=TEXT2, fontfamily='monospace', fontsize=9)
        ax.set_xlim(0, total); ax.set_ylim(-0.5, len(pids)-0.5)
        ax.tick_params(axis='x', colors=TEXT3, labelsize=8)
        ax.tick_params(axis='y', length=0)
        for spine in ax.spines.values(): spine.set_edgecolor(BORDER)
        ax.set_facecolor(BG2)
        ax.xaxis.set_minor_locator(matplotlib.ticker.AutoMinorLocator())
        ax.grid(axis='x', color=BORDER, linewidth=0.4, alpha=0.5)

    # ── Table Drawing — FIXED: use matplotlib Table widget ────────────────────
    def _draw_table(self, ax, sorted_r):
        headers = ["Process", "Arrival", "Burst", "Waiting", "Turnaround", "Finish"]
        col_widths = [0.12, 0.14, 0.12, 0.18, 0.22, 0.15]

        # Build data rows
        max_wt  = max(r['waiting']    for r in sorted_r) or 1
        max_tat = max(r['turnaround'] for r in sorted_r) or 1

        table_data = []
        cell_colors = []

        for r in sorted_r:
            wt_col  = ACC2  if r['waiting']/max_wt   < 0.4 else (ACC3 if r['waiting']/max_wt   < 0.7 else ACC4)
            tat_col = ACC2  if r['turnaround']/max_tat < 0.4 else (ACC3 if r['turnaround']/max_tat < 0.7 else TEXT2)
            table_data.append([
                f"P{r['id']+1}",
                str(r['arrival']),
                str(r['burst']),
                str(r['waiting']),
                str(r['turnaround']),
                str(r['finish']),
            ])
            cell_colors.append([
                PROC_LIGHT[r['id'] % 8],
                TEXT2,
                TEXT2,
                wt_col,
                tat_col,
                TEXT3,
            ])

        # Average row
        avg_wt_v  = avg(sorted_r, 'waiting')
        avg_tat_v = avg(sorted_r, 'turnaround')
        table_data.append(["AVERAGE", "—", "—", f"{avg_wt_v:.2f}", f"{avg_tat_v:.2f}", "—"])
        cell_colors.append([TEXT3, TEXT3, TEXT3, ACCENT, ACC2, TEXT3])

        n_rows = len(table_data)
        n_cols = len(headers)

        # Row height in axes coordinates (0-1 space)
        # Give each row equal share; leave a little top margin for the title
        title_space = 0.08
        usable = 1.0 - title_space
        row_h = usable / (n_rows + 1)  # +1 for header

        # Title
        ax.text(0.0, 0.98, "RESULTS TABLE", color=TEXT2, fontfamily='monospace',
                fontsize=9, fontweight='bold', transform=ax.transAxes, va='top')

        col_x = []
        cx = 0.01
        for w in col_widths:
            col_x.append(cx)
            cx += w

        # Header row
        header_y = 1.0 - title_space - row_h * 0.5
        for hdr, x in zip(headers, col_x):
            ax.text(x, header_y, hdr.upper(), color=TEXT3, fontfamily='monospace',
                    fontsize=7.5, fontweight='bold', transform=ax.transAxes, va='center')

        # Separator line under header
        sep_y = 1.0 - title_space - row_h
        ax.axhline(y=sep_y, xmin=0.01, xmax=0.99,
                   color=BORDER, linewidth=0.8, transform=ax.transAxes)

        # Data rows
        for ri, (row_vals, row_cols) in enumerate(zip(table_data, cell_colors)):
            row_y = sep_y - (ri + 0.5) * row_h

            # Alternating background
            if ri % 2 == 0:
                ax.add_patch(plt.Rectangle(
                    (0.0, row_y - row_h * 0.5), 1.0, row_h,
                    transform=ax.transAxes,
                    facecolor=BG3, alpha=0.35, zorder=0
                ))

            for val, col, x in zip(row_vals, row_cols, col_x):
                is_avg_row = (ri == n_rows - 1)
                fs = 8.5 if is_avg_row else 9
                fw = 'bold'
                ax.text(x, row_y, val, color=col,
                        fontfamily='monospace', fontsize=fs, fontweight=fw,
                        transform=ax.transAxes, va='center')

        # Final separator above average row
        final_sep_y = sep_y - (n_rows - 1) * row_h
        ax.axhline(y=final_sep_y, xmin=0.01, xmax=0.99,
                   color=BORDER, linewidth=0.8, transform=ax.transAxes)

        # Clip axes so nothing bleeds out
        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)

    def _style_ax(self, ax, title):
        ax.set_title(title, color=TEXT2, fontfamily='monospace', fontsize=9, loc='left', pad=8)
        ax.tick_params(colors=TEXT3, labelsize=9)
        for spine in ax.spines.values(): spine.set_edgecolor(BORDER)
        ax.yaxis.grid(True, color=BORDER, linewidth=0.5, alpha=0.6)
        ax.set_axisbelow(True)
        ax.tick_params(axis='x', colors=TEXT3); ax.tick_params(axis='y', colors=TEXT3)
        for label in ax.get_xticklabels(): label.set_fontfamily('monospace')


import matplotlib.ticker

if __name__ == "__main__":
    app = CPUSchedulerApp()
    app.mainloop()
