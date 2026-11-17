# -*- coding: utf-8 -*-
"""
Geo Container Loading Planner
Pallet loading planner for 20' / 40' containers.
All dimensions are in millimetres. Requires only Python 3.8+ (Tkinter is included).
"""
import csv
import math
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from dataclasses import dataclass

APP_TITLE = "Geo Container Loading Planner"
EPS = 0.01
GAP = 50.0      # minimum gap between pallets, mm (5 cm)
MAX_H = 2200.0  # maximum pallet height incl. cargo, mm (220 cm)

# Standard INTERNAL dimensions, mm (length, width, height)
CONTAINERS = {
    "20": ("20 ft Container", 5898, 2352, 2393),
    "40": ("40 ft Container", 12032, 2352, 2393),
}

PALETTE = ["#8ecae6", "#ffb703", "#a7c957", "#f4a6a6", "#c8b6ff", "#90e0ef",
           "#f9c74f", "#b5e48c", "#ffadad", "#bdb2ff", "#9bf6ff", "#fdffb6"]


# ----------------------------------------------------------------------------
#  Model and packing algorithm
# ----------------------------------------------------------------------------
@dataclass
class Pallet:
    number: int
    l: float
    w: float
    h: float


def _split_free(free, bx, by, bz, bx1, by1, bz1, stackable):
    new = []
    for f in free:
        fx, fy, fz, fl, fw, fh = f
        fx2, fy2, fz2 = fx + fl, fy + fw, fz + fh
        if (bx >= fx2 - EPS or bx1 <= fx + EPS or by >= fy2 - EPS or
                by1 <= fy + EPS or bz >= fz2 - EPS or bz1 <= fz + EPS):
            new.append(f)
            continue
        if bx > fx + EPS:
            new.append((fx, fy, fz, bx - fx, fw, fh))
        if bx1 < fx2 - EPS:
            new.append((bx1, fy, fz, fx2 - bx1, fw, fh))
        if by > fy + EPS:
            new.append((fx, fy, fz, fl, by - fy, fh))
        if by1 < fy2 - EPS:
            new.append((fx, by1, fz, fl, fy2 - by1, fh))
        if bz > fz + EPS:
            new.append((fx, fy, fz, fl, fw, bz - fz))
        if stackable and bz1 < fz2 - EPS:
            new.append((fx, fy, bz1, fl, fw, fz2 - bz1))
    # drop free spaces fully contained in other free spaces
    keep = []
    for i, a in enumerate(new):
        ax2, ay2, az2 = a[0] + a[3], a[1] + a[4], a[2] + a[5]
        inside = False
        for j, g in enumerate(new):
            if i == j:
                continue
            if (g[0] <= a[0] + EPS and g[1] <= a[1] + EPS and g[2] <= a[2] + EPS and
                    g[0] + g[3] >= ax2 - EPS and g[1] + g[4] >= ay2 - EPS and
                    g[2] + g[5] >= az2 - EPS):
                same = (abs(g[0] - a[0]) < EPS and abs(g[1] - a[1]) < EPS and
                        abs(g[2] - a[2]) < EPS and abs(g[3] - a[3]) < EPS and
                        abs(g[4] - a[4]) < EPS and abs(g[5] - a[5]) < EPS)
                if not same or j < i:
                    inside = True
                    break
        if not inside:
            keep.append(a)
    return keep


def _run_pack(L, W, H, pallets, order_key, pos_key):
    """Pallets stand on the floor only. The GAP between pallets is ensured by
    enlarging every pallet and the container by GAP in length and width
    (no gap is needed at the walls)."""
    free = [(0.0, 0.0, 0.0, float(L) + GAP, float(W) + GAP, float(H))]
    placed, failed = [], []
    for p in sorted(pallets, key=order_key):
        best = None
        orients = [(p.l, p.w)]
        if abs(p.l - p.w) > EPS:
            orients.append((p.w, p.l))
        for dx, dy in orients:
            for f in free:
                fx, fy, fz, fl, fw, fh = f
                if dx + GAP <= fl + EPS and dy + GAP <= fw + EPS and p.h <= fh + EPS:
                    key = pos_key(fx, fy, fz) + (fx + dx,)
                    if best is None or key < best[0]:
                        best = (key, fx, fy, fz, dx, dy)
        if best is None:
            failed.append(p)
            continue
        _, x, y, z, dx, dy = best
        placed.append(dict(n=p.number, x=x, y=y, z=z, dx=dx, dy=dy, h=p.h,
                           level=1, rotated=(abs(dx - p.l) > EPS), pallet=p))
        free = _split_free(free, x, y, z, x + dx + GAP, y + dy + GAP, z + p.h, False)
    return placed, failed


def plan_loading(L, W, H, pallets):
    """Builds the loading plan. Returns (placed, unplaced[(pallet, reason)])."""
    unplaced = []
    candidates = []
    Hmax = min(H, MAX_H)  # height is limited by both the container and the 220 cm rule
    for p in pallets:
        if p.h > Hmax + EPS:
            unplaced.append((p, f"pallet height exceeds the allowed maximum ({fmt(Hmax)} mm)"))
        elif not ((p.l <= L + EPS and p.w <= W + EPS) or
                  (p.w <= L + EPS and p.l <= W + EPS)):
            unplaced.append((p, "pallet is larger than the container interior"))
        else:
            candidates.append(p)

    order_keys = [
        lambda p: (-p.l * p.w, -p.h, p.number),
        lambda p: (-p.h, -p.l * p.w, p.number),
        lambda p: (-p.l * p.w * p.h, p.number),
        lambda p: (-max(p.l, p.w), -p.l * p.w, p.number),
        lambda p: (p.number,),
    ]
    pos_keys = [lambda x, y, z: (z, x, y),
                lambda x, y, z: (x, y, z),
                lambda x, y, z: (x, z, y)]

    best, best_score = None, None
    for ok_ in order_keys:
        for pk in pos_keys:
            placed, failed = _run_pack(L, W, Hmax, candidates, ok_, pk)
            vol = sum(b["dx"] * b["dy"] * b["h"] for b in placed)
            maxx = max((b["x"] + b["dx"] for b in placed), default=0)
            score = (len(placed), vol, -maxx)
            if best_score is None or score > best_score:
                best_score, best = score, (placed, failed)
    placed, failed = best if best else ([], [])
    for p in failed:
        unplaced.append((p, "not enough space left in the container"))

    # loading sequence: from the front wall towards the doors
    placed.sort(key=lambda b: (round(b["x"], 1), round(b["y"], 1)))
    for i, b in enumerate(placed, 1):
        b["order"] = i
    unplaced.sort(key=lambda t: t[0].number)
    return placed, unplaced


# ----------------------------------------------------------------------------
#  Helpers
# ----------------------------------------------------------------------------
def parse_pos(text, name):
    try:
        v = float(str(text).strip().replace(",", ".").replace(" ", ""))
    except ValueError:
        raise ValueError(f"Field \"{name}\": please enter a number.")
    if v <= 0:
        raise ValueError(f"Field \"{name}\" must be greater than zero.")
    return v


def fmt(v):
    return f"{v:.0f}" if abs(v - round(v)) < 0.05 else f"{v:.1f}"


# ----------------------------------------------------------------------------
#  Add / edit pallet dialog
# ----------------------------------------------------------------------------
class PalletDialog(tk.Toplevel):
    def __init__(self, master, number, pallet=None):
        super().__init__(master)
        self.title(f"Pallet #{number}")
        self.resizable(False, False)
        self.configure(bg="white")
        self.transient(master)
        self.result = None
        self.editing = pallet is not None

        frm = ttk.Frame(self, padding=16)
        frm.pack()
        ttk.Label(frm, text=f"Pallet #{number} - dimensions, mm",
                  font=("Segoe UI", 11, "bold")).grid(row=0, column=0, columnspan=2,
                                                      pady=(0, 10))
        self.vars = {}
        defaults = {"Length": "1200", "Width": "800", "Height": "1500"}
        if pallet:
            defaults = {"Length": fmt(pallet.l), "Width": fmt(pallet.w),
                        "Height": fmt(pallet.h)}
        for i, (name, val) in enumerate(defaults.items(), start=1):
            ttk.Label(frm, text=name + ":").grid(row=i, column=0, sticky="e", padx=(0, 8), pady=4)
            v = tk.StringVar(value=val)
            e = ttk.Entry(frm, textvariable=v, width=14)
            e.grid(row=i, column=1, pady=4)
            self.vars[name] = v
            if i == 1:
                e.focus_set()
                e.select_range(0, tk.END)

        ttk.Label(frm, text=f"Max. height: {fmt(MAX_H)} mm (220 cm)",
                  foreground="#555").grid(row=4, column=0, columnspan=2, sticky="w",
                                          pady=(6, 2))
        self.qty = tk.StringVar(value="1")
        if not self.editing:
            ttk.Label(frm, text="Quantity (identical pallets):").grid(row=5, column=0, sticky="e",
                                                               padx=(0, 8), pady=4)
            ttk.Spinbox(frm, from_=1, to=500, textvariable=self.qty, width=12
                        ).grid(row=5, column=1, pady=4)

        btns = ttk.Frame(frm)
        btns.grid(row=6, column=0, columnspan=2, pady=(12, 0))
        ttk.Button(btns, text="OK", command=self.on_ok, width=12).pack(side="left", padx=4)
        ttk.Button(btns, text="Cancel", command=self.destroy, width=12).pack(side="left", padx=4)
        self.bind("<Return>", lambda e: self.on_ok())
        self.bind("<Escape>", lambda e: self.destroy())

        self.update_idletasks()
        x = master.winfo_rootx() + (master.winfo_width() - self.winfo_width()) // 2
        y = master.winfo_rooty() + (master.winfo_height() - self.winfo_height()) // 3
        self.geometry(f"+{max(x, 0)}+{max(y, 0)}")
        self.grab_set()
        self.wait_window(self)

    def on_ok(self):
        try:
            l = parse_pos(self.vars["Length"].get(), "Length")
            w = parse_pos(self.vars["Width"].get(), "Width")
            h = parse_pos(self.vars["Height"].get(), "Height")
            if h > MAX_H:
                raise ValueError(f"Pallet height must not exceed {fmt(MAX_H)} mm (220 cm).")
            qty = 1
            if not self.editing:
                qty = int(float(self.qty.get().replace(",", ".")))
                if qty < 1:
                    raise ValueError("Quantity must be at least 1.")
        except ValueError as e:
            messagebox.showerror(APP_TITLE, str(e), parent=self)
            return
        self.result = (l, w, h, qty)
        self.destroy()


# ----------------------------------------------------------------------------
#  Loading diagram (top view)
# ----------------------------------------------------------------------------
class PlanCanvas(tk.Canvas):
    def __init__(self, master, L, W, placed, level):
        super().__init__(master, bg="white", highlightthickness=0)
        self.L, self.W, self.placed, self.level = L, W, placed, level
        self.bind("<Configure>", lambda e: self.redraw())

    def redraw(self):
        self.delete("all")
        cw, ch = self.winfo_width(), self.winfo_height()
        if cw < 120 or ch < 100:
            return
        s = min((cw - 150) / self.L, (ch - 100) / self.W)
        ox = (cw - self.L * s) / 2 - 15
        top = (ch - self.W * s) / 2
        bottom = top + self.W * s
        right = ox + self.L * s

        # container
        self.create_rectangle(ox, top, right, bottom, fill="#f3f3f3", outline="#333", width=2)
        self.create_line(right, top, right, bottom, fill="#b00020", width=5)
        self.create_text(right + 10, (top + bottom) / 2, text="DOORS", angle=270,
                         fill="#b00020", font=("Segoe UI", 10, "bold"), anchor="center")
        self.create_text(ox - 10, (top + bottom) / 2, text="FRONT WALL", angle=90,
                         fill="#555", font=("Segoe UI", 9), anchor="center")
        self.create_text((ox + right) / 2, top - 14,
                         text=f"Right wall  |  length {fmt(self.L)} mm",
                         fill="#555", font=("Segoe UI", 9))
        self.create_text((ox + right) / 2, bottom + 14,
                         text=f"Left wall  |  width {fmt(self.W)} mm  "
                              f"(view from the doors, Y is measured from the left wall)",
                         fill="#555", font=("Segoe UI", 9))

        for b in sorted(self.placed, key=lambda b: b["level"]):
            if b["level"] > self.level:
                continue
            x1 = ox + b["x"] * s
            x2 = ox + (b["x"] + b["dx"]) * s
            y2 = bottom - b["y"] * s
            y1 = bottom - (b["y"] + b["dy"]) * s
            if b["level"] < self.level:
                self.create_rectangle(x1, y1, x2, y2, fill="#e2e2e2", outline="#aaa")
                continue
            color = PALETTE[(b["n"] - 1) % len(PALETTE)]
            self.create_rectangle(x1, y1, x2, y2, fill=color, outline="#222", width=1.5)
            rw, rh = x2 - x1, y2 - y1
            if min(rw, rh) >= 14:
                fs = int(max(7, min(16, min(rw, rh) / 2.4)))
                cy = (y1 + y2) / 2 - (7 if rw > 80 and rh > 44 else 0)
                self.create_text((x1 + x2) / 2, cy, text=f"#{b['n']}",
                                 font=("Segoe UI", fs, "bold"))
                if rw > 80 and rh > 44:
                    self.create_text((x1 + x2) / 2, cy + fs + 4,
                                     text=f"{fmt(b['dx'])}×{fmt(b['dy'])}×{fmt(b['h'])}",
                                     font=("Segoe UI", 7))


# ----------------------------------------------------------------------------
#  Result window
# ----------------------------------------------------------------------------
class ResultWindow(tk.Toplevel):
    COLS = [("order", "Loading order", 110), ("n", "Pallet #", 80),
            ("size", "Size L×W×H, mm", 150), ("x", "X, mm", 80), ("y", "Y, mm", 80),
            ("rot", "Orientation", 150)]

    def __init__(self, master, cname, dims, placed, unplaced, total):
        super().__init__(master)
        L, W, H = dims
        self.placed, self.unplaced, self.cname = placed, unplaced, cname
        self.configure(bg="white")
        self.title(f"Loading Plan - {cname}")
        self.geometry("1050x720")

        vol_used = sum(b["dx"] * b["dy"] * b["h"] for b in placed)
        used_len = max((b["x"] + b["dx"] for b in placed), default=0)
        txt = (f"{cname}: {fmt(L)} × {fmt(W)} × {fmt(H)} mm.   "
               f"Pallets loaded: {len(placed)} of {total}.   "
               f"Max. pallet height: {fmt(min(H, MAX_H))} mm.   "
               f"Volume utilisation: {vol_used / (L * W * H) * 100:.1f}%.   "
               f"Length used: {fmt(used_len)} mm, free space to the doors: {fmt(L - used_len)} mm.")
        ttk.Label(self, text=txt, wraplength=1000, padding=(10, 8),
                  font=("Segoe UI", 10, "bold")).pack(fill="x")
        if unplaced:
            lines = "; ".join(f"#{p.number} ({r})" for p, r in unplaced)
            tk.Label(self, text="DID NOT FIT: " + lines, fg="#b00020", bg="white", wraplength=1000,
                     justify="left", font=("Segoe UI", 10, "bold"), padx=10
                     ).pack(fill="x", anchor="w")

        nb = ttk.Notebook(self)
        nb.pack(fill="both", expand=True, padx=8, pady=8)
        levels = sorted({b["level"] for b in placed}) or [1]
        for lv in levels:
            f = ttk.Frame(nb)
            PlanCanvas(f, L, W, placed, lv).pack(fill="both", expand=True)
            nb.add(f, text="Loading diagram (top view)")

        lf = ttk.Frame(nb)
        tree = ttk.Treeview(lf, columns=[c[0] for c in self.COLS], show="headings")
        for key, title, w in self.COLS:
            tree.heading(key, text=title)
            tree.column(key, width=w, anchor="center")
        sb = ttk.Scrollbar(lf, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=sb.set)
        tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        for row in self.rows():
            tree.insert("", "end", values=row)
        nb.add(lf, text="Pallet list")

        bot = ttk.Frame(self, padding=(8, 0, 8, 8))
        bot.pack(fill="x")
        ttk.Label(bot, text="X = from the front wall towards the doors, Y = from the left wall "
                            "(view from the doors). Coordinates are the pallet corner; gap between pallets: "
                            f"{fmt(GAP)} mm.",
                  foreground="#555").pack(side="left")
        ttk.Button(bot, text="Close", command=self.destroy).pack(side="right")
        ttk.Button(bot, text="Save as CSV...", command=self.save_csv).pack(side="right", padx=6)

    def rows(self):
        out = []
        for b in sorted(self.placed, key=lambda b: b["order"]):
            out.append((b["order"], b["n"], f"{fmt(b['dx'])} × {fmt(b['dy'])} × {fmt(b['h'])}",
                        fmt(b["x"]), fmt(b["y"]),
                        "rotated 90°" if b["rotated"] else "lengthwise"))
        return out

    def save_csv(self):
        path = filedialog.asksaveasfilename(parent=self, defaultextension=".csv",
                                            filetypes=[("CSV", "*.csv")],
                                            initialfile="plan_zagruzki.csv")
        if not path:
            return
        with open(path, "w", newline="", encoding="utf-8-sig") as f:
            wr = csv.writer(f, delimiter=";")
            wr.writerow([c[1] for c in self.COLS])
            wr.writerows(self.rows())
            if self.unplaced:
                wr.writerow([])
                wr.writerow(["DID NOT FIT"])
                for p, r in self.unplaced:
                    wr.writerow([f"#{p.number}", f"{fmt(p.l)}×{fmt(p.w)}×{fmt(p.h)}", r])
        messagebox.showinfo(APP_TITLE, "Plan saved.", parent=self)


# ----------------------------------------------------------------------------
#  Design helpers
# ----------------------------------------------------------------------------
ORANGE = "#ff9f1c"
FONT_FUN = ("Comic Sans MS", 26, "bold")

# Real external dimensions (mm) - used only to draw the pictures in correct proportion
CONTAINER_LOOK = {
    "20": dict(ext_len=6058, ext_h=2591, body="#3a86c8", dark="#1d4f80", label="20'", ft="20 ft  (6.06 m)"),
    "40": dict(ext_len=12192, ext_h=2591, body="#2fa88a", dark="#17614f", label="40'", ft="40 ft  (12.19 m)"),
}


def mix(c1, c2, t):
    """Blend two #rrggbb colours (t=0 -> c1, t=1 -> c2)."""
    a = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(c2[i:i + 2], 16) for i in (1, 3, 5)]
    return "#%02x%02x%02x" % tuple(int(x + (y - x) * t) for x, y in zip(a, b))


def draw_container(cv, x, y, w, h, body, dark, label=None):
    """Draws a shipping container (side view with doors on the right)."""
    cv.create_oval(x + 6, y + h - 2, x + w - 6, y + h + 12, fill="#e6e9ed", outline="")
    cv.create_rectangle(x, y, x + w, y + h, fill=body, outline=dark, width=2)
    door_w = max(h * 0.55, 10)
    step = max(5, h * 0.09)
    cx = x + 6 + step
    k = 0
    while cx < x + w - door_w - 4:
        cv.create_line(cx, y + h * 0.1, cx, y + h * 0.9,
                       fill=mix(body, dark, 0.45) if k % 2 == 0 else mix(body, "#ffffff", 0.35))
        cx += step
        k += 1
    rail = max(3, h * 0.07)
    cv.create_rectangle(x, y, x + w, y + rail, fill=dark, outline=dark)
    cv.create_rectangle(x, y + h - rail, x + w, y + h, fill=dark, outline=dark)
    # doors
    dx0 = x + w - door_w
    cv.create_rectangle(dx0, y + rail, x + w, y + h - rail, fill=body, outline=dark, width=2)
    cv.create_line(dx0 + door_w / 2, y + rail, dx0 + door_w / 2, y + h - rail, fill=dark, width=2)
    for fx in (0.2, 0.38, 0.62, 0.8):
        rx = dx0 + door_w * fx
        cv.create_line(rx, y + rail + 2, rx, y + h - rail - 2, fill="#d9dde2", width=2)
    hy = y + h / 2
    for fx in (0.44, 0.56):
        hx = dx0 + door_w * fx
        cv.create_rectangle(hx - 1.5, hy - h * 0.1, hx + 1.5, hy + h * 0.1, fill="#333", outline="")
    # corner castings
    c = max(5, h * 0.13)
    for px, py in ((x, y), (x + w - c, y), (x, y + h - c), (x + w - c, y + h - c)):
        cv.create_rectangle(px, py, px + c, py + c, fill="#4a4f55", outline="#222")
    if label and w > 90:
        mx = x + (w - door_w) / 2
        cv.create_rectangle(mx - 30, y + h / 2 - 17, mx + 30, y + h / 2 + 17,
                            fill="white", outline=dark, width=2)
        cv.create_text(mx, y + h / 2, text=label, fill=dark, font=("Segoe UI", 16, "bold"))


def rounded_poly(x1, y1, x2, y2, r):
    return [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2, x2 - r, y2,
            x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]


class FunButton(tk.Canvas):
    """Big, chunky, bouncy 'kids game' style button. Grey until enabled, then orange."""

    def __init__(self, master, text, command, height=96):
        super().__init__(master, height=height, bg="white", highlightthickness=0)
        self.text, self.command = text, command
        self.enabled, self.pressed, self.hover = False, False, False
        self.phase, self._job = 0.0, None
        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<ButtonPress-1>", self._down)
        self.bind("<ButtonRelease-1>", self._up)
        self.bind("<Enter>", lambda e: self._set_hover(True))
        self.bind("<Leave>", lambda e: self._set_hover(False))
        self.bind("<Destroy>", self._on_destroy)
        self._tick()

    def _on_destroy(self, e):
        if e.widget is self and self._job:
            try:
                self.after_cancel(self._job)
            except Exception:
                pass
            self._job = None

    def _set_hover(self, v):
        self.hover = v
        self.redraw()

    def set_enabled(self, v):
        self.enabled = bool(v)
        self.config(cursor="hand2" if self.enabled else "arrow")
        self.redraw()

    def _tick(self):
        self.phase += 0.2
        if self.enabled and not self.pressed:
            self.redraw()
        self._job = self.after(60, self._tick)

    def _down(self, e):
        if self.enabled:
            self.pressed = True
            self.redraw()

    def _up(self, e):
        was = self.pressed
        self.pressed = False
        self.redraw()
        if was and self.enabled and 0 <= e.x <= self.winfo_width() and 0 <= e.y <= self.winfo_height():
            self.command()

    def redraw(self):
        w, h = self.winfo_width(), self.winfo_height()
        if w < 60 or h < 40:
            return
        self.delete("all")
        if self.enabled:
            face, edge, gloss, line, txt = "#ffa62b", "#d96a00", "#ffcf80", "#7a3200", "white"
        else:
            face, edge, gloss, line, txt = "#d5d9de", "#b2b8bf", "#e8ebee", "#8b929a", "#f4f5f6"
        depth = 12
        pad = 16 - (4 if (self.hover and self.enabled) else 0)
        top, bot = 8, h - depth - 8
        if self.pressed:
            off = depth - 4
        elif self.enabled:
            off = -3 * abs(math.sin(self.phase))
        else:
            off = 0
        # shadow / thick bottom edge
        self.create_polygon(rounded_poly(pad, top + depth, w - pad, bot + depth, 28), smooth=True,
                            fill=edge, outline=line, width=3)
        # face
        t, b = top + off, bot + off
        self.create_polygon(rounded_poly(pad, t, w - pad, b, 28), smooth=True,
                            fill=face, outline=line, width=3)
        # gloss
        self.create_polygon(rounded_poly(pad + 22, t + 8, w - pad - 22, t + (b - t) * 0.38, 12),
                            smooth=True, fill=gloss, outline="")
        cy = (t + b) / 2 + (0 if self.enabled else -8)
        cx = w / 2
        for dx, dy in ((-3, 0), (3, 0), (0, -3), (0, 3), (-2, -2), (2, -2), (-2, 2), (2, 2), (0, 4)):
            self.create_text(cx + dx, cy + dy, text=self.text, font=FONT_FUN, fill=line)
        self.create_text(cx, cy, text=self.text, font=FONT_FUN, fill=txt)
        if self.enabled:
            wig = 3 * math.sin(self.phase * 1.5)
            for sx in (cx - 120, cx + 120):
                self.create_text(sx, cy + wig, text="★", font=("Segoe UI", 24), fill="#fff3b0")
                self.create_text(sx, cy + wig, text="☆", font=("Segoe UI", 24), fill=line)
        else:
            self.create_text(cx, cy + 34, text="add pallets to get started",
                             font=("Segoe UI", 10, "bold"), fill=line)


# ----------------------------------------------------------------------------
#  Main window
# ----------------------------------------------------------------------------
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.geometry("1000x760")
        self.minsize(900, 680)
        self.configure(bg="white")
        self.setup_style()
        self.pallets = []
        self.ckey = None
        self.container = ttk.Frame(self)
        self.container.pack(fill="both", expand=True)
        self.show_select()

    def setup_style(self):
        st = ttk.Style(self)
        st.theme_use("clam")
        st.configure(".", background="white", foreground="#1d3557", font=("Segoe UI", 10))
        st.configure("TFrame", background="white")
        st.configure("TLabel", background="white")
        st.configure("TLabelframe", background="white", bordercolor="#d7dde3")
        st.configure("TLabelframe.Label", background="white", foreground="#1d3557",
                     font=("Segoe UI", 10, "bold"))
        st.configure("TButton", background="#f1f4f7", bordercolor="#c9d1d9", padding=(12, 6))
        st.map("TButton", background=[("active", "#e2e8ee")])
        st.configure("Accent.TButton", background="#2a9d8f", foreground="white",
                     bordercolor="#21867a", font=("Segoe UI", 10, "bold"), padding=(14, 6))
        st.map("Accent.TButton", background=[("active", "#21867a")])
        st.configure("TEntry", fieldbackground="white", bordercolor="#c9d1d9")
        st.configure("TCheckbutton", background="white")
        st.configure("Treeview", background="white", fieldbackground="white", rowheight=28,
                     borderwidth=0)
        st.map("Treeview", background=[("selected", "#ffd9a3")], foreground=[("selected", "black")])
        st.configure("Treeview.Heading", background="#eef2f6", foreground="#1d3557",
                     font=("Segoe UI", 10, "bold"), relief="flat", padding=6)
        st.configure("TNotebook", background="white", bordercolor="#d7dde3")
        st.configure("TNotebook.Tab", background="#eef2f6", padding=(14, 6))
        st.map("TNotebook.Tab", background=[("selected", "white")])

    def clear(self):
        for w in self.container.winfo_children():
            w.destroy()

    # ---------- screen 1: container selection ----------
    def show_select(self):
        self.clear()
        fr = ttk.Frame(self.container, padding=20)
        fr.pack(fill="both", expand=True)
        ttk.Label(fr, text=APP_TITLE, font=("Segoe UI", 24, "bold"),
                  foreground="#1d3557").pack(pady=(14, 4))
        tk.Frame(fr, height=5, width=140, bg=ORANGE).pack()
        ttk.Label(fr, text="Select container type", font=("Segoe UI", 13),
                  foreground="#5c6b7a").pack(pady=(14, 10))

        cards = ttk.Frame(fr)
        cards.pack(expand=True)
        scale = 0.038  # px per mm - SAME scale for both pictures, so sizes are comparable
        for col, key in enumerate(("20", "40")):
            look = CONTAINER_LOOK[key]
            name, L, W, H = CONTAINERS[key]
            cw, ch = look["ext_len"] * scale, look["ext_h"] * scale
            card = tk.Frame(cards, bg="white", highlightthickness=3,
                            highlightbackground="#d7dde3", highlightcolor=ORANGE,
                            padx=16, pady=14, cursor="hand2")
            card.grid(row=0, column=col, padx=18, sticky="s")
            cv = tk.Canvas(card, width=cw + 24, height=ch + 62, bg="white", highlightthickness=0)
            cv.pack()
            draw_container(cv, 12, 14, cw, ch, look["body"], look["dark"], look["label"])
            # dimension arrow
            ay = 14 + ch + 26
            cv.create_line(12, ay, 12 + cw, ay, fill="#5c6b7a", arrow="both")
            cv.create_text(12 + cw / 2, ay + 14, text=look["ft"], fill="#5c6b7a",
                           font=("Segoe UI", 9))
            tk.Label(card, text=name, font=("Segoe UI", 14, "bold"), bg="white",
                     fg="#1d3557").pack(pady=(4, 0))
            tk.Label(card, text=f"interior: {L} × {W} × {H} mm", bg="white",
                     fg="#5c6b7a").pack(pady=(0, 8))
            ttk.Button(card, text="Select", width=18, style="Accent.TButton",
                       command=lambda k=key: self.show_main(k)).pack()

            def hover(on, c=card):
                c.configure(highlightbackground=ORANGE if on else "#d7dde3")

            def bind_all(wid, c=card, k=key):
                if not isinstance(wid, ttk.Button):
                    wid.bind("<Button-1>", lambda e, kk=k: self.show_main(kk))
                wid.bind("<Enter>", lambda e: hover(True), add="+")
                wid.bind("<Leave>", lambda e: hover(False), add="+")
                for ch_ in wid.winfo_children():
                    bind_all(ch_)
            bind_all(card)

    # ---------- screen 2: container and pallets ----------
    def show_main(self, key):
        self.ckey = key
        name, L, W, H = CONTAINERS[key]
        look = CONTAINER_LOOK[key]
        self.clear()
        fr = ttk.Frame(self.container, padding=14)
        fr.pack(fill="both", expand=True)

        head = ttk.Frame(fr)
        head.pack(fill="x")
        ttk.Label(head, text=name, font=("Segoe UI", 18, "bold")).pack(side="left")
        sc = 0.018
        pw, ph = look["ext_len"] * sc, look["ext_h"] * sc
        pic = tk.Canvas(head, width=pw + 16, height=ph + 18, bg="white", highlightthickness=0)
        pic.pack(side="left", padx=16)
        draw_container(pic, 8, 4, pw, ph, look["body"], look["dark"])
        ttk.Button(head, text="← Change container", command=self.show_select).pack(side="right")

        box = ttk.LabelFrame(fr, text="Container interior dimensions, mm (editable)", padding=10)
        box.pack(fill="x", pady=10)
        self.dim_vars = {}
        for i, (lbl, val) in enumerate((("Length", L), ("Width", W), ("Height", H))):
            ttk.Label(box, text=lbl + ":").grid(row=0, column=i * 2, padx=(0 if i == 0 else 20, 6))
            v = tk.StringVar(value=str(val))
            ttk.Entry(box, textvariable=v, width=10).grid(row=0, column=i * 2 + 1)
            self.dim_vars[lbl] = v

        ttk.Label(fr, text=f"Rules: pallets stand on the floor only (no stacking), may be rotated by 90°, "
                           f"minimum gap between pallets {fmt(GAP)} mm, "
                           f"max. pallet height {fmt(MAX_H)} mm.",
                  foreground="#5c6b7a", wraplength=900).pack(fill="x", pady=(0, 8))

        pf = ttk.LabelFrame(fr, text="Pallets", padding=10)
        pf.pack(fill="both", expand=True)
        bar = ttk.Frame(pf)
        bar.pack(fill="x", pady=(0, 8))
        ttk.Button(bar, text="+ Add pallet", style="Accent.TButton",
                   command=self.add_pallet).pack(side="left")
        ttk.Button(bar, text="Edit", command=self.edit_pallet).pack(side="left", padx=6)
        ttk.Button(bar, text="Delete", command=self.delete_pallet).pack(side="left")
        ttk.Button(bar, text="Clear all", command=self.clear_pallets).pack(side="left", padx=6)
        self.count_lbl = ttk.Label(bar, text="", font=("Segoe UI", 10, "bold"))
        self.count_lbl.pack(side="right")

        cols = ("n", "l", "w", "h")
        tf = ttk.Frame(pf)
        tf.pack(fill="both", expand=True)
        self.tree = ttk.Treeview(tf, columns=cols, show="headings", selectmode="extended")
        for c, t, w in (("n", "#", 60), ("l", "Length, mm", 110), ("w", "Width, mm", 110),
                        ("h", "Height, mm", 110)):
            self.tree.heading(c, text=t)
            self.tree.column(c, width=w, anchor="center")
        self.tree.tag_configure("odd", background="#f6f8fa")
        sb = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.tree.bind("<Double-1>", lambda e: self.edit_pallet())
        self.tree.bind("<Delete>", lambda e: self.delete_pallet())

        self.load_btn = FunButton(fr, "LOAD", self.load)
        self.load_btn.pack(fill="x", pady=(12, 0))
        self.refresh()

    def refresh(self):
        for i in self.tree.get_children():
            self.tree.delete(i)
        for idx, p in enumerate(self.pallets):
            self.tree.insert("", "end", iid=str(p.number),
                             values=(p.number, fmt(p.l), fmt(p.w), fmt(p.h)),
                             tags=("odd",) if idx % 2 else ())
        self.count_lbl.config(text=f"Total pallets: {len(self.pallets)}")
        self.load_btn.set_enabled(len(self.pallets) > 0)

    def renumber(self):
        for i, p in enumerate(self.pallets, 1):
            p.number = i

    def add_pallet(self):
        dlg = PalletDialog(self, len(self.pallets) + 1)
        if dlg.result:
            l, w, h, qty = dlg.result
            for _ in range(qty):
                self.pallets.append(Pallet(len(self.pallets) + 1, l, w, h))
            self.refresh()

    def selected(self):
        return [int(i) for i in self.tree.selection()]

    def edit_pallet(self):
        sel = self.selected()
        if not sel:
            messagebox.showinfo(APP_TITLE, "Please select a pallet in the list.")
            return
        p = self.pallets[sel[0] - 1]
        dlg = PalletDialog(self, p.number, p)
        if dlg.result:
            p.l, p.w, p.h, _ = dlg.result
            self.refresh()

    def delete_pallet(self):
        sel = set(self.selected())
        if not sel:
            return
        self.pallets = [p for p in self.pallets if p.number not in sel]
        self.renumber()
        self.refresh()

    def clear_pallets(self):
        if self.pallets and messagebox.askyesno(APP_TITLE, "Remove all pallets from the list?"):
            self.pallets = []
            self.refresh()

    def load(self):
        try:
            L = parse_pos(self.dim_vars["Length"].get(), "Container length")
            W = parse_pos(self.dim_vars["Width"].get(), "Container width")
            H = parse_pos(self.dim_vars["Height"].get(), "Container height")
        except ValueError as e:
            messagebox.showerror(APP_TITLE, str(e))
            return
        if not self.pallets:
            messagebox.showinfo(APP_TITLE, "Please add at least one pallet first.")
            return
        self.config(cursor="watch")
        self.update_idletasks()
        placed, unplaced = plan_loading(L, W, H, self.pallets)
        self.config(cursor="")
        ResultWindow(self, CONTAINERS[self.ckey][0], (L, W, H), placed, unplaced,
                     len(self.pallets))


def main():
    try:  # sharp rendering on Windows with display scaling
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    App().mainloop()


if __name__ == "__main__":
    main()
