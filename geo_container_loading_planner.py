# -*- coding: utf-8 -*-
"""
Geo Container Loading Planner
Pallet loading planner for 20' / 40' containers.
All dimensions are in millimetres. Requires only Python 3.8+ (Tkinter is included).
"""
import csv
import math
import os
import sys
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from dataclasses import dataclass

APP_TITLE = "Geo Container Loading Planner"
EPS = 0.01
GAP = 25.0      # clearance between loads AND to walls / doors, mm (2.5 cm)
MAX_H = 2200.0  # maximum load height, mm (220 cm)

# Standard INTERNAL dimensions, mm (length, width, height)
CONTAINERS = {
    "20": ("20 ft Container", 5898, 2352, 2393),
    "40": ("40 ft Container", 12032, 2352, 2393),
}

PALETTE = ["#9ec5e8", "#f2c77b", "#a8d5ba", "#f0a8a8", "#c3b8f0", "#8fd3e0",
           "#f5dc8a", "#bfe3a0", "#f7b9b9", "#b7c4f4", "#9fe0d6", "#e6e1a1"]

# Corporate colours (website theme colour is #00153b; the rest are matching tints)
NAVY = "#00153b"
NAVY_HOVER = "#0b2d66"
NAVY_DARK = "#000b22"
BLUE = "#2c6fb7"
MUTED = "#5b6b84"
BORDER = "#d5dbe6"


# ----------------------------------------------------------------------------
#  Model and packing algorithm
# ----------------------------------------------------------------------------
@dataclass
class Pallet:
    """A load: either a pallet or a winch."""
    number: int
    l: float
    w: float
    h: float
    kind: str = "Pallet"


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


def _run_pack(Le, We, H, pallets, order_key, pos_key):
    """Loads stand on the floor only. The GAP between loads is ensured by enlarging every
    load and the usable floor by GAP in length and width. Le/We is the usable floor
    (container interior minus the clearance at the walls and doors)."""
    free = [(0.0, 0.0, 0.0, float(Le) + GAP, float(We) + GAP, float(H))]
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
        placed.append(dict(n=p.number, kind=p.kind, x=x, y=y, z=z, dx=dx, dy=dy, h=p.h,
                           level=1, rotated=(abs(dx - p.l) > EPS), pallet=p))
        free = _split_free(free, x, y, z, x + dx + GAP, y + dy + GAP, z + p.h, False)
    return placed, failed


def plan_loading(L, W, H, pallets):
    """Builds the loading plan. Returns (placed, unplaced[(load, reason)])."""
    unplaced = []
    candidates = []
    Hmax = min(H, MAX_H)  # height is limited by both the container and the 220 cm rule
    Le, We = L - 2 * GAP, W - 2 * GAP  # usable floor after clearance from walls and doors
    for p in pallets:
        if p.h > Hmax + EPS:
            unplaced.append((p, f"height exceeds the allowed maximum ({fmt(Hmax)} mm)"))
        elif Le <= 0 or We <= 0 or not ((p.l <= Le + EPS and p.w <= We + EPS) or
                                        (p.w <= Le + EPS and p.l <= We + EPS)):
            unplaced.append((p, f"does not fit the container interior "
                                f"({fmt(GAP)} mm clearance is required on all sides)"))
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
    if candidates:
        for ok_ in order_keys:
            for pk in pos_keys:
                placed, failed = _run_pack(Le, We, Hmax, candidates, ok_, pk)
                vol = sum(b["dx"] * b["dy"] * b["h"] for b in placed)
                maxx = max((b["x"] + b["dx"] for b in placed), default=0)
                score = (len(placed), vol, -maxx)
                if best_score is None or score > best_score:
                    best_score, best = score, (placed, failed)
    placed, failed = best if best else ([], [])
    for p in failed:
        unplaced.append((p, "not enough space left in the container"))

    # shift everything by the clearance so that walls and doors keep their gap
    for b in placed:
        b["x"] += GAP
        b["y"] += GAP

    # loading sequence: from the front wall towards the doors
    placed.sort(key=lambda b: (round(b["x"], 1), round(b["y"], 1)))
    for i, b in enumerate(placed, 1):
        b["order"] = i
    unplaced.sort(key=lambda t: t[0].number)
    return placed, unplaced


# ----------------------------------------------------------------------------
#  Helpers
# ----------------------------------------------------------------------------
def group_unplaced(unplaced):
    """['#24 Pallet, #25 Winch  -  reason', ...] grouped by reason."""
    groups = {}
    for p, r in unplaced:
        groups.setdefault(r, []).append(f"#{p.number} {p.kind}")
    return [", ".join(items) + "  -  " + r for r, items in groups.items()]


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
#  Add / edit load dialog
# ----------------------------------------------------------------------------
KINDS = ("Pallet", "Winch")


class LoadDialog(tk.Toplevel):
    def __init__(self, master, number, load=None):
        super().__init__(master)
        self.title("Edit load" if load else "Add load")
        self.resizable(False, False)
        self.configure(bg="white")
        self.transient(master)
        self.result = None
        self.editing = load is not None

        frm = ttk.Frame(self, padding=16)
        frm.pack()
        ttk.Label(frm, text=f"Load #{number} - type and dimensions",
                  font=("Segoe UI", 11, "bold")).grid(row=0, column=0, columnspan=2, pady=(0, 10))

        ttk.Label(frm, text="Type:").grid(row=1, column=0, sticky="e", padx=(0, 8), pady=4)
        self.kind = tk.StringVar(value=load.kind if load else "Pallet")
        kf = ttk.Frame(frm)
        kf.grid(row=1, column=1, sticky="w")
        for k in KINDS:
            ttk.Radiobutton(kf, text=k, value=k, variable=self.kind).pack(side="left", padx=(0, 14))

        self.vars = {}
        defaults = {"Length": "1200", "Width": "800", "Height": "1500"}
        if load:
            defaults = {"Length": fmt(load.l), "Width": fmt(load.w), "Height": fmt(load.h)}
        for i, (name, val) in enumerate(defaults.items(), start=2):
            ttk.Label(frm, text=name + ", mm:").grid(row=i, column=0, sticky="e", padx=(0, 8), pady=4)
            v = tk.StringVar(value=val)
            e = ttk.Entry(frm, textvariable=v, width=14)
            e.grid(row=i, column=1, pady=4, sticky="w")
            self.vars[name] = v
            if i == 2:
                e.focus_set()
                e.select_range(0, tk.END)

        ttk.Label(frm, text=f"Max. height: {fmt(MAX_H)} mm (220 cm)",
                  foreground=MUTED).grid(row=5, column=0, columnspan=2, sticky="w", pady=(6, 2))
        self.qty = tk.StringVar(value="1")
        if not self.editing:
            ttk.Label(frm, text="Quantity (identical):").grid(row=6, column=0, sticky="e",
                                                              padx=(0, 8), pady=4)
            ttk.Spinbox(frm, from_=1, to=500, textvariable=self.qty, width=12
                        ).grid(row=6, column=1, pady=4, sticky="w")

        btns = ttk.Frame(frm)
        btns.grid(row=7, column=0, columnspan=2, pady=(12, 0))
        ttk.Button(btns, text="OK", command=self.on_ok, width=12,
                   style="Accent.TButton").pack(side="left", padx=4)
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
                raise ValueError(f"Height must not exceed {fmt(MAX_H)} mm (220 cm).")
            qty = 1
            if not self.editing:
                qty = int(float(self.qty.get().replace(",", ".")))
                if qty < 1:
                    raise ValueError("Quantity must be at least 1.")
        except ValueError as e:
            messagebox.showerror(APP_TITLE, str(e), parent=self)
            return
        self.result = (self.kind.get(), l, w, h, qty)
        self.destroy()


# ----------------------------------------------------------------------------
#  Loading diagram (top view) - on screen
# ----------------------------------------------------------------------------
class PlanCanvas(tk.Canvas):
    def __init__(self, master, L, W, placed):
        super().__init__(master, bg="white", highlightthickness=0)
        self.L, self.W, self.placed = L, W, placed
        self.bind("<Configure>", lambda e: self.redraw())

    def redraw(self):
        self.delete("all")
        cw, ch = self.winfo_width(), self.winfo_height()
        if cw < 120 or ch < 100:
            return
        s = min((cw - 130) / self.L, (ch - 100) / self.W)
        ox = (cw - self.L * s) / 2 - 15
        top = (ch - self.W * s) / 2
        bottom = top + self.W * s
        right = ox + self.L * s

        self.create_rectangle(ox, top, right, bottom, fill="#f3f3f3", outline="#333", width=2)
        self.create_line(right, top, right, bottom, fill="#b00020", width=5)
        self.create_text(right + 14, (top + bottom) / 2, text="DOORS", angle=270,
                         fill="#b00020", font=("Segoe UI", 10, "bold"), anchor="center")
        self.create_text((ox + right) / 2, top - 14,
                         text=f"Right wall  |  length {fmt(self.L)} mm",
                         fill=MUTED, font=("Segoe UI", 9))
        self.create_text((ox + right) / 2, bottom + 14,
                         text=f"Left wall  |  width {fmt(self.W)} mm  "
                              f"(view from the doors, Y is measured from the left wall)",
                         fill=MUTED, font=("Segoe UI", 9))

        for b in self.placed:
            x1 = ox + b["x"] * s
            x2 = ox + (b["x"] + b["dx"]) * s
            y2 = bottom - b["y"] * s
            y1 = bottom - (b["y"] + b["dy"]) * s
            color = PALETTE[(b["n"] - 1) % len(PALETTE)]
            self.create_rectangle(x1, y1, x2, y2, fill=color, outline="#222", width=1.5)
            rw, rh = x2 - x1, y2 - y1
            if min(rw, rh) < 14:
                continue
            fs = int(max(7, min(16, min(rw, rh) / 2.6)))
            lines = [(f"#{b['n']}", ("Segoe UI", fs, "bold"), fs)]
            if rw > 55 and rh > 40:
                sz = max(7, int(fs * 0.62))
                lines.append((b["kind"], ("Segoe UI", sz), sz))
            if rw > 80 and rh > 56:
                sz = max(7, int(fs * 0.55))
                lines.append((f"{fmt(b['dx'])}×{fmt(b['dy'])}×{fmt(b['h'])}", ("Segoe UI", sz), sz))
            heights = [sz * 1.55 for _, _, sz in lines]
            yy = (y1 + y2) / 2 - sum(heights) / 2
            for (text, font, _), hh in zip(lines, heights):
                self.create_text((x1 + x2) / 2, yy + hh / 2, text=text, font=font)
                yy += hh


# ----------------------------------------------------------------------------
#  Loading diagram -> image (PNG / PDF export, needs Pillow)
# ----------------------------------------------------------------------------
def _pil_font(size, bold=False):
    from PIL import ImageFont
    names = (["segoeuib.ttf", "arialbd.ttf", "Arial Bold.ttf", "DejaVuSans-Bold.ttf"] if bold
             else ["segoeui.ttf", "arial.ttf", "Arial.ttf", "DejaVuSans.ttf"])
    for n in names:
        try:
            return ImageFont.truetype(n, int(size))
        except OSError:
            pass
    try:
        return ImageFont.load_default(size=int(size))
    except TypeError:
        return ImageFont.load_default()


def _text_center(draw, cx, cy, text, font, fill):
    bb = draw.textbbox((0, 0), text, font=font)
    draw.text((cx - (bb[0] + bb[2]) / 2, cy - (bb[1] + bb[3]) / 2), text, font=font, fill=fill)


def _logo_pil(height):
    from PIL import Image
    res = getattr(Image, "Resampling", Image)
    for d in _resource_dirs():
        for name in ("logo.png", "logo.gif"):
            p = os.path.join(d, name)
            if os.path.exists(p):
                try:
                    im = Image.open(p).convert("RGBA")
                    r = height / im.height
                    return im.resize((max(1, int(im.width * r)), int(height)), res.LANCZOS)
                except Exception:
                    pass
    return None


def render_plan_image(cname, dims, placed, unplaced, total):
    """Draws the loading plan as a PIL image (top view with header, summary and footer)."""
    import textwrap
    from PIL import Image, ImageDraw
    L, W, H = dims
    IW = 2400
    ml, mr = 120, 200
    s = (IW - ml - mr) / L
    ch = W * s

    vol_used = sum(b["dx"] * b["dy"] * b["h"] for b in placed)
    used_len = max((b["x"] + b["dx"] for b in placed), default=0)
    lines = [
        (f"Container interior: {fmt(L)} × {fmt(W)} × {fmt(H)} mm    |    "
         f"Max. load height: {fmt(min(H, MAX_H))} mm    |    Clearance: {fmt(GAP)} mm", MUTED),
        (f"Loads placed: {len(placed)} of {total}    |    Volume utilisation: "
         f"{vol_used / (L * W * H) * 100:.1f}%    |    Length used: {fmt(used_len)} mm, "
         f"free towards the doors: {fmt(L - used_len)} mm", NAVY),
    ]
    if unplaced:
        for g_ in group_unplaced(unplaced):
            for k, ln in enumerate(textwrap.wrap(("DID NOT FIT:  " if not lines[2:] else "") + g_, 120)):
                lines.append((ln, "#b00020"))

    y_lines = 215
    top = y_lines + 46 * len(lines) + 90
    bottom = top + ch
    IH = int(bottom + 90 + 84)
    img = Image.new("RGB", (IW, IH), "white")
    d = ImageDraw.Draw(img)

    # header
    d.rectangle([0, 0, IW, 16], fill=NAVY)
    d.text((60, 46), "Loading Plan", font=_pil_font(66, True), fill=NAVY)
    d.text((62, 128), cname, font=_pil_font(38), fill=MUTED)
    logo = _logo_pil(120)
    if logo:
        img.paste(logo, (IW - 60 - logo.width, 40), logo)
    else:
        d.text((IW - 60, 56), "GEO MARINE", font=_pil_font(54, True), fill=NAVY, anchor="ra")
        d.text((IW - 60, 120), "SURVEY SYSTEMS", font=_pil_font(30, True), fill=BLUE, anchor="ra")
    d.line([60, 190, IW - 60, 190], fill=BORDER, width=3)
    y = y_lines
    for text, col in lines:
        d.text((60, y), text, font=_pil_font(32), fill=col)
        y += 46

    # container
    ox = ml
    right = ox + L * s
    d.rectangle([ox, top, right, bottom], fill="#f3f3f3", outline="#333333", width=5)
    d.line([right, top, right, bottom], fill="#b00020", width=14)
    f_door = _pil_font(36, True)
    bb = d.textbbox((0, 0), "DOORS", font=f_door)
    tmp = Image.new("RGBA", (bb[2] - bb[0] + 12, bb[3] - bb[1] + 12), (255, 255, 255, 0))
    ImageDraw.Draw(tmp).text((6 - bb[0], 6 - bb[1]), "DOORS", font=f_door, fill="#b00020")
    rot = tmp.rotate(270, expand=True)
    img.paste(rot, (int(right + 30), int((top + bottom) / 2 - rot.height / 2)), rot)
    _text_center(d, (ox + right) / 2, top - 30, f"Right wall   |   length {fmt(L)} mm",
                 _pil_font(30), MUTED)
    _text_center(d, (ox + right) / 2, bottom + 34,
                 f"Left wall   |   width {fmt(W)} mm   (view from the doors)", _pil_font(30), MUTED)

    # loads
    for b in placed:
        x1 = ox + b["x"] * s
        x2 = ox + (b["x"] + b["dx"]) * s
        y2 = bottom - b["y"] * s
        y1 = bottom - (b["y"] + b["dy"]) * s
        color = PALETTE[(b["n"] - 1) % len(PALETTE)]
        d.rectangle([x1, y1, x2, y2], fill=color, outline="#222222", width=3)
        rw, rh = x2 - x1, y2 - y1
        if min(rw, rh) < 30:
            continue
        fs = int(max(16, min(46, min(rw, rh) / 4.2)))
        items = [(f"#{b['n']}", fs, True)]
        if rh > fs * 2.6:
            items.append((b["kind"], int(fs * 0.62), False))
        if rh > fs * 3.4:
            items.append((f"{fmt(b['dx'])}×{fmt(b['dy'])}×{fmt(b['h'])}", int(fs * 0.55), False))
        items = [it for it in items
                 if d.textlength(it[0], font=_pil_font(it[1], it[2])) <= rw * 0.96] or items[:1]
        hs = [int(sz * 1.35) for _, sz, _ in items]
        yy = (y1 + y2) / 2 - sum(hs) / 2
        for (text, sz, bold), hh in zip(items, hs):
            _text_center(d, (x1 + x2) / 2, yy + hh / 2, text, _pil_font(sz, bold), "#111111")
            yy += hh

    # footer
    d.rectangle([0, IH - 70, IW, IH], fill=NAVY)
    d.text((60, IH - 52), "© Geo Marine Survey Systems   |   Rotterdam, The Netherlands",
           font=_pil_font(28), fill="#c9d4e8")
    d.text((IW - 60, IH - 52), "Geo Container Loading Planner", font=_pil_font(28),
           fill="#c9d4e8", anchor="ra")
    return img


# ----------------------------------------------------------------------------
#  Result window
# ----------------------------------------------------------------------------
class ResultWindow(tk.Toplevel):
    COLS = [("order", "Loading order", 110), ("n", "#", 60), ("kind", "Type", 90),
            ("size", "Size L×W×H, mm", 150), ("x", "X, mm", 80), ("y", "Y, mm", 80),
            ("rot", "Orientation", 150)]

    def __init__(self, master, cname, dims, placed, unplaced, total):
        super().__init__(master)
        L, W, H = dims
        self.placed, self.unplaced, self.cname = placed, unplaced, cname
        self.dims, self.total = dims, total
        self.title(f"Loading Plan - {cname}")
        self.configure(bg="white")
        self.geometry("1050x800")
        build_header(self, "Loading Plan")

        vol_used = sum(b["dx"] * b["dy"] * b["h"] for b in placed)
        used_len = max((b["x"] + b["dx"] for b in placed), default=0)
        txt = (f"{cname}: {fmt(L)} × {fmt(W)} × {fmt(H)} mm.   "
               f"Loads placed: {len(placed)} of {total}.   "
               f"Max. load height: {fmt(min(H, MAX_H))} mm.   "
               f"Volume utilisation: {vol_used / (L * W * H) * 100:.1f}%.   "
               f"Length used: {fmt(used_len)} mm, free towards the doors: {fmt(L - used_len)} mm.")
        ttk.Label(self, text=txt, wraplength=1000, padding=(10, 8),
                  font=("Segoe UI", 10, "bold")).pack(fill="x")
        if unplaced:
            lines = "\n".join(group_unplaced(unplaced))
            tk.Label(self, text="DID NOT FIT:\n" + lines, fg="#b00020", bg="white",
                     wraplength=1000, justify="left", font=("Segoe UI", 10, "bold"), padx=10
                     ).pack(fill="x", anchor="w")

        bot = ttk.Frame(self, padding=(10, 0, 10, 10))
        bot.pack(side="bottom", fill="x")
        ttk.Label(bot, text=f"Clearance of {fmt(GAP)} mm is kept between loads and to the walls "
                            f"and doors.", foreground=MUTED).pack(side="left")
        ttk.Button(bot, text="Close", command=self.destroy).pack(side="right")
        ttk.Button(bot, text="Save as CSV…", command=self.save_csv).pack(side="right", padx=6)
        ttk.Button(bot, text="Save as PDF", style="Accent.TButton",
                   command=lambda: self.export("pdf")).pack(side="right", padx=6)
        ttk.Button(bot, text="Save as PNG", style="Accent.TButton",
                   command=lambda: self.export("png")).pack(side="right")

        PlanCanvas(self, L, W, placed).pack(fill="both", expand=True, padx=8, pady=8)

    def rows(self):
        out = []
        for b in sorted(self.placed, key=lambda b: b["order"]):
            out.append((b["order"], b["n"], b["kind"],
                        f"{fmt(b['dx'])} × {fmt(b['dy'])} × {fmt(b['h'])}",
                        fmt(b["x"]), fmt(b["y"]),
                        "rotated 90°" if b["rotated"] else "lengthwise"))
        return out

    def export(self, kind):
        try:
            img = render_plan_image(self.cname, self.dims, self.placed, self.unplaced, self.total)
        except ImportError:
            messagebox.showerror(APP_TITLE, "Image export needs the Pillow library.\n"
                                            "Install it with:  pip install pillow", parent=self)
            return
        ext = "." + kind
        path = filedialog.asksaveasfilename(
            parent=self, defaultextension=ext, initialfile="loading_plan" + ext,
            filetypes=[("PNG image", "*.png")] if kind == "png" else [("PDF document", "*.pdf")])
        if not path:
            return
        try:
            if kind == "png":
                img.save(path)
            else:
                img.convert("RGB").save(path, "PDF", resolution=200.0)
        except Exception as e:
            messagebox.showerror(APP_TITLE, f"Could not save the file:\n{e}", parent=self)
            return
        messagebox.showinfo(APP_TITLE, "Saved.", parent=self)

    def save_csv(self):
        path = filedialog.asksaveasfilename(parent=self, defaultextension=".csv",
                                            filetypes=[("CSV", "*.csv")],
                                            initialfile="loading_plan.csv")
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
                    wr.writerow([f"#{p.number}", p.kind,
                                 f"{fmt(p.l)}×{fmt(p.w)}×{fmt(p.h)}", r])
        messagebox.showinfo(APP_TITLE, "Saved.", parent=self)


# ----------------------------------------------------------------------------
#  Design helpers
# ----------------------------------------------------------------------------

# Real external dimensions (mm) - used only to draw the pictures in correct proportion
CONTAINER_LOOK = {
    "20": dict(ext_len=6058, ext_h=2591, body="#2c6fb7", dark="#143e73", label="20'", ft="20 ft  (6.06 m)"),
    "40": dict(ext_len=12192, ext_h=2591, body="#0b2a5e", dark="#00153b", label="40'", ft="40 ft  (12.19 m)"),
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


def _resource_dirs():
    dirs = []
    if getattr(sys, "_MEIPASS", None):
        dirs.append(sys._MEIPASS)
    if getattr(sys, "frozen", False):
        dirs.append(os.path.dirname(sys.executable))
    dirs.append(os.path.dirname(os.path.abspath(__file__)))
    return dirs


def make_logo(parent, height=46):
    """Company logo from logo.png / logo.gif next to the program; text wordmark as fallback."""
    for d in _resource_dirs():
        for name in ("logo.png", "logo.gif"):
            path = os.path.join(d, name)
            if os.path.exists(path):
                try:
                    img = tk.PhotoImage(file=path)
                    ratio = img.height() / height
                    if ratio >= 1.5:
                        img = img.subsample(int(round(ratio)))
                    elif ratio <= 0.67:
                        img = img.zoom(int(round(1 / ratio)))
                    lbl = tk.Label(parent, image=img, bg="white")
                    lbl.image = img  # keep a reference
                    return lbl
                except tk.TclError:
                    pass
    cv = tk.Canvas(parent, width=215, height=height, bg="white", highlightthickness=0)
    cv.create_text(212, height * 0.36, text="GEO MARINE", anchor="e", fill=NAVY,
                   font=("Segoe UI", 17, "bold"))
    cv.create_text(212, height * 0.76, text="SURVEY SYSTEMS", anchor="e", fill=BLUE,
                   font=("Segoe UI", 9, "bold"))
    return cv


def build_header(master, title=APP_TITLE):
    """White header: navy strip on top, title on the left, company logo top right."""
    bar = tk.Frame(master, bg="white")
    bar.pack(side="top", fill="x")
    tk.Frame(bar, bg=NAVY, height=6).pack(side="top", fill="x")
    row = tk.Frame(bar, bg="white")
    row.pack(side="top", fill="x", padx=18, pady=8)
    tk.Label(row, text=title, bg="white", fg=NAVY, font=("Segoe UI", 15, "bold")).pack(side="left")
    make_logo(row).pack(side="right")
    tk.Frame(bar, bg=BORDER, height=1).pack(side="bottom", fill="x")
    return bar


def build_footer(master):
    foot = tk.Frame(master, bg=NAVY, height=26)
    foot.pack(side="bottom", fill="x")
    foot.pack_propagate(False)
    tk.Label(foot, text="© Geo Marine Survey Systems  |  Rotterdam, The Netherlands",
             bg=NAVY, fg="#c9d4e8", font=("Segoe UI", 8)).pack(side="left", padx=16)
    return foot


def rounded_poly(x1, y1, x2, y2, r):
    return [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2, x2 - r, y2,
            x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]


class LoadButton(tk.Canvas):
    """Large, flat, dark-navy primary button. Grey until at least one pallet exists."""

    def __init__(self, master, text, command, height=64):
        super().__init__(master, height=height, bg="white", highlightthickness=0)
        self.text, self.command = text, command
        self.enabled, self.pressed, self.hover = False, False, False
        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<ButtonPress-1>", self._down)
        self.bind("<ButtonRelease-1>", self._up)
        self.bind("<Enter>", lambda e: self._set_hover(True))
        self.bind("<Leave>", lambda e: self._set_hover(False))

    def _set_hover(self, v):
        self.hover = v
        self.redraw()

    def set_enabled(self, v):
        self.enabled = bool(v)
        self.config(cursor="hand2" if self.enabled else "arrow")
        self.redraw()

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
        if w < 60 or h < 30:
            return
        self.delete("all")
        if not self.enabled:
            fill, fg = "#cfd6e2", "#f7f9fc"
        elif self.pressed:
            fill, fg = NAVY_DARK, "white"
        elif self.hover:
            fill, fg = NAVY_HOVER, "white"
        else:
            fill, fg = NAVY, "white"
        off = 1 if self.pressed else 0
        self.create_polygon(rounded_poly(2, 2 + off, w - 2, h - 2 + off, 10), smooth=True,
                            fill=fill, outline=fill)
        if self.enabled:
            self.create_rectangle(14, h - 8 + off, w - 14, h - 5 + off, fill=BLUE, outline="")
        if self.enabled:
            self.create_text(w / 2, h / 2 - 3 + off, text=self.text,
                             font=("Segoe UI", 18, "bold"), fill=fg)
        else:
            self.create_text(w / 2, h / 2 - 9, text=self.text, font=("Segoe UI", 16, "bold"), fill=fg)
            self.create_text(w / 2, h / 2 + 14, text="add at least one load to continue",
                             font=("Segoe UI", 9), fill=fg)


# ----------------------------------------------------------------------------
#  Main window
# ----------------------------------------------------------------------------
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.geometry("1020x800")
        self.minsize(920, 720)
        self.configure(bg="white")
        self.setup_style()
        self.pallets = []
        self.ckey = None
        build_header(self)
        build_footer(self)
        self.container = ttk.Frame(self)
        self.container.pack(fill="both", expand=True)
        self.show_select()

    def setup_style(self):
        st = ttk.Style(self)
        st.theme_use("clam")
        st.configure(".", background="white", foreground=NAVY, font=("Segoe UI", 10))
        st.configure("TFrame", background="white")
        st.configure("TLabel", background="white")
        st.configure("TLabelframe", background="white", bordercolor=BORDER)
        st.configure("TLabelframe.Label", background="white", foreground=NAVY,
                     font=("Segoe UI", 10, "bold"))
        st.configure("TButton", background="#f1f4f7", bordercolor="#c9d1d9", padding=(12, 6))
        st.map("TButton", background=[("active", "#e2e8ee")])
        st.configure("Accent.TButton", background=NAVY, foreground="white",
                     bordercolor=NAVY_HOVER, font=("Segoe UI", 10, "bold"), padding=(14, 6))
        st.map("Accent.TButton", background=[("active", NAVY_HOVER)])
        st.configure("TEntry", fieldbackground="white", bordercolor="#c9d1d9")
        st.configure("TCheckbutton", background="white")
        st.configure("TRadiobutton", background="white")
        st.configure("Treeview", background="white", fieldbackground="white", rowheight=28,
                     borderwidth=0)
        st.map("Treeview", background=[("selected", "#d6e4f7")], foreground=[("selected", "black")])
        st.configure("Treeview.Heading", background="#e9eef6", foreground=NAVY,
                     font=("Segoe UI", 10, "bold"), relief="flat", padding=6)
        st.configure("TNotebook", background="white", bordercolor=BORDER)
        st.configure("TNotebook.Tab", background="#e9eef6", padding=(14, 6))
        st.map("TNotebook.Tab", background=[("selected", "white")])

    def clear(self):
        for w in self.container.winfo_children():
            w.destroy()

    # ---------- screen 1: container selection ----------
    def show_select(self):
        self.clear()
        fr = ttk.Frame(self.container, padding=20)
        fr.pack(fill="both", expand=True)
        ttk.Label(fr, text="Select container type", font=("Segoe UI", 24, "bold"),
                  foreground=NAVY).pack(pady=(14, 4))
        tk.Frame(fr, height=4, width=70, bg=BLUE).pack()
        ttk.Label(fr, text="Choose the container you want to load", font=("Segoe UI", 12),
                  foreground=MUTED).pack(pady=(12, 10))

        cards = ttk.Frame(fr)
        cards.pack(expand=True)
        scale = 0.038  # px per mm - SAME scale for both pictures, so sizes are comparable
        for col, key in enumerate(("20", "40")):
            look = CONTAINER_LOOK[key]
            name, L, W, H = CONTAINERS[key]
            cw, ch = look["ext_len"] * scale, look["ext_h"] * scale
            card = tk.Frame(cards, bg="white", highlightthickness=3,
                            highlightbackground=BORDER, highlightcolor=NAVY,
                            padx=16, pady=14, cursor="hand2")
            card.grid(row=0, column=col, padx=18, sticky="s")
            cv = tk.Canvas(card, width=cw + 24, height=ch + 62, bg="white", highlightthickness=0)
            cv.pack()
            draw_container(cv, 12, 14, cw, ch, look["body"], look["dark"], look["label"])
            # dimension arrow
            ay = 14 + ch + 26
            cv.create_line(12, ay, 12 + cw, ay, fill=MUTED, arrow="both")
            cv.create_text(12 + cw / 2, ay + 14, text=look["ft"], fill=MUTED,
                           font=("Segoe UI", 9))
            tk.Label(card, text=name, font=("Segoe UI", 14, "bold"), bg="white",
                     fg=NAVY).pack(pady=(4, 0))
            tk.Label(card, text=f"interior: {L} × {W} × {H} mm", bg="white",
                     fg=MUTED).pack(pady=(0, 8))
            ttk.Button(card, text="Select", width=18, style="Accent.TButton",
                       command=lambda k=key: self.show_main(k)).pack()

            def hover(on, c=card):
                c.configure(highlightbackground=NAVY if on else BORDER)

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

        ttk.Label(fr, text=f"Rules: loads (pallets / winches) stand on the floor only (no stacking) "
                           f"and may be rotated by 90°. Clearance of {fmt(GAP)} mm between loads "
                           f"and from the walls and doors. Max. load height {fmt(MAX_H)} mm.",
                  foreground=MUTED, wraplength=900).pack(fill="x", pady=(0, 8))

        pf = ttk.LabelFrame(fr, text="Loads", padding=10)
        pf.pack(fill="both", expand=True)
        bar = ttk.Frame(pf)
        bar.pack(fill="x", pady=(0, 8))
        ttk.Button(bar, text="+ Add loads", style="Accent.TButton",
                   command=self.add_load).pack(side="left")
        ttk.Button(bar, text="Duplicate", command=self.duplicate_load).pack(side="left", padx=6)
        ttk.Button(bar, text="Edit", command=self.edit_load).pack(side="left")
        ttk.Button(bar, text="Delete", command=self.delete_load).pack(side="left", padx=6)
        ttk.Button(bar, text="Clear all", command=self.clear_loads).pack(side="left")
        self.count_lbl = ttk.Label(bar, text="", font=("Segoe UI", 10, "bold"))
        self.count_lbl.pack(side="right")

        cols = ("n", "kind", "l", "w", "h")
        tf = ttk.Frame(pf)
        tf.pack(fill="both", expand=True)
        self.tree = ttk.Treeview(tf, columns=cols, show="headings", selectmode="extended")
        for c, t, w in (("n", "#", 60), ("kind", "Type", 110), ("l", "Length, mm", 110),
                        ("w", "Width, mm", 110), ("h", "Height, mm", 110)):
            self.tree.heading(c, text=t)
            self.tree.column(c, width=w, anchor="center")
        self.tree.tag_configure("odd", background="#f6f8fa")
        sb = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.tree.bind("<Double-1>", lambda e: self.edit_load())
        self.tree.bind("<Delete>", lambda e: self.delete_load())

        # right-click menu: Duplicate / Edit / Delete
        self.menu = tk.Menu(self, tearoff=0)
        self.menu.add_command(label="Duplicate", command=self.duplicate_load)
        self.menu.add_command(label="Edit…", command=self.edit_load)
        self.menu.add_separator()
        self.menu.add_command(label="Delete", command=self.delete_load)
        for ev in ("<Button-3>", "<Button-2>", "<Control-Button-1>"):
            self.tree.bind(ev, self.show_menu)

        self.load_btn = LoadButton(fr, "LOAD", self.load)
        self.load_btn.pack(fill="x", pady=(12, 0))
        self.refresh()

    def show_menu(self, event):
        row = self.tree.identify_row(event.y)
        if not row:
            return
        if row not in self.tree.selection():
            self.tree.selection_set(row)
        try:
            self.menu.tk_popup(event.x_root, event.y_root)
        finally:
            self.menu.grab_release()

    def refresh(self, select=None):
        for i in self.tree.get_children():
            self.tree.delete(i)
        for idx, p in enumerate(self.pallets):
            self.tree.insert("", "end", iid=str(p.number),
                             values=(p.number, p.kind, fmt(p.l), fmt(p.w), fmt(p.h)),
                             tags=("odd",) if idx % 2 else ())
        if select:
            ids = [str(n) for n in select]
            self.tree.selection_set(ids)
            self.tree.see(ids[-1])
        self.count_lbl.config(text=f"Total loads: {len(self.pallets)}")
        self.load_btn.set_enabled(len(self.pallets) > 0)

    def renumber(self):
        for i, p in enumerate(self.pallets, 1):
            p.number = i

    def add_load(self):
        dlg = LoadDialog(self, len(self.pallets) + 1)
        if dlg.result:
            kind, l, w, h, qty = dlg.result
            for _ in range(qty):
                self.pallets.append(Pallet(len(self.pallets) + 1, l, w, h, kind))
            self.refresh()

    def selected(self):
        return sorted(int(i) for i in self.tree.selection())

    def duplicate_load(self):
        sel = self.selected()
        if not sel:
            messagebox.showinfo(APP_TITLE, "Please select a load in the list to duplicate.")
            return
        new_ids = []
        for n in sel:
            p = self.pallets[n - 1]
            q = Pallet(len(self.pallets) + 1, p.l, p.w, p.h, p.kind)
            self.pallets.append(q)
            new_ids.append(q.number)
        self.refresh(select=new_ids)

    def edit_load(self):
        sel = self.selected()
        if not sel:
            messagebox.showinfo(APP_TITLE, "Please select a load in the list.")
            return
        p = self.pallets[sel[0] - 1]
        dlg = LoadDialog(self, p.number, p)
        if dlg.result:
            p.kind, p.l, p.w, p.h, _ = dlg.result
            self.refresh(select=[p.number])

    def delete_load(self):
        sel = set(self.selected())
        if not sel:
            return
        self.pallets = [p for p in self.pallets if p.number not in sel]
        self.renumber()
        self.refresh()

    def clear_loads(self):
        if self.pallets and messagebox.askyesno(APP_TITLE, "Remove all loads from the list?"):
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
            messagebox.showinfo(APP_TITLE, "Please add at least one load first.")
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
