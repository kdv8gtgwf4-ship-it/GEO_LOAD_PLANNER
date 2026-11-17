# -*- coding: utf-8 -*-
"""
Geo Container Loading Planner
Pallet loading planner for 20' / 40' containers.
All dimensions are in millimetres. Requires only Python 3.8+ (Tkinter is included).
"""
import base64
import csv
import functools
import io
import json
import math
import os
import re
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
FOOTER_TEXT = "@GEO SENSE TECHNOLOGY, PAK NAM PRAN/THAILAND"
DEFAULT_H = 1500.0  # height assumed for Excel items that have no height, mm


# ----------------------------------------------------------------------------
#  Model and packing algorithm
# ----------------------------------------------------------------------------
@dataclass
class Pallet:
    """A load: either a pallet or a winch.
    src    = index of the Excel file it came from (0 = entered by hand) -> label "3.2"
    origin = text describing where it came from (file / box)"""
    number: int
    l: float
    w: float
    h: float
    kind: str = "Pallet"
    src: int = 0
    assumed_h: bool = False
    origin: str = ""

    @property
    def label(self):
        return f"{self.number}.{self.src}" if self.src else str(self.number)


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
        placed.append(dict(n=p.number, label=p.label, kind=p.kind, x=x, y=y, z=z, dx=dx, dy=dy, h=p.h,
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
        groups.setdefault(r, []).append(f"#{p.label} {p.kind}")
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
#  Excel packing-list reader ("automatic configurator")
# ----------------------------------------------------------------------------
_UNIT_MM = {"mm": 1.0, "cm": 10.0, "m": 1000.0}
_DIM_RE = re.compile(r"(\d+(?:[.,]\d+)?)\s*[x×*]\s*(\d+(?:[.,]\d+)?)"
                     r"(?:\s*[x×*]\s*(\d+(?:[.,]\d+)?))?\s*(mm|cm|m)?\b", re.I)
_WINCH_WORDS = ("winch", "reel", "drum", "spool")


def parse_dims_mm(text):
    """'145 x 125 x 155 cm' -> [1450, 1250, 1550];  '120 x 80 cm' -> [1200, 800];  else None."""
    m = _DIM_RE.search(text or "")
    if not m:
        return None
    vals = [float(g.replace(",", ".")) for g in m.groups()[:3] if g]
    unit = (m.group(4) or "").lower() or ("cm" if max(vals) <= 400 else "mm")
    return [v * _UNIT_MM[unit] for v in vals]


def classify_load(package, contents):
    """Pallet or Winch, decided by the package description and then by its contents."""
    t = (package or "").lower()
    if "pallet" in t:
        return "Pallet"
    if any(w in t for w in _WINCH_WORDS):
        return "Winch"
    if any(w in " ".join(contents).lower() for w in _WINCH_WORDS):
        return "Winch"
    return "Pallet"


def _cell_text(v):
    if v is None:
        return ""
    if isinstance(v, float) and v == int(v):
        return str(int(v))
    return str(v).strip()


def _as_int(v):
    if isinstance(v, bool):
        return None
    if isinstance(v, (int, float)):
        return int(v) if v == int(v) and v > 0 else None
    t = str(v).strip()
    return int(t) if t.isdigit() and int(t) > 0 else None


def read_workbook_rows(path):
    """Returns [(sheet_name, [row, row, ...]), ...] for .xls (xlrd) and .xlsx/.xlsm (openpyxl)."""
    ext = os.path.splitext(path)[1].lower()
    out = []
    if ext == ".xls":
        import xlrd
        wb = xlrd.open_workbook(path)
        for sh in wb.sheets():
            out.append((sh.name, [sh.row_values(r) for r in range(sh.nrows)]))
    else:
        import openpyxl
        wb = openpyxl.load_workbook(path, data_only=True)
        for ws in wb.worksheets:
            out.append((ws.title, [list(r) for r in ws.iter_rows(values_only=True)]))
    return out


def parse_packing_list(path, default_h=DEFAULT_H):
    """Reads one packing list. Every numbered 'Box' row is one package (or several, if Qty > 1).
    Returns (items, warnings); each item is a dict(kind, l, w, h, assumed_h, origin)."""
    name = os.path.basename(path)
    warnings = []
    for sheet, rows in read_workbook_rows(path):
        hdr = None
        for i, r in enumerate(rows):
            low = [_cell_text(c).lower() for c in r]
            if "box" in low and "qty" in low and any(c.startswith("description") for c in low):
                hdr = (i, low.index("box"), low.index("qty"),
                       next(k for k, c in enumerate(low) if c.startswith("description")))
                break
        if hdr is None:
            continue
        h_i, c_box, c_qty, c_desc = hdr
        boxes, cur = [], None
        for r in rows[h_i + 1:]:
            r = list(r) + [""] * (max(c_box, c_qty, c_desc) + 1 - len(r))
            low = " ".join(_cell_text(c).lower() for c in r)
            if "total weight" in low or "packing details" in low:
                break
            bn = _as_int(r[c_box])
            if bn is not None:
                q = _as_int(r[c_qty]) or 1
                cur = dict(box=bn, qty=q, pkg=_cell_text(r[c_desc]), contents=[])
                boxes.append(cur)
            elif cur is not None:
                t = _cell_text(r[c_desc])
                if t and not t.lower().startswith("total"):
                    cur["contents"].append(t)
        items = []
        for bx in boxes:
            kind = classify_load(bx["pkg"], bx["contents"])
            dims = parse_dims_mm(bx["pkg"])
            for t in bx["contents"]:
                if dims:
                    break
                dims = parse_dims_mm(t)
            origin = f"{name} / box {bx['box']}"
            assumed = False
            if dims and len(dims) >= 3:
                l, w, h = dims[:3]
            elif dims:
                l, w = dims[:2]
                h, assumed = default_h, True
            elif "euro" in (bx["pkg"] + " " + " ".join(bx["contents"])).lower():
                l, w, h, assumed = 1200.0, 800.0, default_h, True
                warnings.append(f"{origin}: no dimensions found, Euro pallet 1200 × 800 mm assumed.")
            else:
                warnings.append(f"{origin}: no dimensions found in '{bx['pkg']}' - skipped.")
                continue
            for _ in range(bx["qty"]):
                items.append(dict(kind=kind, l=l, w=w, h=h, assumed_h=assumed, origin=origin))
        if items:
            return items, warnings
    warnings.append(f"{name}: no packing-list table (columns Box / Qty / Description) was found.")
    return [], warnings


class ImportDialog(tk.Toplevel):
    """Preview of the loads read from one or several Excel files, before they are added."""

    def __init__(self, master, files, start_number, start_src, default_h):
        super().__init__(master)
        self.title("Import from Excel")
        self.configure(bg="white")
        self.geometry("980x640")
        self.transient(master)
        self.result = None
        self.items = []
        n = start_number
        for k, fi in enumerate(files):
            for it in fi["items"]:
                it["src"] = start_src + k
                it["number"] = n
                n += 1
                self.items.append(it)

        frm = ttk.Frame(self, padding=14)
        frm.pack(fill="both", expand=True)
        parts = "; ".join(f"file {start_src + k}: {fi['name']} ({len(fi['items'])} loads)"
                          for k, fi in enumerate(files))
        ttk.Label(frm, text=f"{len(self.items)} loads found.  {parts}", wraplength=930,
                  font=("Segoe UI", 10, "bold")).pack(anchor="w")
        ttk.Label(frm, text="Numbering continues across files; the number after the dot is the "
                            "file the load came from (e.g. 6.2 = 6th load, from the 2nd file).",
                  foreground=MUTED, wraplength=930).pack(anchor="w", pady=(2, 8))

        warns = [w for fi in files for w in fi["warnings"]]
        if warns:
            tk.Label(frm, text="\n".join(warns), fg="#b00020", bg="white", justify="left",
                     wraplength=930, anchor="w").pack(fill="x", pady=(0, 8))

        hb = ttk.Frame(frm)
        hb.pack(fill="x", pady=(0, 8))
        ttk.Label(hb, text="Height for loads where the file gives no height, mm:").pack(side="left")
        self.hvar = tk.StringVar(value=fmt(default_h))
        ttk.Entry(hb, textvariable=self.hvar, width=8).pack(side="left", padx=6)
        ttk.Button(hb, text="Apply", command=self.apply_h).pack(side="left")

        cols = ("n", "kind", "l", "w", "h", "origin")
        tf = ttk.Frame(frm)
        tf.pack(fill="both", expand=True)
        self.tree = ttk.Treeview(tf, columns=cols, show="headings")
        for c, t, w, anc in (("n", "#", 60, "center"), ("kind", "Type", 80, "center"),
                             ("l", "Length, mm", 95, "center"), ("w", "Width, mm", 95, "center"),
                             ("h", "Height, mm", 95, "center"), ("origin", "Source", 440, "w")):
            self.tree.heading(c, text=t)
            self.tree.column(c, width=w, anchor=anc)
        self.tree.tag_configure("odd", background="#f6f8fa")
        sb = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.fill()

        bb = ttk.Frame(frm)
        bb.pack(fill="x", pady=(10, 0))
        ttk.Label(bb, text="* = height not in the file (assumed). You can edit any load afterwards.",
                  foreground=MUTED).pack(side="left")
        ttk.Button(bb, text="Cancel", command=self.destroy).pack(side="right")
        ttk.Button(bb, text="Add to configuration", style="Accent.TButton",
                   command=self.on_ok).pack(side="right", padx=8)
        self.bind("<Escape>", lambda e: self.destroy())
        self.grab_set()
        self.wait_window(self)

    def fill(self):
        for i in self.tree.get_children():
            self.tree.delete(i)
        for idx, it in enumerate(self.items):
            self.tree.insert("", "end", values=(
                f"{it['number']}.{it['src']}", it["kind"], fmt(it["l"]), fmt(it["w"]),
                fmt(it["h"]) + ("*" if it["assumed_h"] else ""), it["origin"]),
                tags=("odd",) if idx % 2 else ())

    def apply_h(self):
        try:
            h = parse_pos(self.hvar.get(), "Height")
            if h > MAX_H:
                raise ValueError(f"Height must not exceed {fmt(MAX_H)} mm (220 cm).")
        except ValueError as e:
            messagebox.showerror(APP_TITLE, str(e), parent=self)
            return
        for it in self.items:
            if it["assumed_h"]:
                it["h"] = h
        self.fill()

    def on_ok(self):
        self.result = self.items
        self.destroy()


# ----------------------------------------------------------------------------
#  Loading diagram (top view) - on screen
# ----------------------------------------------------------------------------
class PlanCanvas(tk.Canvas):
    def __init__(self, master, L, W, placed):
        super().__init__(master, bg="white", highlightthickness=0)
        self.L, self.W, self.placed = L, W, placed
        self._fonts = {}
        self.bind("<Configure>", lambda e: self.redraw())

    def _font(self, px, bold=False):
        from tkinter import font as tkfont
        key = (px, bold)
        if key not in self._fonts:
            self._fonts[key] = tkfont.Font(family="Segoe UI", size=-int(px),
                                           weight="bold" if bold else "normal")
        return self._fonts[key]

    def _write_label(self, b, x1, y1, x2, y2):
        """Writes #label, type and size inside the rectangle, using the biggest font that fits."""
        rw, rh = x2 - x1, y2 - y1
        texts = (f"#{b['label']}", b["kind"], f"{fmt(b['dx'])}×{fmt(b['dy'])}×{fmt(b['h'])}")
        for nlines in (3, 2, 1):
            for px in range(18, 6, -1):
                sizes = [px, max(7, int(px * 0.72)), max(7, int(px * 0.64))][:nlines]
                fonts = [self._font(sizes[0], True)] + [self._font(z) for z in sizes[1:]]
                wmax = max(f.measure(t) for f, t in zip(fonts, texts))
                lhs = [f.metrics("linespace") for f in fonts]
                if wmax <= rw * 0.94 and sum(lhs) <= rh * 0.94:
                    yy = (y1 + y2) / 2 - sum(lhs) / 2
                    for f, t, lh in zip(fonts, texts, lhs):
                        self.create_text((x1 + x2) / 2, yy + lh / 2, text=t, font=f)
                        yy += lh
                    return

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
            self._write_label(b, x1, y1, x2, y2)


# ----------------------------------------------------------------------------
#  Loading diagram -> image (PNG / PDF export, needs Pillow)
# ----------------------------------------------------------------------------
@functools.lru_cache(maxsize=None)
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


def _fit_text_in_box(d, rw, rh, label, kind, dims):
    """Largest font size at which #label / type / size all fit inside the rectangle.
    Returns (font size, number of lines)."""
    texts = (label, kind, dims)
    for nlines in (3, 2, 1):
        for fs in range(120, 9, -2):
            sizes = [fs, int(fs * 0.66), int(fs * 0.58)][:nlines]
            fonts = [_pil_font(sizes[0], True)] + [_pil_font(z, False) for z in sizes[1:]]
            wmax = max(d.textlength(t, font=f) for t, f in zip(texts, fonts))
            hh = sum(z * 1.3 for z in sizes)
            if wmax <= rw * 0.92 and hh <= rh * 0.88:
                return fs, nlines
    return 10, 1


def render_plan_image(cname, dims, placed, unplaced, total):
    """Draws the loading plan as a large PIL image (about 4000 px wide): header, summary,
    top view with #label / type / size on every load, and footer."""
    import textwrap
    from PIL import Image, ImageDraw
    L, W, H = dims
    IW = 4000
    u = IW / 2400.0

    def P(v):
        return int(round(v * u))

    ml, mr = P(120), P(210)
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
    first = True
    for g_ in group_unplaced(unplaced):
        for ln in textwrap.wrap(("DID NOT FIT:  " if first else "") + g_, 125):
            lines.append((ln, "#b00020"))
        first = False

    y_lines = P(215)
    row_h = P(46)
    top = y_lines + row_h * len(lines) + P(90)
    bottom = top + ch
    IH = int(bottom + P(90) + P(84))
    img = Image.new("RGB", (IW, IH), "white")
    d = ImageDraw.Draw(img)

    # header
    d.rectangle([0, 0, IW, P(16)], fill=NAVY)
    d.text((P(60), P(46)), "Loading Plan", font=_pil_font(P(66), True), fill=NAVY)
    d.text((P(62), P(128)), cname, font=_pil_font(P(38)), fill=MUTED)
    logo = get_logo_image(P(120))
    if logo:
        img.paste(logo, (IW - P(60) - logo.width, P(40)), logo)
    else:
        d.text((IW - P(60), P(56)), "GEO MARINE", font=_pil_font(P(54), True), fill=NAVY, anchor="ra")
        d.text((IW - P(60), P(120)), "SURVEY SYSTEMS", font=_pil_font(P(30), True), fill=BLUE,
               anchor="ra")
    d.line([P(60), P(190), IW - P(60), P(190)], fill=BORDER, width=P(3))
    y = y_lines
    for text, col in lines:
        d.text((P(60), y), text, font=_pil_font(P(32)), fill=col)
        y += row_h

    # container
    ox = ml
    right = ox + L * s
    d.rectangle([ox, top, right, bottom], fill="#f3f3f3", outline="#333333", width=P(5))
    d.line([right, top, right, bottom], fill="#b00020", width=P(14))
    f_door = _pil_font(P(36), True)
    bb = d.textbbox((0, 0), "DOORS", font=f_door)
    tmp = Image.new("RGBA", (bb[2] - bb[0] + 12, bb[3] - bb[1] + 12), (255, 255, 255, 0))
    ImageDraw.Draw(tmp).text((6 - bb[0], 6 - bb[1]), "DOORS", font=f_door, fill="#b00020")
    rot = tmp.rotate(270, expand=True)
    img.paste(rot, (int(right + P(30)), int((top + bottom) / 2 - rot.height / 2)), rot)
    _text_center(d, (ox + right) / 2, top - P(30), f"Right wall   |   length {fmt(L)} mm",
                 _pil_font(P(30)), MUTED)
    _text_center(d, (ox + right) / 2, bottom + P(34),
                 f"Left wall   |   width {fmt(W)} mm   (view from the doors)", _pil_font(P(30)), MUTED)

    # loads: every one gets #label, type and size (font is chosen to fit the rectangle)
    for b in placed:
        x1 = ox + b["x"] * s
        x2 = ox + (b["x"] + b["dx"]) * s
        y2 = bottom - b["y"] * s
        y1 = bottom - (b["y"] + b["dy"]) * s
        color = PALETTE[(b["n"] - 1) % len(PALETTE)]
        d.rectangle([x1, y1, x2, y2], fill=color, outline="#222222", width=P(3))
        rw, rh = x2 - x1, y2 - y1
        label = f"#{b['label']}"
        dims_t = f"{fmt(b['dx'])}×{fmt(b['dy'])}×{fmt(b['h'])}"
        fs, nlines = _fit_text_in_box(d, rw, rh, label, b["kind"], dims_t)
        items = [(label, fs, True), (b["kind"], int(fs * 0.66), False),
                 (dims_t, int(fs * 0.58), False)][:nlines]
        hs = [int(sz * 1.3) for _, sz, _ in items]
        yy = (y1 + y2) / 2 - sum(hs) / 2
        for (text, sz, bold), hh in zip(items, hs):
            _text_center(d, (x1 + x2) / 2, yy + hh / 2, text, _pil_font(sz, bold), "#111111")
            yy += hh

    # footer
    d.rectangle([0, IH - P(70), IW, IH], fill=NAVY)
    d.text((P(60), IH - P(52)), FOOTER_TEXT, font=_pil_font(P(28), True), fill="#c9d4e8")
    d.text((IW - P(60), IH - P(52)), "Geo Container Loading Planner", font=_pil_font(P(28)),
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
        self.geometry("1200x820")
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
            out.append((b["order"], b["label"], b["kind"],
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
                    wr.writerow([f"#{p.label}", p.kind,
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


def _find_logo_file():
    exts = (".png", ".jpg", ".jpeg", ".gif", ".webp", ".bmp")
    for d in _resource_dirs() + [os.getcwd()]:
        try:
            for name in sorted(os.listdir(d)):
                low = name.lower()
                if low.startswith("logo") and low.endswith(exts):
                    return os.path.join(d, name)
        except OSError:
            pass
    return None


def get_logo_image(height):
    """Company logo as a PIL image scaled to `height` px, or None.
    Looks for the logo embedded at build time (logo_data.py), then for logo.* next to the program."""
    try:
        from PIL import Image
    except ImportError:
        return None
    img = None
    try:
        from logo_data import LOGO_B64  # generated by embed_logo.py during the build
        img = Image.open(io.BytesIO(base64.b64decode(LOGO_B64)))
    except Exception:
        img = None
    if img is None:
        p = _find_logo_file()
        if p:
            try:
                img = Image.open(p)
            except Exception:
                img = None
    if img is None:
        return None
    img = img.convert("RGBA")
    r = height / img.height
    res = getattr(Image, "Resampling", Image)
    return img.resize((max(1, int(img.width * r)), int(height)), res.LANCZOS)


def make_logo(parent, height=50):
    """Company logo widget; a text wordmark is used only if no logo can be loaded."""
    img = get_logo_image(height)
    if img is not None:
        try:
            buf = io.BytesIO()
            img.save(buf, "PNG")
            photo = tk.PhotoImage(data=base64.b64encode(buf.getvalue()))
            lbl = tk.Label(parent, image=photo, bg="white")
            lbl.image = photo  # keep a reference
            return lbl
        except Exception:
            pass
    p = _find_logo_file()  # no Pillow: plain Tk can read PNG / GIF
    if p and p.lower().endswith((".png", ".gif")):
        try:
            photo = tk.PhotoImage(file=p)
            ratio = photo.height() / height
            if ratio >= 1.5:
                photo = photo.subsample(int(round(ratio)))
            elif ratio <= 0.67:
                photo = photo.zoom(int(round(1 / ratio)))
            lbl = tk.Label(parent, image=photo, bg="white")
            lbl.image = photo
            return lbl
        except Exception:
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
    tk.Label(foot, text=FOOTER_TEXT, bg=NAVY, fg="#c9d4e8",
             font=("Segoe UI", 8, "bold")).pack(side="left", padx=16)
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

        ttk.Button(fr, text="Open saved configuration…", command=self.open_config
                   ).pack(pady=(0, 6))

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
        # right corner: automatic configurator + save / open configuration
        ttk.Button(bar, text="Save config…", command=self.save_config).pack(side="right")
        ttk.Button(bar, text="Open config…", command=self.open_config).pack(side="right", padx=6)
        ttk.Button(bar, text="Import from Excel…", style="Accent.TButton",
                   command=self.import_excel).pack(side="right")

        self.count_lbl = ttk.Label(pf, text="", font=("Segoe UI", 10, "bold"))
        self.count_lbl.pack(side="bottom", anchor="e", pady=(6, 0))

        cols = ("n", "kind", "l", "w", "h", "note")
        tf = ttk.Frame(pf)
        tf.pack(fill="both", expand=True)
        self.tree = ttk.Treeview(tf, columns=cols, show="headings", selectmode="extended")
        for c, t, w, anc in (("n", "#", 70, "center"), ("kind", "Type", 90, "center"),
                             ("l", "Length, mm", 100, "center"), ("w", "Width, mm", 100, "center"),
                             ("h", "Height, mm", 100, "center"), ("note", "Source", 380, "w")):
            self.tree.heading(c, text=t)
            self.tree.column(c, width=w, anchor=anc)
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
            note = p.origin + ("  (height assumed)" if p.assumed_h else "")
            self.tree.insert("", "end", iid=str(p.number),
                             values=(p.label, p.kind, fmt(p.l), fmt(p.w),
                                     fmt(p.h) + ("*" if p.assumed_h else ""), note),
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
            q = Pallet(len(self.pallets) + 1, p.l, p.w, p.h, p.kind, p.src, p.assumed_h, p.origin)
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
            p.assumed_h = False
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

    # ---------- save / open configuration ----------
    def save_config(self):
        if not self.pallets:
            messagebox.showinfo(APP_TITLE, "There are no loads to save yet.")
            return
        try:
            dims = {k.lower(): parse_pos(self.dim_vars[k].get(), "Container " + k.lower())
                    for k in ("Length", "Width", "Height")}
        except ValueError as e:
            messagebox.showerror(APP_TITLE, str(e))
            return
        path = filedialog.asksaveasfilename(
            parent=self, defaultextension=".json", initialfile="loading_config.json",
            filetypes=[("Loading configuration", "*.json")], title="Save configuration")
        if not path:
            return
        data = {"app": APP_TITLE, "version": 1, "container": self.ckey, "dims": dims,
                "loads": [dict(kind=p.kind, l=p.l, w=p.w, h=p.h, src=p.src,
                               assumed_h=p.assumed_h, origin=p.origin) for p in self.pallets]}
        try:
            with open(path, "w", encoding="utf-8") as fh:
                json.dump(data, fh, indent=2, ensure_ascii=False)
        except OSError as e:
            messagebox.showerror(APP_TITLE, f"Could not save the file:\n{e}")
            return
        messagebox.showinfo(APP_TITLE, f"Configuration saved ({len(self.pallets)} loads).")

    def open_config(self):
        path = filedialog.askopenfilename(
            parent=self, title="Open configuration",
            filetypes=[("Loading configuration", "*.json"), ("All files", "*.*")])
        if not path:
            return
        try:
            with open(path, encoding="utf-8") as fh:
                data = json.load(fh)
            key = str(data["container"])
            if key not in CONTAINERS:
                raise ValueError("unknown container type")
            loads = [Pallet(i + 1, float(d["l"]), float(d["w"]), float(d["h"]),
                            d.get("kind", "Pallet") if d.get("kind") in KINDS else "Pallet",
                            int(d.get("src", 0)), bool(d.get("assumed_h", False)),
                            str(d.get("origin", "")))
                     for i, d in enumerate(data["loads"])]
            dims = data.get("dims", {})
        except Exception as e:
            messagebox.showerror(APP_TITLE, f"This is not a valid configuration file.\n({e})")
            return
        self.pallets = loads
        self.show_main(key)
        for k in ("Length", "Width", "Height"):
            if k.lower() in dims:
                self.dim_vars[k].set(fmt(float(dims[k.lower()])))

    # ---------- automatic configurator: Excel packing lists ----------
    def import_excel(self):
        paths = filedialog.askopenfilenames(
            parent=self, title="Select one or more packing list files",
            filetypes=[("Excel files", "*.xls *.xlsx *.xlsm"), ("All files", "*.*")])
        if not paths:
            return
        paths = sorted(paths, key=lambda p: os.path.basename(p).lower())
        files = []
        for p in paths:
            try:
                items, warns = parse_packing_list(p, DEFAULT_H)
            except ImportError as e:
                messagebox.showerror(APP_TITLE, "Reading Excel files needs an extra library "
                                                f"({e}).\nInstall with:  pip install xlrd openpyxl")
                return
            except Exception as e:
                messagebox.showerror(APP_TITLE, f"Could not read {os.path.basename(p)}:\n{e}")
                return
            files.append(dict(name=os.path.basename(p), items=items, warnings=warns))
        if not any(fi["items"] for fi in files):
            messagebox.showwarning(APP_TITLE, "No loads were found.\n\n" +
                                   "\n".join(w for fi in files for w in fi["warnings"]))
            return
        if self.pallets:
            ans = messagebox.askyesnocancel(
                APP_TITLE, f"The list already contains {len(self.pallets)} loads.\n\n"
                           "Yes = replace them with the imported loads\n"
                           "No = add the imported loads to the list\nCancel = abort")
            if ans is None:
                return
            if ans:
                self.pallets = []
        start_src = max((p.src for p in self.pallets), default=0) + 1
        dlg = ImportDialog(self, files, len(self.pallets) + 1, start_src, DEFAULT_H)
        if dlg.result:
            for it in dlg.result:
                self.pallets.append(Pallet(len(self.pallets) + 1, it["l"], it["w"], it["h"],
                                           it["kind"], it["src"], it["assumed_h"], it["origin"]))
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
