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
import random
import re
import sys
import time
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
NO_SPACE = "not enough space left in the container"
DEFAULT_H = 1500.0  # height assumed for Excel items that have no height, mm


# ----------------------------------------------------------------------------
#  Model and packing algorithm
# ----------------------------------------------------------------------------
@dataclass
class Pallet:
    """A load: either a pallet or a winch.
    src    = (kept only for old configuration files, not used any more)
    origin = text describing where it came from (Excel file / box)"""
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
        return str(self.number)


def _prune_rects(rects, min_side):
    """Keeps only maximal free rectangles that are still big enough for the smallest load."""
    rects = [r for r in rects if min(r[2], r[3]) >= min_side - EPS]
    rects.sort(key=lambda r: -(r[2] * r[3]))
    keep = []
    for x, y, w, h in rects:
        for kx, ky, kw, kh in keep:
            if kx <= x + EPS and ky <= y + EPS and kx + kw >= x + w - EPS and ky + kh >= y + h - EPS:
                break
        else:
            keep.append((x, y, w, h))
    return keep


def _split_rects(free, bx, by, bx1, by1, min_side):
    new = []
    for fx, fy, fw, fh in free:
        fx2, fy2 = fx + fw, fy + fh
        if bx >= fx2 - EPS or bx1 <= fx + EPS or by >= fy2 - EPS or by1 <= fy + EPS:
            new.append((fx, fy, fw, fh))
            continue
        if bx > fx + EPS:
            new.append((fx, fy, bx - fx, fh))
        if bx1 < fx2 - EPS:
            new.append((bx1, fy, fx2 - bx1, fh))
        if by > fy + EPS:
            new.append((fx, fy, fw, by - fy))
        if by1 < fy2 - EPS:
            new.append((fx, by1, fw, fy2 - by1))
    return _prune_rects(new, min_side)


def _decode(Le, We, order, pref, fixed, min_side):
    """Places the loads one by one (in the given order) at the free spot nearest to the front
    wall. pref[n]: 0 = try both orientations, 1 = long side along the container, 2 = across.
    Everything is in 'effective' coordinates: the floor is enlarged by GAP and each load too,
    so that the GAP between loads is guaranteed (the clearance to walls is added afterwards)."""
    free = [(0.0, 0.0, Le + GAP, We + GAP)]
    for x, y, dx, dy in fixed:
        free = _split_rects(free, x, y, x + dx + GAP, y + dy + GAP, min_side)
    placed, failed = [], []
    for p in order:
        a, b = max(p.l, p.w), min(p.l, p.w)
        pr = pref.get(p.number, 0)
        if pr == 1:
            orients = [(a, b)]
        elif pr == 2:
            orients = [(b, a)]
        else:
            orients = [(a, b), (b, a)] if a - b > EPS else [(a, b)]
        best = None
        for dx, dy in orients:
            for fx, fy, fw, fh in free:
                if dx + GAP <= fw + EPS and dy + GAP <= fh + EPS:
                    key = (fx, fy, fx + dx)
                    if best is None or key < best[0]:
                        best = (key, fx, fy, dx, dy)
        if best is None:
            failed.append(p)
            continue
        _, x, y, dx, dy = best
        placed.append((p, x, y, dx, dy))
        free = _split_rects(free, x, y, x + dx + GAP, y + dy + GAP, min_side)
    return placed, failed


def _objective(placed, failed, fixed_info):
    """(loads that did not fit, 'big-load-nearer-to-the-front' penalty, used length).
    Smaller loads should be at the front wall, the biggest ones next to the doors."""
    items = [(p.l * p.w, x + dx / 2.0) for p, x, y, dx, dy in placed] + list(fixed_info)
    pen = 0.0
    for i, (ai, xi) in enumerate(items):
        for j, (aj, xj) in enumerate(items):
            if i != j and ai < 0.9 * aj and xi > xj + 150:
                pen += (xi - xj - 150) / 1000.0
    maxx = max((x + dx for p, x, y, dx, dy in placed), default=0)
    return (len(failed), round(pen, 3), maxx)


def _solve(loads, Le, We, fixed, fixed_info, budget, seed=1):
    """Searches for an arrangement in which all loads fit and the smallest loads are at the
    front wall and the largest next to the doors (swapping order / orientation, hill climbing)."""
    if not loads:
        return [], []
    rnd = random.Random(seed)
    min_side = min(min(p.l, p.w) for p in loads) + GAP
    key_asc = lambda p: (p.l * p.w, max(p.l, p.w), p.number)
    inits = [sorted(loads, key=key_asc), sorted(loads, key=key_asc, reverse=True),
             sorted(loads, key=lambda p: (-max(p.l, p.w), -min(p.l, p.w))), list(loads)]

    def evaluate(order, pref):
        pl, fl = _decode(Le, We, order, pref, fixed, min_side)
        return _objective(pl, fl, fixed_info), pl, fl

    best = None
    for o in inits:
        ob, pl, fl = evaluate(o, {})
        if best is None or ob < best[0]:
            best = (ob, o, {}, pl, fl)
    cur = best
    t0 = time.perf_counter()
    stall = 0
    since_best = 0
    n = len(loads)
    while time.perf_counter() - t0 < budget:
        if best[0][0] == 0 and (best[0][1] == 0.0 or since_best > 6000):
            break
        o, pf = list(cur[1]), dict(cur[2])
        r = rnd.random()
        if n > 1 and r < 0.45:
            i, j = rnd.sample(range(n), 2)
            o[i], o[j] = o[j], o[i]
        elif n > 1 and r < 0.7:
            o.insert(rnd.randrange(n), o.pop(rnd.randrange(n)))
        else:
            pf[rnd.choice(o).number] = rnd.choice((0, 1, 2))
        ob, pl, fl = evaluate(o, pf)
        if ob <= cur[0]:
            cur = (ob, o, pf, pl, fl)
        if ob < best[0]:
            best = (ob, o, pf, pl, fl)
            stall = since_best = 0
        else:
            stall += 1
            since_best += 1
        if stall > 300:  # restart from a perturbed copy of the best solution
            o, pf = list(best[1]), dict(best[2])
            for _ in range(4):
                if n > 1:
                    i, j = rnd.sample(range(n), 2)
                    o[i], o[j] = o[j], o[i]
            for _ in range(2):
                pf[rnd.choice(o).number] = rnd.choice((0, 1, 2))
            ob, pl, fl = evaluate(o, pf)
            cur = (ob, o, pf, pl, fl)
            stall = 0
    return best[3], best[4]


def boxes_conflict(a, b):
    """True if two placed loads overlap or are closer to each other than GAP."""
    gx = max(b["x"] - (a["x"] + a["dx"]), a["x"] - (b["x"] + b["dx"]))
    gy = max(b["y"] - (a["y"] + a["dy"]), a["y"] - (b["y"] + b["dy"]))
    return max(gx, gy) < GAP - EPS


def assign_order(placed):
    """Loading sequence: from the front wall towards the doors."""
    placed.sort(key=lambda b: (round(b["x"], 1), round(b["y"], 1)))
    for i, b in enumerate(placed, 1):
        b["order"] = i


def plan_loading(L, W, H, pallets, fixed=None, budget=1.5):
    """Builds the loading plan. Returns (placed, unplaced[(load, reason)]).
    fixed = {load number: (x, y, dx, dy)} - loads that must stay exactly where they are;
    all the other loads are arranged around them."""
    fixed = fixed or {}
    unplaced, candidates, fixed_loads = [], [], []
    Hmax = min(H, MAX_H)  # height is limited by both the container and the 220 cm rule
    Le, We = L - 2 * GAP, W - 2 * GAP  # usable floor after clearance from walls and doors
    for p in pallets:
        if p.number in fixed:
            fixed_loads.append(p)
        elif p.h > Hmax + EPS:
            unplaced.append((p, f"height exceeds the allowed maximum ({fmt(Hmax)} mm)"))
        elif Le <= 0 or We <= 0 or not ((p.l <= Le + EPS and p.w <= We + EPS) or
                                        (p.w <= Le + EPS and p.l <= We + EPS)):
            unplaced.append((p, f"does not fit the container interior "
                                f"({fmt(GAP)} mm clearance is required on all sides)"))
        else:
            candidates.append(p)

    fx = [(fixed[p.number][0] - GAP, fixed[p.number][1] - GAP, fixed[p.number][2], fixed[p.number][3])
          for p in fixed_loads]
    info = [(p.l * p.w, fixed[p.number][0] - GAP + fixed[p.number][2] / 2.0) for p in fixed_loads]
    placed_eff, failed = _solve(candidates, Le, We, fx, info, budget)
    for p in failed:
        unplaced.append((p, NO_SPACE))

    placed = []
    for p, x, y, dx, dy in placed_eff:
        placed.append(dict(n=p.number, label=p.label, kind=p.kind, x=x + GAP, y=y + GAP, z=0.0,
                           dx=dx, dy=dy, h=p.h, level=1, rotated=abs(dx - p.l) > EPS, pallet=p))
    for p in fixed_loads:
        x, y, dx, dy = fixed[p.number]
        placed.append(dict(n=p.number, label=p.label, kind=p.kind, x=x, y=y, z=0.0, dx=dx, dy=dy,
                           h=p.h, level=1, rotated=abs(dx - p.l) > EPS, pallet=p))
    assign_order(placed)
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

    def __init__(self, master, files, start_number, default_h):
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
                it["src"] = 0
                it["number"] = n
                n += 1
                self.items.append(it)

        frm = ttk.Frame(self, padding=14)
        frm.pack(fill="both", expand=True)
        parts = "; ".join(f"{fi['name']} ({len(fi['items'])} loads)" for fi in files)
        ttk.Label(frm, text=f"{len(self.items)} loads found.  {parts}", wraplength=930,
                  font=("Segoe UI", 10, "bold")).pack(anchor="w")
        ttk.Label(frm, text="Loads from all files are numbered one after another "
                            "(1, 2, 3, ...). The Source column shows the file and box.",
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
                str(it["number"]), it["kind"], fmt(it["l"]), fmt(it["w"]),
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
    """Top view of the container. Loads can be selected and dragged with the mouse.
    Internal coordinates: X from the front wall (doors at X = L), Y from the left wall.
    door_left=True turns the picture by 180 degrees (doors on the left side)."""

    def __init__(self, master, L, W, placed, door_left=False, on_select=None, on_drop=None):
        super().__init__(master, bg="white", highlightthickness=0)
        self.L, self.W, self.placed = L, W, placed
        self.door_left, self.on_select, self.on_drop = door_left, on_select, on_drop
        self.pinned, self.selected = set(), None
        self._fonts, self._rects, self._drag = {}, {}, None
        self.s = self.ox = self.top = self.bottom = None
        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<ButtonPress-1>", self._press)
        self.bind("<B1-Motion>", self._motion)
        self.bind("<ButtonRelease-1>", self._release)

    def set_data(self, placed, pinned=None, selected=None, door_left=None):
        self.placed = placed
        if pinned is not None:
            self.pinned = pinned
        self.selected = selected
        if door_left is not None:
            self.door_left = door_left
        self.redraw()

    # ---- coordinates -------------------------------------------------------
    def rect_of(self, b):
        s, ox, top, bottom = self.s, self.ox, self.top, self.bottom
        if self.door_left:
            x1 = ox + (self.L - b["x"] - b["dx"]) * s
            y1 = top + b["y"] * s
        else:
            x1 = ox + b["x"] * s
            y1 = bottom - (b["y"] + b["dy"]) * s
        return x1, y1, x1 + b["dx"] * s, y1 + b["dy"] * s

    def internal_xy(self, x1, y1, dx, dy):
        s = self.s
        if self.door_left:
            return self.L - dx - (x1 - self.ox) / s, (y1 - self.top) / s
        return (x1 - self.ox) / s, (self.bottom - y1 - dy * s) / s

    # ---- drawing -----------------------------------------------------------
    def _font(self, px, bold=False):
        from tkinter import font as tkfont
        key = (px, bold)
        if key not in self._fonts:
            self._fonts[key] = tkfont.Font(family="Segoe UI", size=-int(px),
                                           weight="bold" if bold else "normal")
        return self._fonts[key]

    def _write_label(self, b, x1, y1, x2, y2, tag):
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
                        self.create_text((x1 + x2) / 2, yy + lh / 2, text=t, font=f, tags=(tag,))
                        yy += lh
                    return

    def redraw(self):
        self.delete("all")
        self._rects = {}
        cw, ch = self.winfo_width(), self.winfo_height()
        if cw < 120 or ch < 100:
            return
        s = min((cw - 130) / self.L, (ch - 100) / self.W)
        ox = (cw - self.L * s) / 2
        top = (ch - self.W * s) / 2
        bottom = top + self.W * s
        right = ox + self.L * s
        self.s, self.ox, self.top, self.bottom = s, ox, top, bottom

        self.create_rectangle(ox, top, right, bottom, fill="#f3f3f3", outline="#333", width=2)
        door_x = ox if self.door_left else right
        self.create_line(door_x, top, door_x, bottom, fill="#b00020", width=5)
        self.create_text(door_x - 14 if self.door_left else door_x + 14, (top + bottom) / 2,
                         text="DOORS", angle=270, fill="#b00020", font=("Segoe UI", 10, "bold"))
        top_wall, bot_wall = ("Left", "Right") if self.door_left else ("Right", "Left")
        self.create_text((ox + right) / 2, top - 14,
                         text=f"{top_wall} wall  |  length {fmt(self.L)} mm",
                         fill=MUTED, font=("Segoe UI", 9))
        self.create_text((ox + right) / 2, bottom + 14,
                         text=f"{bot_wall} wall  |  width {fmt(self.W)} mm  "
                              f"(view from above, looking from the doors)",
                         fill=MUTED, font=("Segoe UI", 9))

        for b in self.placed:
            x1, y1, x2, y2 = self.rect_of(b)
            tag = f"L{b['n']}"
            color = PALETTE[(b["n"] - 1) % len(PALETTE)]
            sel = (b["n"] == self.selected)
            rid = self.create_rectangle(x1, y1, x2, y2, fill=color, tags=(tag,),
                                        outline="#1e90ff" if sel else "#222",
                                        width=4 if sel else 1.5)
            self._rects[b["n"]] = rid
            self._write_label(b, x1, y1, x2, y2, tag)
            if b["n"] in self.pinned:  # small navy dot = this load is pinned
                self.create_oval(x2 - 14, y1 + 4, x2 - 4, y1 + 14, fill=NAVY, outline="white",
                                 width=1.5, tags=(tag,))
        if self.selected in self._rects:
            self.tag_raise(f"L{self.selected}")

    # ---- mouse -------------------------------------------------------------
    def _hit(self, x, y):
        for b in reversed(self.placed):
            x1, y1, x2, y2 = self.rect_of(b)
            if x1 <= x <= x2 and y1 <= y <= y2:
                return b
        return None

    def _press(self, e):
        if self.s is None:
            return
        b = self._hit(e.x, e.y)
        self.selected = b["n"] if b else None
        self._drag = (dict(n=b["n"], last=(e.x, e.y), start=(e.x, e.y), moved=False)
                      if b else None)
        if self.on_select:
            self.on_select(self.selected)
        self.redraw()  # shows the selection frame

    def _motion(self, e):
        d = self._drag
        if not d:
            return
        if not d["moved"] and abs(e.x - d["start"][0]) + abs(e.y - d["start"][1]) < 4:
            return
        d["moved"] = True
        self.move(f"L{d['n']}", e.x - d["last"][0], e.y - d["last"][1])
        d["last"] = (e.x, e.y)
        self.config(cursor="fleur")

    def _release(self, e):
        d, self._drag = self._drag, None
        self.config(cursor="")
        if not d or not d["moved"]:
            return
        b = next((q for q in self.placed if q["n"] == d["n"]), None)
        if b is None:
            return
        x1, y1, _, _ = self.coords(self._rects[d["n"]])
        x, y = self.internal_xy(x1, y1, b["dx"], b["dy"])
        if self.on_drop:
            self.on_drop(d["n"], x, y)
        self.redraw()


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


def render_plan_image(cname, dims, placed, unplaced, total, door_left=False):
    """Draws the loading plan as a large PIL image (about 4000 px wide): header, summary,
    top view with #label / type / size on every load, and footer."""
    import textwrap
    from PIL import Image, ImageDraw
    L, W, H = dims
    IW = 4000
    u = IW / 2400.0

    def P(v):
        return int(round(v * u))

    ml, mr = P(210), P(210)
    s = (IW - ml - mr) / L
    ch = W * s

    vol_used = sum(b["dx"] * b["dy"] * b["h"] for b in placed)
    used_len = max((b["x"] + b["dx"] for b in placed), default=0)
    lines = [
        (f"Container interior: {fmt(L)} × {fmt(W)} × {fmt(H)} mm    |    "
         f"Max. load height: {fmt(min(H, MAX_H))} mm    |    Clearance: {fmt(GAP)} mm    |    "
         f"Doors: {'left' if door_left else 'right'}", MUTED),
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
    door_x = ox if door_left else right
    d.line([door_x, top, door_x, bottom], fill="#b00020", width=P(14))
    f_door = _pil_font(P(36), True)
    bb = d.textbbox((0, 0), "DOORS", font=f_door)
    tmp = Image.new("RGBA", (bb[2] - bb[0] + 12, bb[3] - bb[1] + 12), (255, 255, 255, 0))
    ImageDraw.Draw(tmp).text((6 - bb[0], 6 - bb[1]), "DOORS", font=f_door, fill="#b00020")
    rot = tmp.rotate(270, expand=True)
    rx = int(door_x - P(30) - rot.width) if door_left else int(door_x + P(30))
    img.paste(rot, (rx, int((top + bottom) / 2 - rot.height / 2)), rot)
    top_wall, bot_wall = ("Left", "Right") if door_left else ("Right", "Left")
    _text_center(d, (ox + right) / 2, top - P(30), f"{top_wall} wall   |   length {fmt(L)} mm",
                 _pil_font(P(30)), MUTED)
    _text_center(d, (ox + right) / 2, bottom + P(34),
                 f"{bot_wall} wall   |   width {fmt(W)} mm   (view from above, looking from the doors)",
                 _pil_font(P(30)), MUTED)

    # loads: every one gets #label, type and size (font is chosen to fit the rectangle)
    for b in placed:
        if door_left:  # picture turned by 180 degrees
            x1 = ox + (L - b["x"] - b["dx"]) * s
            y1 = top + b["y"] * s
        else:
            x1 = ox + b["x"] * s
            y1 = bottom - (b["y"] + b["dy"]) * s
        x2, y2 = x1 + b["dx"] * s, y1 + b["dy"] * s
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
#  Result window: diagram + editing of the arrangement
# ----------------------------------------------------------------------------
class ResultWindow(tk.Toplevel):
    COLS = [("order", "Loading order", 110), ("n", "#", 60), ("kind", "Type", 90),
            ("size", "Size L×W×H, mm", 150), ("x", "X, mm", 80), ("y", "Y, mm", 80),
            ("rot", "Orientation", 150)]

    def __init__(self, master, cname, dims, loads, placed, unplaced):
        super().__init__(master)
        L, W, H = dims
        self.cname, self.dims, self.loads = cname, dims, loads
        self.total = len(loads)
        self.placed, self.unplaced = placed, unplaced
        self.pinned, self.history, self.sel = set(), [], None
        self._lock = False
        self.door = tk.StringVar(value="right")
        self.auto = tk.BooleanVar(value=True)
        self.title(f"Loading Plan - {cname}")
        self.configure(bg="white")
        self.geometry("1420x900")
        self.minsize(1100, 700)
        build_header(self, "Loading Plan")

        self.summary = ttk.Label(self, text="", wraplength=1360, padding=(10, 8),
                                 font=("Segoe UI", 10, "bold"))
        self.summary.pack(fill="x")
        self.warn = tk.Label(self, text="", fg="#b00020", bg="white", wraplength=1360,
                             justify="left", font=("Segoe UI", 10, "bold"), padx=10)
        self.warn.pack(fill="x", anchor="w")

        bot = ttk.Frame(self, padding=(10, 0, 10, 10))
        bot.pack(side="bottom", fill="x")
        ttk.Label(bot, text=f"Clearance of {fmt(GAP)} mm is kept between loads and to the walls "
                            f"and doors.   Drag a load in the picture to move it - the other loads "
                            f"are re-arranged around it.", foreground=MUTED).pack(side="left")
        ttk.Button(bot, text="Close", command=self.destroy).pack(side="right")
        ttk.Button(bot, text="Save as CSV…", command=self.save_csv).pack(side="right", padx=6)
        ttk.Button(bot, text="Save as PDF", style="Accent.TButton",
                   command=lambda: self.export("pdf")).pack(side="right", padx=6)
        ttk.Button(bot, text="Save as PNG", style="Accent.TButton",
                   command=lambda: self.export("png")).pack(side="right")

        pw = ttk.PanedWindow(self, orient="horizontal")
        pw.pack(fill="both", expand=True, padx=8, pady=8)
        left = ttk.Frame(pw)
        right = ttk.Frame(pw, padding=(8, 0, 0, 0))
        pw.add(left, weight=4)
        pw.add(right, weight=1)
        self.canvas = PlanCanvas(left, L, W, self.placed, False, self.on_canvas_select, self.on_drop)
        self.canvas.configure(width=900, height=520)
        self.canvas.pack(fill="both", expand=True)
        self.build_panel(right)
        self.refresh_all()

    # ---------- right-hand panel ----------
    def build_panel(self, p):
        box = ttk.LabelFrame(p, text="Doors", padding=8)
        box.pack(fill="x")
        ttk.Radiobutton(box, text="Doors on the right", value="right", variable=self.door,
                        command=self.on_door).pack(side="left")
        ttk.Radiobutton(box, text="Doors on the left", value="left", variable=self.door,
                        command=self.on_door).pack(side="left", padx=14)

        lf = ttk.LabelFrame(p, text="Loads  (click a row or a load in the picture)", padding=8)
        lf.pack(fill="both", expand=True, pady=8)
        cols = ("n", "kind", "size", "x", "y", "order", "pin")
        self.tree = ttk.Treeview(lf, columns=cols, show="headings", selectmode="browse", height=10)
        for c, t, w in (("n", "#", 38), ("kind", "Type", 56), ("size", "Size, mm", 100),
                        ("x", "X", 52), ("y", "Y", 52), ("order", "Seq.", 40), ("pin", "Pin", 36)):
            self.tree.heading(c, text=t)
            self.tree.column(c, width=w, anchor="center", stretch=(c == "size"))
        self.tree.tag_configure("unplaced", foreground="#b00020")
        sb = ttk.Scrollbar(lf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.tree.bind("<<TreeviewSelect>>", self.on_tree_select)

        sf = ttk.LabelFrame(p, text="Selected load", padding=8)
        sf.pack(fill="x")
        self.sel_lbl = ttk.Label(sf, text="none selected", font=("Segoe UI", 10, "bold"),
                                 wraplength=330)
        self.sel_lbl.pack(anchor="w")
        r1 = ttk.Frame(sf)
        r1.pack(fill="x", pady=(6, 0))
        ttk.Button(r1, text="Rotate 90°", command=self.rotate_selected).pack(side="left")
        ttk.Button(r1, text="Pin / Unpin", command=self.toggle_pin).pack(side="left", padx=6)
        ttk.Label(sf, text="Slide as far as possible:", foreground=MUTED).pack(anchor="w", pady=(8, 2))
        g = ttk.Frame(sf)
        g.pack(fill="x")
        for i, (txt, d) in enumerate((("To front wall", "front"), ("To doors", "door"),
                                      ("To left wall", "left"), ("To right wall", "right"))):
            ttk.Button(g, text=txt, command=lambda d=d: self.slide(d)).grid(
                row=i // 2, column=i % 2, sticky="ew", padx=2, pady=2)
        g.columnconfigure((0, 1), weight=1)
        r3 = ttk.Frame(sf)
        r3.pack(fill="x", pady=(8, 0))
        self.xv, self.yv = tk.StringVar(), tk.StringVar()
        ttk.Label(r3, text="X:").pack(side="left")
        ttk.Entry(r3, textvariable=self.xv, width=7).pack(side="left", padx=(2, 8))
        ttk.Label(r3, text="Y:").pack(side="left")
        ttk.Entry(r3, textvariable=self.yv, width=7).pack(side="left", padx=(2, 8))
        ttk.Button(r3, text="Apply", command=self.apply_xy).pack(side="left")
        ttk.Label(sf, text="X from the front wall, Y from the left wall (mm, corner of the load).",
                  foreground=MUTED, wraplength=330).pack(anchor="w", pady=(4, 0))

        af = ttk.LabelFrame(p, text="Arrangement", padding=8)
        af.pack(fill="x", pady=(8, 0))
        ttk.Checkbutton(af, text="Re-arrange the other loads automatically\n"
                                "when a moved load is in their way",
                        variable=self.auto).pack(anchor="w")
        r4 = ttk.Frame(af)
        r4.pack(fill="x", pady=(6, 0))
        ttk.Button(r4, text="Re-arrange others", command=self.rearrange).pack(side="left")
        ttk.Button(r4, text="Unpin all", command=self.unpin_all).pack(side="left", padx=6)
        r5 = ttk.Frame(af)
        r5.pack(fill="x", pady=(6, 0))
        ttk.Button(r5, text="Undo", command=self.undo).pack(side="left")
        ttk.Button(r5, text="Start over (auto layout)", command=self.start_over).pack(side="left", padx=6)

    # ---------- state helpers ----------
    def get_placed(self, n):
        return next((b for b in self.placed if b["n"] == n), None)

    def inside(self, b):
        L, W, _ = self.dims
        return (b["x"] >= GAP - EPS and b["y"] >= GAP - EPS and
                b["x"] + b["dx"] <= L - GAP + EPS and b["y"] + b["dy"] <= W - GAP + EPS)

    def snapshot(self):
        self.history.append(([dict(b) for b in self.placed], list(self.unplaced), set(self.pinned)))
        del self.history[:-40]

    def undo(self):
        if not self.history:
            messagebox.showinfo(APP_TITLE, "Nothing to undo.", parent=self)
            return
        self.placed, self.unplaced, self.pinned = self.history.pop()
        self.refresh_all()

    def refresh_all(self):
        assign_order(self.placed)
        self.update_summary()
        self.fill_tree()
        self.canvas.set_data(self.placed, self.pinned, self.sel, self.door.get() == "left")
        self.update_selection_panel()

    def update_summary(self):
        L, W, H = self.dims
        vol = sum(b["dx"] * b["dy"] * b["h"] for b in self.placed)
        used = max((b["x"] + b["dx"] for b in self.placed), default=0)
        self.summary.config(text=(
            f"{self.cname}: {fmt(L)} × {fmt(W)} × {fmt(H)} mm.   "
            f"Loads placed: {len(self.placed)} of {self.total}.   "
            f"Max. load height: {fmt(min(H, MAX_H))} mm.   "
            f"Volume utilisation: {vol / (L * W * H) * 100:.1f}%.   "
            f"Length used: {fmt(used)} mm, free towards the doors: {fmt(L - used)} mm.   "
            f"Doors: {self.door.get()}."))
        self.warn.config(text=("DID NOT FIT:\n" + "\n".join(group_unplaced(self.unplaced)))
                         if self.unplaced else "")

    def fill_tree(self):
        for i in self.tree.get_children():
            self.tree.delete(i)
        rows = [(b["n"], (b["label"], b["kind"], f"{fmt(b['dx'])}×{fmt(b['dy'])}", fmt(b["x"]),
                          fmt(b["y"]), b["order"], "●" if b["n"] in self.pinned else ""), ())
                for b in self.placed]
        rows += [(p.number, (p.label, p.kind, f"{fmt(p.l)}×{fmt(p.w)}", "-", "-", "-", ""),
                  ("unplaced",)) for p, _ in self.unplaced]
        for n, vals, tags in sorted(rows, key=lambda r: r[0]):
            self.tree.insert("", "end", iid=str(n), values=vals, tags=tags)
        if self.sel is not None and self.tree.exists(str(self.sel)):
            self._lock = True
            self.tree.selection_set(str(self.sel))
            self._lock = False

    def update_selection_panel(self):
        b = self.get_placed(self.sel) if self.sel is not None else None
        if b:
            self.sel_lbl.config(text=f"#{b['label']}  {b['kind']}  {fmt(b['dx'])} × {fmt(b['dy'])} × "
                                     f"{fmt(b['h'])} mm" + ("   (pinned)" if b["n"] in self.pinned else ""))
            self.xv.set(fmt(b["x"]))
            self.yv.set(fmt(b["y"]))
        elif self.sel is not None:
            self.sel_lbl.config(text=f"#{self.sel}: does not fit - use 'Re-arrange others' or Undo")
            self.xv.set("")
            self.yv.set("")
        else:
            self.sel_lbl.config(text="none selected")
            self.xv.set("")
            self.yv.set("")

    # ---------- selection ----------
    def on_tree_select(self, event=None):
        if self._lock:
            return
        sel = self.tree.selection()
        self.sel = int(sel[0]) if sel else None
        self.canvas.set_data(self.placed, self.pinned, self.sel)
        self.update_selection_panel()

    def on_canvas_select(self, n):
        self.sel = n
        self._lock = True
        if n is not None and self.tree.exists(str(n)):
            self.tree.selection_set(str(n))
            self.tree.see(str(n))
        else:
            self.tree.selection_set(())
        self._lock = False
        self.update_selection_panel()
        self.canvas.selected = n

    def on_door(self):
        self.update_summary()
        self.canvas.set_data(self.placed, self.pinned, self.sel, self.door.get() == "left")

    def need_selected(self):
        b = self.get_placed(self.sel) if self.sel is not None else None
        if b is None:
            messagebox.showinfo(APP_TITLE, "Select a placed load first (click it in the list "
                                           "or in the picture).", parent=self)
        return b

    # ---------- moving things ----------
    def place_manually(self, nb):
        """Applies a new position / orientation for one load (and pins it)."""
        n = nb["n"]
        others = [o for o in self.placed if o["n"] != n]
        pinned_conf = [o for o in others if o["n"] in self.pinned and boxes_conflict(nb, o)]
        if pinned_conf:
            messagebox.showinfo(APP_TITLE, f"That position is too close to the pinned load "
                                           f"#{pinned_conf[0]['label']} (clearance {fmt(GAP)} mm is "
                                           f"required). Unpin it first or choose another place.",
                                parent=self)
            self.refresh_all()
            return False
        conf = [o for o in others if boxes_conflict(nb, o)]
        if conf and not self.auto.get():
            messagebox.showinfo(APP_TITLE, f"That position is too close to load #{conf[0]['label']}. "
                                           "Switch on 'Re-arrange the other loads automatically' "
                                           "or move that load first.", parent=self)
            self.refresh_all()
            return False
        self.snapshot()
        b = self.get_placed(n)
        b.update(x=nb["x"], y=nb["y"], dx=nb["dx"], dy=nb["dy"], rotated=nb["rotated"])
        self.pinned.add(n)
        if conf:
            self.repack({o["n"] for o in conf})
        self.refresh_all()
        return True

    def repack(self, conflicting=None):
        """Arranges the loads that are not pinned again. If `conflicting` is given, first only
        those loads (and the unplaced ones) are moved and everything else stays where it is."""
        L, W, H = self.dims
        self.config(cursor="watch")
        self.update_idletasks()

        def attempt(movable):
            fixed = {b["n"]: (b["x"], b["y"], b["dx"], b["dy"])
                     for b in self.placed if b["n"] not in movable}
            return plan_loading(L, W, H, self.loads, fixed=fixed, budget=1.0)

        def all_fit(res):
            return not any(r == NO_SPACE for _, r in res[1])

        result = None
        if conflicting:
            res = attempt(set(conflicting))
            if all_fit(res):
                result = res
        if result is None:
            result = attempt({b["n"] for b in self.placed if b["n"] not in self.pinned})
        self.config(cursor="")
        self.placed, self.unplaced = result
        if not all_fit(result):
            self.after(50, lambda: messagebox.showwarning(
                APP_TITLE, "Not all loads fit around the pinned loads. The loads that do not fit "
                           "are listed in red. Use Undo, or unpin some loads and try again.",
                parent=self))

    def rotate_selected(self):
        b = self.need_selected()
        if not b:
            return
        L, W, _ = self.dims
        nb = dict(b, dx=b["dy"], dy=b["dx"], rotated=not b["rotated"])
        nb["x"] = min(max(b["x"], GAP), L - GAP - nb["dx"])
        nb["y"] = min(max(b["y"], GAP), W - GAP - nb["dy"])
        if not self.inside(nb):
            messagebox.showinfo(APP_TITLE, "This load cannot be rotated: it would not fit "
                                           "inside the container.", parent=self)
            return
        self.place_manually(nb)

    def toggle_pin(self):
        b = self.need_selected()
        if not b:
            return
        self.snapshot()
        self.pinned.symmetric_difference_update({b["n"]})
        self.refresh_all()

    def slide(self, direction):
        b = self.need_selected()
        if not b:
            return
        L, W, _ = self.dims
        others = [o for o in self.placed if o["n"] != b["n"]]
        nb = dict(b)
        if direction in ("front", "door"):
            lim = GAP if direction == "front" else L - GAP - b["dx"]
            for o in others:
                if max(o["y"] - (b["y"] + b["dy"]), b["y"] - (o["y"] + o["dy"])) >= GAP - EPS:
                    continue  # not side by side with this load
                if direction == "front" and o["x"] + o["dx"] <= b["x"] + EPS:
                    lim = max(lim, o["x"] + o["dx"] + GAP)
                if direction == "door" and o["x"] >= b["x"] + b["dx"] - EPS:
                    lim = min(lim, o["x"] - GAP - b["dx"])
            nb["x"] = lim
        else:
            lim = GAP if direction == "left" else W - GAP - b["dy"]
            for o in others:
                if max(o["x"] - (b["x"] + b["dx"]), b["x"] - (o["x"] + o["dx"])) >= GAP - EPS:
                    continue
                if direction == "left" and o["y"] + o["dy"] <= b["y"] + EPS:
                    lim = max(lim, o["y"] + o["dy"] + GAP)
                if direction == "right" and o["y"] >= b["y"] + b["dy"] - EPS:
                    lim = min(lim, o["y"] - GAP - b["dy"])
            nb["y"] = lim
        if abs(nb["x"] - b["x"]) < 0.5 and abs(nb["y"] - b["y"]) < 0.5:
            messagebox.showinfo(APP_TITLE, "This load is already as far as it can go in that "
                                           "direction.", parent=self)
            return
        self.place_manually(nb)

    def apply_xy(self):
        b = self.need_selected()
        if not b:
            return
        try:
            x = parse_pos(self.xv.get(), "X")
            y = parse_pos(self.yv.get(), "Y")
        except ValueError as e:
            messagebox.showerror(APP_TITLE, str(e), parent=self)
            return
        nb = dict(b, x=x, y=y)
        if not self.inside(nb):
            messagebox.showinfo(APP_TITLE, f"Outside the container: loads must stay {fmt(GAP)} mm "
                                           "away from the walls and doors.", parent=self)
            return
        self.place_manually(nb)

    def snap(self, b, x, y, thr=60):
        """Clamps the dropped position to the container and snaps it to walls / neighbours."""
        L, W, _ = self.dims
        dx, dy = b["dx"], b["dy"]
        cx, cy = [GAP, L - GAP - dx], [GAP, W - GAP - dy]
        for o in self.placed:
            if o["n"] == b["n"]:
                continue
            cx += [o["x"] + o["dx"] + GAP, o["x"] - GAP - dx, o["x"], o["x"] + o["dx"] - dx]
            cy += [o["y"] + o["dy"] + GAP, o["y"] - GAP - dy, o["y"], o["y"] + o["dy"] - dy]
        x = min(max(x, GAP), L - GAP - dx)
        y = min(max(y, GAP), W - GAP - dy)
        bx = min(cx, key=lambda v: abs(v - x))
        by = min(cy, key=lambda v: abs(v - y))
        if abs(bx - x) <= thr:
            x = bx
        if abs(by - y) <= thr:
            y = by
        return (round(min(max(x, GAP), L - GAP - dx), 1), round(min(max(y, GAP), W - GAP - dy), 1))

    def on_drop(self, n, x, y):
        b = self.get_placed(n)
        if b is None:
            return
        x, y = self.snap(b, x, y)
        if abs(x - b["x"]) < 0.5 and abs(y - b["y"]) < 0.5:
            return
        self.place_manually(dict(b, x=x, y=y))

    def rearrange(self):
        self.snapshot()
        self.repack()
        self.refresh_all()

    def unpin_all(self):
        self.snapshot()
        self.pinned.clear()
        self.refresh_all()

    def start_over(self):
        self.snapshot()
        self.pinned.clear()
        L, W, H = self.dims
        self.config(cursor="watch")
        self.update_idletasks()
        self.placed, self.unplaced = plan_loading(L, W, H, self.loads, budget=1.5)
        self.config(cursor="")
        self.refresh_all()

    # ---------- export ----------
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
            img = render_plan_image(self.cname, self.dims, self.placed, self.unplaced, self.total,
                                    door_left=(self.door.get() == "left"))
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
        dlg = ImportDialog(self, files, len(self.pallets) + 1, DEFAULT_H)
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
        placed, unplaced = plan_loading(L, W, H, self.pallets, budget=1.5)
        self.config(cursor="")
        ResultWindow(self, CONTAINERS[self.ckey][0], (L, W, H), list(self.pallets), placed, unplaced)


def main():
    try:  # sharp rendering on Windows with display scaling
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    App().mainloop()


if __name__ == "__main__":
    main()
