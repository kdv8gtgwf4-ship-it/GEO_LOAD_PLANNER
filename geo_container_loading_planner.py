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
GAP = 25.0      # clearance between loads, mm (can be changed in the loading plan window)
WALL = 25.0     # clearance from the walls and doors, mm (can be changed as well)
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
PACK_MODE = "balanced"   # balanced / order / length - see set_pack_mode()
BALANCE_SLACK = 300.0    # balanced mode: how much longer than the shortest layout is acceptable, mm
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


def set_pack_mode(mode):
    """balanced = as compact as possible (+ BALANCE_SLACK) and, within that, small loads at the
    front wall and big ones at the doors;  order = small -> big has priority, the layout may be
    longer;  length = shortest layout, the order is only a second criterion."""
    global PACK_MODE
    PACK_MODE = mode if mode in ("balanced", "order", "length") else "balanced"


def set_clearance(between, walls):
    """Changes the clearances for the whole program (used by the planner and the editor)."""
    global GAP, WALL
    GAP, WALL = float(between), float(walls)


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


def _objective(placed, failed, fixed_info, mode="order", cap=None, fixed_maxx=0.0):
    """Smaller is better. First: loads that did not fit. Then, depending on the mode, the used
    length and / or the penalty for big loads standing nearer to the front wall than small ones
    (smaller loads should be at the front wall, the biggest ones next to the doors)."""
    items = [(p.l * p.w, x + dx / 2.0) for p, x, y, dx, dy in placed] + list(fixed_info)
    pen = 0.0
    for i, (ai, xi) in enumerate(items):
        for j, (aj, xj) in enumerate(items):
            if i != j and ai < 0.9 * aj and xi > xj + 150:
                pen += (xi - xj - 150) / 1000.0
    maxx = max([x + dx for p, x, y, dx, dy in placed] + [fixed_maxx])
    pen = round(pen, 3)
    if mode == "length":
        return (len(failed), maxx, pen)
    if mode == "capped":
        return (len(failed), max(0.0, maxx - cap), pen, maxx)
    return (len(failed), pen, maxx)


def _solve(loads, Le, We, fixed, fixed_info, budget, seed=1, mode="order", cap=None, fixed_maxx=0.0):
    """Searches for an arrangement in which all loads fit and the smallest loads are at the
    front wall and the largest next to the doors (swapping order / orientation, hill climbing)."""
    if not loads:
        return [], [], None
    rnd = random.Random(seed)
    min_side = min(min(p.l, p.w) for p in loads) + GAP
    key_asc = lambda p: (p.l * p.w, max(p.l, p.w), p.number)
    inits = [sorted(loads, key=key_asc), sorted(loads, key=key_asc, reverse=True),
             sorted(loads, key=lambda p: (-max(p.l, p.w), -min(p.l, p.w))), list(loads)]

    def evaluate(order, pref):
        pl, fl = _decode(Le, We, order, pref, fixed, min_side)
        return _objective(pl, fl, fixed_info, mode, cap, fixed_maxx), pl, fl

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
        if best[0][0] == 0 and since_best > 6000:
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
    return best[3], best[4], best[0]


def boxes_conflict(a, b):
    """True if two placed loads overlap or are closer to each other than GAP."""
    gx = max(b["x"] - (a["x"] + a["dx"]), a["x"] - (b["x"] + b["dx"]))
    gy = max(b["y"] - (a["y"] + a["dy"]), a["y"] - (b["y"] + b["dy"]))
    return max(gx, gy) < GAP - EPS


def assign_order(placed):
    """Loading sequence: from the front wall towards the doors; a load that stands on another
    one comes right after the load below it."""
    by_n = {b["n"]: b for b in placed}

    def root_key(b):
        seen = 0
        while b.get("base") and b["base"] in by_n and seen < 20:
            b = by_n[b["base"]]
            seen += 1
        return (round(b["x"], 1), round(b["y"], 1))

    placed.sort(key=lambda b: (root_key(b), b.get("level", 1), b["n"]))
    for i, b in enumerate(placed, 1):
        b["order"] = i


def attach_stacks(floor, stack, by_n):
    """Adds the loads that stand on top of other loads to the floor loads.
    stack = {top number: dict(base, u, v, du, dv)} - position of the top load in the frame of the
    load below it (u along its length, v along its width), so a stack moves and turns as one.
    Returns (all placed loads, numbers of top loads whose base load is not placed)."""
    placed = {b["n"]: b for b in floor}
    pending = dict(stack)
    progress = True
    while pending and progress:
        progress = False
        for n, st in list(pending.items()):
            bb = placed.get(st["base"])
            if bb is None or n not in by_n:
                continue
            p = by_n[n]
            if bb["rotated"]:
                x, y, dx, dy = bb["x"] + st["v"], bb["y"] + st["u"], st["dv"], st["du"]
            else:
                x, y, dx, dy = bb["x"] + st["u"], bb["y"] + st["v"], st["du"], st["dv"]
            placed[n] = dict(n=n, label=p.label, kind=p.kind, x=x, y=y, z=bb["z"] + bb["h"],
                             dx=dx, dy=dy, h=p.h, level=bb["level"] + 1,
                             rotated=abs(dx - p.l) > EPS, pallet=p, base=st["base"])
            del pending[n]
            progress = True
    has_top = {b["base"] for b in placed.values() if b.get("base")}
    for b in placed.values():
        if b["n"] in has_top or b.get("base"):
            b["label"] = f"{b['n']}/{b['level']}"
    return list(placed.values()), list(pending)


def plan_loading(L, W, H, pallets, fixed=None, budget=1.5, skip=()):
    """Builds the loading plan. Returns (placed, unplaced[(load, reason)]).
    fixed = {load number: (x, y, dx, dy)} - loads that must stay exactly where they are;
    all the other loads are arranged around them. skip = numbers of loads that are put on top
    of other loads by hand (they are not placed on the floor)."""
    fixed = fixed or {}
    unplaced, candidates, fixed_loads = [], [], []
    Hmax = min(H, MAX_H)  # height is limited by both the container and the 220 cm rule
    Le, We = L - 2 * WALL, W - 2 * WALL  # usable floor after clearance from walls and doors
    for p in pallets:
        if p.number in skip:
            continue
        if p.number in fixed:
            fixed_loads.append(p)
        elif p.h > Hmax + EPS:
            unplaced.append((p, f"height exceeds the allowed maximum ({fmt(Hmax)} mm)"))
        elif Le <= 0 or We <= 0 or not ((p.l <= Le + EPS and p.w <= We + EPS) or
                                        (p.w <= Le + EPS and p.l <= We + EPS)):
            unplaced.append((p, f"does not fit the container interior "
                                f"({fmt(WALL)} mm clearance from walls and doors is required)"))
        else:
            candidates.append(p)

    fx = [(fixed[p.number][0] - WALL, fixed[p.number][1] - WALL, fixed[p.number][2], fixed[p.number][3])
          for p in fixed_loads]
    info = [(p.l * p.w, fixed[p.number][0] - WALL + fixed[p.number][2] / 2.0) for p in fixed_loads]
    fmaxx = max([x + dx for x, y, dx, dy in fx], default=0.0)
    if PACK_MODE == "length":
        placed_eff, failed, _ = _solve(candidates, Le, We, fx, info, budget, mode="length",
                                       fixed_maxx=fmaxx)
    elif PACK_MODE == "order":
        placed_eff, failed, _ = _solve(candidates, Le, We, fx, info, budget, mode="order",
                                       fixed_maxx=fmaxx)
    else:  # balanced: first find how short the layout can be, then order the loads within that
        pl1, fl1, ob1 = _solve(candidates, Le, We, fx, info, budget * 0.45, mode="length",
                               fixed_maxx=fmaxx)
        if ob1 is None or ob1[0] > 0:  # not everything fits: just use the best fit found
            placed_eff, failed = pl1, fl1
        else:
            cap = ob1[1] + BALANCE_SLACK
            placed_eff, failed, _ = _solve(candidates, Le, We, fx, info, budget * 0.55,
                                           mode="capped", cap=cap, fixed_maxx=fmaxx)
            if len(failed) > 0:
                placed_eff, failed = pl1, fl1
    for p in failed:
        unplaced.append((p, NO_SPACE))

    placed = []
    for p, x, y, dx, dy in placed_eff:
        placed.append(dict(n=p.number, label=p.label, kind=p.kind, x=x + WALL, y=y + WALL, z=0.0,
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
def parse_nonneg(text, name):
    try:
        v = float(str(text).strip().replace(",", ".").replace(" ", ""))
    except ValueError:
        raise ValueError(f"Field \"{name}\": please enter a number.")
    if v < 0:
        raise ValueError(f"Field \"{name}\" must not be negative.")
    return v


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
        fit_window(self, 980, 640, 760, 480)
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
#  Saved configuration / layout files
# ----------------------------------------------------------------------------
def config_from_data(data):
    """Reads a configuration file (container, dimensions, loads). Returns (key, loads, dims)."""
    key = str(data["container"])
    if key not in CONTAINERS:
        raise ValueError("unknown container type")
    loads = [Pallet(i + 1, float(d["l"]), float(d["w"]), float(d["h"]),
                    d.get("kind") if d.get("kind") in KINDS else "Pallet",
                    0, bool(d.get("assumed_h", False)), str(d.get("origin", "")))
             for i, d in enumerate(data["loads"])]
    cl = data.get("clearance")
    if cl:
        set_clearance(float(cl.get("between", GAP)), float(cl.get("walls", WALL)))
    return key, loads, data.get("dims", {})


# ----------------------------------------------------------------------------
#  Loading diagram (top view) - on screen
# ----------------------------------------------------------------------------
class PlanCanvas(tk.Canvas):
    """Top view of the container. Loads can be selected and dragged with the mouse.
    Internal coordinates: X from the front wall (doors at X = L), Y from the left wall.
    door_left=True turns the picture by 180 degrees (doors on the left side).
    Loads standing on other loads are drawn on top of them (shadow + navy frame)."""

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
        self.on_context = None
        for ev in ("<Button-3>", "<Button-2>", "<Control-Button-1>"):
            self.bind(ev, self._context)

    def _context(self, e):
        """Right click on a load in the picture: select it and open its menu."""
        if self.s is None:
            return
        b = self._hit(e.x, e.y)
        if b is None:
            return
        self.selected = b["n"]
        if self.on_select:
            self.on_select(b["n"])
        self.redraw()
        if self.on_context:
            self.on_context(b["n"], e.x_root, e.y_root)

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

    def _drawing_order(self):
        return sorted(self.placed, key=lambda b: b.get("level", 1))

    def _stack_members(self, n):
        """The load with number n, the loads below it and everything standing on them."""
        by_n = {b["n"]: b for b in self.placed}
        root = n
        for _ in range(30):
            base = by_n.get(root, {}).get("base")
            if not base:
                break
            root = base
        members, todo = {root}, [root]
        while todo:
            c = todo.pop()
            for b in self.placed:
                if b.get("base") == c and b["n"] not in members:
                    members.add(b["n"])
                    todo.append(b["n"])
        return members

    # ---- drawing -----------------------------------------------------------
    def _font(self, px, bold=False):
        from tkinter import font as tkfont
        key = (px, bold)
        if key not in self._fonts:
            self._fonts[key] = tkfont.Font(family="Segoe UI", size=-int(px),
                                           weight="bold" if bold else "normal")
        return self._fonts[key]

    def _fit_texts(self, texts, x1, y1, x2, y2, tag, min_lines=1, min_px=7):
        """Writes the lines into the rectangle with the biggest font that fits; False if none."""
        rw, rh = x2 - x1, y2 - y1
        if rw <= 4 or rh <= 4:
            return False
        for nlines in (3, 2, 1):
            if nlines < min_lines or nlines > len(texts):
                continue
            for px in range(18, min_px - 1, -1):
                sizes = [px, max(7, int(px * 0.72)), max(7, int(px * 0.64))][:nlines]
                fonts = [self._font(sizes[0], True)] + [self._font(z) for z in sizes[1:]]
                wmax = max(f.measure(t) for f, t in zip(fonts, texts))
                lhs = [f.metrics("linespace") for f in fonts]
                if wmax <= rw * 0.94 and sum(lhs) <= rh * 0.94:
                    yy = (y1 + y2) / 2 - sum(lhs) / 2
                    for f, t, lh in zip(fonts, texts, lhs):
                        self.create_text((x1 + x2) / 2, yy + lh / 2, text=t, font=f, tags=(tag,))
                        yy += lh
                    return True
        return False

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

        tops_of = {}
        for b in self.placed:
            if b.get("base"):
                tops_of.setdefault(b["base"], []).append(b)
        order = self._drawing_order()
        # 1. the rectangles (loads standing on others get a shadow, a lighter fill and a navy frame)
        for b in order:
            x1, y1, x2, y2 = self.rect_of(b)
            tag = f"L{b['n']}"
            color = PALETTE[(b["n"] - 1) % len(PALETTE)]
            sel = (b["n"] == self.selected)
            if b.get("base"):
                self.create_rectangle(x1 + 3, y1 + 3, x2 + 3, y2 + 3, fill="#7a8599", outline="",
                                      tags=(tag,))
                fill, outline, width = mix(color, "#ffffff", 0.35), NAVY, 3
            else:
                fill, outline, width = color, "#222", 1.5
            if sel:
                outline, width = "#1e90ff", 4
            self._rects[b["n"]] = self.create_rectangle(x1, y1, x2, y2, fill=fill, outline=outline,
                                                        width=width, tags=(tag,))
        # 2. loads that carry others: text into the free strips around the upper loads, or a plate
        plates = []  # (base number, x1, y1, x2, y2, lines)
        for b in order:
            tops = tops_of.get(b["n"])
            if not tops:
                continue
            x1, y1, x2, y2 = self.rect_of(b)
            tag = f"L{b['n']}"
            texts = (f"#{b['label']}", b["kind"], f"{fmt(b['dx'])}×{fmt(b['dy'])}×{fmt(b['h'])}")
            two = (f"#{b['label']}  {b['kind']}", texts[2])
            rects = [self.rect_of(t) for t in tops]
            bx1, by1 = min(r[0] for r in rects), min(r[1] for r in rects)
            bx2, by2 = max(r[2] for r in rects), max(r[3] for r in rects)
            strips = [(x1, y1, x2, by1), (x1, by2, x2, y2), (x1, y1, bx1, y2), (bx2, y1, x2, y2)]
            strips.sort(key=lambda r: -((r[2] - r[0]) * (r[3] - r[1])))
            if not any(self._fit_texts(texts, *r, tag, min_lines=3, min_px=9) or
                       self._fit_texts(two, *r, tag, min_lines=2, min_px=9) for r in strips):
                f1, f2 = self._font(10, True), self._font(9)
                w = min(max(f1.measure(two[0]), f2.measure(two[1])) + 10, x2 - x1 - 4)
                plates.append((b["n"], x1 + 2, y1 + 2, x1 + 2 + w, y1 + 34, two))
        for n, px1, py1, px2, py2, lines in plates:
            tag = f"L{n}"
            self.create_rectangle(px1, py1, px2, py2, fill="white", outline="#222", tags=(tag,))
            self.create_text(px1 + 5, py1 + 10, text=lines[0], font=self._font(10, True), anchor="w",
                             tags=(tag,))
            self.create_text(px1 + 5, py1 + 24, text=lines[1], font=self._font(9), anchor="w",
                             tags=(tag,))
        # 3. text of all the other loads (kept clear of the plates)
        for b in order:
            if b["n"] in tops_of:
                x1, y1, x2, y2 = self.rect_of(b)
            else:
                x1, y1, x2, y2 = self.rect_of(b)
                for n, px1, py1, px2, py2, _ in plates:
                    if n != b["n"] and px1 < x2 and px2 > x1 and py1 < y2 and py2 > y1:
                        y1 = max(y1, py2 + 2)
                texts = (f"#{b['label']}", b["kind"], f"{fmt(b['dx'])}×{fmt(b['dy'])}×{fmt(b['h'])}")
                self._fit_texts(texts, x1, y1, x2, y2, f"L{b['n']}")
            if b["n"] in self.pinned:  # small navy dot = this load is pinned
                x1, y1, x2, y2 = self.rect_of(b)
                self.create_oval(x2 - 14, y1 + 4, x2 - 4, y1 + 14, fill=NAVY, outline="white",
                                 width=1.5, tags=(f"L{b['n']}",))

    # ---- mouse -------------------------------------------------------------
    def _hit(self, x, y):
        for b in reversed(self._drawing_order()):
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
        for m in self._stack_members(d["n"]):  # a stack moves as one
            self.move(f"L{m}", e.x - d["last"][0], e.y - d["last"][1])
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
#  Loading diagram -> images (PNG / PDF export, needs Pillow): page 1 plan, page 2 3D view
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


def _fit_block(d, rw, rh, specs, min_fs=10, max_fs=120):
    """specs = [(text, size factor, bold)]. Largest font size at which all lines fit into the
    rectangle rw x rh, or None."""
    if rw <= 4 or rh <= 4:
        return None
    for fs in range(max_fs, int(min_fs) - 1, -2):
        wmax = max(d.textlength(t, font=_pil_font(max(6, int(fs * k)), b)) for t, k, b in specs)
        hh = sum(int(fs * k * 1.3) for _, k, _ in specs)
        if wmax <= rw * 0.92 and hh <= rh * 0.88:
            return fs
    return None


def _draw_block(d, cx, cy, specs, fs, color="#111111"):
    hs = [int(fs * k * 1.3) for _, k, _ in specs]
    yy = cy - sum(hs) / 2
    for (text, k, bold), hh in zip(specs, hs):
        _text_center(d, cx, yy + hh / 2, text, _pil_font(max(6, int(fs * k)), bold), color)
        yy += hh


def _spec_options(label, kind, dims):
    """Text layouts, richest first: 3 lines / 2 lines / label only."""
    return [[(label, 1.0, True), (kind, 0.66, False), (dims, 0.58, False)],
            [(f"{label}  {kind}", 1.0, True), (dims, 0.66, False)],
            [(label, 1.0, True)]]


def _summary_lines(dims, placed, unplaced, total, door_left):
    import textwrap
    L, W, H = dims
    used = max((b["x"] + b["dx"] for b in placed), default=0)
    stacked = sum(1 for b in placed if b.get("base"))
    l2 = (f"Loads placed: {len(placed)} of {total}    |    Length used: {fmt(used)} mm, "
          f"free towards the doors: {fmt(L - used)} mm")
    if stacked:
        l2 += f"    |    Loads standing on others: {stacked}"
    lines = [
        (f"Container interior: {fmt(L)} × {fmt(W)} × {fmt(H)} mm    |    "
         f"Max. load height: {fmt(min(H, MAX_H))} mm", MUTED),
        (f"Clearance: between loads {fmt(GAP)} mm, from walls / doors {fmt(WALL)} mm    |    "
         f"Doors: {'left' if door_left else 'right'}", MUTED),
        (l2, NAVY),
    ]
    first = True
    for g_ in group_unplaced(unplaced):
        for ln in textwrap.wrap(("DID NOT FIT:  " if first else "") + g_, 125):
            lines.append((ln, "#b00020"))
        first = False
    return lines


def _new_page(IW, P, title, cname, lines, content_h):
    """Page with header (title, company logo, summary lines) and footer. Returns
    (image, draw, y of the top of the content area)."""
    from PIL import Image, ImageDraw
    y_lines, row_h = P(215), P(46)
    top = y_lines + row_h * len(lines) + P(90)
    IH = int(top + content_h + P(90) + P(84))
    img = Image.new("RGB", (IW, IH), "white")
    d = ImageDraw.Draw(img)
    d.rectangle([0, 0, IW, P(16)], fill=NAVY)
    d.text((P(60), P(46)), title, font=_pil_font(P(66), True), fill=NAVY)
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
    d.rectangle([0, IH - P(70), IW, IH], fill=NAVY)
    d.text((P(60), IH - P(52)), FOOTER_TEXT, font=_pil_font(P(28), True), fill="#c9d4e8")
    d.text((IW - P(60), IH - P(52)), "Geo Container Loading Planner   |   created by Evgenii",
           font=_pil_font(P(28)), fill="#c9d4e8", anchor="ra")
    return img, d, top


def render_plan_image(cname, dims, placed, unplaced, total, door_left=False):
    """Page 1: top view with #label / type / size on every load (about 4000 px wide).
    Loads standing on others are drawn on top of them with a shadow and a navy frame."""
    L, W, H = dims
    IW = 4000
    u = IW / 2400.0

    def P(v):
        return int(round(v * u))

    ml, mr = P(210), P(210)
    s = (IW - ml - mr) / L
    ch = W * s
    lines = _summary_lines(dims, placed, unplaced, total, door_left)
    img, d, top = _new_page(IW, P, "Loading Plan", cname, lines, ch)
    bottom = top + ch

    ox = ml
    right = ox + L * s
    d.rectangle([ox, top, right, bottom], fill="#f3f3f3", outline="#333333", width=P(5))
    door_x = ox if door_left else right
    d.line([door_x, top, door_x, bottom], fill="#b00020", width=P(14))
    f_door = _pil_font(P(36), True)
    from PIL import Image, ImageDraw
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

    def rect(b):
        if door_left:  # picture turned by 180 degrees
            x1 = ox + (L - b["x"] - b["dx"]) * s
            y1 = top + b["y"] * s
        else:
            x1 = ox + b["x"] * s
            y1 = bottom - (b["y"] + b["dy"]) * s
        return x1, y1, x1 + b["dx"] * s, y1 + b["dy"] * s

    tops_of = {}
    for b in placed:
        if b.get("base"):
            tops_of.setdefault(b["base"], []).append(b)
    order = sorted(placed, key=lambda b: b.get("level", 1))
    # 1. the rectangles (a load standing on another one: shadow, lighter fill, navy frame)
    for b in order:
        x1, y1, x2, y2 = rect(b)
        color = PALETTE[(b["n"] - 1) % len(PALETTE)]
        if b.get("base"):
            d.rectangle([x1 + P(6), y1 + P(6), x2 + P(6), y2 + P(6)], fill="#7a8599")
            d.rectangle([x1, y1, x2, y2], fill=mix(color, "#ffffff", 0.35), outline=NAVY, width=P(5))
        else:
            d.rectangle([x1, y1, x2, y2], fill=color, outline="#222222", width=P(3))
    # 2. loads that carry others: text into the free strips around the upper loads, else a plate
    plates = []  # (base number, x1, y1, x2, y2, specs, font size)
    for b in order:
        tops = tops_of.get(b["n"])
        if not tops:
            continue
        x1, y1, x2, y2 = rect(b)
        opts = _spec_options(f"#{b['label']}", b["kind"], f"{fmt(b['dx'])}×{fmt(b['dy'])}×{fmt(b['h'])}")
        rects = [rect(t) for t in tops]
        bx1, by1 = min(r[0] for r in rects), min(r[1] for r in rects)
        bx2, by2 = max(r[2] for r in rects), max(r[3] for r in rects)
        strips = [(x1, y1, x2, by1), (x1, by2, x2, y2), (x1, y1, bx1, y2), (bx2, y1, x2, y2)]
        strips.sort(key=lambda r: -((r[2] - r[0]) * (r[3] - r[1])))
        done = False
        for sx1, sy1, sx2, sy2 in strips:
            for specs in opts[:2]:
                fs = _fit_block(d, sx2 - sx1, sy2 - sy1, specs, min_fs=P(15))
                if fs:
                    _draw_block(d, (sx1 + sx2) / 2, (sy1 + sy2) / 2, specs, fs)
                    done = True
                    break
            if done:
                break
        if not done:
            specs = opts[1]
            for fs in range(P(26), P(11), -2):
                w = max(d.textlength(t, font=_pil_font(int(fs * k), bl)) for t, k, bl in specs) + P(18)
                if w <= (x2 - x1) - P(8):
                    break
            hh = sum(int(fs * k * 1.3) for _, k, _ in specs) + P(12)
            plates.append((b["n"], x1 + P(4), y1 + P(4), x1 + P(4) + w, y1 + P(4) + hh, specs, fs))
    for n, px1, py1, px2, py2, specs, fs in plates:
        d.rectangle([px1, py1, px2, py2], fill="white", outline="#222222", width=P(2))
        _draw_block(d, (px1 + px2) / 2, (py1 + py2) / 2, specs, fs)
    # 3. text of all the other loads (kept clear of the plates)
    for b in order:
        if b["n"] in tops_of:
            continue
        x1, y1, x2, y2 = rect(b)
        for n, px1, py1, px2, py2, _, _ in plates:
            if n != b["n"] and px1 < x2 and px2 > x1 and py1 < y2 and py2 > y1:
                y1 = max(y1, py2 + P(4))
        opts = _spec_options(f"#{b['label']}", b["kind"], f"{fmt(b['dx'])}×{fmt(b['dy'])}×{fmt(b['h'])}")
        for specs in opts:
            fs = _fit_block(d, x2 - x1, y2 - y1, specs)
            if fs:
                _draw_block(d, (x1 + x2) / 2, (y1 + y2) / 2, specs, fs)
                break
        else:
            _draw_block(d, (x1 + x2) / 2, (y1 + y2) / 2, opts[2], 10)
    return img


def render_3d_image(cname, dims, placed, unplaced, total, door_left=False):
    """Page 2: the same arrangement in 3D (oblique view from the doors side), so that loads
    standing on other loads can be seen."""
    import math
    L, W, H = dims
    IW = 4000
    u = IW / 2400.0

    def P(v):
        return int(round(v * u))

    kx, ky = 0.5, 1.3   # how the width axis is drawn (more "from above" so back rows stay visible)
    wmm, hmm = L + W * kx, H + W * ky
    margin = P(170)
    s = (IW - 2 * margin) / wmm
    lines = _summary_lines(dims, placed, unplaced, total, door_left)
    img, d, top = _new_page(IW, P, "Loading Plan - 3D view", cname, lines, hmm * s + P(60))
    y0 = top + P(30)

    def pr(x, y, z):
        return (margin + (x + y * kx) * s, y0 + (hmm - (z + y * ky)) * s)

    def poly(pts, fill, outline="#222222", width=P(2)):
        d.polygon([pr(*p) for p in pts], fill=fill, outline=outline)
        pp = [pr(*p) for p in pts]
        d.line(pp + [pp[0]], fill=outline, width=width)

    # container: floor and the two far walls (the doors are at the near end, on the right)
    poly([(0, 0, 0), (L, 0, 0), (L, W, 0), (0, W, 0)], "#e4e9f1", "#8a96ab", P(3))
    poly([(0, W, 0), (L, W, 0), (L, W, H), (0, W, H)], "#f3f5f9", "#9aa5b8", P(3))
    poly([(0, 0, 0), (0, W, 0), (0, W, H), (0, 0, H)], "#edf0f5", "#9aa5b8", P(3))

    boxes = [(b, b["x"], b["x"] + b["dx"], b["y"], b["y"] + b["dy"], b["z"], b["z"] + b["h"])
             for b in placed]
    n = len(boxes)

    def overlap(A, B):
        return (A[1] + A[3] * kx < B[2] + B[4] * kx - 1e-6 and B[1] + B[3] * kx < A[2] + A[4] * kx - 1e-6
                and A[5] + A[3] * ky < B[6] + B[4] * ky - 1e-6 and B[5] + B[3] * ky < A[6] + A[4] * ky - 1e-6)

    def behind(A, B):  # A is farther from the viewer than B (viewer: right, front, above)
        return A[2] <= B[1] + EPS or A[3] >= B[4] - EPS or A[6] <= B[5] + EPS

    after = [[] for _ in range(n)]
    indeg = [0] * n
    for i in range(n):
        for j in range(n):
            if i != j and overlap(boxes[i], boxes[j]) and behind(boxes[i], boxes[j]) \
                    and not behind(boxes[j], boxes[i]):
                after[i].append(j)
                indeg[j] += 1
    key = lambda i: (boxes[i][1] - boxes[i][3] + boxes[i][5], i)
    done, order = set(), []
    while len(order) < n:
        ready = [i for i in range(n) if i not in done and indeg[i] == 0] or \
                [i for i in range(n) if i not in done]
        i = min(ready, key=key)
        done.add(i)
        order.append(i)
        for j in after[i]:
            indeg[j] -= 1

    for i in order:
        b, x0, x1, ya, yb, z0, z1 = boxes[i]
        color = PALETTE[(b["n"] - 1) % len(PALETTE)]
        poly([(x1, ya, z0), (x1, yb, z0), (x1, yb, z1), (x1, ya, z1)], mix(color, "#000000", 0.28))
        poly([(x0, ya, z1), (x1, ya, z1), (x1, yb, z1), (x0, yb, z1)], mix(color, "#ffffff", 0.35))
        poly([(x0, ya, z0), (x1, ya, z0), (x1, ya, z1), (x0, ya, z1)], color)
        # text on the front face: number, type and size
        fx1, fy1 = pr(x0, ya, z1)
        fx2, fy2 = pr(x1, ya, z0)
        label = f"#{b['label']}"
        dims_t = f"{fmt(b['dx'])}×{fmt(b['dy'])}×{fmt(b['h'])}"
        for specs in _spec_options(label, b["kind"], dims_t):
            fs = _fit_block(d, fx2 - fx1, fy2 - fy1, specs, min_fs=P(8), max_fs=70)
            if fs:
                _draw_block(d, (fx1 + fx2) / 2, (fy1 + fy2) / 2, specs, fs)
                break
        # number on the top face as well (the front face may be hidden by other loads)
        tx, ty = pr((x0 + x1) / 2, (ya + yb) / 2, z1)
        fs = _fit_block(d, (x1 - x0) * s * 0.8, (yb - ya) * ky * s * 0.8, [(label, 1.0, True)],
                        min_fs=P(8), max_fs=60)
        if fs:
            _draw_block(d, tx, ty, [(label, 1.0, True)], fs)

    # door frame at the near end
    pp = [pr(L, 0, 0), pr(L, W, 0), pr(L, W, H), pr(L, 0, H)]
    d.line(pp + [pp[0]], fill="#b00020", width=P(9))
    _text_center(d, pr(L, W / 2, 0)[0] + P(95), (pr(L, 0, 0)[1] + pr(L, W, H)[1]) / 2, "DOORS",
                 _pil_font(P(36), True), "#b00020")
    _text_center(d, pr(L / 2, 0, 0)[0], pr(0, 0, 0)[1] + P(36),
                 f"length {fmt(L)} mm   |   width {fmt(W)} mm   |   height {fmt(H)} mm",
                 _pil_font(P(30)), MUTED)
    return img


# ----------------------------------------------------------------------------
#  Result window: diagram + editing of the arrangement
# ----------------------------------------------------------------------------
def fit_window(win, width, height, min_w=900, min_h=600):
    """Opens the window centred and never bigger than the screen (taskbar and title included)."""
    sw, sh = win.winfo_screenwidth(), win.winfo_screenheight()
    w, h = min(width, sw - 40), min(height, sh - 110)
    win.geometry(f"{w}x{h}+{max(0, (sw - w) // 2)}+{max(0, (sh - h) // 2 - 20)}")
    win.minsize(min(min_w, w), min(min_h, h))


class ScrollFrame(ttk.Frame):
    """A frame whose content can be scrolled up and down (scroll bar and mouse wheel)."""

    def __init__(self, master, width=380):
        super().__init__(master)
        self.canvas = tk.Canvas(self, bg="white", highlightthickness=0, width=width)
        self.vsb = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)
        self.vsb.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.inner = ttk.Frame(self.canvas)
        self._win = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
        self.inner.bind("<Configure>",
                        lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.bind("<Configure>", lambda e: self.canvas.itemconfigure(self._win, width=e.width))
        self.bind_all("<MouseWheel>", self._on_wheel, add="+")

    def _on_wheel(self, e):
        try:
            if not self.winfo_exists():
                return
            if isinstance(e.widget, (ttk.Treeview, tk.Listbox)):
                return  # lists scroll themselves
            w = self.winfo_containing(e.x_root, e.y_root)
            while w is not None and w is not self:
                w = w.master
            if w is None:
                return  # the pointer is not over this panel
            if self.inner.winfo_reqheight() <= self.canvas.winfo_height():
                return  # everything is visible, nothing to scroll
            self.canvas.yview_scroll(-1 if e.delta > 0 else 1, "units")
        except (tk.TclError, KeyError):
            pass


class ResultWindow(tk.Toplevel):
    COLS = [("order", "Loading order", 110), ("n", "#", 60), ("kind", "Type", 90),
            ("size", "Size L×W×H, mm", 150), ("x", "X, mm", 80), ("y", "Y, mm", 80),
            ("z", "Z, mm", 70), ("rot", "Orientation", 150)]

    def __init__(self, master, cname, dims, loads, placed, unplaced, ckey=None, layout=None):
        super().__init__(master)
        L, W, H = dims
        self.cname, self.dims, self.loads, self.ckey = cname, dims, loads, ckey
        self.by_n = {p.number: p for p in loads}
        self.total = len(loads)
        self.placed, self.unplaced = placed, unplaced
        self.stack = {}                      # top load number -> position on the load below it
        self.pinned, self.history, self.sel = set(), [], None
        self._lock = False
        self.door = tk.StringVar(value="right")
        self.auto = tk.BooleanVar(value=True)
        self.gap_var, self.wall_var = tk.StringVar(value=fmt(GAP)), tk.StringVar(value=fmt(WALL))
        self.title(f"Loading Plan - {cname}")
        self.configure(bg="white")
        fit_window(self, 1440, 920, 1000, 600)
        try:
            self.state("zoomed")  # use the whole screen on Windows
        except tk.TclError:
            pass
        build_header(self, "Loading Plan")

        self.summary = ttk.Label(self, text="", wraplength=1380, padding=(10, 8),
                                 font=("Segoe UI", 10, "bold"))
        self.summary.pack(fill="x")
        self.warn = tk.Label(self, text="", fg="#b00020", bg="white", wraplength=1380,
                             justify="left", font=("Segoe UI", 10, "bold"), padx=10)
        self.warn.pack(fill="x", anchor="w")
        self.bind("<Configure>", self._on_resize)

        bot = ttk.Frame(self, padding=(10, 0, 10, 8))
        bot.pack(side="bottom", fill="x")
        btnrow = ttk.Frame(bot)
        btnrow.pack(side="bottom", fill="x")
        ttk.Label(bot, text="Drag a load in the picture - the others are re-arranged around it.   "
                            "Select a load and press 'Put on' (or right-click it in the list "
                            "or in the picture) to stand it on another load.",
                  foreground=MUTED).pack(side="bottom", anchor="w", pady=(0, 4))
        ttk.Button(btnrow, text="Close", command=self.destroy).pack(side="right")
        ttk.Button(btnrow, text="Save as CSV…", command=self.save_csv).pack(side="right", padx=6)
        ttk.Button(btnrow, text="Save as PDF", style="Accent.TButton",
                   command=lambda: self.export("pdf")).pack(side="right", padx=6)
        ttk.Button(btnrow, text="Save as PNG", style="Accent.TButton",
                   command=lambda: self.export("png")).pack(side="right")
        ttk.Button(btnrow, text="Open layout…", command=self.load_layout).pack(side="right",
                                                                              padx=(6, 18))
        ttk.Button(btnrow, text="Save layout…", command=self.save_layout).pack(side="right")

        pw = ttk.PanedWindow(self, orient="horizontal")
        pw.pack(fill="both", expand=True, padx=8, pady=8)
        left = ttk.Frame(pw)
        right = ttk.Frame(pw, padding=(8, 0, 0, 0))
        pw.add(left, weight=4)
        pw.add(right, weight=1)
        self.canvas = PlanCanvas(left, L, W, self.placed, False, self.on_canvas_select, self.on_drop)
        self.canvas.configure(width=900, height=520)
        self.canvas.on_context = self.canvas_menu
        self.canvas.pack(fill="both", expand=True)
        self.build_panel(right)
        if layout:
            try:
                self.load_layout_data(layout)
            except Exception as e:
                messagebox.showerror(APP_TITLE, f"The saved layout could not be restored.\n({e})",
                                     parent=self)
                self.refresh_all()
        else:
            self.refresh_all()

    def _on_resize(self, e):
        if e.widget is self:
            w = max(300, e.width - 40)
            self.summary.config(wraplength=w)
            self.warn.config(wraplength=w)

    # ---------- right-hand panel (scrollable) ----------
    def build_panel(self, parent):
        sfr = ScrollFrame(parent, width=390)
        sfr.pack(fill="both", expand=True)
        p = sfr.inner
        box = ttk.LabelFrame(p, text="Doors and clearance", padding=8)
        box.pack(fill="x")
        r0 = ttk.Frame(box)
        r0.pack(fill="x")
        ttk.Radiobutton(r0, text="Doors on the right", value="right", variable=self.door,
                        command=self.on_door).pack(side="left")
        ttk.Radiobutton(r0, text="Doors on the left", value="left", variable=self.door,
                        command=self.on_door).pack(side="left", padx=14)
        r1 = ttk.Frame(box)
        r1.pack(fill="x", pady=(8, 0))
        ttk.Label(r1, text="Between loads, mm:").grid(row=0, column=0, sticky="w")
        ttk.Entry(r1, textvariable=self.gap_var, width=7).grid(row=0, column=1, padx=6, pady=2)
        ttk.Label(r1, text="From walls / doors, mm:").grid(row=1, column=0, sticky="w")
        ttk.Entry(r1, textvariable=self.wall_var, width=7).grid(row=1, column=1, padx=6, pady=2)
        ttk.Button(r1, text="Apply", command=self.apply_clearance).grid(row=0, column=2, rowspan=2,
                                                                       padx=6)

        lf = ttk.LabelFrame(p, text="Loads  (click a row or a load; right-click for more)", padding=8)
        lf.pack(fill="x", pady=8)
        cols = ("n", "kind", "size", "x", "y", "order", "pin")
        self.tree = ttk.Treeview(lf, columns=cols, show="headings", selectmode="browse", height=9)
        for c, t, w in (("n", "#", 44), ("kind", "Type", 56), ("size", "Size, mm", 96),
                        ("x", "X", 50), ("y", "Y", 50), ("order", "Seq.", 40), ("pin", "Pin", 34)):
            self.tree.heading(c, text=t)
            self.tree.column(c, width=w, anchor="center", stretch=(c == "size"))
        self.tree.tag_configure("unplaced", foreground="#b00020")
        self.tree.tag_configure("stacked", background="#eaf1fb")
        sb = ttk.Scrollbar(lf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.tree.bind("<<TreeviewSelect>>", self.on_tree_select)
        for ev in ("<Button-3>", "<Button-2>", "<Control-Button-1>"):
            self.tree.bind(ev, self.tree_menu)

        sf = ttk.LabelFrame(p, text="Selected load", padding=8)
        sf.pack(fill="x")
        self.sel_lbl = ttk.Label(sf, text="none selected", font=("Segoe UI", 10, "bold"),
                                 wraplength=340)
        self.sel_lbl.pack(anchor="w")
        r1 = ttk.Frame(sf)
        r1.pack(fill="x", pady=(6, 0))
        ttk.Button(r1, text="Rotate 90°", command=self.rotate_selected).pack(side="left")
        ttk.Button(r1, text="Pin / Unpin", command=self.toggle_pin).pack(side="left", padx=6)
        r1b = ttk.Frame(sf)
        r1b.pack(fill="x", pady=(6, 0))
        self.put_btn = ttk.Button(r1b, text="Put on  ▸", style="Accent.TButton",
                                  command=self.put_on_button)
        self.put_btn.pack(side="left")
        ttk.Button(r1b, text="Take off", command=self.take_off_selected).pack(side="left", padx=6)
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
        ttk.Label(sf, text="X from the front wall, Y from the left wall (mm, corner of the load). "
                           "A load standing on another one moves together with it.",
                  foreground=MUTED, wraplength=340).pack(anchor="w", pady=(4, 0))

        af = ttk.LabelFrame(p, text="Arrangement", padding=8)
        af.pack(fill="x", pady=(8, 0))
        ttk.Checkbutton(af, text="Re-arrange the other loads automatically\n"
                                "when a moved load is in their way",
                        variable=self.auto).pack(anchor="w")
        r4 = ttk.Frame(af)
        r4.pack(fill="x", pady=(6, 0))
        ttk.Button(r4, text="Re-arrange others", command=self.rearrange).pack(side="left")
        ttk.Button(r4, text="Unpin all", command=self.unpin_all).pack(side="left", padx=6)
        r6 = ttk.Frame(af)
        r6.pack(fill="x", pady=(8, 0))
        ttk.Label(r6, text="Auto layout priority:").pack(side="left")
        self.mode_names = {"Balanced (compact, small first)": "balanced",
                           "Smallest loads first": "order", "Shortest length": "length"}
        self.mode_var = tk.StringVar(value=next(k for k, v in self.mode_names.items()
                                                if v == PACK_MODE))
        cb = ttk.Combobox(r6, textvariable=self.mode_var, values=list(self.mode_names), width=30,
                          state="readonly")
        cb.pack(side="left", padx=6)
        cb.bind("<<ComboboxSelected>>", lambda e: set_pack_mode(self.mode_names[self.mode_var.get()]))
        r5 = ttk.Frame(af)
        r5.pack(fill="x", pady=(6, 0))
        ttk.Button(r5, text="Undo", command=self.undo).pack(side="left")
        ttk.Button(r5, text="Start over (auto layout)", command=self.start_over).pack(side="left", padx=6)

    # ---------- state helpers ----------
    def get_placed(self, n):
        return next((b for b in self.placed if b["n"] == n), None)

    def floor_loads(self):
        return [b for b in self.placed if b["n"] not in self.stack]

    def tops_on(self, n):
        return [t for t, st in self.stack.items() if st["base"] == n]

    def descendants(self, n):
        out, todo = set(), [n]
        while todo:
            for t in self.tops_on(todo.pop()):
                if t not in out:
                    out.add(t)
                    todo.append(t)
        return out

    def root_of(self, n):
        for _ in range(30):
            if n in self.stack:
                n = self.stack[n]["base"]
            else:
                break
        return self.get_placed(n)

    def subtree_height(self, n):
        return self.by_n[n].h + max((self.subtree_height(c) for c in self.tops_on(n)), default=0)

    def inside(self, b):
        L, W, _ = self.dims
        return (b["x"] >= WALL - EPS and b["y"] >= WALL - EPS and
                b["x"] + b["dx"] <= L - WALL + EPS and b["y"] + b["dy"] <= W - WALL + EPS)

    def snapshot(self):
        self.history.append(([dict(b) for b in self.placed], list(self.unplaced), set(self.pinned),
                             {k: dict(v) for k, v in self.stack.items()}, GAP, WALL))
        del self.history[:-40]

    def undo(self):
        if not self.history:
            messagebox.showinfo(APP_TITLE, "Nothing to undo.", parent=self)
            return
        self.placed, self.unplaced, self.pinned, self.stack, g, w = self.history.pop()
        set_clearance(g, w)
        self.gap_var.set(fmt(GAP))
        self.wall_var.set(fmt(WALL))
        self.refresh_all()

    def reattach(self):
        """Puts the loads that stand on others back on top of them (after anything moved)."""
        floor = [b for b in self.placed if b["n"] not in self.stack]
        placed, orphans = attach_stacks(floor, self.stack, self.by_n)
        self.placed = placed
        ns = {b["n"] for b in placed}
        self.unplaced = [(p, r) for p, r in self.unplaced if p.number not in ns]
        have = {p.number for p, _ in self.unplaced}
        for n in orphans:
            if n not in have:
                self.unplaced.append((self.by_n[n], "the load it stands on is not placed"))
        self.unplaced.sort(key=lambda t: t[0].number)

    def refresh_all(self):
        assign_order(self.placed)
        self.update_summary()
        self.fill_tree()
        self.canvas.L, self.canvas.W = self.dims[0], self.dims[1]
        self.canvas.set_data(self.placed, self.pinned, self.sel, self.door.get() == "left")
        self.update_selection_panel()

    def update_summary(self):
        L, W, H = self.dims
        used = max((b["x"] + b["dx"] for b in self.placed), default=0)
        stacked = len(self.stack)
        self.summary.config(text=(
            f"{self.cname}: {fmt(L)} × {fmt(W)} × {fmt(H)} mm.   "
            f"Loads placed: {len(self.placed)} of {self.total}.   "
            f"Max. load height: {fmt(min(H, MAX_H))} mm.   "
            f"Length used: {fmt(used)} mm, free towards the doors: {fmt(L - used)} mm.   "
            + (f"Loads standing on others: {stacked}.   " if stacked else "")
            + f"Doors: {self.door.get()}."))
        self.warn.config(text=("DID NOT FIT:\n" + "\n".join(group_unplaced(self.unplaced)))
                         if self.unplaced else "")

    def fill_tree(self):
        for i in self.tree.get_children():
            self.tree.delete(i)
        rows = [(b["n"], (b["label"], b["kind"], f"{fmt(b['dx'])}×{fmt(b['dy'])}", fmt(b["x"]),
                          fmt(b["y"]), b["order"], "●" if b["n"] in self.pinned else ""),
                 ("stacked",) if b.get("base") else ()) for b in self.placed]
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
            extra = ""
            if b.get("base"):
                extra = f"   (standing on #{self.by_n[b['base']].number})"
            elif b["n"] in self.pinned:
                extra = "   (pinned)"
            self.sel_lbl.config(text=f"#{b['label']}  {b['kind']}  {fmt(b['dx'])} × {fmt(b['dy'])} × "
                                     f"{fmt(b['h'])} mm" + extra)
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

    # ---------- clearance ----------
    def apply_clearance(self):
        try:
            g = parse_nonneg(self.gap_var.get(), "Between loads")
            w = parse_nonneg(self.wall_var.get(), "From walls / doors")
        except ValueError as e:
            messagebox.showerror(APP_TITLE, str(e), parent=self)
            return
        if abs(g - GAP) < EPS and abs(w - WALL) < EPS:
            return
        self.snapshot()
        set_clearance(g, w)
        bad = set()
        floor = self.floor_loads()
        keep = [b for b in floor if b["n"] in self.pinned]
        for b in keep:
            if not self.inside(b):
                bad.add(b["n"])
        keep = [b for b in keep if b["n"] not in bad]
        for i, a in enumerate(keep):
            for c in keep[i + 1:]:
                if boxes_conflict(a, c):
                    bad.add(c["n"])
        self.pinned -= bad
        self.repack()
        self.refresh_all()
        if bad:
            messagebox.showinfo(APP_TITLE, "With the new clearance some pinned loads no longer fit "
                                           "where they were; they were unpinned and re-arranged.",
                                parent=self)

    # ---------- moving things ----------
    def place_manually(self, nb):
        """Applies a new position / orientation for one floor load (and pins it)."""
        n = nb["n"]
        others = [o for o in self.floor_loads() if o["n"] != n]
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
        else:
            self.reattach()
        self.refresh_all()
        return True

    def repack(self, conflicting=None):
        """Arranges the floor loads that are not pinned again. If `conflicting` is given, first
        only those loads (and the unplaced ones) are moved and everything else stays put.
        Loads that were put on others by hand are not touched (they stay on their base)."""
        L, W, H = self.dims
        self.config(cursor="watch")
        self.update_idletasks()
        skip = set(self.stack)

        def attempt(movable):
            fixed = {b["n"]: (b["x"], b["y"], b["dx"], b["dy"])
                     for b in self.floor_loads() if b["n"] not in movable}
            return plan_loading(L, W, H, self.loads, fixed=fixed, budget=1.0, skip=skip)

        def all_fit(res):
            return not any(r == NO_SPACE for _, r in res[1])

        free_unplaced = {p.number for p, _ in self.unplaced if p.number not in skip}
        result = None
        if conflicting:
            res = attempt(set(conflicting) | free_unplaced)
            if all_fit(res):
                result = res
        if result is None:
            result = attempt({b["n"] for b in self.floor_loads() if b["n"] not in self.pinned}
                             | free_unplaced)
        self.config(cursor="")
        self.placed, self.unplaced = result
        self.reattach()
        if not all_fit(result):
            self.after(50, lambda: messagebox.showwarning(
                APP_TITLE, "Not all loads fit around the pinned loads. The loads that do not fit "
                           "are listed in red. Use Undo, or unpin some loads and try again.",
                parent=self))

    def rotate_selected(self):
        b = self.need_selected()
        if not b:
            return
        if b["n"] in self.stack:
            self.rotate_top(b)
            return
        L, W, _ = self.dims
        nb = dict(b, dx=b["dy"], dy=b["dx"], rotated=not b["rotated"])
        nb["x"] = min(max(b["x"], WALL), L - WALL - nb["dx"])
        nb["y"] = min(max(b["y"], WALL), W - WALL - nb["dy"])
        if not self.inside(nb):
            messagebox.showinfo(APP_TITLE, "This load cannot be rotated: it would not fit "
                                           "inside the container.", parent=self)
            return
        self.place_manually(nb)

    def rotate_top(self, b):
        """Turns a load that stands on another load (it must stay within the base footprint)."""
        n = b["n"]
        st = self.stack[n]
        base = self.by_n[st["base"]]
        du, dv = st["dv"], st["du"]
        if du > base.l + EPS or dv > base.w + EPS:
            messagebox.showinfo(APP_TITLE, "This load cannot be rotated: it would stick out over "
                                           "the load it stands on.", parent=self)
            return
        u = min(max(st["u"], 0), base.l - du)
        v = min(max(st["v"], 0), base.w - dv)
        if self.overlaps_siblings(st["base"], n, u, v, du, dv):
            messagebox.showinfo(APP_TITLE, "No room to rotate it: another load stands next to it "
                                           "on the same base.", parent=self)
            return
        self.snapshot()
        self.stack[n] = dict(st, u=u, v=v, du=du, dv=dv)
        self.reattach()
        self.refresh_all()

    def toggle_pin(self):
        b = self.need_selected()
        if not b:
            return
        root = self.root_of(b["n"])
        self.snapshot()
        self.pinned.symmetric_difference_update({root["n"]})
        self.refresh_all()

    def slide(self, direction):
        sel = self.need_selected()
        if not sel:
            return
        b = self.root_of(sel["n"])  # a stack is moved as a whole
        L, W, _ = self.dims
        others = [o for o in self.floor_loads() if o["n"] != b["n"]]
        nb = dict(b)
        if direction in ("front", "door"):
            lim = WALL if direction == "front" else L - WALL - b["dx"]
            for o in others:
                if max(o["y"] - (b["y"] + b["dy"]), b["y"] - (o["y"] + o["dy"])) >= GAP - EPS:
                    continue  # not side by side with this load
                if direction == "front" and o["x"] + o["dx"] <= b["x"] + EPS:
                    lim = max(lim, o["x"] + o["dx"] + GAP)
                if direction == "door" and o["x"] >= b["x"] + b["dx"] - EPS:
                    lim = min(lim, o["x"] - GAP - b["dx"])
            nb["x"] = lim
        else:
            lim = WALL if direction == "left" else W - WALL - b["dy"]
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
        sel = self.need_selected()
        if not sel:
            return
        b = self.root_of(sel["n"])
        try:
            x = parse_pos(self.xv.get(), "X")
            y = parse_pos(self.yv.get(), "Y")
        except ValueError as e:
            messagebox.showerror(APP_TITLE, str(e), parent=self)
            return
        if sel is not b:  # the typed position is the position of the selected (upper) load
            x, y = b["x"] + (x - sel["x"]), b["y"] + (y - sel["y"])
        nb = dict(b, x=x, y=y)
        if not self.inside(nb):
            messagebox.showinfo(APP_TITLE, f"Outside the container: loads must stay {fmt(WALL)} mm "
                                           "away from the walls and doors.", parent=self)
            return
        self.place_manually(nb)

    def snap(self, b, x, y, thr=60):
        """Clamps the dropped position to the container and snaps it to walls / neighbours."""
        L, W, _ = self.dims
        dx, dy = b["dx"], b["dy"]
        cx, cy = [WALL, L - WALL - dx], [WALL, W - WALL - dy]
        for o in self.floor_loads():
            if o["n"] == b["n"]:
                continue
            cx += [o["x"] + o["dx"] + GAP, o["x"] - GAP - dx, o["x"], o["x"] + o["dx"] - dx]
            cy += [o["y"] + o["dy"] + GAP, o["y"] - GAP - dy, o["y"], o["y"] + o["dy"] - dy]
        x = min(max(x, WALL), L - WALL - dx)
        y = min(max(y, WALL), W - WALL - dy)
        bx = min(cx, key=lambda v: abs(v - x))
        by = min(cy, key=lambda v: abs(v - y))
        if abs(bx - x) <= thr:
            x = bx
        if abs(by - y) <= thr:
            y = by
        return (round(min(max(x, WALL), L - WALL - dx), 1), round(min(max(y, WALL), W - WALL - dy), 1))

    def on_drop(self, n, x, y):
        b = self.get_placed(n)
        if b is None:
            return
        root = self.root_of(n)
        if root is not b:  # an upper load was dragged: the whole stack follows
            x, y = root["x"] + (x - b["x"]), root["y"] + (y - b["y"])
        x, y = self.snap(root, x, y)
        if abs(x - root["x"]) < 0.5 and abs(y - root["y"]) < 0.5:
            return
        self.place_manually(dict(root, x=x, y=y))

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
        self.stack.clear()
        L, W, H = self.dims
        self.config(cursor="watch")
        self.update_idletasks()
        self.placed, self.unplaced = plan_loading(L, W, H, self.loads, budget=1.5)
        self.config(cursor="")
        self.refresh_all()

    # ---------- standing a load on another load (manual only) ----------
    def overlaps_siblings(self, base_n, n, u, v, du, dv):
        for m, st in self.stack.items():
            if st["base"] != base_n or m == n:
                continue
            if not (u >= st["u"] + st["du"] + GAP - EPS or st["u"] >= u + du + GAP - EPS or
                    v >= st["v"] + st["dv"] + GAP - EPS or st["v"] >= v + dv + GAP - EPS):
                return True
        return False

    def stack_geometry(self, p, bb):
        """Where load p would stand on the load bb: a stack record, or an error text."""
        _, _, H = self.dims
        total = bb["z"] + bb["h"] + self.subtree_height(p.number)
        if total > H + EPS:
            return f"too high ({fmt(total)} mm, the container is {fmt(H)} mm high)"
        opts = [(p.l, p.w)] + ([(p.w, p.l)] if abs(p.l - p.w) > EPS else [])
        opts = [o for o in opts if o[0] <= bb["dx"] + EPS and o[1] <= bb["dy"] + EPS]
        if not opts:
            return "too big for it (it must not stick out)"
        opts.sort(key=lambda o: 0 if (o[0] >= o[1]) == (bb["dx"] >= bb["dy"]) else 1)
        tdx, tdy = opts[0]
        base = self.by_n[bb["n"]]
        du, dv = (tdy, tdx) if bb["rotated"] else (tdx, tdy)
        u0, v0 = (base.l - du) / 2.0, (base.w - dv) / 2.0
        if self.overlaps_siblings(bb["n"], p.number, u0, v0, du, dv):
            spot = None
            for v in range(0, int(base.w - dv) + 1, 25):
                for u in range(0, int(base.l - du) + 1, 25):
                    if not self.overlaps_siblings(bb["n"], p.number, u, v, du, dv):
                        spot = (float(u), float(v))
                        break
                if spot:
                    break
            if spot is None:
                return "no free room on top of it"
            u0, v0 = spot
        res = dict(base=bb["n"], u=u0, v=v0, du=du, dv=dv)
        if total > MAX_H + EPS:  # above the 220 cm rule: allowed only if the user confirms
            res["over"] = total
        return res

    def put_on(self, n, base_n):
        p, bb = self.by_n[n], self.get_placed(base_n)
        if bb is None or n == base_n or base_n in self.descendants(n):
            return
        res = self.stack_geometry(p, bb)
        if isinstance(res, str):
            messagebox.showinfo(APP_TITLE, f"#{p.number} cannot be put on #{base_n}: {res}.", parent=self)
            return
        over = res.pop("over", None)
        if over and not messagebox.askyesno(
                APP_TITLE, f"The stack would be {fmt(over)} mm high - more than the {fmt(MAX_H)} mm "
                           f"limit.\n\nPut #{p.number} on #{base_n} anyway?", parent=self):
            return
        self.snapshot()
        self.placed = [b for b in self.placed if b["n"] != n]
        self.unplaced = [(q, r) for q, r in self.unplaced if q.number != n]
        self.pinned.discard(n)
        self.stack[n] = res
        self.reattach()
        self.sel = n
        self.refresh_all()

    def take_off(self, n):
        if n not in self.stack:
            return
        self.snapshot()
        del self.stack[n]
        self.placed = [b for b in self.placed if b["n"] != n]
        if all(q.number != n for q, _ in self.unplaced):
            self.unplaced.append((self.by_n[n], NO_SPACE))
        self.repack({n})  # finds a free place on the floor for it
        self.sel = n
        self.refresh_all()

    def take_off_selected(self):
        b = self.need_selected()
        if not b:
            return
        if b["n"] not in self.stack:
            messagebox.showinfo(APP_TITLE, "This load is not standing on another load.", parent=self)
            return
        self.take_off(b["n"])

    def put_on_candidates_menu(self, parent, n):
        """A menu listing all the loads that load n could be put on. Returns (menu, has entries)."""
        p = self.by_n[n]
        sub = tk.Menu(parent, tearoff=0)
        banned = self.descendants(n) | {n}
        cands = [b for b in sorted(self.placed, key=lambda b: b["n"]) if b["n"] not in banned]
        for b in cands:
            res = self.stack_geometry(p, b)
            label = f"#{b['label']}   {b['kind']}   {fmt(b['dx'])} × {fmt(b['dy'])} × {fmt(b['h'])}"
            if isinstance(res, str):
                sub.add_command(label=f"{label}   ({res.split(' (')[0]})", state="disabled")
            else:
                if res.get("over"):
                    label += f"   (stack {fmt(res['over'])} mm - above the limit)"
                sub.add_command(label=label, command=lambda t=b["n"]: self.put_on(n, t))
        return sub, bool(cands)

    def put_on_button(self):
        n = self.sel
        if n is None or n not in self.by_n:
            messagebox.showinfo(APP_TITLE, "Select the load that should stand on top first "
                                           "(click it in the list or in the picture).", parent=self)
            return
        sub, has = self.put_on_candidates_menu(self, n)
        if not has:
            messagebox.showinfo(APP_TITLE, "There is no other placed load to put it on.", parent=self)
            return
        x = self.put_btn.winfo_rootx()
        y = self.put_btn.winfo_rooty() + self.put_btn.winfo_height()
        try:
            sub.tk_popup(x, y)
        finally:
            sub.grab_release()

    def tree_menu(self, event):
        row = self.tree.identify_row(event.y)
        if not row:
            return
        self.tree.selection_set(row)
        self.show_load_menu(int(row), event.x_root, event.y_root)

    def canvas_menu(self, n, x_root, y_root):
        self.show_load_menu(n, x_root, y_root)

    def show_load_menu(self, n, x_root, y_root):
        """Right-click menu of a load (in the list or in the picture)."""
        m = tk.Menu(self, tearoff=0)
        sub, has = self.put_on_candidates_menu(m, n)
        if has:
            m.add_cascade(label="Put on  ▸", menu=sub)
        else:
            m.add_command(label="Put on  (no other placed loads)", state="disabled")
        m.add_command(label="Take off (back to the floor)", command=lambda: self.take_off(n),
                      state="normal" if n in self.stack else "disabled")
        m.add_separator()
        m.add_command(label="Rotate 90°", command=self.rotate_selected)
        m.add_command(label="Pin / Unpin", command=self.toggle_pin)
        try:
            m.tk_popup(x_root, y_root)
        finally:
            m.grab_release()

    # ---------- save / open the arrangement ----------
    def save_layout(self):
        path = filedialog.asksaveasfilename(
            parent=self, defaultextension=".json", initialfile="loading_layout.json",
            filetypes=[("Loading configuration with layout", "*.json")], title="Save layout")
        if not path:
            return
        L, W, H = self.dims
        data = {"app": APP_TITLE, "version": 2, "container": self.ckey,
                "dims": {"length": L, "width": W, "height": H},
                "clearance": {"between": GAP, "walls": WALL},
                "loads": [dict(kind=p.kind, l=p.l, w=p.w, h=p.h, src=0,
                               assumed_h=p.assumed_h, origin=p.origin) for p in self.loads],
                "layout": {"door": self.door.get(), "pinned": sorted(self.pinned),
                           "placed": [dict(n=b["n"], x=b["x"], y=b["y"], dx=b["dx"], dy=b["dy"])
                                      for b in self.floor_loads()],
                           "stack": [dict(n=t, **st) for t, st in self.stack.items()]}}
        try:
            with open(path, "w", encoding="utf-8") as fh:
                json.dump(data, fh, indent=2, ensure_ascii=False)
        except OSError as e:
            messagebox.showerror(APP_TITLE, f"Could not save the file:\n{e}", parent=self)
            return
        messagebox.showinfo(APP_TITLE, "Layout saved. You can open it again with 'Open layout…' "
                                       "or 'Open config…' in the main window.", parent=self)

    def load_layout(self):
        path = filedialog.askopenfilename(
            parent=self, title="Open layout",
            filetypes=[("Loading configuration with layout", "*.json"), ("All files", "*.*")])
        if not path:
            return
        try:
            with open(path, encoding="utf-8") as fh:
                data = json.load(fh)
            if "layout" not in data:
                raise ValueError("this file has no saved layout - it is only a list of loads")
            self.snapshot()
            self.load_layout_data(data)
        except Exception as e:
            messagebox.showerror(APP_TITLE, f"This is not a valid layout file.\n({e})", parent=self)

    def load_layout_data(self, data):
        key, loads, dims = config_from_data(data)
        lay = data["layout"]
        L, W, H = (float(dims.get("length", self.dims[0])), float(dims.get("width", self.dims[1])),
                   float(dims.get("height", self.dims[2])))
        by_n = {p.number: p for p in loads}
        placed = []
        for d in lay.get("placed", []):
            p = by_n[int(d["n"])]
            dx, dy = float(d["dx"]), float(d["dy"])
            placed.append(dict(n=p.number, label=p.label, kind=p.kind, x=float(d["x"]),
                               y=float(d["y"]), z=0.0, dx=dx, dy=dy, h=p.h, level=1,
                               rotated=abs(dx - p.l) > EPS, pallet=p))
        stack = {int(d["n"]): dict(base=int(d["base"]), u=float(d["u"]), v=float(d["v"]),
                                   du=float(d["du"]), dv=float(d["dv"]))
                 for d in lay.get("stack", []) if int(d["n"]) in by_n}
        # everything went well - now take it over
        self.ckey, self.cname = key, CONTAINERS[key][0]
        self.title(f"Loading Plan - {self.cname}")
        self.dims, self.loads, self.by_n, self.total = (L, W, H), loads, by_n, len(loads)
        self.stack, self.pinned = stack, {int(n) for n in lay.get("pinned", [])}
        self.placed = placed
        ns = {b["n"] for b in placed} | set(stack)
        self.unplaced = [(p, NO_SPACE) for p in loads if p.number not in ns]
        self.sel = None
        self.door.set("left" if lay.get("door") == "left" else "right")
        self.gap_var.set(fmt(GAP))
        self.wall_var.set(fmt(WALL))
        self.reattach()
        self.refresh_all()

    # ---------- export ----------
    def rows(self):
        out = []
        for b in sorted(self.placed, key=lambda b: b["order"]):
            out.append((b["order"], b["label"], b["kind"],
                        f"{fmt(b['dx'])} × {fmt(b['dy'])} × {fmt(b['h'])}",
                        fmt(b["x"]), fmt(b["y"]), fmt(b["z"]),
                        "rotated 90°" if b["rotated"] else "lengthwise"))
        return out

    def export(self, kind):
        door_left = (self.door.get() == "left")
        try:
            img2 = render_plan_image(self.cname, self.dims, self.placed, self.unplaced, self.total,
                                     door_left=door_left)
            img3 = render_3d_image(self.cname, self.dims, self.placed, self.unplaced, self.total,
                                   door_left=door_left)
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
                path3 = os.path.splitext(path)[0] + "_3D.png"
                img2.save(path)
                img3.save(path3)
                msg = f"Saved 2 pictures:\n{path}\n{path3}"
            else:
                img2.convert("RGB").save(path, "PDF", resolution=200.0, save_all=True,
                                         append_images=[img3.convert("RGB")])
                msg = "Saved. Page 1: loading plan, page 2: 3D view."
        except Exception as e:
            messagebox.showerror(APP_TITLE, f"Could not save the file:\n{e}", parent=self)
            return
        messagebox.showinfo(APP_TITLE, msg, parent=self)

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
    tk.Label(foot, text="Geo Container Loading Planner   |   created by Evgenii", bg=NAVY,
             fg="#c9d4e8", font=("Segoe UI", 8)).pack(side="right", padx=16)
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
        fit_window(self, 1020, 800, 900, 600)
        self.configure(bg="white")
        self.setup_style()
        self.pallets = []
        self.ckey = None
        build_header(self)
        build_footer(self)
        self.container = ttk.Frame(self)
        self.container.pack(fill="both", expand=True)
        self.show_select()

    def report_callback_exception(self, exc, val, tb):
        """Tk swallows errors in button / menu handlers; in the .exe nobody would ever see them."""
        import traceback
        text = "".join(traceback.format_exception(exc, val, tb))
        log = os.path.join(os.path.expanduser("~"), "GeoContainerPlanner_error.log")
        try:
            with open(log, "a", encoding="utf-8") as fh:
                fh.write(time.strftime("%Y-%m-%d %H:%M:%S") + "\n" + text + "\n")
        except OSError:
            pass
        try:
            messagebox.showerror(APP_TITLE, f"Something went wrong:\n\n{val}\n\n"
                                            f"Details were saved to:\n{log}")
        except Exception:
            pass

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
                           f"and may be rotated by 90° (loads can be put on top of each other by hand in the "
                           f"loading plan window). Clearance between loads and from walls / doors: "
                           f"{fmt(GAP)} / {fmt(WALL)} mm, adjustable in the loading plan window. "
                           f"Max. load height {fmt(MAX_H)} mm.",
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
        data = {"app": APP_TITLE, "version": 2, "container": self.ckey, "dims": dims,
                "clearance": {"between": GAP, "walls": WALL},
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
            key, loads, dims = config_from_data(data)
        except Exception as e:
            messagebox.showerror(APP_TITLE, f"This is not a valid configuration file.\n({e})")
            return
        self.pallets = loads
        self.show_main(key)
        for k in ("Length", "Width", "Height"):
            if k.lower() in dims:
                self.dim_vars[k].set(fmt(float(dims[k.lower()])))
        if "layout" in data:
            if messagebox.askyesno(APP_TITLE, "This file also contains a saved loading layout.\n\n"
                                              "Open the loading plan now?"):
                try:
                    L, W, H = (float(self.dim_vars[k].get()) for k in ("Length", "Width", "Height"))
                except ValueError:
                    return
                ResultWindow(self, CONTAINERS[key][0], (L, W, H), list(self.pallets), [], [],
                             ckey=key, layout=data)

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
        ResultWindow(self, CONTAINERS[self.ckey][0], (L, W, H), list(self.pallets), placed, unplaced,
                     ckey=self.ckey)


def main():
    try:  # sharp rendering on Windows with display scaling
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    App().mainloop()


if __name__ == "__main__":
    main()
