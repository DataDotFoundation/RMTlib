"""Shared look and helpers for the Dissemination videos.

Canonical copy: DataDotFoundation/MeaningLib, Dissemination/common/style.py. Downstream repositories
carry byte-identical copies, checked and refreshed by scripts/check_pins.py (MeaningLib#44). Change
it here, then bump the pins.

Each video imports this module with

    import sys, pathlib
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "common"))
    from style import *

so the videos stay independent of one another but share colours, titles and drawing helpers.

Status labels: every claim on screen carries its maturity, in one visual form (`status`), with the
names of MeaningLib's ladder (MeaningLib.Claim):
idea < conjecture < checked < published < stated < proved < pinned.
The same maturity always looks the same (`MATURITY`, `styled`), matching the line styles of
MeaningLib.Storyboard.defaultMaturityStyle. Older words map onto the ladder (`STATUS_ALIASES`).
"""

from manim import *

INF_COL = BLUE_C     # the archimedean place, infinity
P_COL = ORANGE       # the finite places, primes
Z_COL = TEAL_C       # zeta, global objects, kernels
L_COL = YELLOW       # punchlines
DIM = GREY_B         # side remarks


def header(scene, text, sub=None, size=34):
    """A section title at the top of the frame."""
    t = Text(text, font_size=size, weight=BOLD).to_edge(UP, buff=0.35)
    if t.width > 13.4:
        t.scale_to_fit_width(13.4)
    group = VGroup(t)
    if sub:
        group.add(Text(sub, font_size=22, color=DIM).next_to(t, DOWN, buff=0.15))
    scene.play(FadeIn(group, shift=DOWN * 0.2))
    return group


def clear(scene, run_time=0.8):
    scene.play(*[FadeOut(m) for m in scene.mobjects], run_time=run_time)


def footer(*lines, size=17):
    """One or more small grey lines at the bottom of the frame."""
    return VGroup(*[Text(t, font_size=size, color=DIM) for t in lines]).arrange(
        DOWN, buff=0.06).to_edge(DOWN, buff=0.15)


def moral(text, size=24):
    return Text(text, font_size=size, color=L_COL).to_edge(DOWN, buff=0.3)


def title_card(scene, title, sub, hold=1.5):
    t = Text(title, font_size=54, weight=BOLD)
    if t.width > 13:
        t.scale_to_fit_width(13)
    s = Text(sub, font_size=26, color=DIM).next_to(t, DOWN, buff=0.4)
    scene.play(Write(t), run_time=1.5)
    scene.play(FadeIn(s, shift=UP * 0.2))
    scene.wait(hold)
    return VGroup(t, s)


def young(shape, cell=0.22, color=WHITE, fill=None):
    """A Young diagram (English convention) as a VGroup of squares."""
    g = VGroup()
    for i, row in enumerate(shape):
        for j in range(row):
            sq = Square(side_length=cell, stroke_width=1.5, stroke_color=color)
            if fill is not None:
                sq.set_fill(fill, opacity=0.5)
            sq.move_to(np.array([j * cell, -i * cell, 0]))
            g.add(sq)
    if len(g) == 0:
        g.add(Dot(radius=0.04, color=color))
    return g


def russian(shape, s=0.35, fill=None, stroke=WHITE, width=1.5):
    """A Young diagram in Russian notation: cell (i, j) is the diamond centred at
    (x, y) = (j - i, i + j + 1), in units of s; x is the content.
    Returns (VGroup of diamonds, dict (i, j) -> diamond)."""
    g, cells = VGroup(), {}
    for i, r in enumerate(shape):
        for j in range(r):
            d = diamond_at(j - i, i + j + 1, s, stroke=stroke, width=width)
            if fill is not None:
                d.set_fill(fill, opacity=0.35)
            g.add(d)
            cells[(i, j)] = d
    return g, cells


def diamond_at(x, y, s, stroke=WHITE, width=1.5):
    return Polygon(np.array([x, y - 1, 0]) * s, np.array([x + 1, y, 0]) * s,
                   np.array([x, y + 1, 0]) * s, np.array([x - 1, y, 0]) * s,
                   stroke_color=stroke, stroke_width=width)


def cone(s=0.35, reach=6.0, color=GREY_C):
    """The light cone |x| in the same units as `russian`."""
    return VGroup(DashedLine(ORIGIN, np.array([-reach, reach, 0]) * s, color=color),
                  DashedLine(ORIGIN, np.array([reach, reach, 0]) * s, color=color))


def corners(shape):
    """Contents of the valleys (addable cells) and peaks (removable cells) of a partition."""
    lam = list(shape)
    valleys, peaks = [], []
    for i in range(len(lam) + 1):
        row = lam[i] if i < len(lam) else 0
        above = lam[i - 1] if i > 0 else None
        if above is None or row < above:
            valleys.append(row - i)
        if i < len(lam) and row > 0 and (i == len(lam) - 1 or lam[i + 1] < row):
            peaks.append(row - 1 - i)
    return valleys, peaks


# ---- layout helpers (from RH-Dual videos 4 and 5) ----------------------------------------------

def foot(*lines, size=15):
    """A footer whose lines are scaled to fit the frame width."""
    f = footer(*lines, size=size)
    for line in f:
        if line.width > 13.4:
            line.scale_to_fit_width(13.4)
    return f.to_edge(DOWN, buff=0.15)


def lifted_moral(text):
    """A moral above the footer, without overlap."""
    return moral(text).shift(UP * 0.5)


def tag(text, col=DIM, size=18):
    """A small italic label."""
    return Text(text, font_size=size, color=col, slant=ITALIC)


def axis_line(x0, x1, y, scale, color=DIM):
    """A horizontal line (a Maya line) from x0 to x1 at height y."""
    return Line(np.array([x0 * scale, y, 0]), np.array([x1 * scale, y, 0]), stroke_width=1.5, color=color)


def charges_on(positions, y, scale, color, x_off=0.0, r=0.07):
    """Charges (dots) at the given positions on a Maya line."""
    return VGroup(*[Dot(np.array([p * scale + x_off, y, 0]), radius=r, color=color) for p in positions])


def light_cone(shape, s, origin, reach=6.0, fill=WHITE, opacity=0.12, stroke=WHITE):
    """A partition in Russian notation inside its light cone, with the content axis.
    Returns (diamonds, cells, cone, axis)."""
    dia, cells = russian(shape, s=s, fill=fill, stroke=stroke)
    dia.set_fill(opacity=opacity).shift(origin)
    lc = cone(s=s, reach=reach).shift(origin)
    axis = Line(origin + LEFT * reach * s, origin + RIGHT * reach * s, stroke_width=1, color=DIM)
    return dia, cells, lc, axis


def charge_marks(shape, s, origin, dy=0.3):
    """+ at the valleys, - at the peaks of a partition, under the content axis."""
    valleys, peaks = corners(shape)
    marks = VGroup()
    for x in valleys:
        marks.add(MathTex("+", font_size=30, color=GREEN_C).move_to(origin + RIGHT * x * s + DOWN * dy))
    for y in peaks:
        marks.add(MathTex("-", font_size=30, color=RED_C).move_to(origin + RIGHT * y * s + DOWN * dy))
    return marks


def weight_label(c, size=18, col=INF_COL):
    """The weight N + c of a cell of content c at the archimedean place."""
    return MathTex("N" if c == 0 else f"N{c:+d}", font_size=size, color=col)


# ---- claim status: one visual form per maturity (MeaningLib#45) -------------------------------

# maturity -> (label, colour, line style); the line styles are MeaningLib.Storyboard's defaults
MATURITY = {
    "idea":       ("idea",       GREY_B,   "dotted"),
    "conjecture": ("conjecture", PURPLE_B, "dashed"),
    "checked":    ("computed",   TEAL_B,   "dashed-dense"),
    "published":  ("known",      BLUE_B,   "thin"),
    "stated":     ("stated",     GOLD_B,   "hollow"),
    "proved":     ("proved",     GREEN_C,  "solid"),
    "pinned":     ("proved · pinned", GREEN_D, "solid-pinned"),
}

# words used in earlier videos -> maturity
STATUS_ALIASES = {
    "reading": "idea", "hypothesis": "conjecture", "inferred": "conjecture",
    "computed": "checked", "exact": "checked", "read": "checked",
}


def maturity_of(status):
    """The maturity name for a status word (a maturity name or an alias)."""
    m = STATUS_ALIASES.get(status, status)
    if m not in MATURITY:
        raise ValueError(f"unknown status {status!r}; use one of {list(MATURITY)} or {list(STATUS_ALIASES)}")
    return m


def status(s, size=18):
    """The status label of a claim on screen: its maturity, in its colour, italic."""
    label, col, _ = MATURITY[maturity_of(s)]
    return tag(label, col=col, size=size)


def styled(mob, s):
    """Draw a mobject in the line style of a maturity: how sure a claim is shows in how it is drawn."""
    style = MATURITY[maturity_of(s)][2]
    if style in ("dotted", "dashed", "dashed-dense"):
        n = {"dotted": 40, "dashed": 15, "dashed-dense": 30}[style]
        ratio = {"dotted": 0.2, "dashed": 0.5, "dashed-dense": 0.6}[style]
        return VGroup(*[DashedVMobject(m, num_dashes=n, dashed_ratio=ratio)
                        if len(getattr(m, "points", [])) else m for m in mob.family_members_with_points()])
    if style == "hollow":
        return mob.set_fill(opacity=0)
    if style == "thin":
        return mob.set_stroke(width=1.5)
    if style == "solid-pinned":
        return VGroup(mob, Dot(radius=0.05, color=MATURITY["pinned"][1]).next_to(mob, UR, buff=0.05))
    return mob
