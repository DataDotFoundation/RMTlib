"""Shared look and helpers for the Dissemination videos (copied from RH-Dual/Dissemination/common/style.py).

Each video imports this module with

    import sys, pathlib
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "common"))
    from style import *

so the videos stay independent of one another but share colours, titles and drawing helpers.
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
