"""Video 1: the string-insertion law.

A partition is a finite set of particles on a line (its Maya diagram). Its hook product, in
Frobenius' form, is an energy of those particles: a one-body weight l! per particle, divided by the
pair Vandermonde. Inserting a string of consecutive particles into empty sites changes the hook
product by an exact increment, the self-energy of the string over its mutual energy with what is
already there. The increments telescope along any sequence of insertions, and two insertions commute
exactly. At a finite place the one-body weight T^l is affine in position, at infinity l! is not. The
video ends with the string-insertion law along theta lifts, checked on the proof's own family.

Source of truth: RMTlib docs/string-insertion.md (RMTlib#49). Tags used on screen:
Labels use the shared maturity ladder (style.status, MeaningLib#45), licensed by RMT.Claims:
  proved      in RMTlib (RMT.frobenius, RMT.StringInsertion.vd_union / fac_union / hset_step, claims F3, F9;
              ¬ IsExpLinear rhoInf, claim onebodyPotential);
  computed    checked on the proof's family by RH-Dual (claim F4; band facts, RH-Dual #74, #128);
  idea        our language (charges, energies, log-gas), not a theorem;
  conjecture  the asymptotic log-gas reading (d).
Every number on screen is an exact integer computation on the example L = {0, 2, 5} (lambda = (3, 1)).

    manim -ql string_insertion.py OneInsertion     # one scene, quick preview
    ../render.sh 01_string_insertion               # all scenes, stitched
"""

import math
import sys
import pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "common"))
from style import *  # noqa: E402,F401

PART = Z_COL          # particles (occupied sites)
NEW = L_COL           # the inserted string
SELF = INF_COL        # self-energy
MUT = RED_C           # mutual energy
OK = GREEN_C
REPO = "github.com/DataDotFoundation/RMTlib"
NOTE = "source: RMTlib docs/string-insertion.md"


# ------------------------------------------------------------------------------------------------
# Exact arithmetic on Maya sets (the note's definitions)


def hset(L):
    L = sorted(L)
    num = math.prod(math.factorial(l) for l in L)
    den = math.prod(b - a for i, a in enumerate(L) for b in L[i + 1:])
    return num, den


def shape_of(L):
    """The partition whose Maya set (padded with |L| rows) is L."""
    L = sorted(L, reverse=True)
    n = len(L)
    return [l - (n - 1 - i) for i, l in enumerate(L) if l - (n - 1 - i) > 0]


# ------------------------------------------------------------------------------------------------
# Drawing helpers


def foot(*lines, size=15):
    f = footer(*lines, size=size)
    for line in f:
        if line.width > 13.4:
            line.scale_to_fit_width(13.4)
    return f.to_edge(DOWN, buff=0.15)


def lifted_moral(text):
    m = moral(text)
    if m.width > 13.2:
        m.scale_to_fit_width(13.2)
    return m.shift(UP * 0.5)


def tag(text, col=DIM, size=18):
    return Text(text, font_size=size, color=col, slant=ITALIC)


def maya_picture(L, s, M, max_site, new=(), clash=(), show_shape=True, labels=True):
    """Russian-notation shape above its Maya diagram, aligned site by site.

    M is the left end of site 0 on the Maya line. With n = |L| particles, site l sits under the
    content interval [l - n, l - n + 1] of the profile, so the light-cone apex is at M + n s
    (shifted up). An occupied site is a profile step of slope -1, an empty one a step of slope +1.
    """
    n = len(L)
    apex = M + RIGHT * n * s + UP * 0.45
    g = VGroup()
    # light cone, drawn over the visible sites
    left = n + 2
    right = max_site + 2 - n
    lc = VGroup(DashedLine(apex, apex + np.array([-left, left, 0]) * s, color=GREY_C, stroke_width=1.5),
                DashedLine(apex, apex + np.array([right, right, 0]) * s, color=GREY_C, stroke_width=1.5))
    dia = VGroup()
    if show_shape:
        d, _ = russian(shape_of(L), s=s, fill=WHITE, stroke=GREY_B, width=1)
        d.set_fill(opacity=0.10).shift(apex)
        dia = d
    # profile
    prof = VGroup()
    f = n + 2
    x = -(n + 2)
    pts = []
    for _ in range(2):          # the Dirac sea below site 0: slope -1
        pts.append((x, f))
        x, f = x + 1, f - 1
    for l in range(max_site + 1):
        occ = l in L
        x1, f1 = x + 1, f - 1 if occ else f + 1
        col = (NEW if l in new else PART) if occ else WHITE
        prof.add(Line(apex + np.array([x, f, 0]) * s, apex + np.array([x1, f1, 0]) * s,
                      color=col, stroke_width=4 if occ else 2.5))
        x, f = x1, f1
    sea = VGroup(*[Line(apex + np.array([p[0], p[1], 0]) * s, apex + np.array([p[0] + 1, p[1] - 1, 0]) * s,
                        color=PART, stroke_width=4, stroke_opacity=0.4) for p in pts])
    # Maya line
    line = Line(M + LEFT * 2.2 * s, M + RIGHT * (max_site + 1.4) * s, color=DIM, stroke_width=1.2)
    sites = VGroup()
    nums = VGroup()
    for l in range(-2, max_site + 1):
        c = M + RIGHT * (l + 0.5) * s
        if l < 0:
            sites.add(Dot(c, radius=0.07, color=PART, fill_opacity=0.35))
            continue
        if l in clash:
            sites.add(Dot(c, radius=0.1, color=MUT))
        elif l in L:
            sites.add(Dot(c, radius=0.1, color=NEW if l in new else PART))
        else:
            sites.add(Circle(radius=0.09, color=GREY_B, stroke_width=1.5).move_to(c))
        if labels:
            nums.add(MathTex(str(l), font_size=18, color=DIM).move_to(c + DOWN * 0.3))
    g.add(lc, dia, sea, prof, line, sites, nums)
    return g


def string_brace(S, s, M, text, col=NEW):
    a, b = min(S), max(S)
    seg = Line(M + RIGHT * a * s + DOWN * 0.55, M + RIGHT * (b + 1) * s + DOWN * 0.55)
    br = Brace(seg, DOWN, buff=0.02, color=col)
    lab = MathTex(text, font_size=24, color=col).next_to(br, DOWN, buff=0.05)
    return VGroup(br, lab)


# ------------------------------------------------------------------------------------------------


class Title(Scene):
    def construct(self):
        card = title_card(self, "The string-insertion law",
                          "hook products as charge energies, and what one growth step costs")
        self.play(card.animate.shift(UP * 1.5))
        s = 0.3
        M = LEFT * 1.8 + DOWN * 3.4
        pic = maya_picture({0, 2, 5}, s, M, 10, labels=False)
        self.play(FadeIn(pic, lag_ratio=0.05))
        pic2 = maya_picture({0, 2, 5, 6, 7}, s, M, 10, new={6, 7}, labels=False)
        self.play(Transform(pic, pic2), run_time=1.5)
        self.play(FadeIn(tag("proved identities, and one law, checked on the proof's family", size=20)
                         .next_to(card, DOWN, buff=0.3)),
                  FadeIn(Text(REPO, font_size=18, color=DIM).to_corner(DR, buff=0.2)))
        self.wait(2)
        clear(self)


class MayaDiagram(Scene):
    def construct(self):
        header(self, "A shape is a set of particles", "the Maya diagram under the light cone")
        lam = [3, 1]
        eng = young(lam, cell=0.4).move_to(LEFT * 5.4 + UP * 1.6)
        lab = MathTex(r"\lambda=(3,1)", font_size=30).next_to(eng, DOWN, buff=0.25)
        self.play(FadeIn(eng), FadeIn(lab))
        s = 0.42
        M = LEFT * 4.2 + DOWN * 1.6
        L = {0, 2, 5}
        pic = maya_picture(L, s, M, 9)
        self.play(FadeIn(pic[0]), FadeIn(pic[1]), run_time=1)
        self.play(Create(pic[2]), Create(pic[3]), run_time=2)
        self.play(FadeIn(pic[4]), FadeIn(pic[5]), FadeIn(pic[6]))
        side = VGroup(
            MathTex(r"L(\lambda)=\{\lambda_i+N-1-i\}", font_size=32),
            MathTex(r"\lambda=(3,1),\ N=3:\quad L=\{5,2,0\}", font_size=30),
            Tex(r"profile slope $-1$: a particle (filled)", font_size=26, color=PART),
            Tex(r"profile slope $+1$: a hole (empty)", font_size=26),
            Tex(r"left of site $0$: the filled sea", font_size=26, color=DIM),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.2).move_to(RIGHT * 3.6 + UP * 0.9)
        self.play(FadeIn(side, lag_ratio=0.3), run_time=2.5)
        self.wait(1)
        # padding is a gauge
        L2 = {0, 1, 3, 6}
        pic2 = maya_picture(L2, s, M, 9)
        g = VGroup(
            Tex(r"Pad with one more row ($N=4$): $L=\{6,3,1,0\}$", font_size=22),
            Tex(r"every particle moves up by one, one enters at $0$;", font_size=26),
            Tex(r"the shape does not change.", font_size=26),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.12).next_to(side, DOWN, buff=0.45).align_to(side, LEFT)
        self.play(FadeIn(g))
        self.play(Transform(pic, pic2), run_time=2)
        self.play(FadeIn(lifted_moral("The padding N is a gauge: a shift, with a new particle at the bottom.")))
        self.add(foot("RMTlib: RMT.Fermion (occ_ofRows_rowLen, up to the shift by the charge)"))
        self.wait(2.5)
        clear(self)


class HookEnergy(Scene):
    def construct(self):
        header(self, "The hook product is an energy", "Frobenius' form, on the Maya set")
        f = MathTex(r"H_{\mathrm{set}}(L)\;=\;", r"\prod_{\ell\in L}\ell!", r"\;\Big/\;",
                    r"\prod_{\ell<\ell'\in L}(\ell'-\ell)", font_size=44).shift(UP * 1.8)
        f[1].set_color(SELF)
        f[3].set_color(MUT)
        self.play(Write(f))
        fr = MathTex(r"H_{\mathrm{set}}(L(\lambda)) = H(\lambda) = \prod_{\text{cells}}\text{hook}"
                     r"\quad\text{for every padding } N", font_size=32).next_to(f, DOWN, buff=0.35)
        st = status("proved").next_to(fr, RIGHT, buff=0.3)
        self.play(FadeIn(fr), FadeIn(st))
        # worked example
        eng = young([3, 1], cell=0.45).move_to(LEFT * 4.6 + DOWN * 1.0)
        hooks = [(0, 0, 4), (0, 1, 2), (0, 2, 1), (1, 0, 1)]
        hl = VGroup(*[MathTex(str(h), font_size=26).move_to(eng[k].get_center())
                      for k, (_, _, h) in enumerate(hooks)])
        self.play(FadeIn(eng), FadeIn(hl))
        ex = VGroup(
            MathTex(r"H(3,1)=4\cdot2\cdot1\cdot1=8", font_size=32),
            MathTex(r"L=\{0,2,5\}:\quad", r"\frac{0!\,2!\,5!}{2\cdot5\cdot3}", r"=\frac{240}{30}=8",
                    font_size=32),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.3).move_to(RIGHT * 1.2 + DOWN * 0.9)
        self.play(FadeIn(ex[0]))
        self.play(FadeIn(ex[1]))
        read = VGroup(
            Text("each particle sits in a one-body well  log ℓ!", font_size=22, color=SELF),
            Text("each pair repels:  − log |ℓ′ − ℓ|", font_size=22, color=MUT),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.12).to_edge(DOWN, buff=0.75)
        rl = status("idea").next_to(read, RIGHT, buff=0.3)
        self.play(FadeIn(read), FadeIn(rl))
        self.add(foot("proved: RMT.frobenius · idea: log H is the energy of a log-gas of particles"))
        self.wait(3)
        clear(self)


class OneInsertion(Scene):
    def construct(self):
        header(self, "Inserting a string", "consecutive particles dropped into empty sites")
        s = 0.42
        M = LEFT * 5.6 + DOWN * 1.3
        L = {0, 2, 5}
        S = {3, 4}
        pic = maya_picture(L, s, M, 9)
        self.play(FadeIn(pic))
        br = string_brace(S, s, M, r"S=\{3,4\}")
        self.play(FadeIn(br))
        pic2 = maya_picture(L | S, s, M, 9, new=S)
        self.play(Transform(pic, pic2), run_time=2)
        shp = MathTex(r"(3,1)\ \to\ (1,1,1,1)", font_size=26, color=DIM).next_to(pic, UP, buff=0.1)
        self.play(FadeIn(shp.shift(LEFT * 0.5)))
        law = MathTex(r"H_{\mathrm{set}}(L\sqcup S)\cdot", r"\mathrm{Mut}(L,S)", r"\;=\;H_{\mathrm{set}}(L)\cdot",
                      r"H_{\mathrm{set}}(S)", font_size=32).move_to(RIGHT * 2.9 + UP * 1.9)
        law[1].set_color(MUT)
        law[3].set_color(SELF)
        self.play(Write(law))
        defs = VGroup(
            MathTex(r"\mathrm{Mut}(L,S)=\prod_{\ell\in L,\,s\in S}|\ell-s|", font_size=28, color=MUT),
            MathTex(r"H_{\mathrm{set}}(S)=\frac{\prod_{s\in S}s!}{\prod_{k<t}k!}\quad(\text{a string of length }t)",
                    font_size=28, color=SELF),
            MathTex(r"24\cdot", r"48", r"\;=\;8\cdot", r"144", font_size=32),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.25).next_to(law, DOWN, buff=0.35)
        defs[2][1].set_color(MUT)
        defs[2][3].set_color(SELF)
        self.play(FadeIn(defs, lag_ratio=0.4), run_time=2)
        inc = MathTex(r"\Delta\log H \;=\;", r"\log H_{\mathrm{set}}(S)", r"\;-\;", r"\log\mathrm{Mut}(L,S)",
                      font_size=34).next_to(defs, DOWN, buff=0.35)
        inc[1].set_color(SELF)
        inc[3].set_color(MUT)
        self.play(Write(inc))
        st = status("proved").next_to(inc, DOWN, buff=0.15)
        self.play(FadeIn(st))
        self.play(FadeIn(lifted_moral("one step = the string's self-energy minus its mutual energy")))
        self.add(foot("proved in RMTlib (Vandermonde form): RMT.StringInsertion.vd_union, with fac_union"))
        self.wait(2.5)
        # Pauli: a colliding string is not insertable
        self.play(FadeOut(br), *[FadeOut(m) for m in [defs, inc, st, shp]])
        pic3 = maya_picture(L, s, M, 9, clash={5}, show_shape=True)
        self.play(Transform(pic, pic3))
        br2 = string_brace({5, 6}, s, M, r"S=\{5,6\}", col=MUT)
        self.play(FadeIn(br2))
        pa = VGroup(
            Tex(r"$S\cap L\neq\emptyset$: site $5$ is taken.", font_size=28, color=MUT),
            Tex(r"Not insertable (Pauli): $\mathrm{Mut}(L,S)=0$.", font_size=28, color=MUT),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.15).next_to(law, DOWN, buff=0.5)
        self.play(FadeIn(pa))
        self.wait(2.5)
        clear(self)


class Telescoping(Scene):
    def construct(self):
        header(self, "Steps telescope", "each increment is taken against everything inserted before")
        s = 0.3
        M = LEFT * 5.9 + DOWN * 2.3
        L = {0, 2, 5}
        pic = maya_picture(L, s, M, 11)
        self.play(FadeIn(pic))
        steps = [({7}, r"\tfrac{7!}{70}=72", "576"),
                 ({3, 4}, r"\tfrac{144}{576}=\tfrac14", "144"),
                 ({9, 10}, r"\tfrac{9!\,10!}{762048000}=1728", "248832")]
        rows = VGroup(MathTex(r"H_{\mathrm{set}}(L_0)=8", font_size=28))
        rows.move_to(LEFT * 0.6 + UP * 2.0, aligned_edge=LEFT)
        self.play(FadeIn(rows[0]))
        cur = set(L)
        for S, frac, val in steps:
            cur |= S
            new = maya_picture(cur, s, M, 11, new=S)
            sname = r"\{" + ",".join(str(x) for x in sorted(S)) + r"\}"
            r = MathTex(r"+" + sname + r":\ \times", frac, r"\ \to\ ", val, font_size=28)
            r[1].set_color(NEW)
            r.next_to(rows[-1], DOWN, buff=0.3, aligned_edge=LEFT)
            self.play(Transform(pic, new), FadeIn(r), run_time=1.8)
            rows.add(r)
            self.wait(0.4)
        tot = MathTex(r"8\cdot72\cdot\tfrac14\cdot1728=248832=H(3,3,2,1,1,1,1)", font_size=28, color=L_COL)
        tot.next_to(rows, DOWN, buff=0.4, aligned_edge=LEFT)
        self.play(Write(tot))
        rem = VGroup(
            Tex(r"An increment can be $<1$: a string dropped", font_size=24),
            Tex(r"between particles pays more mutual energy than it brings.", font_size=24),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.08).next_to(tot, DOWN, buff=0.35, aligned_edge=LEFT)
        self.play(FadeIn(rem))
        st = status("proved").next_to(rem, DOWN, buff=0.2, aligned_edge=LEFT)
        self.play(FadeIn(st))
        self.add(foot("proved per step (RMT.StringInsertion.hset_step, claim F9); the product of the increments telescopes to the final hook product"))
        self.wait(3)
        clear(self)


class CommutingSquare(Scene):
    def construct(self):
        header(self, "Two strings, two orders", "a cell of a growth diagram")
        A = r"\{3,4\}"
        B = r"\{7\}"
        pos = {"L": LEFT * 5.0 + DOWN * 1.7, "A": LEFT * 5.0 + UP * 1.3,
               "B": LEFT * 1.0 + DOWN * 1.7, "AB": LEFT * 1.0 + UP * 1.3}
        val = {"L": (r"L", "8"), "A": (r"L\sqcup" + A, "24"), "B": (r"L\sqcup" + B, "576"),
               "AB": (r"L\sqcup" + A + r"\sqcup" + B, "144")}
        nodes = {}
        for k, p in pos.items():
            name, v = val[k]
            nodes[k] = VGroup(MathTex(name, font_size=26), MathTex(r"H=" + v, font_size=26, color=PART)
                              ).arrange(DOWN, buff=0.08).move_to(p)
        self.play(*[FadeIn(n) for n in nodes.values()])

        def arrow(a, b, lab, side):
            if abs(side[0]) > 0:          # label at the side: a vertical edge
                p, q = nodes[a].get_top(), nodes[b].get_bottom()
            else:                         # horizontal edge, kept at the height of the node names
                y = nodes[a][0].get_center()[1]
                p = np.array([nodes[a].get_right()[0], y, 0])
                q = np.array([nodes[b].get_left()[0], y, 0])
            ar = Arrow(p, q, buff=0.15, stroke_width=3, color=GREY_B)
            t = MathTex(lab, font_size=24, color=NEW).next_to(ar, side, buff=0.1)
            return VGroup(ar, t)

        e1 = arrow("L", "A", r"\times\tfrac{144}{48}=3", LEFT)
        e2 = arrow("A", "AB", r"\times\tfrac{5040}{840}=6", UP)
        e3 = arrow("L", "B", r"\times\tfrac{5040}{70}=72", DOWN)
        e4 = arrow("B", "AB", r"\times\tfrac{144}{576}=\tfrac14", RIGHT)
        self.play(Create(e1), Create(e2))
        self.play(Create(e3), Create(e4))
        eq = MathTex(r"8\cdot3\cdot6\;=\;144\;=\;8\cdot72\cdot\tfrac14", font_size=32, color=L_COL)
        eq.move_to(LEFT * 3.0 + DOWN * 2.85)
        self.play(Write(eq))
        side = VGroup(
            MathTex(r"A=\{3,4\},\quad B=\{7\}", font_size=26, color=NEW),
            Tex(r"Both routes reach the same set,", font_size=26),
            Tex(r"so the square commutes: no defect.", font_size=26),
            status("proved"),
            Tex(r"The mutual energies swap between edges:", font_size=24, color=DIM),
            MathTex(r"\mathrm{Mut}(L\sqcup B,A)\,\mathrm{Mut}(L,B)", font_size=26, color=DIM),
            MathTex(r"=\mathrm{Mut}(L\sqcup A,B)\,\mathrm{Mut}(L,A)", font_size=26, color=DIM),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.13).move_to(RIGHT * 3.9 + UP * 1.2)
        self.play(FadeIn(side, lag_ratio=0.25), run_time=2)
        self.wait(1.5)
        diag = VGroup(
            Tex(r"So a defect is a diagnostic:", font_size=26, color=L_COL),
            MathTex(r"\text{measured }\Delta(\text{slack})-\big[\text{translation}+\log H_{\mathrm{set}}(S)-\log\mathrm{Mut}(L,S)\big]",
                    font_size=24),
            Tex(r"vanishes at every true string insertion;", font_size=24),
            Tex(r"where it does not, the step is a collision,", font_size=24),
            Tex(r"not a translation followed by a disjoint insertion.", font_size=24),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.08).next_to(side, DOWN, buff=0.3).align_to(side, LEFT)
        for line in diag:
            if line.get_right()[0] > 6.9:
                line.scale_to_fit_width(6.9 - line.get_left()[0])
                line.align_to(side, LEFT)
        self.play(FadeIn(diag))
        self.add(foot("proved: the cell rule is vd_union / fac_union (claim F3) · "
                      "idea: 'Fomin-type'; the defect as a diagnostic is RH-Dual's check (claim F4)"))
        self.wait(3)
        clear(self)


class PlaceReading(Scene):
    def construct(self):
        header(self, "Where the place enters", "one-body weight over the Vandermonde")
        f = MathTex(r"H_{\mathrm{set}}(L)=\frac{\prod_{\ell\in L}", r"\rho_v(\ell)", r"}{\Delta(L)}",
                    font_size=38).shift(UP * 2.0 + LEFT * 3.2)
        f[1].set_color(L_COL)
        self.play(Write(f))
        places = VGroup(
            MathTex(r"\rho_\infty(\ell)=\ell!", font_size=32, color=INF_COL),
            MathTex(r"\rho_p(\ell)=T^{\ell}", font_size=32, color=P_COL),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.2).next_to(f, RIGHT, buff=0.8)
        self.play(FadeIn(places))
        ax = Axes(x_range=[0, 7, 1], y_range=[0, 32, 8], x_length=6.2, y_length=3.4, tips=False,
                  axis_config={"color": DIM, "include_numbers": True, "font_size": 18}).shift(LEFT * 2.6 + DOWN * 1.3)
        xl = MathTex(r"a", font_size=26, color=DIM).next_to(ax.x_axis, RIGHT, buff=0.1)
        yl = Tex(r"self-energy of $S_a=\{a,a{+}1,a{+}2\}$", font_size=22, color=DIM).next_to(ax, UP, buff=0.1)
        self.play(Create(ax), FadeIn(xl), FadeIn(yl))

        def e_inf(a):
            return sum(math.lgamma(a + j + 1) for j in range(3)) - math.log(2)

        def e_p(a, logT=1.5):
            return (3 * a + 3) * logT - math.log(2)

        pi = VGroup(*[Dot(ax.c2p(a, e_inf(a)), radius=0.06, color=INF_COL) for a in range(8)])
        ci = ax.plot(e_inf, x_range=[0, 7], color=INF_COL)
        pp = VGroup(*[Dot(ax.c2p(a, e_p(a)), radius=0.06, color=P_COL) for a in range(8)])
        cp = ax.plot(e_p, x_range=[0, 7], color=P_COL)
        self.play(Create(ci), FadeIn(pi))
        self.play(Create(cp), FadeIn(pp))
        lab = VGroup(Tex(r"$\infty$: $\sum\log s!$, convex in $a$", font_size=24, color=INF_COL),
                     Tex(r"$p$: $(3a{+}3)\log T$, affine in $a$", font_size=24, color=P_COL),
                     Tex(r"(picture: $\log T=1.5$; both minus $\log 2!\,1!\,0!$)", font_size=20, color=DIM)
                     ).arrange(DOWN, aligned_edge=LEFT, buff=0.12).move_to(RIGHT * 3.6 + DOWN * 0.2)
        self.play(FadeIn(lab))
        side = VGroup(
            Tex(r"An affine one-body weight changes a", font_size=24),
            Tex(r"string's self-energy affinely in its position.", font_size=24),
            Tex(r"Only the non-affine part of $\log\ell!$", font_size=24, color=L_COL),
            Tex(r"makes where the string sits matter.", font_size=24, color=L_COL),
            Tex(r"$\mathrm{Mut}$ uses only $\Delta$: the same at every place.", font_size=24),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.1).next_to(lab, DOWN, buff=0.35).align_to(lab, LEFT)
        self.play(FadeIn(side, lag_ratio=0.3), run_time=2)
        self.add(foot("proved: ¬ IsExpLinear rhoInf (RMT.BDTW) · idea: the place reading, "
                      "RMTlib#21's root (b) at the level of slack"))
        self.wait(3)
        clear(self)


class Hypothesis(Scene):
    def construct(self):
        header(self, "The string-insertion law", "checked on the proof's family")
        st = status("checked").scale(1.2).next_to(VGroup(*self.mobjects), DOWN, buff=0.15)
        h = VGroup(
            Tex(r"Along the theta lifts of the proof, each step translates the old charges", font_size=26),
            Tex(r"and inserts the one that crosses the band (a translation is not a gauge).", font_size=26),
            Tex(r"(a) $\Delta\log H$ = translation + self-energy $-$ mutual energy at each step;",
                font_size=24),
            Tex(r"(b) it telescopes along any path;", font_size=24),
            Tex(r"(c) the grid of lifts is a growth diagram whose squares commute exactly;", font_size=24),
            Tex(r"(d) asymptotically the slack is a log-gas energy: "
                r"$\sum\log\ell!-\sum\log|\ell-\ell'|$.", font_size=24),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.14).next_to(st, DOWN, buff=0.3)
        h[2:].shift(RIGHT * 0.4)
        self.play(FadeIn(st))
        self.play(FadeIn(h, lag_ratio=0.25), run_time=3)
        self.wait(1.5)
        ref = VGroup(
            Text("Refuted by:", font_size=22, color=MUT),
            Text("• a step that is not a translation followed by a disjoint string insertion (the defect sits there);",
                 font_size=19),
            Text("• a string-insertion step whose slack increment differs from translation + self − mutual;", font_size=19),
            Text("• a nonzero defect on a square of two disjoint insertions (a mis-identified Maya set).",
                 font_size=19),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.08).next_to(h, DOWN, buff=0.3).align_to(h, LEFT)
        for line in ref:
            if line.width > 11.6:
                line.scale_to_fit_width(11.6)
        # Scaling a line moves its left edge (it scales about its centre): re-align the lines.
        ref.arrange(DOWN, aligned_edge=LEFT, buff=0.08)
        if ref.width > 10.8:
            ref.scale_to_fit_width(10.8)
        ref.next_to(h, DOWN, buff=0.3).align_to(h, LEFT)
        self.play(FadeIn(ref, lag_ratio=0.2), run_time=2)
        self.add(foot("proved for every Maya set: (a), (b) (claim F9, RMT.StringInsertion.log_hset_step) · "
                      "computed: the proof's lifts are such steps, and (c) (RH-Dual, claim F4)",
                      "conjecture: (d) · " + NOTE))
        self.wait(4)


SCENES = [Title, MayaDiagram, HookEnergy, OneInsertion, Telescoping, CommutingSquare, PlaceReading,
          Hypothesis]
