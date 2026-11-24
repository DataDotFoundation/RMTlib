#!/usr/bin/env python3
"""Load the joint-moment data of Dehaye, "Joint moments of derivatives of characteristic
polynomials" (Algebra & Number Theory 2 (2008) 31-68, arXiv:math/0703440), as attached to its
arXiv source, and expose the ratios Hall's method uses.

Data: docs/data/dehaye-joint-moments/ (see its README.md).

Normalisation (paper, Theorems 1 and 16):
    (M)(2k, r)    = (-i/2)^r   g(k) X_r(2k)      / Y_r(2k)
    |M|(2k, 2h)   = 2^{-2h}    g(k) Xhat_{2h}(2k) / Y_{2h}(2k)
    |V|(2k, 2h)   = Ctilde(h)  g(k) Xtil_{2h}(2k) / Y_{2h}(2k),   Ctilde(h) = (2h)!/(h! 2^{3h})
with g(k) = G(k+1)^2/G(2k+1) and
    Y_r(u) = prod_{a odd, 1 <= a <= r-1} (u^2 - a^2)^{alpha_a(r)},
    alpha_a(r) = floor((-a + sqrt(a^2 + 4r)) / 2).
The monic normalisation of the numerators with these constants is stated as conjectural for |M| and
|V| in the paper (Theorem 16); it is checked here only through the low cases.

Hall's inputs are the ratios beta_h(k) = |V|(2k,2h)/|V|(2k,0) = Ctilde(h) Xtil_{2h}(2k)/Y_{2h}(2k);
g(k) and the arithmetic factor a(k) cancel.

Usage: python3 scripts/dehaye_joint_moments.py   (runs the checks; exit 0 on success)
"""
from fractions import Fraction
from math import factorial, isqrt
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(ROOT, "docs", "data", "dehaye-joint-moments")  # ROOT = the repository root


def parse_magma_list(path):
    """Parse a Magma list of polynomials in u into lists of integer coefficients (index = power)."""
    text = open(path, encoding="utf-8").read()
    text = "\n".join(l for l in text.splitlines() if not l.strip().startswith("//"))
    body = text[text.index("[") + 1: text.rindex("]")]
    polys = []
    for item in body.split(","):
        item = re.sub(r"\s+", "", item)
        if not item:
            continue
        coeffs = {}
        for sign, coef, var, power in re.findall(r"([+-]?)(\d*)\*?(u?)(?:\^(\d+))?", item):
            if not coef and not var:
                continue
            c = int(coef) if coef else 1
            if sign == "-":
                c = -c
            e = (int(power) if power else 1) if var else 0
            coeffs[e] = coeffs.get(e, 0) + c
        deg = max(coeffs)
        polys.append([coeffs.get(i, 0) for i in range(deg + 1)])
    return polys


def peval(p, x):
    return sum(Fraction(c) * Fraction(x) ** i for i, c in enumerate(p))


def alpha(a, r):
    return (-a + isqrt(a * a + 4 * r)) // 2


def Y(r, u):
    out = Fraction(1)
    for a in range(1, r, 2):
        out *= (Fraction(u) ** 2 - a * a) ** alpha(a, r)
    return out


def Y_degree(r):
    return 2 * sum(alpha(a, r) for a in range(1, r, 2))


def ctilde(h):
    return Fraction(factorial(2 * h), factorial(h) * 2 ** (3 * h))


XTIL = None


def xtil(h):
    """Xtil_{2h}(u) for h >= 1 (paper's Table 3; data up to h = 30)."""
    global XTIL
    if XTIL is None:
        XTIL = parse_magma_list(os.path.join(DATA, "NumeratorsNormedV"))
    return XTIL[h - 1]


def beta(h, k):
    """beta_h(k) = |V|(2k,2h)/|V|(2k,0), exact for rational k away from poles."""
    if h == 0:
        return Fraction(1)
    u = 2 * Fraction(k)
    return ctilde(h) * peval(xtil(h), u) / Y(2 * h, u)


def main():
    checks = 0
    xt = parse_magma_list(os.path.join(DATA, "NumeratorsNormedV"))
    assert len(xt) == 30, len(xt)
    checks += 1
    # beta_1, beta_2 against hall-theta-dictionary.md (Hughes's form), several k.
    for k in [Fraction(n) for n in range(1, 13)] + [Fraction(7, 3), Fraction(11, 4)]:
        assert beta(1, k) == Fraction(1, 4) / (4 * k * k - 1)
        K = 2 * k
        assert beta(2, k) == Fraction(3, 16) / ((K * K - 1) * (K * K - 9))
        checks += 2
    # Theorem 16's (conjectural) degree statement: deg X_{2h} - deg Xtil_{2h} = 2h, with
    # deg X_r = deg Y_r (Theorem 1).
    for h in range(1, 31):
        assert Y_degree(2 * h) - (len(xt[h - 1]) - 1) == 2 * h, h
        checks += 1
    # Monic and even numerators.
    for h, p in enumerate(xt, 1):
        assert p[-1] == 1 and all(c == 0 for c in p[1::2]), h
        checks += 1
    print(f"dehaye_joint_moments: {checks} checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
