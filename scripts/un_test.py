"""U(N) test of the place-agnostic form of Dehaye (arXiv:1201.4478) Theorem 3.

Three computations of the U(N) moment polynomial P_k(N) = E|Lambda_g(1)|^{2k}:
  (exact) prod_{i,j<=k} (N+i+j-1)/(i+j-1)                       [Keating-Snaith / Bump-Gamburd]
  (swap)  CFKRS sum over swaps, kernel Z(u) = 1/(1-e^{-u}), x = N  [CFKRS 2003, U(N) theorem]
  (thm3)  c_M = 1/(k^2-M)! sum_{|kappa|+|lambda|=M} d_{kappa lambda} dim(lambda, S_k(kappa)),
          d from the Schur expansion of f~(A;B) = prod_{a,b} g(a-b), g(u) = u/(1-e^{-u}).
"""
from fractions import Fraction as Fr
from itertools import combinations, product
from functools import lru_cache
from math import comb, factorial
import sys

import sympy as sp

N = sp.Symbol('N')

# ---------- the local kernel at the single place of U(N) ----------
def g_coeffs(D):
    """Taylor coefficients of g(u) = u/(1-e^{-u}) up to u^D (Bernoulli numbers, B_1 = +1/2)."""
    h = [Fr((-1) ** n, factorial(n + 1)) for n in range(D + 1)]  # (1-e^{-u})/u
    g = [Fr(0)] * (D + 1)
    g[0] = 1 / h[0]
    for n in range(1, D + 1):
        g[n] = -sum(h[j] * g[n - j] for j in range(1, n + 1)) / h[0]
    return g

# ---------- (exact) ----------
def exact(k):
    P = sp.Integer(1)
    for i in range(1, k + 1):
        for j in range(1, k + 1):
            P *= (N + i + j - 1) / sp.Integer(i + j - 1)
    return sp.expand(P)

# ---------- (swap) CFKRS sum over swaps, limit D -> 0 along delta_i = eps * r_i ----------
def swap(k, r=None):
    K2 = k * k
    gc = g_coeffs(K2)
    r = r or [Fr(p) for p in [1, 3, 7, 12, 20, 33][: 2 * k]]
    total = sp.Integer(0)
    idx = range(2 * k)
    for A in combinations(idx, k):
        B = [i for i in idx if i not in A]
        # series in eps (coefficients are sympy polynomials in N), truncated at eps^K2
        ser = [sp.Integer(0)] * (K2 + 1)
        sB = sum(r[b] for b in B)
        for n in range(K2 + 1):  # e^{-N eps sB}
            ser[n] = (-N * sB) ** n / sp.factorial(n)
        den = Fr(1)
        for a in A:
            for b in B:
                d = r[a] - r[b]
                den *= d
                fac = [gc[n] * d ** n for n in range(K2 + 1)]
                new = [sp.Integer(0)] * (K2 + 1)
                for i in range(K2 + 1):
                    if ser[i] == 0:
                        continue
                    for j in range(K2 + 1 - i):
                        new[i + j] += ser[i] * sp.Rational(fac[j].numerator, fac[j].denominator)
                ser = [sp.expand(s) for s in new]
        total += ser[K2] / sp.Rational(den.numerator, den.denominator)
    return sp.expand(total)

# ---------- (thm3) Schur expansion of f~ and skew dimensions ----------
def poly_mul(p, q, nv, D=None):
    out = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = tuple(x + y for x, y in zip(e1, e2))
            if D is not None and sum(e) > D:
                continue
            out[e] = out.get(e, 0) + c1 * c2
    return {e: c for e, c in out.items() if c != 0}

def lin(nv, i, j):
    """a_i - b_j as a polynomial in nv = 2k variables (a's first)."""
    e1 = [0] * nv; e1[i] = 1
    e2 = [0] * nv; e2[j] = 1
    return {tuple(e1): Fr(1), tuple(e2): Fr(-1)}

def fseries(k):
    """f~(A;B) = prod_{i,j} g(a_i - b_j), truncated at total degree k^2."""
    nv, D = 2 * k, k * k
    gc = g_coeffs(D)
    F = {tuple([0] * nv): Fr(1)}
    for i in range(k):
        for j in range(k):
            u = lin(nv, i, k + j)
            gu, upow = {tuple([0] * nv): gc[0]}, {tuple([0] * nv): Fr(1)}
            for n in range(1, D + 1):
                upow = poly_mul(upow, u, nv, D)
                for e, c in upow.items():
                    gu[e] = gu.get(e, 0) + gc[n] * c
            F = poly_mul(F, gu, nv, D)
    return F

def vandermonde(k, offset, nv):
    V = {tuple([0] * nv): Fr(1)}
    for i in range(k):
        for j in range(i + 1, k):
            V = poly_mul(V, lin(nv, offset + i, offset + j) if offset == 0 else
                         {tuple(1 if t == offset + i else 0 for t in range(nv)): Fr(1),
                          tuple(1 if t == offset + j else 0 for t in range(nv)): Fr(-1)}, nv)
    return V

def partitions_in_box(k, maxsize):
    out = []
    def rec(prefix, maxpart, left):
        if len(prefix) == k:
            out.append(tuple(prefix)); return
        for p in range(min(maxpart, left), -1, -1):
            rec(prefix + [p], p, left - p)
    rec([], k, maxsize)
    return out

@lru_cache(maxsize=None)
def dim(lam, mu):
    """Number of paths lam -> mu in Young's lattice (skew SYT of shape mu/lam); tuples padded."""
    if lam == mu:
        return 1
    if sum(mu) <= sum(lam) or any(l > m for l, m in zip(lam, mu)):
        return 0
    tot = 0
    for i in range(len(mu)):
        nxt = mu[i + 1] if i + 1 < len(mu) else 0
        if mu[i] > nxt:
            m2 = list(mu); m2[i] -= 1
            tot += dim(lam, tuple(m2))
    return tot

def transpose(p, k):
    return tuple(sum(1 for x in p if x > j) for j in range(k))

def thm3(k, variant):
    nv, D = 2 * k, k * k
    F = fseries(k)
    G = poly_mul(poly_mul(F, vandermonde(k, 0, nv), nv), vandermonde(k, k, nv), nv)
    delta = list(range(k - 1, -1, -1))
    parts = partitions_in_box(k, D)
    P = sp.Integer(0)
    for kap in parts:
        for lam in parts:
            M = sum(kap) + sum(lam)
            if M > D:
                continue
            e = tuple([kap[i] + delta[i] for i in range(k)] + [lam[i] + delta[i] for i in range(k)])
            c = G.get(e, 0)
            if c == 0:
                continue
            d = c * (-1) ** sum(lam)
            rot = tuple(k - kap[k - 1 - i] for i in range(k))      # rotated complement of kappa
            S = rot if variant == 'rot' else transpose(rot, k)
            P += sp.Rational(d.numerator, d.denominator) * dim(lam, S) * N ** (D - M) / sp.factorial(D - M)
    return sp.expand(P)

if __name__ == '__main__':
    for k in [int(a) for a in sys.argv[1:]] or [2, 3]:
        ex, sw = exact(k), swap(k)
        print(f'k={k}')
        print('  exact :', sp.factor(ex), '=', ex)
        print('  swap  :', sp.expand(sw - ex) == 0)
        for v in ['rot', 'transpose']:
            t3 = thm3(k, v)
            print(f'  thm3[{v}] matches:', sp.expand(t3 - ex) == 0, '' if sp.expand(t3 - ex) == 0 else t3)
