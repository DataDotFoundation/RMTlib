"""Fock (Fischer) pairing on class functions of N x N matrices: checks
<s_lambda(X), s_mu(X)>_Fock = delta * prod_{(i,c) in lambda} (N + c - i)
for N = 2 (|lambda| <= 4) and N = 3 (|lambda| <= 3), and prints ||(tr X)^m||^2, ||tr X^k||^2.
See RMTlib/Fock/ClassFunction.lean."""
import sympy as sp, itertools, math
from sympy.utilities.iterables import partitions

def setup(N):
    X = sp.Matrix(N, N, lambda i,j: sp.Symbol(f"x{i}{j}"))
    t = sp.Symbol('t')
    cp = sp.expand((sp.eye(N) + t*X).det())
    e = [sp.expand(cp.coeff(t, k)) for k in range(N+1)]
    return X, e

def hs(e, N, K):
    h = [sp.Integer(1)]
    for k in range(1, K+1):
        s = 0
        for i in range(1, min(k, N)+1):
            s += (-1)**(i+1) * e[i] * h[k-i]
        h.append(sp.expand(s))
    return h

def schur(lam, h):
    n = len(lam)
    M = sp.Matrix(n, n, lambda i,j: (h[lam[i]-i+j] if lam[i]-i+j >= 0 else 0))
    return sp.expand(M.det())

def fischer(f, g, gens):
    pf, pg = sp.Poly(f, *gens), sp.Poly(g, *gens)
    dg = dict(pg.terms())
    tot = 0
    for mon, c in pf.terms():
        if mon in dg:
            tot += c * dg[mon] * math.prod(math.factorial(a) for a in mon)
    return tot

def contents(lam, N):
    return math.prod(N + c - i for i, row in enumerate(lam) for c in range(row))

for N in [2, 3]:
    X, e = setup(N)
    gens = list(X)
    h = hs(e, N, 6)
    shapes = []
    for m in range(1, 5 if N == 2 else 4):
        for p in partitions(m):
            lam = sorted([k for k, v in p.items() for _ in range(v)], reverse=True)
            if len(lam) <= N: shapes.append(tuple(lam))
    S = {lam: schur(list(lam), h) for lam in shapes}
    ok = True
    for a in shapes:
        for b in shapes:
            v = fischer(S[a], S[b], gens)
            want = contents(a, N) if a == b else 0
            if v != want:
                ok = False; print("MISMATCH", N, a, b, v, want)
    print("N =", N, "shapes", shapes, "all match:", ok)
    # trace powers and power sums
    p = [None] + [sp.expand((X**k).trace()) for k in range(1, 4)]
    for m in range(1, 4):
        print(" N", N, "||(tr X)^%d||^2 =" % m, fischer(sp.expand(p[1]**m), sp.expand(p[1]**m), gens), " m! N^m =", math.factorial(m)*N**m)
    for k in range(1, 4):
        print(" N", N, "||tr X^%d||^2 =" % k, fischer(p[k], p[k], gens))
