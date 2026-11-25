"""Schensted's ω for Hage's super-RSK (RMTlib#74, step 1).

Schensted: for ordinary RSK, reversing a permutation transposes its insertion tableau,
P(w reversed) = P(w)ᵀ. This checks the super version on the super-RSK of `growth_rules.py`
(Hage 2022, LNS super row insertion), exhaustively on small fillings:

  reverse the biword (the rows of A in reverse order) AND flip every parity (rows and letters)
  ⇒ P transposes exactly.

It also checks that each partial version fails (reversal alone; reversal with only the row
parities flipped; reversal with only the letter parities flipped), and that the local rule is NOT
ω-equivariant square by square (fixed orientation): the symmetry is a reflection of the whole
grid, not a property of one square.

Run: python3 -I scripts/super_schensted_omega.py   (stdlib only; exit 0 iff all checks pass)
"""
import collections
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import growth_rules as g  # noqa: E402

FLIP = {'b': 'f', 'f': 'b'}


def transpose(P):
    if not P:
        return []
    return [[P[i][j] for i in range(len(P)) if j < len(P[i])] for j in range(len(P[0]))]


def valid(A, rp, cp):
    """Mixed-parity entries are 0 or 1."""
    return all(A[i][j] <= 1 for i in range(len(A)) for j in range(len(A[0])) if rp[i] != cp[j])


VARIANTS = {
    'reverse, flip rows and letters': (True, True),
    'reverse only': (False, False),
    'reverse, flip rows only': (True, False),
    'reverse, flip letters only': (False, True),
}


def global_check(sizes=((1, 2), (2, 2), (2, 3), (3, 2), (3, 3)), maxent=2, maxsum=4):
    stats = collections.Counter()
    for n, m in sizes:
        for rp in itertools.product('bf', repeat=n):
            for cp in itertools.product('bf', repeat=m):
                for ent in itertools.product(range(maxent + 1), repeat=n * m):
                    if sum(ent) > maxsum:
                        continue
                    A = [list(ent[i * m:(i + 1) * m]) for i in range(n)]
                    if not valid(A, rp, cp):
                        continue
                    P = g.insertion(A, rp, cp)[0]
                    for name, (fr, fc) in VARIANTS.items():
                        rp2 = tuple(FLIP[x] if fr else x for x in rp[::-1])
                        cp2 = tuple(FLIP[x] if fc else x for x in cp)
                        if not valid(A[::-1], rp2, cp2):
                            continue
                        P2 = g.insertion(A[::-1], rp2, cp2)[0]
                        stats[name, 'cases'] += 1
                        stats[name, 'P2 = Pᵀ'] += P2 == transpose(P)
    return stats


def local_check(N=6, W=8, maxpart=3, maxx=3):
    """Square by square, fixed orientation: is conj ∘ fwd_flip ∘ conj = fwd ?"""
    out = {}
    for pi, pj in [('b', 'b'), ('b', 'f'), ('f', 'b'), ('f', 'f')]:
        eq = tot = 0
        for rho in itertools.product(range(maxpart + 1), repeat=3):
            if not g.is_part(rho):
                continue
            rho = tuple(rho) + (0,) * (N - 3)
            for mu in g.strips_over(pi, rho, maxpart + 1):
                for nu in g.strips_over(pj, rho, maxpart + 1):
                    for x in range(maxx + 1 if pi == pj else 2):
                        lam, t = g.fwd_c(pi, pj, rho, mu, nu, x)
                        if t != 0 or not g.is_part(lam) or sum(1 for a in lam if a) > W - 1:
                            continue
                        c = lambda p: g.conj(p, W)
                        lam2, t2 = g.fwd_c(FLIP[pi], FLIP[pj], c(rho), c(mu), c(nu), x)
                        if t2 != 0:
                            continue
                        tot += 1
                        eq += g.conj(lam2, N) == lam
        out[pi, pj] = (eq, tot)
    return out


def main():
    ok = True
    st = global_check()
    for name in VARIANTS:
        n, k = st[name, 'cases'], st[name, 'P2 = Pᵀ']
        print(f"{name:34s} P(reversed) = Pᵀ on {k}/{n}")
    full = 'reverse, flip rows and letters'
    ok &= st[full, 'P2 = Pᵀ'] == st[full, 'cases'] > 0
    ok &= all(st[v, 'P2 = Pᵀ'] < st[v, 'cases'] for v in VARIANTS if v != full)
    for t, (eq, tot) in local_check().items():
        print(f"local, fixed orientation, type {t}: equivariant on {eq}/{tot} squares")
        ok &= eq < tot
    print('OK' if ok else 'FAIL')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
