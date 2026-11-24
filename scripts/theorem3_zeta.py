"""Dehaye's Theorem 3 (arXiv:1201.4478) checked for zeta itself, and compared with U(N).

Theorem 3:  c_M(k) = 1/(k^2-M)! * sum_{|kappa|+|lambda|=M} d_{kappa lambda} dim(lambda, S_k(kappa)),
with d from the Schur expansion of f~(A;B) = sum d s_kappa(A) s_lambda(B-underline).

For k = 2 the arithmetic factor is in closed form, A = 1/zeta(2 + a1 + a2 - b1 - b2), so

    zeta:  f~ = prod_{a,b} G(a-b) / zeta(2 + sum A - sum B),   G(u) = u zeta(1+u)
    U(N):  f~ = prod_{a,b} g(a-b),                              g(u) = u/(1-e^{-u})

The script computes d for both, assembles Theorem 3, and compares the zeta polynomial with the
independent swap computation of toy_examples/scripts/places.py (RMTandMeaningLib). It prints the table of d_{kappa lambda}
side by side: everything Theorem 3 needs from the primes is in the difference.

    python3 scripts/theorem3_zeta.py
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from math import factorial
import mpmath as mp
import un_test as U

mp.mp.dps = 40
K_DEFAULT = 2

def series_coeffs_G(D):
    """u*zeta(1+u) = 1 + sum_n (-1)^n gamma_n u^{n+1}/n!."""
    g = [mp.mpf(1)] + [mp.mpf(0)] * D
    for n in range(D):
        g[n + 1] = (-1) ** n * mp.stieltjes(n) / mp.factorial(n)
    return g

def series_coeffs_todd(D):
    return [mp.mpf(c.numerator) / c.denominator for c in U.g_coeffs(D)]

def fseries(k, kern, arith):
    """prod_{i,j} kern(a_i - b_j) * arith(sum a - sum b), truncated at total degree k^2."""
    nv, D = 2 * k, k * k
    one = {tuple([0] * nv): mp.mpf(1)}
    F = dict(one)
    def series_of_linear(lin, coeffs):
        out, pw = {tuple([0] * nv): coeffs[0]}, dict(one)
        for n in range(1, D + 1):
            pw = U.poly_mul(pw, lin, nv, D)
            for e, c in pw.items():
                out[e] = out.get(e, 0) + coeffs[n] * c
        return out
    for i in range(k):
        for j in range(k):
            F = U.poly_mul(F, series_of_linear(U.lin(nv, i, k + j), kern), nv, D)
    if arith is not None:
        s = {}
        for i in range(k):
            e = [0] * nv; e[i] = 1; s[tuple(e)] = mp.mpf(1)
            e = [0] * nv; e[k + i] = 1; s[tuple(e)] = mp.mpf(-1)
        F = U.poly_mul(F, series_of_linear(s, arith), nv, D)
    return F

def d_table(k, F):
    nv, D = 2 * k, k * k
    G = U.poly_mul(U.poly_mul(F, U.vandermonde(k, 0, nv), nv), U.vandermonde(k, k, nv), nv)
    delta = list(range(k - 1, -1, -1))
    parts = U.partitions_in_box(k, D)
    d = {}
    for kap in parts:
        for lam in parts:
            if sum(kap) + sum(lam) > D:
                continue
            e = tuple([kap[i] + delta[i] for i in range(k)] + [lam[i] + delta[i] for i in range(k)])
            c = G.get(e, 0)
            if c != 0:
                d[(kap, lam)] = c * (-1) ** sum(lam)
    return d

def theorem3(k, d):
    D = k * k
    coeffs = [mp.mpf(0)] * (D + 1)   # coefficient of x^j
    for (kap, lam), dk in d.items():
        M = sum(kap) + sum(lam)
        rot = tuple(k - kap[k - 1 - i] for i in range(k))
        S = U.transpose(rot, k)
        coeffs[D - M] += dk * U.dim(lam, S) / mp.factorial(D - M)
    return coeffs

def show_partition(p):
    q = [x for x in p if x]
    return '(' + ','.join(map(str, q)) + ')' if q else '∅'

if __name__ == '__main__':
    k = int(sys.argv[1]) if len(sys.argv) > 1 else K_DEFAULT
    assert k == 2, "closed-form arithmetic factor only for k = 2"
    D = k * k
    inv_zeta2 = mp.taylor(lambda u: 1 / mp.zeta(2 + u), 0, D)
    dz = d_table(k, fseries(k, series_coeffs_G(D), inv_zeta2))
    du = d_table(k, fseries(k, series_coeffs_todd(D), None))
    Pz, Pu = theorem3(k, dz), theorem3(k, du)
    swap_zeta = [mp.mpf('1.31242438628573'), mp.mpf('3.22790796485076'), mp.mpf('2.42596219884961'),
                 mp.mpf('0.698869884878905'), mp.mpf('0.0506605918211696')]   # toy_examples/scripts/places.py (RMTandMeaningLib) 2 40
    print(f'k = {k}: Theorem 3 assembled from d_kappa,lambda')
    print('  x^j   zeta (Theorem 3)        zeta (swap, places.py)   U(N) (Theorem 3)   U(N) exact')
    exact_un = [1, mp.mpf(7) / 3, mp.mpf(23) / 12, mp.mpf(2) / 3, mp.mpf(1) / 12]
    for j in range(D, -1, -1):
        print(f'  x^{j}   {mp.nstr(Pz[j], 15):>22}   {mp.nstr(swap_zeta[j], 15):>22}   '
              f'{mp.nstr(Pu[j], 10):>16}   {mp.nstr(exact_un[j], 10):>12}')
    print('  max |zeta Thm3 - swap| =', mp.nstr(max(abs(a - b) for a, b in zip(Pz, swap_zeta)), 3))
    print('\n  d_kappa,lambda (|kappa|+|lambda| <= 3):  zeta  |  U(N)  |  ratio')
    keys = sorted(set(dz) | set(du), key=lambda kl: (sum(kl[0]) + sum(kl[1]), kl))
    for kl in keys:
        if sum(kl[0]) + sum(kl[1]) > 3:
            continue
        a, b = dz.get(kl, 0), du.get(kl, 0)
        r = mp.nstr(a / b, 8) if b != 0 else '—'
        print(f'  {show_partition(kl[0]):>6} {show_partition(kl[1]):>6}   {mp.nstr(a, 12):>18}  {mp.nstr(b, 10):>14}  {r:>12}')
