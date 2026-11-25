#!/usr/bin/env python3
"""The moment measure on the k x N box and the wall (RMTlib#19, B6; docs/loops/*wall-moments*).

E_{U(N)} |Lambda_U(1)|^{2k} = sum_{lambda in k x N box} s_lambda(1^k)^2 = s_{<N^k>}(1^{2k}).
P(lambda) = s_lambda(1^k)^2 / s_{<N^k>}(1^{2k}) is the moment measure. Exact arithmetic, stdlib only.

usage: python3 -I scripts/wall_moments.py [KMAX] [NMAX]
"""
import sys
from fractions import Fraction
from itertools import combinations_with_replacement
from math import prod


def dim(lam, k):
    """s_lambda(1^k) by Weyl's dimension formula (lam has length k, weakly decreasing)."""
    num = prod(lam[i] - lam[j] + j - i for i in range(k) for j in range(i + 1, k))
    den = prod(j - i for i in range(k) for j in range(i + 1, k))
    assert num % den == 0
    return num // den


def rect_value(N, k):
    """s_{<N^k>}(1^{2k}) by hook-content: prod over the k x N rectangle of (2k + c)/h."""
    num, den = 1, 1
    for i in range(k):
        for j in range(N):
            num *= 2 * k + (j - i)
            den *= (N - j - 1) + (k - i - 1) + 1
    assert num % den == 0
    return num // den


def shapes(k, N):
    """Weakly decreasing k-tuples with entries in [0, N]."""
    for c in combinations_with_replacement(range(N + 1), k):
        yield tuple(sorted(c, reverse=True))


def run(k, N):
    w = {lam: dim(lam, k) ** 2 for lam in shapes(k, N)}
    total = sum(w.values())
    bw1 = total == rect_value(N, k)
    comp = lambda lam: tuple(N - lam[k - 1 - i] for i in range(k))
    bw2 = all(w[lam] == w[comp(lam)] for lam in w)
    top = [0] * (N + 1)
    for lam, x in w.items():
        top[lam[0]] += x
    p_wall = Fraction(top[N], total)
    mode_at_wall = all(top[N] > top[m] for m in range(N))
    mean_top = Fraction(sum(m * top[m] for m in range(N + 1)), total)
    return dict(k=k, N=N, bw1=bw1, bw2=bw2, mode_at_wall=mode_at_wall,
                N_p_wall=float(N * p_wall), mean_top_over_N=float(mean_top / N) if N else 0.0,
                argmax_top=max(range(N + 1), key=lambda m: top[m]))


def main():
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    print("k\tN\tBW1\tBW2\tmode@wall\targmax(l1)\tN*P(l1=N)\tE[l1]/N")
    for k in range(1, kmax + 1):
        for N in [1, 2, 3, 5, 10, 20, 30, 40]:
            if N > nmax:
                continue
            r = run(k, N)
            print(f"{k}\t{N}\t{r['bw1']}\t{r['bw2']}\t{r['mode_at_wall']}\t{r['argmax_top']}\t"
                  f"{r['N_p_wall']:.4f}\t{r['mean_top_over_N']:.4f}")


if __name__ == "__main__":
    main()
