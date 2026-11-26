#!/usr/bin/env python3
"""Search small RMT.Tower chains (StepOK at every step) for Keating–Snaith ratios (RMTlib#171).

Stdlib only: `python3 -I scripts/erdos_chain_search.py R CMAX DMAX NMAX` (e.g. 12 3 20 3).
Starts with X ⊂ [−R, −1] (all below the band), band half-width c ≤ CMAX, gaps ≤ DMAX,
rank N ≤ NMAX, and one crossing per step. It reports chains whose factor ratios
factorInf(i+1)/factorInf(i) (or their inverses) are C(2k+i,k)/C(k+i,k), and chains whose
total ratio is M_N(k), for k ≤ 7.
"""
import itertools, sys
from fractions import Fraction as F
from math import factorial, comb

def hset(L):
    L = sorted(L); num = 1; den = 1
    for x in L: num *= factorial(x)
    for i in range(len(L)):
        for j in range(i+1, len(L)): den *= L[j]-L[i]
    return F(num, den)

def cut(Y, c):
    return [y-c for y in Y if y >= c], [-y-c for y in Y if y <= -c]

def band_empty(Y, c): return all(y <= -c or y >= c for y in Y)

def step_ok(Y, c, d):
    if d < 0 or not band_empty(Y, c) or not band_empty([y+d for y in Y], c): return None
    cr = [y for y in Y if y <= -c and y+d >= c]
    return cr[0] if len(cr) == 1 else None

def target(k, i): return F(comb(2*k+i, k), comb(k+i, k))
def M(N, k):
    r = F(1)
    for j in range(N): r *= target(k, j)
    return r

R, CMAX, DMAX = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
NMAX = int(sys.argv[4])
hits = {}
for N in range(1, NMAX+1):
  for c in range(1, CMAX+1):
    for X in itertools.combinations(range(-R, 0), N):  # all below the band at level 0
      if not band_empty(X, c): continue
      # chain: N steps, each one crossing
      def dfs(Y, steps, fac):
          if len(steps) == N:
              return [(list(steps), list(fac))]
          out = []
          for d in range(0, DMAX+1):
              z = step_ok(Y, c, d)
              if z is None: continue
              Y2 = [y+d for y in Y]
              a, b = cut(Y2, c)
              out += dfs(Y2, steps+[d], fac+[hset(a)*hset(b)])
          return out
      a, b = cut(X, c)
      for steps, fac in dfs(list(X), [], [hset(a)*hset(b)]):
          ratios = [fac[i+1]/fac[i] for i in range(N)]
          for k in range(1, 8):
              tg = [target(k, i) for i in range(N)]
              for nm, rr in (("ratio", ratios), ("inverse", [1/r for r in ratios])):
                  if rr == tg:
                      hits.setdefault((N, k, nm), []).append((c, X, steps))
              tot = fac[-1]/fac[0]
              for nm, v in (("total", tot), ("total_inv", 1/tot)):
                  if v == M(N, k):
                      hits.setdefault((N, k, nm), []).append((c, X, steps))
for key in sorted(hits):
    print(key, len(hits[key]), hits[key][:3])
print("done")
