#!/usr/bin/env python3
"""
Fomin growth-diagram local rules for RSK, dual RSK and super RSK,
in the conventions of RMTlib/RSK/Growth.lean.

Which super RSK: the insertion below (`insertion`) is N. Hage's super-RSK, arXiv:2206.15451,
Algorithm 'A:RSkalgo' (two-rowed array ordered by the recording letter; for an odd recording
letter the inserted letters are read in DECREASING order), built on the super row insertion of
La Scala-Nardozza-Senato (IJAC 16 (2006), arXiv:0904.0605, Def. 'row-insertion'). It is NOT
the Berele-Regev (k,l)-RSK, which (as described by Shimozono-White and by Muth) column-inserts
odd letters. See `literature_checks` and scripts/README.md for the comparison with Hage,
Bonetti-Senato-Venezia, Muth and Berele-Regev.

Conventions (as in Growth.lean)
-------------------------------
* A shape is a padded vector of fixed length N (list of N naturals), row 0 first.
* Grid: g(i,j) for 0<=i<=n, 0<=j<=m, g(0,j)=g(i,0)=0^N.  The square (i,j) has
      rho = g(i,j), mu = g(i+1,j), nu = g(i,j+1), entry x = A[i][j], lam = g(i+1,j+1).
  So the mu-edge (rho->mu) is a step in i (matrix ROW index), the nu-edge (rho->nu) a step in j
  (matrix COLUMN index).
* P = chain along the top edge g(n,0..m): the boxes of g(n,j+1)/g(n,j) get label j.
  Q = chain along the right edge g(0..n,m): the boxes of g(i+1,m)/g(i,m) get label i.
  This is Knuth RSK of the two-line array whose pairs (i,j) appear A[i][j] times in lex order
  (top = row index i = "time", bottom = column index j = inserted value), exactly
  RMT.Growth.twoLineOfRows / rskTwoLine, except labels here are 0-based (Lean: i+1, j+1).
* Parities: row i has parity rp[i], column j has parity cp[j] ('b' or 'f').
  Edges in the i direction are horizontal strips if rp[i]='b', vertical if 'f';
  edges in the j direction likewise with cp[j].

The local rule (carry form), t_0 = x, for k = 0..N-1:
    c_k   = min(t_k, cap_k)
    lam_k = max(mu_k, nu_k) + c_k
    t_{k+1} = t_k + min(mu_k, nu_k) - rho_k - c_k
  with cap_k depending on (rp[i], cp[j]):
    (b,b): inf                        (all of the carry is deposited: Fomin/Krattenthaler RSK rule)
    (b,f): mu_k + 1 - max(mu_k, nu_k) (dual RSK)
    (f,b): nu_k + 1 - max(mu_k, nu_k) (transposed dual RSK)
    (f,f): rho_k + 1 - max(mu_k, nu_k) (Hage's and Muth's super RSK; NOT the conjugated RSK rule)
  carry-out t_N must be 0 (room).
Backward (the 180-degree rotation; carry s from the bottom, s_N = 0), for k = N-1..0:
    c'_k   = min(s_{k+1}, cap'_k)
    rho_k  = min(mu_k, nu_k) - c'_k
    s_k    = s_{k+1} + lam_k - max(mu_k, nu_k) - c'_k
  with cap'_k: (b,b) inf; (b,f) min(mu_k,nu_k)+1-nu_k; (f,b) min(mu_k,nu_k)+1-mu_k;
  (f,f) min(mu_k,nu_k)+1-lam_k.   x = s_0.
All subtractions are written as truncated natural subtraction (as in Lean's Nat); the checks
below also verify that no truncation actually happens on valid squares.
"""
import itertools, collections, sys, time

INF = float('inf')
FAIL = []
LOG = []


def sub(a, b):  # Nat subtraction
    return a - b if a >= b else 0


def info(name, detail=""):
    LOG.append(("INFO", name, detail))
    print("INFO " + name + ("  [" + detail + "]" if detail else ""), flush=True)


FF_CONJ = False   # if True, (f,f) cells use the conjugated bosonic rule instead of the Hage/Muth rule


def report(name, ok, detail=""):
    LOG.append(("PASS" if ok else "FAIL", name, detail))
    print(("PASS " if ok else "FAIL ") + name + ("  [" + detail + "]" if detail else ""), flush=True)
    if not ok:
        FAIL.append(name)

# ---------------------------------------------------------------------------
# Local rules
# ---------------------------------------------------------------------------


def cap_fwd(pi, pj, r, m, v):
    """How much of the carry may be deposited in this row."""
    if (pi, pj) == ('b', 'b'):
        return INF
    if (pi, pj) == ('b', 'f'):
        return sub(m + 1, max(m, v))      # lam_k <= mu_k + 1
    if (pi, pj) == ('f', 'b'):
        return sub(v + 1, max(m, v))      # lam_k <= nu_k + 1
    return sub(r + 1, max(m, v))          # ff: lam_k <= rho_k + 1


def cap_bwd(pi, pj, m, v, l):
    """Backward cap (180-degree rotation of cap_fwd)."""
    if (pi, pj) == ('b', 'b'):
        return INF
    if (pi, pj) == ('b', 'f'):
        return sub(min(m, v) + 1, v)      # rho_k >= nu_k - 1
    if (pi, pj) == ('f', 'b'):
        return sub(min(m, v) + 1, m)      # rho_k >= mu_k - 1
    return sub(min(m, v) + 1, l)          # ff: rho_k >= lam_k - 1


def fwd_c(pi, pj, rho, mu, nu, x):
    """Unified forward rule; returns (lam, carry_out)."""
    if FF_CONJ and pi == pj == 'f':
        N = len(rho)
        W = max(mu[0], nu[0]) + x + 1
        lc, t = fwd_c('b', 'b', conj(rho, W), conj(mu, W), conj(nu, W), x)
        return conj(lc, N), t + max(0, max(lc) - N)
    t = x
    lam = []
    for r, m, v in zip(rho, mu, nu):
        c = min(t, cap_fwd(pi, pj, r, m, v))
        lam.append(max(m, v) + c)
        t = sub(t + min(m, v), r + c)
    return tuple(lam), t


def fwd(pi, pj, rho, mu, nu, x):
    return fwd_c(pi, pj, rho, mu, nu, x)[0]


def bwd(pi, pj, mu, nu, lam):
    """Unified backward rule; returns (rho, x)."""
    if FF_CONJ and pi == pj == 'f':
        N = len(mu)
        W = lam[0] + 1
        r, x = bwd('b', 'b', conj(mu, W), conj(nu, W), conj(lam, W))
        return conj(r, N), x
    s = 0
    rho = [0] * len(mu)
    for k in range(len(mu) - 1, -1, -1):
        m, v, l = mu[k], nu[k], lam[k]
        c = min(s, cap_bwd(pi, pj, m, v, l))
        rho[k] = sub(min(m, v), c)
        s = sub(s + l, max(m, v) + c)
    return tuple(rho), s


# --- the rules as stated in the literature / alternative forms, for cross-checks ---

def fwd_kratt(rho, mu, nu, x):
    """Krattenthaler (2006): lam_1 = max(mu_1,nu_1)+x, lam_{i+1} = max(mu_{i+1},nu_{i+1})+min(mu_i,nu_i)-rho_i
    (truncated at N rows)."""
    N = len(rho)
    return tuple([max(mu[0], nu[0]) + x] +
                 [max(mu[k + 1], nu[k + 1]) + min(mu[k], nu[k]) - rho[k] for k in range(N - 1)])


def bwd_bos_closed(mu, nu, lam):
    """rho_k = min(mu_k,nu_k) + max(mu_{k+1},nu_{k+1}) - lam_{k+1}  (lam_N := 0, mu_N=nu_N:=0),
    x = lam_0 - max(mu_0,nu_0)."""
    N = len(mu)
    g = lambda v, k: v[k] if k < N else 0
    rho = tuple(min(mu[k], nu[k]) + max(g(mu, k + 1), g(nu, k + 1)) - g(lam, k + 1) for k in range(N))
    return rho, lam[0] - max(mu[0], nu[0])


def fwd_dual_alt(rho, mu, nu, x):
    """(b,f) rule in the form: lam_k = max(mu_k + t_k, nu_k),
    t_{k+1} = [nu_k > rho_k and (t_k = 1 or mu_k > rho_k)], t_0 = x in {0,1}."""
    t = x
    lam = []
    for r, m, v in zip(rho, mu, nu):
        lam.append(max(m + t, v))
        t = 1 if (v > r and (t == 1 or m > r)) else 0
    return tuple(lam), t


def bwd_dual_alt(mu, nu, lam):
    """(b,f) backward in terms of the FORWARD carry t: going up from t_N = 0,
    rho_k = min(mu_k, nu_k - t_{k+1}), t_k = (lam_k - max(mu_k,nu_k)) + [nu_k > mu_k] * t_{k+1}, x = t_0."""
    t = 0
    rho = [0] * len(mu)
    for k in range(len(mu) - 1, -1, -1):
        m, v, l = mu[k], nu[k], lam[k]
        rho[k] = min(m, v - t)
        t = (l - max(m, v)) + (t if v > m else 0)
    return tuple(rho), t


def conj(p, W):
    """Conjugate of a padded shape, padded to length W."""
    return tuple(sum(1 for a in p if a > c) for c in range(W))


# ---------------------------------------------------------------------------
# Strip predicates (entrywise)
# ---------------------------------------------------------------------------

def is_part(p):
    return all(p[k] <= p[k - 1] for k in range(1, len(p)))


def hstrip(a, b):
    """b/a horizontal strip:  a_k <= b_k  and  b_k <= a_{k-1} (k>0)."""
    return all(a[k] <= b[k] and (k == 0 or b[k] <= a[k - 1]) for k in range(len(a)))


def vstrip(a, b):
    """b/a vertical strip:  a_k <= b_k <= a_k + 1  and  b_k <= b_{k-1} (k>0)."""
    return all(a[k] <= b[k] <= a[k] + 1 and (k == 0 or b[k] <= b[k - 1]) for k in range(len(a)))


def strip(p, a, b):
    return hstrip(a, b) if p == 'b' else vstrip(a, b)


def square_hyp(pi, pj, rho, mu, nu, x):
    """Hypotheses of the local theorem (without room)."""
    return (strip(pi, rho, mu) and strip(pj, rho, nu) and (pi == pj or x <= 1))


# ---------------------------------------------------------------------------
# Insertion (Knuth RSK, dual RSK, Hage's super RSK by LNS super row insertion)
# ---------------------------------------------------------------------------

def row_insert(P, x, par):
    """Super row insertion of x (La Scala-Nardozza-Senato 2006): the CURRENT letter x bumps the leftmost entry >= x if
    par[x] = 'f', the leftmost entry > x if par[x] = 'b'; the bumped letter goes to the next row."""
    P = [r[:] for r in P]
    k = 0
    while True:
        if k == len(P):
            P.append([x])
            return P, k
        r = P[k]
        for idx, y in enumerate(r):
            if (y >= x) if par[x] == 'f' else (y > x):
                r[idx], x = x, y
                break
        else:
            r.append(x)
            return P, k
        k += 1


def insertion(A, rp, cp):
    """Super RSK by row insertion. Row i of A is read as the word of column indices j,
    each j repeated A[i][j] times, increasing if rp[i]='b', decreasing if rp[i]='f';
    letter j is inserted with bumping rule of parity cp[j]. Returns P, Q and the shape table
    sh[i][j] = shape of (P after rows < i) restricted to letters < j."""
    n, m = len(A), len(A[0])
    P, Q = [], []
    hist = []
    for i in range(n + 1):
        hist.append([r[:] for r in P])
        if i == n:
            break
        js = [j for j in range(m) for _ in range(A[i][j])]
        if rp[i] == 'f':
            js.reverse()
        for v in js:
            P, k = row_insert(P, v, cp)
            if k == len(Q):
                Q.append([])
            Q[k].append(i)
    return P, Q, hist


def restricted_shape(P, j, N):
    s = [sum(1 for v in r if v < j) for r in P] + [0] * N
    return tuple(s[:N])

# ---------------------------------------------------------------------------
# Grids
# ---------------------------------------------------------------------------


def grow(A, rp, cp, N, rule=fwd):
    n, m = len(A), len(A[0])
    z = (0,) * N
    g = [[z] * (m + 1) for _ in range(n + 1)]
    for i in range(n):
        for j in range(m):
            g[i + 1][j + 1] = rule(rp[i], cp[j], g[i][j], g[i + 1][j], g[i][j + 1], A[i][j])
    return g


def back(top, right, rp, cp):
    """Backward grid from top edge top[j] = g(n,j) and right edge right[i] = g(i,m)."""
    n, m = len(right) - 1, len(top) - 1
    b = [[None] * (m + 1) for _ in range(n + 1)]
    A = [[0] * m for _ in range(n)]
    for j in range(m + 1):
        b[n][j] = top[j]
    for i in range(n + 1):
        b[i][m] = right[i]
    for i in range(n - 1, -1, -1):
        for j in range(m - 1, -1, -1):
            b[i][j], A[i][j] = bwd(rp[i], cp[j], b[i + 1][j], b[i][j + 1], b[i + 1][j + 1])
    return b, A


def chain_tab(chain):
    """Tableau of a chain of shapes: boxes of chain[k+1]/chain[k] get label k."""
    T = []
    for k in range(len(chain) - 1):
        a, b = chain[k], chain[k + 1]
        for r in range(len(a)):
            for _ in range(b[r] - a[r]):
                while len(T) <= r:
                    T.append([])
                T[r].append(k)
    return T


def super_ssyt(T, par):
    """Rows and columns weakly increasing; letters of parity b strictly increase down columns,
    letters of parity f strictly increase along rows."""
    for r, row in enumerate(T):
        for c, v in enumerate(row):
            if c > 0:
                u = row[c - 1]
                if u > v or (u == v and par[v] == 'f'):
                    return False
            if r > 0:
                if c >= len(T[r - 1]):
                    return False
                u = T[r - 1][c]
                if u > v or (u == v and par[v] == 'b'):
                    return False
    return all(len(T[r]) <= len(T[r - 1]) for r in range(1, len(T)))


def shape_of(T):
    return tuple(len(r) for r in T)

# ---------------------------------------------------------------------------
# Counting super tableaux by content (independent of growth): chains of strips
# ---------------------------------------------------------------------------


def hstrips(lam, a, N):
    """All mu with mu/lam a horizontal strip of size a, N rows."""
    out = []

    def rec(k, rem, cur):
        if k == N:
            if rem == 0:
                out.append(tuple(cur))
            return
        hi = rem if k == 0 else min(rem, lam[k - 1] - lam[k])
        for d in range(hi + 1):
            rec(k + 1, rem - d, cur + [lam[k] + d])
    rec(0, a, [])
    return out


def vstrips(lam, a, N):
    out = []
    for rows in itertools.combinations(range(N), a):
        mu = list(lam)
        for r in rows:
            mu[r] += 1
        if is_part(mu):
            out.append(tuple(mu))
    return out


_TC = {}


def tableau_counts(content, par, N):
    key = (content, par, N)
    if key not in _TC:
        _TC[key] = _tableau_counts(content, par, N)
    return _TC[key]


def _tableau_counts(content, par, N):
    st = {(0,) * N: 1}
    for a, p in zip(content, par):
        nst = collections.Counter()
        for lam, c in st.items():
            for mu in (hstrips(lam, a, N) if p == 'b' else vstrips(lam, a, N)):
                nst[mu] += c
        st = nst
    return st

# ---------------------------------------------------------------------------
# Global checks for one parity pattern over a family of matrices
# ---------------------------------------------------------------------------


def matrices(n, m, rp, cp, maxsum):
    cells = [(i, j) for i in range(n) for j in range(m)]
    like = [rp[i] == cp[j] for i, j in cells]

    def rec(k, rem, cur):
        if k == len(cells):
            yield cur
            return
        hi = rem if like[k] else min(rem, 1)
        for v in range(hi + 1):
            yield from rec(k + 1, rem - v, cur + [v])
    for vals in rec(0, maxsum, []):
        A = [[0] * m for _ in range(n)]
        for (i, j), v in zip(cells, vals):
            A[i][j] = v
        yield A


def global_checks(rp, cp, maxsum, stats, check_counts=True, expect_c_fail=False):
    n, m = len(rp), len(cp)
    # enough rows: a shape has at most (#b letters + total of f letters) rows on either side
    bound = lambda par: par.count('b') + (maxsum if 'f' in par else 0)
    N = 1 + min(maxsum, bound(rp), bound(cp))
    seen = {}
    margins = collections.Counter()
    for A in matrices(n, m, rp, cp, maxsum):
        stats['matrices'] += 1
        g = grow(A, rp, cp, N)
        # (a) every square satisfies the hypotheses, including carry-out 0
        for i in range(n):
            for j in range(m):
                rho, mu, nu = g[i][j], g[i + 1][j], g[i][j + 1]
                lam, tout = fwd_c(rp[i], cp[j], rho, mu, nu, A[i][j])
                if not (square_hyp(rp[i], cp[j], rho, mu, nu, A[i][j]) and tout == 0
                        and is_part(rho)):
                    stats['a_fail'] += 1
                    if stats['a_fail'] < 3:
                        print("  (a) bad square", rp, cp, A, i, j, rho, mu, nu)
                stats['squares'] += 1
        # (b) backward grid rebuilds grid and matrix
        top = [g[n][j] for j in range(m + 1)]
        right = [g[i][m] for i in range(n + 1)]
        b, B = back(top, right, rp, cp)
        if b != g or B != A:
            stats['b_fail'] += 1
            if stats['b_fail'] < 3:
                print("  (b) fail", rp, cp, A)
        # (c) grid == restricted insertion shapes; edges == (P, Q) of super insertion
        P, Q, hist = insertion(A, rp, cp)
        ok = all(g[i][j] == restricted_shape(hist[i], j, N) for i in range(n + 1) for j in range(m + 1))
        Pg, Qg = chain_tab(top), chain_tab(right)
        if not (ok and Pg == P and Qg == Q):
            stats['c_fail'] += 1
            if stats['c_fail'] < 3 and not expect_c_fail:
                print("  (c) fail", rp, cp, A, P, Q, Pg, Qg)
        # (d) edges are super SSYT of the same shape with the right contents
        alpha = tuple(sum(r) for r in A)
        beta = tuple(sum(A[i][j] for i in range(n)) for j in range(m))
        okd = (super_ssyt(Pg, cp) and super_ssyt(Qg, rp) and shape_of(Pg) == shape_of(Qg)
               and all(sum(r.count(j) for r in Pg) == beta[j] for j in range(m))
               and all(sum(r.count(i) for r in Qg) == alpha[i] for i in range(n)))
        key = (str(Pg), str(Qg))
        if key in seen:
            okd = False
        seen[key] = 1
        if not okd:
            stats['d_fail'] += 1
            if stats['d_fail'] < 3:
                print("  (d) fail", rp, cp, A, Pg, Qg)
        margins[(alpha, beta)] += 1
    if check_counts:
        # count check: #fillings with margins (alpha,beta) == sum_lam K^s_{lam,alpha} K^s_{lam,beta}
        # over ALL margins with total <= maxsum (including those with zero fillings)
        rowcap = [sum(maxsum if rp[i] == cp[j] else 1 for j in range(m)) for i in range(n)]
        colcap = [sum(maxsum if rp[i] == cp[j] else 1 for i in range(n)) for j in range(m)]
        for tot in range(maxsum + 1):
            for alpha in compositions(tot, n):
                if any(a > c for a, c in zip(alpha, rowcap)):
                    continue
                ka = tableau_counts(alpha, rp, N)
                for beta in compositions(tot, m):
                    if any(b > c for b, c in zip(beta, colcap)):
                        continue
                    kb = tableau_counts(beta, cp, N)
                    s = sum(c * kb.get(l, 0) for l, c in ka.items())
                    stats['count_cases'] += 1
                    if s != margins.get((alpha, beta), 0):
                        stats['count_fail'] += 1
                        if stats['count_fail'] < 3:
                            print("  count fail", rp, cp, alpha, beta, s, margins.get((alpha, beta), 0))


def compositions(tot, k):
    if k == 1:
        yield (tot,)
        return
    for a in range(tot + 1):
        for rest in compositions(tot - a, k - 1):
            yield (a,) + rest


def run_global(name, patterns, maxsum, expect_c_fail=False):
    stats = collections.Counter()
    t0 = time.time()
    for rp, cp in patterns:
        global_checks(rp, cp, maxsum, stats, expect_c_fail=expect_c_fail)
    d = "%d matrices, %d squares, %d margin pairs, %.1fs" % (
        stats['matrices'], stats['squares'], stats['count_cases'], time.time() - t0)
    report(name + " (a) every grid square satisfies hypotheses (strips, x-bound, carry-out 0)",
           stats['a_fail'] == 0, d)
    report(name + " (b) backward grid rebuilds forward grid and matrix", stats['b_fail'] == 0)
    if expect_c_fail:
        info(name + " (c) agreement with Hage super-RSK insertion: %s" % (stats['c_fail'] == 0),
             "%d matrices disagree" % stats['c_fail'])
    else:
        report(name + " (c) grid = restricted insertion shapes; top/right edges = (P,Q) of insertion",
               stats['c_fail'] == 0)
    report(name + " (d1) P,Q are super-SSYT of equal shape and right contents; (P,Q) injective",
           stats['d_fail'] == 0)
    report(name + " (d2) #fillings(alpha,beta) = sum_lam K_{lam,alpha} K_{lam,beta} (all margins)",
           stats['count_fail'] == 0)

# ---------------------------------------------------------------------------
# Local square enumeration (task 4)
# ---------------------------------------------------------------------------


def strips_over(p, rho, maxpart):
    N = len(rho)
    out = []
    if p == 'b':
        def rec(k, cur):
            if k == N:
                out.append(tuple(cur))
                return
            hi = maxpart if k == 0 else min(maxpart, rho[k - 1])
            for v in range(rho[k], hi + 1):
                rec(k + 1, cur + [v])
        rec(0, [])
    else:
        for d in itertools.product((0, 1), repeat=N):
            mu = tuple(r + e for r, e in zip(rho, d))
            if max(mu) <= maxpart and is_part(mu):
                out.append(mu)
    return out


def local_checks(Nmax=4, maxpart=4, maxx=4):
    for pi, pj in [('b', 'b'), ('b', 'f'), ('f', 'b'), ('f', 'f')]:
        st = collections.Counter()
        for N in range(1, Nmax + 1):
            for rho in itertools.product(range(maxpart + 1), repeat=N):
                part = is_part(rho)
                # mu, nu range over ALL vectors with parts <= maxpart that satisfy the strip
                # predicate (strip predicates are entrywise, so this is complete)
                mus = strips_over(pi, rho, maxpart) if (pi == 'f' or True) else None
                nus = strips_over(pj, rho, maxpart)
                for mu in mus:
                    for nu in nus:
                        for x in range(maxx + 1 if pi == pj else 2):
                            lam, tout = fwd_c(pi, pj, rho, mu, nu, x)
                            st['sq'] += 1
                            if not part:
                                st['nonpart'] += 1
                            size_ok = sum(mu) + sum(nu) - sum(rho) + x <= N
                            last0 = rho[-1] == mu[-1] == nu[-1] == 0
                            # simple sufficient room conditions per type
                            if (pi, pj) == ('b', 'b'):
                                simple = min(mu[-1], nu[-1]) == rho[-1]
                            elif (pi, pj) == ('b', 'f'):
                                simple = nu[-1] == rho[-1]
                            elif (pi, pj) == ('f', 'b'):
                                simple = mu[-1] == rho[-1]
                            else:
                                simple = size_ok
                            if simple and tout != 0:
                                st['simple_room_insufficient'] += 1
                            if size_ok and part and tout != 0:
                                st['size_room_insufficient'] += 1
                            if last0 and (pi, pj) != ('f', 'f') and tout != 0:
                                st['last0_insufficient'] += 1
                            inv = bwd(pi, pj, mu, nu, lam) == (rho, x)
                            # no truncation in the Nat subtractions (compare with exact integer run)
                            if tout == 0:
                                st['room'] += 1
                                if not inv:
                                    st['inv_fail'] += 1
                                    if not part:
                                        st['inv_fail_nonpart'] += 1
                                    if st['inv_fail'] < 3:
                                        print("   inv fail", pi, pj, rho, mu, nu, x, lam)
                                pres = strip(pj, mu, lam) and strip(pi, nu, lam)
                                if not pres:
                                    st['pres_fail'] += 1
                                    if part:
                                        st['pres_fail_part'] += 1
                                if not is_part(lam):
                                    st['lam_nonpart'] += 1
                            else:
                                st['noroom'] += 1
                                if inv:
                                    st['noroom_inv_ok'] += 1
        report("local %s%s: carry-out 0 + strips (+x<=1 if mixed) => bwd(fwd)=id" % (pi, pj),
               st['inv_fail'] == 0,
               "N<=%d parts<=%d x<=%d: %d squares, %d with room, %d with non-partition rho"
               % (Nmax, maxpart, maxx, st['sq'], st['room'], st['nonpart']))
        info("local %s%s: fwd preserves strips (lam/mu type of j, lam/nu type of i) for ARBITRARY rho vector: %s"
             % (pi, pj, "yes" if st['pres_fail'] == 0 else "NO"), "%d failures, all with rho non-partition: %s"
             % (st['pres_fail'], st['pres_fail_part'] == 0))
        report("local %s%s: fwd preserves strips when rho is a partition" % (pi, pj),
               st['pres_fail_part'] == 0)
        report("local %s%s: carry-out != 0 => bwd(fwd) != id (room is necessary)" % (pi, pj),
               st['noroom_inv_ok'] == 0, "%d squares without room" % st['noroom'])
        if (pi, pj) == ('f', 'f'):
            report("local ff: room condition |mu|+|nu|-|rho|+x <= N (rho partition) => carry-out 0",
                   st['simple_room_insufficient'] == 0 and st['size_room_insufficient'] == 0)
        else:
            nm = {('b', 'b'): "min(mu_{N-1},nu_{N-1}) = rho_{N-1}",
                  ('b', 'f'): "nu_{N-1} = rho_{N-1}",
                  ('f', 'b'): "mu_{N-1} = rho_{N-1}"}[(pi, pj)]
            report("local %s%s: %s => carry-out 0" % (pi, pj, nm), st['simple_room_insufficient'] == 0)
            report("local %s%s: rho,mu,nu all 0 in last row => carry-out 0" % (pi, pj),
                   st['last0_insufficient'] == 0)
            report("local %s%s: |mu|+|nu|-|rho|+x <= N (rho partition) => carry-out 0" % (pi, pj),
                   st['size_room_insufficient'] == 0)


def local_converse(Nmax=4, maxpart=4):
    """fwd(bwd) = id on the backward domain: lam/mu and lam/nu strips of the right type,
    lam a partition, backward carry-out s_N = 0 is automatic (s_N := 0) -- check that bwd
    returns a square satisfying the forward hypotheses with carry-out 0 and fwd gives lam back."""
    for pi, pj in [('b', 'b'), ('b', 'f'), ('f', 'b'), ('f', 'f')]:
        bad = 0
        cnt = 0
        for N in range(1, Nmax + 1):
            for lam in itertools.product(range(maxpart + 1), repeat=N):
                if not is_part(lam):
                    continue
                # mu with lam/mu of type pj, nu with lam/nu of type pi
                mus = [m for m in itertools.product(range(maxpart + 1), repeat=N)
                       if is_part(m) and strip(pj, m, lam)]
                nus = [v for v in itertools.product(range(maxpart + 1), repeat=N)
                       if is_part(v) and strip(pi, v, lam)]
                for mu in mus:
                    for nu in nus:
                        cnt += 1
                        rho, x = bwd(pi, pj, mu, nu, lam)
                        l2, t = fwd_c(pi, pj, rho, mu, nu, x)
                        if not (square_hyp(pi, pj, rho, mu, nu, x) and t == 0 and l2 == lam):
                            bad += 1
                            if bad < 3:
                                print("   converse fail", pi, pj, mu, nu, lam, rho, x, l2, t)
        report("local %s%s converse: lam,mu,nu partitions, lam/mu, lam/nu strips => bwd gives valid square, fwd(bwd)=id"
               % (pi, pj), bad == 0, "%d triples" % cnt)


def crosscheck_forms(Nmax=4, maxpart=4, maxx=4):
    bad_k = bad_kb = bad_d = bad_db = bad_c = 0
    cnt = 0
    for N in range(1, Nmax + 1):
        for rho in itertools.product(range(maxpart + 1), repeat=N):
            if not is_part(rho):
                continue
            hs = strips_over('b', rho, maxpart)
            vs = strips_over('f', rho, maxpart)
            for mu in hs:
                for nu in hs:
                    for x in range(maxx + 1):
                        lam, t = fwd_c('b', 'b', rho, mu, nu, x)
                        if t:
                            continue
                        cnt += 1
                        if fwd_kratt(rho, mu, nu, x) != lam:
                            bad_k += 1
                        if bwd_bos_closed(mu, nu, lam) != (rho, x):
                            bad_kb += 1
                for nu in vs:
                    for x in range(2):
                        lam, t = fwd_c('b', 'f', rho, mu, nu, x)
                        if t:
                            continue
                        if fwd_dual_alt(rho, mu, nu, x) != (lam, 0):
                            bad_d += 1
                        if bwd_dual_alt(mu, nu, lam) != (rho, x):
                            bad_db += 1
            for mu in vs:
                for nu in vs:
                    for x in range(maxx + 1):
                        lam, t = fwd_c('f', 'f', rho, mu, nu, x)
                        if t:
                            continue
                        W = maxpart + maxx + 2
                        lc = fwd_c('b', 'b', conj(rho, W), conj(mu, W), conj(nu, W), x)
                        if lc[1] != 0 or conj(lc[0], N) != lam:
                            bad_c += 1
    report("bb carry form == Krattenthaler's closed formula (forward)", bad_k == 0, "%d squares" % cnt)
    report("bb backward == closed form rho_k = min(mu_k,nu_k)+max(mu_{k+1},nu_{k+1})-lam_{k+1}, x = lam_0-max(mu_0,nu_0)",
           bad_kb == 0)
    report("bf carry form == alt form lam_k=max(mu_k+t_k,nu_k), t_{k+1}=[nu_k>rho_k & (t_k=1 | mu_k>rho_k)]",
           bad_d == 0)
    report("bf backward == alt form rho_k=min(mu_k,nu_k-t_{k+1}), t_k=lam_k-max(mu_k,nu_k)+[nu_k>mu_k]t_{k+1}",
           bad_db == 0)
    info("ff (Hage/Muth) rule == conjugate of bb rule on conjugate shapes? %s" % (bad_c == 0),
         "%d squares (with carry-out 0, N<=4) where they differ, e.g. rho=mu=nu=(1,0), x=1: Hage/Muth give (2,0), conj-bb (= BSV) gives (1,1)" % bad_c)


# ---------------------------------------------------------------------------
# Literature: other super-RSK insertions, and which local rules they force
# ---------------------------------------------------------------------------
# Letters are column indices j (parity cp[j]); recording letters are row indices i (parity rp[i]);
# the alphabets are ordered by index, with the parities interleaved arbitrarily (all of Hage, LNS,
# BSV, Muth allow this; Berele-Regev/Remmel take all even letters below all odd ones).
# Tableaux are dicts {(row, col): letter}.

def _rows_of(T):
    R = []
    for (r, c), v in sorted(T.items()):
        while len(R) <= r:
            R.append([])
        R[r].append(v)
    return R


def bsv_insertion(A, rp, cp):
    """Bonetti-Senato-Venezia super RSK, in the form of La Scala-Nardozza-Senato (arXiv:0904.0605),
    Def. 'S -> (T,U)': biletters ordered by recording letter i, then inserted letter j increasing;
    rp[i]='b': super ROW insertion of j (bump first entry > j if j even, >= j if j odd), i appended at
    the end of that row of U; rp[i]='f': super COLUMN insertion of j (bump first entry >= j if j even,
    > j if j odd), i appended at the bottom of that column of U."""
    n, m = len(A), len(A[0])
    T, U, hist = {}, {}, []
    for i in range(n):
        hist.append(dict(T))
        for x0 in [j for j in range(m) for _ in range(A[i][j])]:
            x, k = x0, 0
            while True:
                if rp[i] == 'b':
                    line = sorted(c for (r, c) in T if r == k)
                    cell = lambda c: (k, c)
                    hit = [c for c in line if ((x < T[(k, c)]) if cp[x] == 'b' else (x <= T[(k, c)]))]
                else:
                    line = sorted(r for (r, c) in T if c == k)
                    cell = lambda r: (r, k)
                    hit = [r for r in line if ((x <= T[(r, k)]) if cp[x] == 'b' else (x < T[(r, k)]))]
                if not hit:
                    T[cell(len(line))] = x
                    U[cell(len(line))] = i
                    break
                node = cell(hit[0])
                T[node], x = x, T[node]
                k += 1
    hist.append(dict(T))
    return _rows_of(T), _rows_of(U), hist


def muth_insert(T, eps, x, cp):
    """Muth's eps-insertion (arXiv:1711.00420, Sec. 3.1; Haiman's mixed insertion for eps = 0):
    a letter of parity p is inserted into a ROW if eps + p = 0 and into a COLUMN if eps + p = 1,
    bumping the first entry > x (eps = 0) or >= x (eps = 1); a bumped letter goes to the next
    row/column after the bumping node, according to its own parity. Returns the added node."""
    par = lambda a: 0 if cp[a] == 'b' else 1
    idx = 0
    while True:
        d = (eps + par(x)) % 2
        k = 0
        while True:
            node = (idx, k) if d == 0 else (k, idx)
            if node not in T or ((x < T[node]) if eps == 0 else (x <= T[node])):
                break
            k += 1
        if node not in T:
            T[node] = x
            return node
        T[node], x = x, T[node]
        idx = node[(eps + par(x)) % 2] + 1


def muth_insertion(A, rp, cp):
    """Muth's sRSK: biletters ordered by recording letter i, then inserted letter j in the order
    'odd letters decreasing, then even letters increasing'; eps = parity of i.
    For all recording letters even and Q standard (words), this is the Berele-Regev (k,l)-RSK as
    described by Shimozono-White (arXiv:math/0103206, Sec. 1-2) and by Muth (Remark 'insertinLitH'):
    even letters row-inserted, odd letters column-inserted."""
    n, m = len(A), len(A[0])
    T, U, hist = {}, {}, []
    order = [j for j in range(m) if cp[j] == 'f'][::-1] + [j for j in range(m) if cp[j] == 'b']
    for i in range(n):
        hist.append(dict(T))
        for j in order:
            for _ in range(A[i][j]):
                U[muth_insert(T, 0 if rp[i] == 'b' else 1, j, cp)] = i
    hist.append(dict(T))
    return _rows_of(T), _rows_of(U), hist


def hage_insertion(A, rp, cp):
    P, Q, hist = insertion(A, rp, cp)
    return P, Q, [{(r, c): v for r, row in enumerate(h) for c, v in enumerate(row)} for h in hist]


def _restricted(Td, j, N):
    s = [0] * N
    for (r, c), v in Td.items():
        if v < j:
            s[r] += 1
    return tuple(s)


def _mat(pairs, n, m):
    """pairs (inserted letter, recording letter) -> matrix A[recording][inserted]."""
    A = [[0] * m for _ in range(n)]
    for x, y in pairs:
        A[y][x] += 1
    return A


def conj_rule(t, rho, mu, nu, x):
    """The unified rule of the parity-flipped type, on conjugate shapes:
    lam = conj(fwd(flip t)(conj rho, conj mu, conj nu, x))."""
    flip = {'b': 'f', 'f': 'b'}
    N = len(rho)
    W = max(mu[0], nu[0]) + x + 2
    lam = fwd(flip[t[0]], flip[t[1]], conj(rho, W), conj(mu, W), conj(nu, W), x)
    return conj(lam, N)


def literature_checks():
    T = lambda rows: [list(r) for r in rows]
    # 1. Hage, arXiv:2206.15451, Example 'Ex:RSKExample1': Sigma = Sigma' = [6], even letters {1,3,4}.
    top = [1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6]
    bot = [2, 4, 2, 1, 4, 5, 6, 3, 5, 6, 4, 3, 1, 5, 4, 1]
    par = ''.join('b' if k in (1, 3, 4) else 'f' for k in range(1, 7))
    P, Q, _ = insertion(_mat([(b - 1, t - 1) for t, b in zip(top, bot)], 6, 6), par, par)
    expP = [[1, 1, 1, 4, 4], [2, 3, 3, 5], [2, 4, 4], [5, 6], [5, 6]]
    expQ = [[1, 2, 3, 3, 3], [2, 4, 4, 4], [2, 5, 6], [5, 6], [5, 6]]
    report("literature: script insertion reproduces Hage (arXiv:2206.15451) Example Ex:RSKExample1",
           ([[v + 1 for v in r] for r in P], [[v + 1 for v in r] for r in Q]) == (expP, expQ))
    # 2. Muth, arXiv:1711.00420, Example 'bigex': alphabet ^1<1<^2<2<^3<3 (-> 0..5, hats odd).
    par = 'fbfbfb'
    w = [(4, 0), (1, 2), (3, 3), (5, 3), (4, 4), (4, 4), (2, 5), (0, 5)]
    A = _mat(w, 6, 6)
    At = [list(r) for r in zip(*A)]
    muth = (T([[0, 2, 4, 5], [1, 3, 4], [4]]), T([[0, 3, 3, 4], [2, 5, 5], [4]]))
    bsv = (T([[0, 2, 5], [1, 3], [4], [4], [4]]), T([[0, 2, 3], [3, 5], [4], [4], [5]]))
    bsv_inv = (T([[0, 2, 3, 3], [4, 5, 5], [4]]), T([[0, 2, 4, 5], [1, 3, 4], [4]]))
    ok = (muth_insertion(A, par, par)[:2] == muth and muth_insertion(At, par, par)[:2] == muth[::-1]
          and bsv_insertion(A, par, par)[:2] == bsv and bsv_insertion(At, par, par)[:2] == bsv_inv)
    report("literature: Muth and BSV implementations reproduce Muth's Example bigex (w and w^inv)", ok)
    hP, hQ, _ = insertion(A, par, par)
    hPi, hQi, _ = insertion(At, par, par)
    info("literature: on Muth's Example bigex the script (Hage) gives P=%s Q=%s (symmetric: %s)"
         % (hP, hQ, (hPi, hQi) == (hQ, hP)), "shape differs from Muth's (4,3,1) and BSV's (3,2,1,1,1)")
    # 3. Shimozono-White, arXiv:math/0103206, Example in Sec. 1 (Berele-Regev (k,l)-RSK and its
    #    shuffles): v = u2 t1 t2 u1; A: t1<t2<u1<u2 gives P = t1 t2 u2 / u1; B: u1<u2<t1<t2 gives
    #    P = u1 u2 t2 / t1; Q = 1 2 3 / 4 in both.
    wA = _mat([(3, 0), (0, 1), (1, 2), (2, 3)], 4, 4)
    wB = _mat([(1, 0), (2, 1), (3, 2), (0, 3)], 4, 4)
    ok = (muth_insertion(wA, 'bbbb', 'bbff')[:2] == ([[0, 1, 3], [2]], [[0, 1, 2], [3]])
          and muth_insertion(wB, 'bbbb', 'ffbb')[:2] == ([[0, 1, 3], [2]], [[0, 1, 2], [3]]))
    report("literature: Muth eps=0 insertion reproduces Shimozono-White's Berele-Regev example", ok)
    info("literature: the script's insertion on that word, shuffle A, gives P=%s"
         % insertion(wA, 'bbbb', 'bbff')[0], "Berele-Regev: [[0, 1, 3], [2]]")
    # 4. Growth grids of each insertion: is lam a function of (type, rho, mu, nu, x), and which?
    words = sorted({''.join(p) for k in (1, 2, 3) for p in itertools.product('bf', repeat=k)},
                   key=lambda s: (len(s), s))
    pats = [(a, b) for a in words for b in words]
    maxsum = 4
    expect = {'Hage': {'bb': 'script', 'bf': 'script', 'fb': 'script', 'ff': 'script'},
              'Muth': {'bb': 'script', 'bf': 'conj', 'fb': 'conj', 'ff': 'script'},
              'BSV': {'bb': 'script', 'bf': 'script', 'fb': 'conj', 'ff': 'conj'}}
    t0 = time.time()
    for name, alg in [('Hage', hage_insertion), ('Muth', muth_insertion), ('BSV', bsv_insertion)]:
        table, conflicts = {}, 0
        bad = collections.Counter()
        sq = collections.Counter()
        for rp, cp in pats:
            n, m = len(rp), len(cp)
            N = 1 + maxsum
            for A in matrices(n, m, rp, cp, maxsum):
                hist = alg(A, rp, cp)[2]
                g = [[_restricted(hist[i], j, N) for j in range(m + 1)] for i in range(n + 1)]
                for i in range(n):
                    for j in range(m):
                        t = rp[i] + cp[j]
                        args = (g[i][j], g[i + 1][j], g[i][j + 1], A[i][j])
                        lam = g[i + 1][j + 1]
                        sq[t] += 1
                        if table.setdefault((t,) + args, lam) != lam:
                            conflicts += 1
                        if fwd(t[0], t[1], *args) != lam:
                            bad[(t, 'script')] += 1
                        if conj_rule(t, *args) != lam:
                            bad[(t, 'conj')] += 1
        report("literature: %s growth grid obeys a local rule (no conflicting squares)" % name, conflicts == 0,
               "words of length <=3 on both sides, entry sum <= %d, %d squares" % (maxsum, sum(sq.values())))
        for t in ('bb', 'bf', 'fb', 'ff'):
            e = expect[name][t]
            other = 'conj' if e == 'script' else 'script'
            report("literature: %s %s squares follow the %s rule%s" % (
                name, t, "script's" if e == 'script' else "conjugated parity-flipped (conj_rule)",
                "" if bad[(t, other)] else " (both rules agree here!)"),
                bad[(t, e)] == 0 and bad[(t, other)] > 0,
                "%d squares, %d differ from the other rule" % (sq[t], bad[(t, other)]))
    info("literature: local-rule identification took %.1fs" % (time.time() - t0))


def main():
    t0 = time.time()
    print("== Local cross-checks of equivalent forms ==")
    crosscheck_forms()
    print("== Task 4: local square hypotheses (all N<=4, parts<=4) ==")
    local_checks()
    local_converse()

    print("== Task 1: bosonic RSK (all parities b), all n x m <= 3x3, entry sum <= 7 ==")
    pats = [('b' * n, 'b' * m) for n in range(1, 4) for m in range(1, 4)]
    run_global("RSK", pats, 7)

    print("== Task 2: dual RSK (rows b, columns f), all 0/1 matrices up to 4x4 ==")
    pats = [('b' * n, 'f' * m) for n in range(1, 5) for m in range(1, 5)]
    run_global("dualRSK", pats, 16)
    print("== Task 2': dual RSK transposed (rows f, columns b), all 0/1 matrices up to 3x4/4x3 ==")
    pats = [('f' * n, 'b' * m) for n in range(1, 5) for m in range(1, 5) if n * m <= 12]
    run_global("dualRSK^T", pats, 12)
    print("== (f,f) alone (all-fermion Hage super RSK), all n x m <= 3x3, entry sum <= 6 ==")
    pats = [('f' * n, 'f' * m) for n in range(1, 4) for m in range(1, 4)]
    run_global("ffRSK", pats, 6)

    print("== Task 3: super RSK ==")
    words = set()
    for nb in (1, 2):
        for nf in (1, 2):
            for w in itertools.permutations('b' * nb + 'f' * nf):
                words.add(''.join(w))
    words = sorted(words, key=lambda w: (len(w), w))
    short = [w for w in words if len(w) <= 3]
    pats = [(a, b) for a in short for b in short]
    run_global("superRSK (all parity words with 1-2 b and 1-2 f of length <=3, both sides; sum <= 5)",
               pats, 5)
    long4 = [w for w in words if len(w) == 4]
    pats = [(a, b) for a in long4 for b in long4] + [(a, b) for a in long4 for b in short] + \
           [(a, b) for a in short for b in long4]
    run_global("superRSK (pairs involving a length-4 word with 2 b and 2 f; sum <= 3)", pats, 3)
    pats = [(a, b) for a in long4 for b in long4 if a in ('bbff', 'fbfb', 'ffbb') and b in ('bfbf', 'fbbf', 'bffb')]
    run_global("superRSK (9 pairs of length-4 words; sum <= 5)", pats, 5)

    print("== Literature: Hage, Muth, Bonetti-Senato-Venezia, Berele-Regev (via Shimozono-White) ==")
    literature_checks()

    print("== Variant: (f,f) cells with the CONJUGATED bosonic rule (fwd/bwd via conjugation) ==")
    global FF_CONJ
    FF_CONJ = True
    pats = [(a, b) for a in short for b in short] + [('ff', 'ff'), ('fff', 'ff')]
    run_global("superRSK-ffconj (length<=3 words, sum <= 4)", pats, 4, expect_c_fail=True)
    FF_CONJ = False

    print()
    print("Total time %.1fs; %d checks, %d failures" % (time.time() - t0, len(LOG), len(FAIL)))
    if FAIL:
        print("FAILED:", *FAIL, sep="\n  ")
        sys.exit(1)


if __name__ == '__main__':
    main()
