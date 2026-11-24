#!/usr/bin/env python3
"""Numerical checks for the multiset hook length formula (Dehaye–Han, arXiv:1104.5435, Theorem 1).

Companion to the Lean files `RMTlib/Tableaux/MultisetHook*.lean`, which hold the
statements and proofs; the examples live here, not in Lean. Conventions follow the Lean files:
the Maya site of row i (from 0) is λ_i − i − 1, V(λ) = {x ∈ M : x + t ∉ M}, the integer coding
a is V sorted decreasingly, and the paper's coding is v = a + (t + 1)/2.

Checks:
  * the paper's worked examples (Tables 1 and 2) and the hook multiset of (6,3,3,2);
  * the printed condition (i) fails for the empty 2-core;
  * for 1 ≤ t ≤ 6 and every t-core of size ≤ 14: the coding conditions (with (i) corrected),
    Eq. (1), the paper's Eq. (2) in multiset form, the folded β-free form (N5), the charge
    (N6), conjugation (N7), and the degree-1 character;
  * the residue identity (N4) for random complete residue systems of every charge;
  * bijectivity by counting: #t-cores of size n = #V_t-codings of norm n (t ≤ 4, n ≤ 12);
  * Corollary 4 (the sign [t ≡ 3 mod 4]) and Theorem 17 (ψ_t, Eqs. (40), (41)) on the same cores;
  * every q-series statement of PaperStatements.lean (Theorems 2, 5, 11 specialised, 15, 16,
    Lemmas 13, 14, Corollaries 6–10), exactly over ℚ with generic parameters, for n ≤ 8.

Exit code 0 when every check passes, 1 otherwise.
"""

import itertools
import random
import sys
from collections import Counter
from fractions import Fraction

FAILURES = []


def check(cond, msg):
    if not cond:
        FAILURES.append(msg)


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def conjugate(lam):
    return tuple(sum(1 for r in lam if r > j) for j in range(lam[0])) if lam else ()


def hooks(lam):
    conj = conjugate(lam)
    return [lam[i] - j + conj[j] - i - 1 for i in range(len(lam)) for j in range(lam[i])]


def is_core(lam, t):
    return all(h % t for h in hooks(lam))


def occ(lam, x):
    """x is a Maya site λ_i − i − 1 (rows padded with zeros)."""
    ell = len(lam)
    if x < -ell:
        return True  # the sites −i − 1 for i ≥ ℓ
    return any(lam[i] - i - 1 == x for i in range(ell))


def vset(lam, t):
    lo = -len(lam) - t
    hi = (lam[0] if lam else 0)
    return sorted((x for x in range(lo, hi + 1) if occ(lam, x) and not occ(lam, x + t)), reverse=True)


def vcoding(lam, t):
    return [Fraction(a) + Fraction(t + 1, 2) for a in vset(lam, t)]


def beta(lam, t, i):
    return hooks(lam).count(t - i)


def pair_diffs(a):
    return [a[i] - a[j] for i in range(len(a)) for j in range(i + 1, len(a))]


def paper_eq2(lam, t):
    """The paper's Eq. (2) as a multiset identity (all terms positive)."""
    H = hooks(lam)
    lhs = Counter([h - t for h in H] + [h + t for h in H])
    for i in range(1, t):
        lhs[i] += beta(lam, t, i) + t - i
    rhs = Counter(H) + Counter(H) + Counter(pair_diffs(vset(lam, t)))
    for i in range(1, t):
        rhs[-i] += beta(lam, t, i)
    return +lhs == +rhs


def lap(D, t):
    """Folded Laplacian: [h] ↦ [|h − t|] + [h + t] − 2[h], extended linearly."""
    out = Counter()
    for h, n in D.items():
        out[abs(h - t)] += n
        out[h + t] += n
        out[h] -= 2 * n
    return out


def clean(D):
    return {k: v for k, v in D.items() if v}


def folded(lam, t):
    """N5: lap(H) + Σ (t − i)[i] = Σ_{b<a ∈ V} [a − b]."""
    lhs = lap(Counter(hooks(lam)), t)
    for i in range(1, t):
        lhs[i] += t - i
    rhs = Counter(pair_diffs(vset(lam, t)))
    return clean(lhs) == clean(rhs)


def pair_hooks(d, t):
    """Σ_{n=1}^{⌊d/t⌋} ray(d mod t, n)."""
    D = Counter()
    q, r = divmod(d, t)
    for n in range(1, max(q, 0) + 1):
        for j in range(n):
            D[r + t * j] += 1
    return D


def residue_identity(V, t):
    """N4 for a complete residue system V."""
    lhs = Counter()
    for a in V:
        for b in V:
            for k, v in lap(pair_hooks(a - b, t), t).items():
                lhs[k] += v
    for i in range(1, t):
        lhs[i] += t - i
    rhs = Counter(a - b for a in V for b in V if b < a)
    return clean(lhs) == clean(rhs)


def psi(lam, t):
    """ψ_t(λ): μ_i = a_i − a_{t−1} − (t − 1 − i), rows from 0."""
    a = vset(lam, t)
    return [a[i] - a[-1] - (t - 1 - i) for i in range(t)]


def u_coding(lam, t):
    """Class-sorted coding: u_i ≡ i + ⌊t/2⌋ (mod t)."""
    a = vset(lam, t)
    return [next(x for x in a if x % t == (i + t // 2) % t) for i in range(t)]


def eq41_div(lam, t):
    """Eq. (41) as a multiset identity: {h−t}+{h+t}+Σβ_i[i]+{h(μ)} = 2{h}+Σβ_i[−i]+{t+c(μ)}."""
    H = hooks(lam)
    mu = tuple(x for x in psi(lam, t) if x > 0)
    lhs = Counter([h - t for h in H] + [h + t for h in H] + hooks(mu))
    rhs = Counter(H) + Counter(H)
    rhs += Counter(t + j - i for i in range(len(mu)) for j in range(mu[i]))
    for i in range(1, t):
        lhs[i] += beta(lam, t, i)
        rhs[-i] += beta(lam, t, i)
    return +lhs == +rhs


# --- q-series statements (PaperStatements.lean), exact over ℚ with generic parameters ---------

def divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def exp_coeffs(a, N):
    """IsExp: f₀ = 1, (n+1) f_{n+1} = Σ_{j≤n} (j+1) a_{j+1} f_{n−j}."""
    f = [Fraction(1)]
    for n in range(N):
        f.append(sum((j + 1) * a(j + 1) * f[n - j] for j in range(n + 1)) / (n + 1))
    return f


def log_prod(c, e, n):
    return -e * sum(Fraction(c) ** k / k for k in divisors(n))


def tau(w, k):
    return Fraction(w) ** k - Fraction(w) ** (-k)


def prod(xs):
    out = Fraction(1)
    for x in xs:
        out *= x
    return out


def check_statements(N=8):
    w, v, x, a = Fraction(3, 2), Fraction(5, 7), Fraction(2, 3), Fraction(2, 3)
    parts = {n: list(partitions(n)) for n in range(N + 1)}
    def hooksum(n, r, g):
        return sum(prod(g(h) for h in hooks(l) if h % r == 0) for l in parts[n])
    # Corollary 6, 7
    e = exp_coeffs(lambda n: log_prod(1, -1, n), N)
    check(all(len(parts[n]) == e[n] for n in range(N + 1)), "Corollary 6")
    beta = Fraction(11, 3)
    e = exp_coeffs(lambda n: log_prod(1, beta - 1, n), N)
    check(all(hooksum(n, 1, lambda h: 1 - beta / h ** 2) == e[n] for n in range(N + 1)), "Corollary 7")
    # Theorem 5, Theorem 2
    t5 = lambda n: sum((1 - (v ** k - v ** -k) ** 2 / tau(w, k) ** 2) / k for k in divisors(n))
    sw = lambda h: 1 - (v - 1 / v) ** 2 / tau(w, h) ** 2
    e = exp_coeffs(t5, N)
    check(all(hooksum(n, 1, sw) == e[n] for n in range(N + 1)), "Theorem 5")
    for r in (2, 3):
        t2 = lambda n: sum(Fraction(1, k) for k in divisors(n)) - (
            sum(Fraction(r, k) * (v ** k - v ** -k) ** 2 / tau(w, r * k) ** 2
                for k in divisors(n // r)) if n % r == 0 else 0)
        e = exp_coeffs(t2, N)
        check(all(hooksum(n, r, sw) == e[n] for n in range(N + 1)), f"Theorem 2 (r={r})")
    # Lemma 13, Lemma 14, Macdonald (t odd)
    for t in (1, 3, 5):
        coresum = lambda n, g: sum(prod(g(h) for h in hooks(l)) for l in parts[n] if is_core(l, t))
        wt = lambda h: 1 - tau(w, t) ** 2 / tau(w, h) ** 2
        l13 = lambda n: log_prod(1, t - 1, n) + sum(
            log_prod(w ** (2 * (t - i)), i, n) + log_prod(w ** (-2 * (t - i)), i, n) for i in range(1, t))
        e13 = exp_coeffs(l13, N)
        check(all(coresum(n, wt) == e13[n] for n in range(N + 1)), f"Lemma 13 (t={t})")
        e14 = exp_coeffs(lambda n: sum((1 - (w ** (t * k) - w ** (-t * k)) ** 2 / tau(w, k) ** 2) / k
                                       for k in divisors(n)), N)
        check(e13 == e14, f"Lemma 14 (t={t})")
        P = prod(tau(w, k) ** (t - k) for k in range(1, t))
        for n in range(N + 1):
            U = sum(prod(tau(w, u[i] - u[j]) for i in range(t) for j in range(i + 1, t))
                    for l in parts[n] if is_core(l, t) for u in [u_coding(l, t)])
            check(U == (-1) ** ((t - 1) // 2) * P * e13[n], f"Macdonald (t={t}, n={n})")
    # Theorem 15 (Han–Ji)
    rho = lambda h: 1 + Fraction(h, 7)
    for r in (2, 3):
        c = exp_coeffs(lambda n: sum(Fraction(1, k) for k in divisors(n)) - (
            sum(Fraction(r, k) for k in divisors(n // r)) if n % r == 0 else 0), N)
        f = [sum(prod(rho(r * h) for h in hooks(l)) for l in parts[m]) for m in range(N + 1)]
        for n in range(N + 1):
            lhs = sum(x ** sum(1 for h in hooks(l) if h % r == 0) *
                      prod(rho(h) for h in hooks(l) if h % r == 0) for l in parts[n])
            rhs = 0
            for a0 in range(n + 1):
                if (n - a0) % r:
                    continue
                b = (n - a0) // r
                conv = sum(prod(f[bi] for bi in bs) for bs in itertools.product(range(b + 1), repeat=r)
                           if sum(bs) == b)
                rhs += c[a0] * x ** b * conv
            check(lhs == rhs, f"Theorem 15 (r={r}, n={n})")
    # Corollaries 8, 9, 10
    e = exp_coeffs(lambda n: Fraction(-1) / (n * tau(w, n) ** 2), N)
    check(all(hooksum(n, 1, lambda h: -1 / tau(w, h) ** 2) == e[n] for n in range(N + 1)), "Corollary 8")
    cot2 = lambda k: -(w ** k + w ** -k) ** 2 / tau(w, k) ** 2
    e = exp_coeffs(lambda n: sum((-1) ** (n // k - 1) * cot2(k) / k if k % 2 else Fraction(1, k)
                                 for k in divisors(n)), N)
    check(all(hooksum(n, 1, cot2) == e[n] for n in range(N + 1)), "Corollary 9")
    e = exp_coeffs(lambda n: log_prod(-a, 1, n) + log_prod(-1 / a, 1, n) + log_prod(1, 1, n), N)
    check(all((1 + 1 / a) * e[n] == sum(a ** m for m in range(-n - 1, n + 1) if m * (m + 1) == 2 * n)
              for n in range(N + 1)), "Corollary 10")
    # Theorem 16 (hook-content), small shapes
    p = Fraction(3, 5)
    for lam in [(1,), (2,), (1, 1), (2, 1), (3, 1), (2, 2), (3, 2, 1)]:
        for nn in range(1, 4):
            cells = [(i, j) for i in range(len(lam)) for j in range(lam[i])]
            tot = 0
            for vals in itertools.product(range(nn), repeat=len(cells)):
                T = dict(zip(cells, vals))
                if all(T[(i, j)] <= T[(i, j + 1)] for (i, j) in cells if (i, j + 1) in T) and \
                   all(T[(i, j)] < T[(i + 1, j)] for (i, j) in cells if (i + 1, j) in T):
                    tot += p ** sum(vals)
            conj = conjugate(lam)
            rhs = p ** sum(i for (i, j) in cells) * prod(
                (1 - p ** (nn + j - i)) / (1 - p ** (lam[i] - j + conj[j] - i - 1)) for (i, j) in cells)
            check(tot == rhs, f"Theorem 16 (λ={lam}, n={nn})")


def main():
    # --- the paper's examples -------------------------------------------------------------
    lam = (8, 4, 3, 2, 2, 1)
    check(is_core(lam, 5), "Table 1: (8,4,3,2,2,1) is a 5-core")
    check(vcoding(lam, 5) == [10, 3, 1, -6, -8], "Table 1: V(λ)")
    check(vcoding(conjugate(lam), 5) == [8, 6, -1, -3, -10], "Table 1: V(λᵗ)")
    check(sorted(hooks((6, 3, 3, 2))) == sorted([2, 1, 4, 3, 1, 5, 4, 2, 9, 8, 6, 3, 2, 1]),
          "hooks of (6,3,3,2)")
    lam = (8, 5, 4, 1, 1, 1)
    check(is_core(lam, 6), "Table 2: (8,5,4,1,1,1) is a 6-core")
    check(vcoding(lam, 6) == [Fraction(x, 2) for x in (21, 13, -1, -7, -9, -17)], "Table 2: V(λ)")

    # --- condition (i) as printed fails for the empty 2-core ------------------------------
    v = vcoding((), 2)
    check(v == [Fraction(1, 2), Fraction(-1, 2)], "empty 2-core: V = (½, −½)")
    check((v[0] - 0) - (v[1] - 1) == 2, "printed (i): v₀ − 0 ≡ v₁ − 1 (mod 2)")

    # --- exhaustive: every t-core of size ≤ 14, 1 ≤ t ≤ 6 ---------------------------------
    ncores = 0
    for t in range(1, 7):
        for n in range(15):
            for lam in partitions(n):
                if not is_core(lam, t):
                    continue
                ncores += 1
                tag = f"t={t}, λ={lam}"
                v = vcoding(lam, t)
                a = vset(lam, t)
                check(len(a) == t, f"{tag}: |V| = t")
                check(all(v[i] > v[i + 1] for i in range(t - 1)), f"{tag}: strictly decreasing")
                check(sum(v) == 0, f"{tag}: Σ v = 0")
                check(len({x % t for x in a}) == t, f"{tag}: incongruent mod t")
                check(2 * sum(a) == -t * (t + 1), f"{tag}: charge (N6)")
                check(Fraction(n) == sum(x * x for x in v) / (2 * t) - Fraction(t * t - 1, 24),
                      f"{tag}: Eq. (1)")
                check(paper_eq2(lam, t), f"{tag}: paper's Eq. (2)")
                check(folded(lam, t), f"{tag}: folded Eq. (2) (N5)")
                check(vcoding(conjugate(lam), t) == [-x for x in reversed(v)], f"{tag}: Eq. (6)")
                check(sum(pair_diffs(a)) == 2 * sum(beta(lam, t, i) * i for i in range(1, t))
                      + sum((t - i) * i for i in range(1, t)), f"{tag}: degree-1 character")
                # Corollary 4: the sign is [t ≡ 3 mod 4]
                u = u_coding(lam, t)
                inv = sum(1 for i in range(t) for j in range(i + 1, t) if u[i] < u[j])
                nlt = sum(1 for h in hooks(lam) if h < t)
                check((nlt + inv) % 2 == (1 if t % 4 == 3 else 0), f"{tag}: Corollary 4 sign")
                # Theorem 17: ψ_t(λ), Eqs. (40) and (41)
                mu = psi(lam, t)
                M = sum(mu)
                check(all(x >= 0 for x in mu) and mu[-1] == 0
                      and all(mu[i] >= mu[i + 1] for i in range(t - 1))
                      and len({(mu[i] - i) % t for i in range(t)}) == t, f"{tag}: ψ_t(λ) in target")
                check(Fraction(n) == Fraction(-M * (M + t + t * t), 2 * t * t)
                      + sum(Fraction(mu[i] ** 2 + 2 * (t - i) * mu[i], 2 * t) for i in range(t)),
                      f"{tag}: Eq. (40)")
                check(eq41_div(lam, t), f"{tag}: Eq. (41)")

    # --- N4 for complete residue systems of every charge ----------------------------------
    rng = random.Random(0)
    for t in range(1, 8):
        for _ in range(50):
            V = [r + t * rng.randint(-6, 6) for r in range(t)]
            check(residue_identity(V, t), f"residue identity t={t}, V={V}")

    check_statements()

    # --- bijectivity by counting ----------------------------------------------------------
    for t in range(1, 5):
        codings = Counter()
        for m in itertools.product(range(-6, 7), repeat=t):
            a = [r + t * mr for r, mr in enumerate(m)]
            if 2 * sum(a) != -t * (t + 1):
                continue
            norm = sum((Fraction(x) + Fraction(t + 1, 2)) ** 2 for x in a) / (2 * t) \
                - Fraction(t * t - 1, 24)
            if norm.denominator == 1 and norm <= 12:
                codings[int(norm)] += 1
        for n in range(13):
            cores = sum(1 for lam in partitions(n) if is_core(lam, t))
            check(cores == codings[n], f"bijection count t={t}, n={n}: {cores} vs {codings[n]}")

    if FAILURES:
        print(f"{len(FAILURES)} failures:")
        for f in FAILURES[:30]:
            print("  " + f)
        return 1
    print(f"all checks passed ({ncores} (t, core) pairs)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
