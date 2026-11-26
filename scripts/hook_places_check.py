#!/usr/bin/env python3
"""Hook products at every place (RMTlib#53): exact checks behind claim `omegaEveryPlace`.

Stdlib only; run with `python3 -I scripts/hook_places_check.py [--out FILE]`.

1. Defect (Frobenius-coordinate) form at infinity, on every partition with 1 <= |lam| <= 12:
     H(lam) = prod a_i! * prod b_i! * prod_{i,j} (a_i + b_j + 1) / prod_{i<j} (a_i - a_j)(b_i - b_j),
   with lam = (a_1, ..., a_d | b_1, ..., b_d).
2. The p-components are core statistics, for p in {2, 3, 5}, j <= 3, 1 <= |lam| <= 13:
     #{boxes : p^j divides h(box)} = (|lam| - |core_{p^j}(lam)|) / p^j.
3. omega at every place: core_q(lam') = core_q(lam)' for the same q = p^j and range.

Prints a JSON summary (also written to --out); exits 1 on any failure.
"""
import argparse
import json
from fractions import Fraction
from math import factorial


def partitions(n, largest=None):
    if largest is None:
        largest = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, largest), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def conjugate(lam):
    return tuple(sum(1 for r in lam if r > c) for c in range(lam[0])) if lam else ()


def hooks(lam):
    conj = conjugate(lam)
    return [lam[i] - j + conj[j] - i - 1 for i in range(len(lam)) for j in range(lam[i])]


def hook_product(lam):
    out = 1
    for h in hooks(lam):
        out *= h
    return out


def frobenius(lam):
    conj = conjugate(lam)
    d = sum(1 for i, r in enumerate(lam) if r > i)
    return [lam[i] - i - 1 for i in range(d)], [conj[i] - i - 1 for i in range(d)]


def defect_form(lam):
    a, b = frobenius(lam)
    num = Fraction(1)
    for x in a + b:
        num *= factorial(x)
    for x in a:
        for y in b:
            num *= x + y + 1
    for i in range(len(a)):
        for j in range(i + 1, len(a)):
            num /= (a[i] - a[j]) * (b[i] - b[j])
    return num


def core(lam, q):
    """The q-core, by removing q-rim hooks on the beta-set (abacus)."""
    n = len(lam)
    beta = set(lam[i] + n - 1 - i for i in range(n))
    moved = True
    while moved:
        moved = False
        for x in sorted(beta, reverse=True):
            if x - q >= 0 and x - q not in beta:
                beta.remove(x)
                beta.add(x - q)
                moved = True
                break
    parts = sorted(beta, reverse=True)
    return tuple(p for p in (parts[i] - (n - 1 - i) for i in range(n)) if p > 0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out")
    args = ap.parse_args()

    defect = {"checked": 0, "failures": []}
    for n in range(1, 13):
        for lam in partitions(n):
            defect["checked"] += 1
            if defect_form(lam) != hook_product(lam):
                defect["failures"].append(list(lam))

    cores = {"checked": 0, "failures": []}
    omega = {"checked": 0, "failures": []}
    qs = [p ** j for p in (2, 3, 5) for j in (1, 2, 3)]
    for n in range(1, 14):
        for lam in partitions(n):
            hs = hooks(lam)
            for q in qs:
                c = core(lam, q)
                cores["checked"] += 1
                if sum(1 for h in hs if h % q == 0) * q != n - sum(c):
                    cores["failures"].append([list(lam), q])
                omega["checked"] += 1
                if core(conjugate(lam), q) != conjugate(c):
                    omega["failures"].append([list(lam), q])

    summary = {
        "defect_form_infinity": defect,
        "hook_count_eq_core_defect": cores,
        "core_of_conjugate": omega,
        "ok": not (defect["failures"] or cores["failures"] or omega["failures"]),
    }
    text = json.dumps(summary, indent=2, sort_keys=True) + "\n"
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
    print(text, end="")
    raise SystemExit(0 if summary["ok"] else 1)


if __name__ == "__main__":
    main()
