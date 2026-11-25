# Loop 3: where the moment measure meets the wall (verdicts)

Verdicts on `20261125T0315Z-wall-moments-predictions.md`. All runs use `scripts/wall_moments.py` with exact arithmetic (about 1 s for `k ≤ 4`, `N ≤ 40`). Tags: **computed**, **inferred**.

| | Prediction | Verdict | Tag |
|---|---|---|---|
| BW1 | (0.95) `Σ_{λ⊆k×N} s_λ(1^k)² = s_{⟨N^k⟩}(1^{2k})` | **held**, every `k ≤ 4`, `N ≤ 40` | computed |
| BW2 | (0.85) `P` is symmetric under the box complement | **held**, every case | computed |
| BW3 | (0.7) for `k ≥ 2` the mode of `λ₁` is at the wall | **held**, every case; `k = 1` is uniform | computed |
| BW4 | (0.6) `N·P(λ₁ = N) → c_k > 0`, increasing in `k` | **held**, and `c_k = k²` fits | computed / inferred |
| BW5 | (0.5) `E[λ₁]/N →` a constant in `(1/2, 1)`, increasing in `k` | **held**: about 0.800, 0.90, 0.94 for `k = 2, 3, 4` | computed |

## Details

**BW4.** The values of `N·P(λ₁ = N)`:

| `k` | target `k²` | values (`N`) |
|---|---|---|
| 1 | 1 | `N/(N+1)` (exact) |
| 2 | 4 | 3.677 (40), 3.832 (80), 3.914 (160), 3.957 (320) |
| 3 | 9 | 7.639 (40), 8.050 (60), 8.501 (120) |
| 4 | 16 | 12.32 (40), 13.37 (60) |

- For `k = 2` the gap to `4` halves at each doubling of `N`, so the correction is `O(1/N)`.
- **Inferred reading:** `λ/N` tends to the `k`-point **Legendre ensemble** (Jacobi with `a = b = 0`, `β = 2`) on `[0, 1]`, because `dim(λ)²` is a squared Vandermonde.
- The wall `λ₁ = N` becomes its **hard edge** `x = 1`. The density of a point at the edge is the Christoffel–Darboux kernel there, `Σ_{j<k} (2j+1) P_j(1)² = k²`, which gives `P(λ₁ = N) ≈ k²/N`.

## What the loop says about the wall (inferred unless tagged)

1. **For moments, the mass sits at the wall** (computed: BW3, BW4). For `k ≥ 2` the top row touches `N` with probability `≈ k²/N`, more than any other value. So the large partitions that carry the moment `E|Λ|^{2k}` are pressed against the wall.
2. **The fluctuations there are hard-edge, not soft-edge.** The local statistics at `λ₁ = N` should be Bessel-kernel (hard edge, `a = 0`), not Airy/Tracy–Widom. Not checked: the next step is the gap distribution of `N − λ₁` at fixed `k`.
3. **The wall at `N` is the mirror of the trivial wall** (computed: BW2). Under the box complement, which is the functional equation `Λ(x) ↔ x^N Λ(1/x)` through `det^N`, the ∞ wall `λ₁ ≤ N` and the trivial wall `λ_k ≥ 0` are exchanged. The wall the boson hits at ∞ is the reflection of the floor of the partition.
4. **For BDTW (#19):** in this regime the Toeplitz-minor correction is concentrated at the hard edge. The next numerical target is the Bessel-kernel check of point 2, and then the same measure with `s_λ(1^k) s_μ(1^k)` for `λ ≠ μ`, i.e. the minor's off-diagonal entries.
