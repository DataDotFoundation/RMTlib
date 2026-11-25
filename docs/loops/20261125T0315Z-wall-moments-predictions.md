# Loop 3: where the moment measure meets the wall (predictions)

Written before any code of this loop. RMTlib#19 (B6). The verdicts go in a later file in this folder.

**Setup.** By dual Cauchy and orthogonality on `U(N)` (**lit**; Bump–Gamburd):

`E_{U(N)} |Λ_U(1)|^{2k} = Σ_{λ ⊆ k × N} s_λ(1^k)² = s_{⟨N^k⟩}(1^{2k})`.

So the moment is a sum over partitions **cut at the wall** `λ₁ ≤ N`. The rows are at most `k` automatically, from the `k` variables. Without the wall the sum diverges (`s_λ(1^k)` grows with `λ`), so the wall is what makes the moment finite.

The **moment measure** `P(λ) = s_λ(1^k)² / s_{⟨N^k⟩}(1^{2k})` on the `k × N` box is a probability measure. "Where do large partitions fluctuate" becomes "where does `P` put its mass, relative to the wall".

**Tool.** `scripts/wall_moments.py`: stdlib only, exact `Fraction` arithmetic, Weyl's dimension formula for `s_λ(1^k)`, hook–content for `s_{⟨N^k⟩}(1^{2k})`. Ranges: `k ≤ 4`, `N ≤ 40`.

**Predictions:**
- **BW1** (p = 0.95): `Σ_{λ ⊆ k×N} s_λ(1^k)² = s_{⟨N^k⟩}(1^{2k})` exactly, for every `k ≤ 4` and `N ≤ 40`. This is a sanity check of the setup.
- **BW2** (p = 0.85): `P` is symmetric under the **box complement** `λ_i ↦ N − λ_{k+1−i}`. Inferred mechanism: `s_λ(1^k) = s_{λ^c}(1^k)`, the `det^N` twist, which is the functional equation `Λ(x) ↔ x^N Λ(1/x)`. So **the wall at `N` is the mirror image of the trivial wall `λ_k ≥ 0`**.
- **BW3** (p = 0.7): for `k ≥ 2` the law of `λ₁` has its **mode at the wall**: `P(λ₁ = N) > P(λ₁ = m)` for every `m < N`. The Vandermonde-squared weight `dim(λ)²` pushes rows apart, against both walls. For `k = 1` the law is uniform (exact).
- **BW4** (p = 0.6): `N · P(λ₁ = N)` converges, as `N` grows, to a positive constant `c_k` that increases with `k`. The mass at the wall is `Θ(1/N)`, a hard-edge regime, not `o(1/N)`.
- **BW5** (p = 0.5): `E[λ₁]/N` converges to a constant in `(1/2, 1)`, increasing in `k`.
