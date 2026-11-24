# Loop 1: RMTlib.Moments through the places frame (predictions)

Written before any code of this loop. The verdicts go in a later file in this folder.

**Loop.**
- **Target:** `RMTlib.Moments`, Dehaye's Theorem 3 for `U(N)`.
- **Frame:** places, our reading of Scholze, not his claim. Roles `archContent` (`c ↦ N + c`, content at `∞`) and `finContent` (`c ↦ T`, content at a finite place), with the twin rule `archContent ↦ finContent`.
- **Tool:** MeaningLib's in-repo report (`#frame_report`). For each theorem it gives a reading, a witnessed twin, a proposed twin, or `unknown`.
- **Metric:** the range of `M` for which Theorem 3 is proved for every `k` (today `M ≤ 1`).

**Design computation, not a prediction** (done by hand while choosing the binding; to be checked by Lean):
- `momentPoly k = ∏_{i,j<k} (X + i + j + 1) / ∏ (i + j + 1)`. Reflecting `i ↦ k − 1 − i` makes it a content product over the `k × k` square with content `c ↦ (X + k) + c`.
- The finite-place twin `(X + k)^{k²} / ∏ (i + j + 1)` drops the contents.
- At `k = 2` the weights are `1, 2, 2, 3`. Then `e₁ = 8` and `4·2 = 8` agree, while `e₂ = 23` and `C(4,2)·4 = 24` differ.
- In general, with `Σ c = 0` over the square, the two `e₂` differ by exactly `−Σ c²/2`.

**Predictions:**
- **PL1** (p = 0.75): run on `RMTlib.Moments` as it stands, the frame reads no theorem (nothing is stated with the roles). Its first output is therefore a restatement task, not a twin.
- **PL2** (p = 0.7): the restatement `momentPoly k = C (∏ w)⁻¹ * contentProd (archContent (X + k)) (square k)` is proved in at most 80 lines.
- **PL3** (p = 0.6): after the restatement, the report proposes exactly one well-typed twin per restated theorem, and finds no witness for it.
- **PL4** (p = 0.8): the twin of Theorem 3 holds for `M ≤ 1` and every `k`: the coefficients agree, because the contents of the square sum to `0`. It fails at `M = 2` for every `k ≥ 2`, the defect being the second content moment `Σ c²`. Within this loop, at least the `M ≤ 1` agreement and the `k = 2`, `M = 2` failure are proved.
- **PL5** (p = 0.85): the metric does not move in this loop; Theorem 3 stays proved for `M ≤ 1` only. What the loop can produce is the shape of the `M = 2` statement, not its proof.
- **PL6** (p = 0.5): the MeaningLib self-test and the RMTlib report each run in under 60 s.
