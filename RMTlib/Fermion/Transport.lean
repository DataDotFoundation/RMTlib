import RMTlib.Fermion.Rows
import RMTlib.Fermion.Conj
import RMTlib.Tableaux.MultisetHook.Maya

/-!
# The MultisetHook Maya diagram is the Fock layer's

`RMT.MultisetHook.Occ μ` (the occupied sites `site μ i = λ_i − i − 1` of a Young diagram, used by
the multiset hook length formula) is the Maya diagram `RMT.Fermion.ofRows 0 ν` of the Fock
layer, for the rows `ν i = λ_i` padded to any length `N` at least the number of rows
(`occ_ofRows_rowLen`, RMTlib#1 §2). Results on `Occ` can therefore be read through the Fock layer,
and conversely.

Under this identification transposition is particle–hole conjugation: `occ_ofRows_transpose`
combines `MultisetHook.occ_transpose` (`Occ μ′ z ↔ ¬ Occ μ (−1 − z)`) with `Maya.occ_conj`.
-/

namespace RMT.Fermion

open MultisetHook

/-- The rows of `μ`, padded with zeros to length `N`. -/
def rowsOf (μ : YoungDiagram) (N : ℕ) : Fin N → ℕ := fun i => μ.rowLen i

/-- **Transport**: for `N` at least the number of rows of `μ`, the occupied sites of `μ` in the
multiset hook sense are those of the Maya diagram of its rows in charge `0`. -/
theorem occ_ofRows_rowLen (μ : YoungDiagram) {N : ℕ} (hN : μ.colLen 0 ≤ N) (z : ℤ) :
    Occ μ z ↔ (ofRows 0 (rowsOf μ N)).occ z := by
  rw [occ_ofRows]
  simp only [rowSites, Finset.mem_image, Finset.mem_univ, true_and, add_zero, zero_sub]
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i < N
    · exact Or.inl ⟨⟨i, hi⟩, by simp [site, Symmetric.Corners.maya, rowsOf]⟩
    · right
      rw [site_of_ge μ (by omega)]
      omega
  · rintro (⟨i, rfl⟩ | h)
    · exact ⟨i, by simp [site, Symmetric.Corners.maya, rowsOf]⟩
    · refine ⟨(-z - 1).toNat, ?_⟩
      rw [site_of_ge μ (by omega)]
      omega

/-- **Transposition is particle–hole conjugation** on the Maya diagrams of rows. -/
theorem occ_ofRows_transpose (μ : YoungDiagram) {N K : ℕ} (hN : μ.colLen 0 ≤ N)
    (hK : μ.transpose.colLen 0 ≤ K) (z : ℤ) :
    (ofRows 0 (rowsOf μ.transpose K)).occ z ↔
      (Maya.conj (ofRows 0 (rowsOf μ N))).occ z := by
  rw [← occ_ofRows_rowLen _ hK, occ_transpose, Maya.occ_conj, occ_ofRows_rowLen _ hN]

/-- The Maya diagram of the rows of `μ′` is the conjugate of that of `μ`. -/
theorem ofRows_transpose (μ : YoungDiagram) {N K : ℕ} (hN : μ.colLen 0 ≤ N)
    (hK : μ.transpose.colLen 0 ≤ K) :
    ofRows 0 (rowsOf μ.transpose K) = Maya.conj (ofRows 0 (rowsOf μ N)) :=
  Maya.eq_of_occ (occ_ofRows_transpose μ hN hK)

end RMT.Fermion
