import RMTlib.Symmetric.DualCauchy
import RMTlib.Symmetric.WeightedCauchy

/-!
# The wall: where finitely many variables cut off sums over partitions

With finitely many variables, or at an integer rank `N`, sums over partitions stop early. The
**boson hits a wall** at the rows, the fermion at the columns, and `ω` (`λ ↦ λ′`) exchanges the two
walls. So at a fixed rank `ω` alone is broken; what survives is `ω` together with `N ↦ −N`
(`RMT.Symmetric.omegaHookContent`). At a finite place in content form (`finContent T`,
`T^{|λ|}`) there is no wall. See RMTlib#13.

* `schurV_eq_zero_of_length` (**the boson's wall**): `s_λ(a₀, …, a_{m−1}) = 0` when `λ` has more
  than `m` rows. It is proved **through the fermion's wall**: by dual Jacobi–Trudi
  (`schurV_eq_eDet_conjV`), `s_λ = det (e_{λ′_i − i + j})`, and `λ′₀ = ℓ(λ) > m` kills the first
  row because `e_k = 0` for `k > m` (`eV_eq_zero_of_lt`, Pauli). The boson's wall is the
  `ω`-image of the fermion's.
* The content form of the same pair of walls is `contentProd_nat_add_eq_zero_iff`
  (`∏ (N + c) = 0 ↔ ℓ(λ) > N`) and `contentProd_nat_sub_eq_zero_iff` (`∏ (N − c) = 0 ↔ λ₁ > N`).
-/

namespace RMT.Symmetric

open Finset

variable {R : Type*} [CommRing R] {K N : ℕ}

/-- **The boson's wall**: a Schur polynomial in `m` variables vanishes on a shape with more than
`m` rows (`μ_i > 0` for some `i ≥ m`). Proved through the fermion's wall `e_k = 0` for `k > m`,
via dual Jacobi–Trudi. `N` is any bound on the parts. -/
theorem schurV_eq_zero_of_length (a : ℕ → R) (m : ℕ) {mu : Fin K → ℕ} (hm : Antitone mu)
    (hN : ∀ j, mu j ≤ N) {i : Fin K} (hi : m ≤ (i : ℕ)) (hpos : 0 < mu i) :
    schurV a K m mu = 0 := by
  have hN0 : 0 < N := hpos.trans_le (hN i)
  rw [schurV_eq_eDet_conjV a m hm hN]
  have hlt : (i : ℕ) < conjV N mu ⟨0, hN0⟩ := (lt_conjV_iff hm i ⟨0, hN0⟩).mpr hpos
  exact eDet_eq_zero_of_lt a (antitone_conjV mu) (i := ⟨0, hN0⟩) (by omega)

/-- **The fermion's wall** (`e_k(a₀, …, a_{m−1}) = 0` for `k > m`), restated next to the boson's. -/
theorem eV_wall (a : ℕ → R) {m k : ℕ} (h : m < k) : eV a m k = 0 := eV_eq_zero_of_lt a h

end RMT.Symmetric
