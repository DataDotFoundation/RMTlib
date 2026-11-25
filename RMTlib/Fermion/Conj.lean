import RMTlib.Fermion.Maya

/-!
# Particle–hole conjugation of Maya diagrams

`conj ⟨P, H⟩ = ⟨H, P⟩` exchanges particles and holes. On sites it is the reflection
`z ↦ −1 − z` followed by complement: `z` is occupied in `conj M` exactly when `−1 − z` is empty in
`M` (`occ_conj`). This is `ω` on the fermionic Fock space, the Maya form of `λ ↦ λ′`
(`RMT.MultisetHook.occ_transpose`, recorded as `RMT.Symmetric.omegaOcc`), and it carries the
`N ↦ −N` twin of the boson/fermion programme: `charge (conj M) = −charge M` (RMTlib#1 §2).

* `conj_conj`: an involution.
* `occ_conj`: `occ (conj M) z ↔ ¬ occ M (−1 − z)`.
* `charge_conj`: `charge (conj M) = −charge M`.
* `energy_conj`: `energy (conj M) = energy M + charge M`. In the `ℤ`-convention used here a
  particle at `p ≥ 0` costs `p` and a hole at `−h − 1` costs `h + 1`, so the reflection
  `z ↦ −1 − z` shifts the energy by the charge. (In the `ℤ + ½` convention the reflection is
  `z ↦ −z` and the energy is invariant; RMTlib#1 §2 stated the invariant form.)
* `weight_conj`: `weight φ (conj M) = (weight (φ ∘ (−1 − ·)) M)⁻¹` for a one-body potential.
-/

namespace RMT.Fermion.Maya

open Finset

/-- **Particle–hole conjugation**: particles become holes and holes become particles. -/
def conj (M : Maya) : Maya := ⟨M.H, M.P⟩

@[simp] theorem conj_P (M : Maya) : (conj M).P = M.H := rfl

@[simp] theorem conj_H (M : Maya) : (conj M).H = M.P := rfl

/-- Conjugation is an involution. -/
@[simp] theorem conj_conj (M : Maya) : conj (conj M) = M := rfl

theorem conj_involutive : Function.Involutive conj := conj_conj

/-- **Conjugation on sites**: `z` is occupied in `conj M` iff `−1 − z` is empty in `M`. -/
theorem occ_conj (M : Maya) (z : ℤ) : (conj M).occ z ↔ ¬ M.occ (-1 - z) := by
  rcases le_or_gt 0 z with hz | hz
  · rw [occ_of_nonneg _ hz, occ_of_neg _ (by omega), not_not, conj_P]
    have : (-(-1 - z) - 1).toNat = z.toNat := by omega
    rw [this]
  · rw [occ_of_neg _ hz, occ_of_nonneg _ (by omega), conj_H]
    have : (-1 - z).toNat = (-z - 1).toNat := by omega
    rw [this]

/-- **`N ↦ −N`**: conjugation negates the charge. -/
theorem charge_conj (M : Maya) : (conj M).charge = -M.charge := by
  simp [charge]

/-- Conjugation shifts the energy by the charge (`ℤ`-convention). -/
theorem energy_conj (M : Maya) : ((conj M).energy : ℤ) = M.energy + M.charge := by
  simp only [energy, charge, conj_P, conj_H, sum_add_distrib, sum_const, smul_eq_mul, mul_one]
  push_cast
  ring

/-- **One-body weights**: conjugation inverts the weight and reflects the potential. -/
theorem weight_conj {G : Type*} [CommGroup G] (φ : ℤ → G) (M : Maya) :
    weight φ (conj M) = (weight (fun b => φ (-1 - b)) M)⁻¹ := by
  simp only [weight, conj_P, conj_H, holeSite, inv_div]
  congr 1
  · refine prod_congr rfl fun h _ => ?_
    congr 1
    ring
  · refine prod_congr rfl fun p _ => ?_
    congr 1
    ring

end RMT.Fermion.Maya
