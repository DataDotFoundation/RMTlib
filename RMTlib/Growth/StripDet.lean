import RMTlib.Growth.PiecewiseLinear
import RMTlib.Symmetric.InterlacingDet

/-!
# Horizontal strips as an interlacing determinant on Maya sites (RMTlib#163, target 3)

On `k` rows, a horizontal strip `κ ⊆ ν` (`HStrip`, RMTlib#146) is a set of non-overtaking particle
hops on the Maya line: particle `b` moves right from `site κ b` to `site ν b`, and particle `b + 1`
lands strictly left of where particle `b` started. This file proves that the indicator of such a
hop configuration is a determinant:

`det [site κ c < site ν b + 1]_{b, c < k} = [κ_b ≤ ν_b ∀ b] · [ν_{b+1} ≤ κ_b ∀ b + 1 < k]`.

It is `det_interlacing_indicator` (RMTlib#161/#162) with `x_b = site ν b + 1 = ν_b − b` and
`y_c = site κ c = κ_c − c − 1` in `ℤ`. Each entry `[y_c < x_b]` is a one-particle question ("may
particle `c` of `κ` reach site `b` of `ν`?"), and the determinant is the fermionic
(Lindström–Gessel–Viennot-free) answer for all `k` particles at once: the per-letter factor of
the condensed edition's pieriCone (RMTlib#163).
-/

open Finset Matrix

namespace RMT.Growth

variable {R : Type*} [CommRing R] {k : ℕ}

/-- The shifted sites of an antitone row-length function are antitone. -/
theorem antitone_site {f : ℕ → ℕ} (hf : Antitone f) : Antitone (site f) := fun a b hab => by
  unfold site; have := hf hab; omega

open Classical in
/-- **Horizontal strips on `k` rows are an interlacing determinant on Maya sites.** -/
theorem det_site_strip (κ ν : ℕ → ℕ) (hκ : Antitone κ) (hν : Antitone ν) :
    det (of fun b c : Fin k => if site κ c < site ν b + 1 then (1 : R) else 0) =
      if (∀ b : Fin k, κ b ≤ ν b) ∧ (∀ b : ℕ, b + 1 < k → ν (b + 1) ≤ κ b) then 1 else 0 := by
  have hx : Antitone fun b : Fin k => site ν b + 1 := fun a b hab => by
    have := antitone_site hν (Fin.le_def.mp hab); simp only; omega
  have hy : Antitone fun c : Fin k => site κ c := fun a b hab => antitone_site hκ (Fin.le_def.mp hab)
  rw [RMT.Symmetric.det_interlacing_indicator (fun b : Fin k => site ν b + 1)
    (fun c : Fin k => site κ c) hx hy]
  congr 1
  apply propext
  apply and_congr
  · refine forall_congr' fun b => ?_
    unfold site; omega
  · constructor
    · intro h b hb
      have := h ⟨b, by omega⟩ ⟨b + 1, hb⟩ rfl
      unfold site at this; push_cast at this; omega
    · intro h b c hbc
      have := h b (by omega)
      unfold site; rw [hbc]; push_cast; omega

open Classical in
/-- On `k` rows, with `ν` (hence `κ`) a partition, the determinant detects `HStrip` restricted to
the first `k` particles, phrased directly in Maya sites (`hStrip_iff_site`). -/
theorem det_site_strip_iff (κ ν : ℕ → ℕ) (hκ : Antitone κ) (hν : Antitone ν) :
    det (of fun b c : Fin k => if site κ c < site ν b + 1 then (1 : R) else 0) =
      if (∀ b : ℕ, b < k → site κ b ≤ site ν b) ∧
          (∀ b : ℕ, b + 1 < k → site ν (b + 1) < site κ b) then 1 else 0 := by
  rw [det_site_strip κ ν hκ hν]
  congr 1
  apply propext
  unfold site
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun b hb => by have := h1 ⟨b, hb⟩; simp only at this; omega,
      fun b hb => by have := h2 b hb; push_cast; omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun b => by have := h1 b b.2; omega, fun b hb => by have := h2 b hb; push_cast at this; omega⟩

end RMT.Growth
