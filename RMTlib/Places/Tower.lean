import RMTlib.Places.BandStep

/-!
# The theta tower as one object (RMTlib#79)

RH-Dual's picture (`bridge/work/TOWER.md`, RMTlib#72): at one archimedean place the theta tower is
* a finite set `X ⊂ ℤ` of distinct points (the Harish-Chandra parameter);
* **levels** `e 0 < e 1 < …` (a translation per lift);
* a **band** `(−c, c)` with `c > 0`.

Level `i` reads `X + e i` through the band: the points above give the particle side `a⁺_i`
(positions `y − c`), the points below give the hole side `a⁻_i`, reflected (positions `−y − c`). The
factor at `∞` is `H(a⁺_i) · H(a⁻_i)`. One lift slides by `Δ = e (i+1) − e i`, and exactly one point
crosses the band.

Here:
* `above`, `below`, `cut`: the reading of a configuration through the band;
* `card_above_add_card_below`: **charge conservation**, if the band is empty;
* `above_translate`, `below_eq_insert`: **the step as set maps**. If the band is empty before and
  after a translation by `d`, and exactly one point `z` crosses, then the particle side gains `z`
  after the translation, and the hole side loses it before the translation;
* `Tower.log_hset_above_succ`: **`Δ log H(a⁺) = T + S + V`** along the tower (F9 on the tower);
* `Tower.hset_below_succ_le`: **draining**, `H(a⁻_{i+1}) ≤ H(a⁻_i)` (`hset_drain` on the tower);
* `above_reflect`, `below_reflect`: the move `X ↦ −X` (M8) exchanges the two sides. This is
  particle ↔ hole on one Maya diagram, kept distinct from `ω` (`λ ↦ λ′`), per RH-Dual's rule 4.

Whether one crossing per step follows from the proof's interlacing and gap conditions (`HCParam`)
is the identification RH-Dual is making (lane C); here it is a hypothesis (`OneCrossing`).
-/

namespace RMT.Tower

open Finset RMT.StringInsertion

/-! ## Reading a configuration through the band -/

/-- No point of `Y` lies in the band `(−c, c)`. -/
def BandEmpty (Y : Finset ℤ) (c : ℤ) : Prop := ∀ y ∈ Y, y ≤ -c ∨ c ≤ y

/-- The particle side: points `y ≥ c`, at positions `y − c`. -/
def above (Y : Finset ℤ) (c : ℤ) : Finset ℕ := (Y.filter (c ≤ ·)).image fun y => (y - c).toNat

/-- The hole side, reflected: points `y ≤ −c`, at positions `−y − c`. -/
def below (Y : Finset ℤ) (c : ℤ) : Finset ℕ := (Y.filter (· ≤ -c)).image fun y => (-y - c).toNat

/-- Translate a configuration by `d`. -/
def translate (Y : Finset ℤ) (d : ℤ) : Finset ℤ := Y.map (addRightEmbedding d)

theorem mem_above {Y : Finset ℤ} {c : ℤ} {n : ℕ} :
    n ∈ above Y c ↔ ∃ y ∈ Y, c ≤ y ∧ (y - c).toNat = n := by
  simp [above, and_assoc]

theorem mem_below {Y : Finset ℤ} {c : ℤ} {n : ℕ} :
    n ∈ below Y c ↔ ∃ y ∈ Y, y ≤ -c ∧ (-y - c).toNat = n := by
  simp [below, and_assoc]

theorem mem_translate {Y : Finset ℤ} {d w : ℤ} : w ∈ translate Y d ↔ ∃ y ∈ Y, y + d = w := by
  simp [translate]

/-- **Charge conservation**: with the band empty, the two sides together have as many points as
the configuration. -/
theorem card_above_add_card_below {Y : Finset ℤ} {c : ℤ} (hc : 0 < c) (hY : BandEmpty Y c) :
    (above Y c).card + (below Y c).card = Y.card := by
  have h1 : (above Y c).card = (Y.filter (c ≤ ·)).card := by
    refine card_image_of_injOn fun a ha b hb hab => ?_
    simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
    omega
  have h2 : (below Y c).card = (Y.filter (· ≤ -c)).card := by
    refine card_image_of_injOn fun a ha b hb hab => ?_
    simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
    omega
  have h3 : Y.filter (fun y => ¬ c ≤ y) = Y.filter (· ≤ -c) := by
    refine filter_congr fun y hy => ?_
    rcases hY y hy with h | h <;> constructor <;> intro <;> omega
  rw [h1, h2, ← h3, card_filter_add_card_filter_not]

/-! ## One step: translate, and exactly one point crosses -/

/-- Exactly one point `z` of `Y` crosses the band under the translation by `d`: it starts below and
ends above, and it is the only point that does. -/
structure OneCrossing (Y : Finset ℤ) (c d z : ℤ) : Prop where
  /-- The crossing point is a point of the configuration. -/
  mem : z ∈ Y
  /-- It starts below the band. -/
  below : z ≤ -c
  /-- It lands above the band. -/
  lands : c ≤ z + d
  /-- No other point crosses. -/
  unique : ∀ w ∈ Y, w ≤ -c → c ≤ w + d → w = z

/-- **The particle side gains the crossing point.** -/
theorem above_translate {Y : Finset ℤ} {c d z : ℤ} (hd : 0 ≤ d) (hY : BandEmpty Y c)
    (h : OneCrossing Y c d z) :
    above (translate Y d) c = insert (z + d - c).toNat (shift (above Y c) d.toNat) := by
  ext n
  simp only [mem_above, mem_translate, mem_insert, mem_shift]
  constructor
  · rintro ⟨w, ⟨y, hy, rfl⟩, hcw, rfl⟩
    rcases hY y hy with hb | ha
    · left; rw [h.unique y hy hb hcw]
    · right; exact ⟨(y - c).toNat, ⟨y, hy, ha, rfl⟩, by omega⟩
  · rintro (rfl | ⟨x, ⟨y, hy, ha, rfl⟩, rfl⟩)
    · exact ⟨z + d, ⟨z, h.mem, rfl⟩, h.lands, rfl⟩
    · exact ⟨y + d, ⟨y, hy, rfl⟩, by omega, by omega⟩

/-- **The hole side loses the crossing point**: before the translation it is the translated hole
side plus the crossing point. -/
theorem below_eq_insert {Y : Finset ℤ} {c d z : ℤ} (hd : 0 ≤ d)
    (hY' : BandEmpty (translate Y d) c) (h : OneCrossing Y c d z) :
    below Y c = insert (-z - c).toNat (shift (below (translate Y d) c) d.toNat) := by
  ext n
  simp only [mem_below, mem_translate, mem_insert, mem_shift]
  constructor
  · rintro ⟨y, hy, hb, rfl⟩
    by_cases hcr : c ≤ y + d
    · left; rw [h.unique y hy hb hcr]
    · right
      have hb' : y + d ≤ -c := by
        rcases hY' (y + d) (mem_translate.mpr ⟨y, hy, rfl⟩) with h' | h'
        · exact h'
        · exact absurd h' hcr
      exact ⟨(-(y + d) - c).toNat, ⟨y + d, ⟨y, hy, rfl⟩, hb', rfl⟩, by omega⟩
  · rintro (rfl | ⟨x, ⟨w, ⟨y, hy, rfl⟩, hb, rfl⟩, rfl⟩)
    · exact ⟨z, h.mem, h.below, rfl⟩
    · exact ⟨y, hy, by omega, by omega⟩

/-- The crossing point is a new site on the particle side. -/
theorem crossing_not_mem_shift_above {Y : Finset ℤ} {c d z : ℤ} (hc : 0 < c) (hd : 0 ≤ d)
    (h : OneCrossing Y c d z) : (z + d - c).toNat ∉ shift (above Y c) d.toNat := by
  rw [mem_shift]
  rintro ⟨x, hx, hxe⟩
  obtain ⟨y, hy, ha, rfl⟩ := mem_above.mp hx
  have := h.below; have := h.lands
  omega

/-- The crossing point was the lowest hole: every other hole sits above it. -/
theorem crossing_lt_holes {Y : Finset ℤ} {c d z : ℤ} (hc : 0 < c) (hd : 0 ≤ d)
    (h : OneCrossing Y c d z) :
    ∀ x ∈ below (translate Y d) c, (-z - c).toNat < x + d.toNat := by
  intro x hx
  obtain ⟨w, hw, hb, rfl⟩ := mem_below.mp hx
  obtain ⟨y, hy, rfl⟩ := mem_translate.mp hw
  have := h.below; have := h.lands
  omega

/-! ## The tower -/

/-- **The theta tower at one place**: a configuration `X`, levels `e i` (one translation per lift)
and a band half-width `c`. The conditions are separate predicates, so that a tower can be built
before they are checked. -/
structure _root_.RMT.Tower where
  /-- The Harish-Chandra parameter, as a set of distinct points. -/
  X : Finset ℤ
  /-- The levels: level `i` is `X + e i`. -/
  e : ℕ → ℤ
  /-- The band half-width `c = (t + 1)/2`. -/
  c : ℤ

end RMT.Tower

namespace RMT.Tower

open Finset RMT.StringInsertion

variable (T : RMT.Tower)

/-- The configuration at level `i`. -/
def level (i : ℕ) : Finset ℤ := translate T.X (T.e i)

/-- **The cut at level `i`**: `(a⁺_i, a⁻_i)`, the particle side and the reflected hole side. -/
def cut (i : ℕ) : Finset ℕ × Finset ℕ := (above (T.level i) T.c, below (T.level i) T.c)

/-- The step from level `i` to level `i + 1`. -/
def gap (i : ℕ) : ℤ := T.e (i + 1) - T.e i

/-- The factor at `∞` at level `i`: `H(a⁺_i) · H(a⁻_i)`. -/
noncomputable def factorInf (i : ℕ) : ℚ := hset (T.cut i).1 * hset (T.cut i).2

theorem level_succ (i : ℕ) : T.level (i + 1) = translate (T.level i) (T.gap i) := by
  ext w
  simp only [level, gap, mem_translate]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y + T.e i, ⟨y, hy, rfl⟩, by ring⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, by ring⟩

/-- **The conditions of one lift** `i → i + 1`: a positive band, a nonnegative step, the band empty
at both levels, and exactly one point `z` crossing. -/
structure StepOK (i : ℕ) (z : ℤ) : Prop where
  /-- The band is nonempty. -/
  hc : 0 < T.c
  /-- The levels go up. -/
  hd : 0 ≤ T.gap i
  /-- No point in the band at level `i`. -/
  band : BandEmpty (T.level i) T.c
  /-- No point in the band at level `i + 1`. -/
  band' : BandEmpty (T.level (i + 1)) T.c
  /-- Exactly one point crosses. -/
  one : OneCrossing (T.level i) T.c (T.gap i) z

/-- **The step on the particle side**: `a⁺_{i+1} = insert ℓ (a⁺_i + Δ)`. -/
theorem cut_succ_fst {i : ℕ} {z : ℤ} (h : T.StepOK i z) :
    (T.cut (i + 1)).1 = insert (z + T.gap i - T.c).toNat (shift (T.cut i).1 (T.gap i).toNat) := by
  simp only [cut, level_succ]
  exact above_translate h.hd h.band h.one

/-- **The step on the hole side**: `a⁻_i = insert ℓ′ (a⁻_{i+1} + Δ)`. -/
theorem cut_fst_snd {i : ℕ} {z : ℤ} (h : T.StepOK i z) :
    (T.cut i).2 = insert (-z - T.c).toNat (shift (T.cut (i + 1)).2 (T.gap i).toNat) := by
  have hb' := h.band'
  rw [level_succ] at hb'
  simp only [cut, level_succ]
  exact below_eq_insert h.hd hb' h.one

/-- **`Δ log H(a⁺) = T + S + V` along the tower** (F9 at each lift). -/
theorem log_hset_above_succ {i : ℕ} {z : ℤ} (h : T.StepOK i z) :
    Real.log (hset (T.cut (i + 1)).1) - Real.log (hset (T.cut i).1) =
      (∑ x ∈ (T.cut i).1, Real.log (((x + (T.gap i).toNat).factorial : ℝ) / x.factorial)) +
      Real.log (z + T.gap i - T.c).toNat.factorial -
      ∑ x ∈ (T.cut i).1, Real.log (Nat.dist (x + (T.gap i).toNat) (z + T.gap i - T.c).toNat : ℝ) := by
  rw [T.cut_succ_fst h]
  exact log_hset_step (crossing_not_mem_shift_above h.hc h.hd h.one)

/-- **Draining along the tower**: `H(a⁻_{i+1}) ≤ H(a⁻_i)`. -/
theorem hset_below_succ_le {i : ℕ} {z : ℤ} (h : T.StepOK i z) :
    hset (T.cut (i + 1)).2 ≤ hset (T.cut i).2 := by
  rw [T.cut_fst_snd h]
  refine hset_drain ?_ ?_
  · have := h.one.below; have := h.one.lands; have := h.hc
    omega
  · have hl := crossing_lt_holes h.hc h.hd h.one
    simpa [cut, level_succ] using hl

/-- **Charge conservation along the tower**: both sides together always hold `|X|` points. -/
theorem card_cut {i : ℕ} (hc : 0 < T.c) (hb : BandEmpty (T.level i) T.c) :
    (T.cut i).1.card + (T.cut i).2.card = T.X.card := by
  rw [cut, card_above_add_card_below hc hb, level, translate, card_map]

/-! ## The reflection move (M8) -/

/-- Reflect a configuration, `Y ↦ −Y`. -/
def reflect (Y : Finset ℤ) : Finset ℤ := Y.map ⟨Neg.neg, neg_injective⟩

theorem above_reflect (Y : Finset ℤ) (c : ℤ) : above (reflect Y) c = below Y c := by
  ext n
  simp only [mem_above, mem_below, reflect, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, h1, rfl⟩; exact ⟨y, hy, by omega, by omega⟩
  · rintro ⟨y, hy, h1, rfl⟩; exact ⟨-y, ⟨y, hy, rfl⟩, by omega, by omega⟩

theorem below_reflect (Y : Finset ℤ) (c : ℤ) : below (reflect Y) c = above Y c := by
  ext n
  simp only [mem_above, mem_below, reflect, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, h1, rfl⟩; exact ⟨y, hy, by omega, by omega⟩
  · rintro ⟨y, hy, h1, rfl⟩; exact ⟨-y, ⟨y, hy, rfl⟩, by omega, by omega⟩

/-- **M8 on the tower**: `X ↦ −X`, `e ↦ −e`. -/
def reflectTower : RMT.Tower := ⟨reflect T.X, fun i => -T.e i, T.c⟩

theorem level_reflectTower (i : ℕ) : T.reflectTower.level i = reflect (T.level i) := by
  ext w
  simp only [level, reflectTower, reflect, mem_translate, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y + T.e i, ⟨y, hy, rfl⟩, by ring⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨-y, ⟨y, hy, rfl⟩, by ring⟩

/-- **M8 swaps the two sides** of every cut (particle ↔ hole; not `ω`). -/
theorem cut_reflectTower (i : ℕ) : T.reflectTower.cut i = ((T.cut i).2, (T.cut i).1) := by
  unfold cut
  rw [level_reflectTower]
  exact Prod.ext (above_reflect _ _) (below_reflect _ _)

/-- The factor at `∞` is invariant under M8. -/
theorem factorInf_reflectTower (i : ℕ) : T.reflectTower.factorInf i = T.factorInf i := by
  simp [factorInf, cut_reflectTower, mul_comm]

end RMT.Tower
