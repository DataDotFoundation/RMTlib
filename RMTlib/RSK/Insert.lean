import RMTlib.RSK.Semistandard

/-!
# Row insertion preserves semistandardness

The classical bumping lemma: inserting a value into a semistandard tableau by row bumping
(`Nested.ins`) gives a semistandard tableau. The proof follows `Nested.ins`. At each row it
tracks where the inserted value landed (`InsAt`): at the first position `p` holding a larger
entry, or at the end. One row down, the bumped entry `y = r[p]` lands at a position `≤ p`,
because the entry of the next row below position `p` is larger than `y`; this is what is
needed to check the columns.
-/

namespace RMT.RSK

/-- `r'` is `r` with `x` written at position `p`: the first position holding an entry `> x`,
or the end of the row. -/
def InsAt (r : Row) (x p : Nat) (r' : Row) : Prop :=
  p ≤ r.length ∧ (∀ i, i < p → r.getD i 0 ≤ x) ∧ (p < r.length → x < r.getD p 0) ∧
    r'.length = max r.length (p + 1) ∧ ∀ i, r'.getD i 0 = if i = p then x else r.getD i 0

namespace Nested

theorem rowIns_insAt (x : Nat) : ∀ (r : Row),
    ∃ p, InsAt r x p (rowIns x r).1 ∧
      (rowIns x r).2 = if p < r.length then some (r.getD p 0) else none
  | [] => by
    refine ⟨0, ⟨by simp, by simp, by simp, by simp [rowIns], ?_⟩, by simp [rowIns]⟩
    intro i; cases i with
    | zero => simp [rowIns]
    | succ i => simp [rowIns]
  | z :: zs => by
    by_cases hxz : x < z
    · refine ⟨0, ?_, ?_⟩
      · refine ⟨by simp, by simp, by simpa using hxz, by simp [rowIns, hxz], ?_⟩
        intro i; cases i <;> simp [rowIns, hxz]
      · simp [rowIns, hxz]
    · obtain ⟨p, ⟨h1, h2, h3, h4, h5⟩, hb⟩ := rowIns_insAt x zs
      refine ⟨p + 1, ⟨by simpa using h1, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro i hi; cases i with
        | zero => simp <;> omega
        | succ i => simpa using h2 i (by omega)
      · intro h; simpa using h3 (by simpa using h)
      · simp [rowIns, hxz, h4]
      · intro i; cases i with
        | zero => simp [rowIns, hxz]
        | succ i => simpa [rowIns, hxz] using h5 i
      · simp only [rowIns, hxz, ↓reduceIte, hb, List.length_cons]
        by_cases h : p < zs.length <;> simp [h]

/-- **Row insertion preserves semistandardness**, and the top row changes as `InsAt` says. -/
theorem ins_ssyt (x : Nat) : ∀ (t : Tab), SSYT t →
    SSYT (ins x t).1 ∧ ∃ p, InsAt (t.headD []) x p ((ins x t).1.headD [])
  | [], _ => by
    refine ⟨⟨?_, trivial⟩, 0, ?_⟩
    · intro r hr; simp [ins] at hr; subst hr; simp [Sorted]
    · refine ⟨by simp, by simp, by simp, by simp [ins], ?_⟩
      intro i; cases i with
      | zero => simp [ins]
      | succ i => simp [ins]
  | r :: rs, hss => by
    have hr := hss.good r (by simp)
    obtain ⟨p, hp, hb⟩ := rowIns_insAt x r
    have hr' : Sorted (rowIns x r).1 ∧ (rowIns x r).1 ≠ [] :=
      ⟨rowIns_sorted x r hr.1, rowIns_ne_nil x r⟩
    obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hp
    by_cases hpl : p < r.length
    · -- `y = r[p]` is bumped into the rows below
      rw [ite_eq_left hpl] at hb
      have e : ins x (r :: rs) = ((rowIns x r).1 :: (ins (r.getD p 0) rs).1,
          (ins (r.getD p 0) rs).2 + 1) := by
        simp only [ins]; rw [show rowIns x r = ((rowIns x r).1, some (r.getD p 0)) from
          Prod.ext rfl hb]
      rw [e]
      obtain ⟨hss', q, hq1, hq2, hq3, hq4, hq5⟩ := ins_ssyt (r.getD p 0) rs hss.tail
      refine ⟨?_, p, ⟨hp1, hp2, hp3, hp4, hp5⟩⟩
      -- the new tableau is `r' :: s' :: rest'`
      cases hins : (ins (r.getD p 0) rs).1 with
      | nil =>
        exfalso; cases rs with
        | nil => simp [ins] at hins
        | cons s ss =>
          simp only [ins] at hins; split at hins <;> simp at hins
      | cons s' rest' =>
        rw [hins] at hss' hq4 hq5
        refine ⟨?_, ?_, hss'.2⟩
        · intro u hu; simp at hu; rcases hu with rfl | hu
          · exact hr'
          · exact hss'.good u (by simp [hu])
        · -- `Col2 r' s'`
          simp only [List.headD_cons] at hq4 hq5
          -- `q ≤ p`
          have hcol : ∀ k, k < (rs.headD []).length → r.getD k 0 < (rs.headD []).getD k 0 := by
            cases rs with
            | nil => intro k hk; simp at hk
            | cons s ss => exact hss.2.1.2
          have hlen : (rs.headD []).length ≤ r.length := by
            cases rs with
            | nil => simp
            | cons s ss => exact hss.2.1.1
          have hqp : q ≤ p := by
            refine Nat.le_of_not_lt fun hc => ?_
            have := hq2 p hc
            by_cases hps : p < (rs.headD []).length
            · have := hcol p hps; omega
            · omega
          refine ⟨by rw [hq4, hp4]; omega, ?_⟩
          intro k hk
          rw [hp5 k, hq5 k]
          by_cases hkq : k = q
          · subst hkq
            rw [ite_eq_left rfl]
            by_cases hkp : k = p
            · subst hkp; rw [ite_eq_left rfl]; exact hp3 hpl
            · rw [ite_eq_right hkp]; have := hp2 k (by omega); have := hp3 hpl; omega
          · rw [ite_eq_right hkq]
            have hks : k < (rs.headD []).length := by rw [hq4] at hk; omega
            have := hcol k hks
            by_cases hkp : k = p
            · subst hkp; rw [ite_eq_left rfl]; have := hp3 hpl; omega
            · rw [ite_eq_right hkp]; omega
    · -- `x` is appended to the top row
      rw [ite_eq_right hpl] at hb
      have happ : (rowIns x r).1 = r ++ [x] := rowIns_none x r hb
      have e : ins x (r :: rs) = ((rowIns x r).1 :: rs, 0) := by
        simp only [ins]; rw [show rowIns x r = ((rowIns x r).1, none) from Prod.ext rfl hb]
      rw [e]
      refine ⟨?_, p, ⟨hp1, hp2, hp3, hp4, hp5⟩⟩
      refine ⟨?_, ?_⟩
      · intro u hu; simp at hu; rcases hu with rfl | hu
        · exact hr'
        · exact hss.good u (by simp [hu])
      · cases rs with
        | nil => trivial
        | cons s ss =>
          refine ⟨⟨?_, ?_⟩, hss.2.2⟩
          · rw [happ]; simp; have := hss.2.1.1; omega
          · intro k hk
            have := hss.2.1.2 k hk
            have hkr : k < r.length := by have := hss.2.1.1; omega
            rw [happ]; simpa [List.getElem?_append_left hkr] using this

/-- RSK of a word (`Nested.rsk`) produces a semistandard tableau. -/
theorem rsk_ssyt : ∀ w, SSYT (rsk w).1
  | [] => ⟨fun r hr => by simp [rsk] at hr, trivial⟩
  | x :: w => (ins_ssyt x _ (rsk_ssyt w)).1

end Nested

end RMT.RSK
