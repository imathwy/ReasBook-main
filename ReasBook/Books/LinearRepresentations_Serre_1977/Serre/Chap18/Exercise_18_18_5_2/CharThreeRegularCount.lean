import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_1
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.RegularConjClassCore

-- The Fong–Swan import chain re-introduces the global `Field.henselian` instance, which makes
-- typeclass search loop on local rings.  Disable it locally, mirroring the sibling files in this
-- directory.
attribute [-instance] Field.henselian

noncomputable section

open Equiv.Perm

namespace Exercise_18_18_5_2

/-- `S₄`, the symmetric group on four letters. -/
abbrev S4 := Equiv.Perm (Fin 4)

/-- Local notation for the `3`-regular conjugacy classes of `S₄`. -/
abbrev RegClasses := Representation.PRegularConjClass S4 3

/-! ## Explicit `3`-regular representatives and their cycle types -/

/-- A transposition in `S₄` (cycle type `{2}`, order `2`). -/
def transp : S4 := Equiv.swap 0 1

/-- A double transposition in `S₄` (cycle type `{2, 2}`, order `2`). -/
def dbl : S4 := Equiv.swap 0 1 * Equiv.swap 2 3

/-- A four-cycle in `S₄` (cycle type `{4}`, order `4`). -/
def four : S4 := finRotate 4

@[simp] theorem transp_cycleType : transp.cycleType = {2} := by decide
@[simp] theorem dbl_cycleType : dbl.cycleType = {2, 2} := by decide
@[simp] theorem four_cycleType : four.cycleType = {4} := by decide
@[simp] theorem one_cycleType : (1 : S4).cycleType = 0 := by decide

/-- The identity of `S₄` is `3`-regular. -/
theorem one_isPRegular : IsPRegular 3 (1 : S4) := isPRegular_one 3

/-- The transposition is `3`-regular. -/
theorem transp_isPRegular : IsPRegular 3 transp := by
  have ho : orderOf transp = 2 := by rw [← Equiv.Perm.lcm_cycleType, transp_cycleType]; decide
  show Nat.Coprime 3 (orderOf transp)
  rw [ho]; decide

/-- The double transposition is `3`-regular. -/
theorem dbl_isPRegular : IsPRegular 3 dbl := by
  have ho : orderOf dbl = 2 := by rw [← Equiv.Perm.lcm_cycleType, dbl_cycleType]; decide
  show Nat.Coprime 3 (orderOf dbl)
  rw [ho]; decide

/-- The four-cycle is `3`-regular. -/
theorem four_isPRegular : IsPRegular 3 four := by
  have ho : orderOf four = 4 := by rw [← Equiv.Perm.lcm_cycleType, four_cycleType]; decide
  show Nat.Coprime 3 (orderOf four)
  rw [ho]; decide

/-! ## Cycle-type classification of `3`-regular elements -/

/-- Enumeration: every element of `S₄` has one of the five cycle types
`∅`, `{2}`, `{3}`, `{4}`, `{2, 2}`. -/
theorem cycleType_enum (g : S4) :
    g.cycleType = 0 ∨ g.cycleType = {2} ∨ g.cycleType = {3}
      ∨ g.cycleType = {4} ∨ g.cycleType = {2, 2} := by
  revert g
  decide

/-- Every `3`-regular element of `S₄` has one of the four cycle types `∅`, `{2}`, `{2,2}`,
`{4}`.  The fifth possible cycle type `{3}` (the 3-cycles) is excluded because such elements have
order `3`, which is not coprime to `3`. -/
theorem cycleType_of_isPRegular (g : S4) (hg : IsPRegular 3 g) :
    g.cycleType = 0 ∨ g.cycleType = {2} ∨ g.cycleType = {2, 2} ∨ g.cycleType = {4} := by
  rcases cycleType_enum g with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · -- The 3-cycle case contradicts `3`-regularity.
    exfalso
    have ho : orderOf g = 3 := by rw [← Equiv.Perm.lcm_cycleType, h]; decide
    have hg' : Nat.Coprime 3 (orderOf g) := hg
    rw [ho] at hg'
    exact (by decide : ¬ Nat.Coprime 3 3) hg'
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

/-! ## The bijection with `Fin 4` -/

open Representation in
/-- The cycle type of the chosen representative of `PRegularConjClass.ofSubtype 3 s` equals the
cycle type of `s.1`, because the representative is conjugate to `s.1`. -/
theorem cycleType_representative_ofSubtype (s : { x : S4 // IsPRegular 3 x }) :
    (PRegularConjClass.representative
        (PRegularConjClass.ofSubtype (G := S4) 3 s)).1.cycleType = s.1.cycleType := by
  have hconj :
      IsConj
        (PRegularConjClass.representative
          (PRegularConjClass.ofSubtype (G := S4) 3 s)).1 s.1 := by
    apply (ConjClasses.mk_eq_mk_iff_isConj).1
    have h := PRegularConjClass.mk_representative
      (G := S4) (p := 3) (PRegularConjClass.ofSubtype (G := S4) 3 s)
    rw [h, PRegularConjClass.coe_ofSubtype]
  exact Equiv.Perm.isConj_iff_cycleType_eq.1 hconj

open Representation in
/-- Code each `3`-regular conjugacy class of `S₄` by its cycle type, landing in `Fin 4`. -/
noncomputable def code (c : RegClasses) : Fin 4 :=
  if (PRegularConjClass.representative c).1.cycleType = 0 then 0
  else if (PRegularConjClass.representative c).1.cycleType = {2} then 1
  else if (PRegularConjClass.representative c).1.cycleType = {2, 2} then 2
  else 3

open Representation in
/-- The four concrete `3`-regular conjugacy classes of `S₄`. -/
def classOfCode : Fin 4 → RegClasses
  | 0 => PRegularConjClass.ofSubtype (G := S4) 3 ⟨1, one_isPRegular⟩
  | 1 => PRegularConjClass.ofSubtype (G := S4) 3 ⟨transp, transp_isPRegular⟩
  | 2 => PRegularConjClass.ofSubtype (G := S4) 3 ⟨dbl, dbl_isPRegular⟩
  | 3 => PRegularConjClass.ofSubtype (G := S4) 3 ⟨four, four_isPRegular⟩

open Representation in
theorem code_classOfCode (i : Fin 4) : code (classOfCode i) = i := by
  fin_cases i
  · show code (classOfCode 0) = 0
    have h : (PRegularConjClass.representative (classOfCode 0)).1.cycleType = 0 := by
      rw [classOfCode]; rw [cycleType_representative_ofSubtype]; exact one_cycleType
    rw [code, if_pos h]
  · show code (classOfCode 1) = 1
    have h : (PRegularConjClass.representative (classOfCode 1)).1.cycleType = {2} := by
      rw [classOfCode]; rw [cycleType_representative_ofSubtype]; exact transp_cycleType
    rw [code, h]; decide
  · show code (classOfCode 2) = 2
    have h : (PRegularConjClass.representative (classOfCode 2)).1.cycleType = {2, 2} := by
      rw [classOfCode]; rw [cycleType_representative_ofSubtype]; exact dbl_cycleType
    rw [code, h]; decide
  · show code (classOfCode 3) = 3
    have h : (PRegularConjClass.representative (classOfCode 3)).1.cycleType = {4} := by
      rw [classOfCode]; rw [cycleType_representative_ofSubtype]; exact four_cycleType
    rw [code, h]; decide

open Representation in
theorem classOfCode_code (c : RegClasses) : classOfCode (code c) = c := by
  set g := (PRegularConjClass.representative c).1 with hg_def
  have hreg : IsPRegular 3 g := (PRegularConjClass.representative c).2
  -- The cycle type of `classOfCode (code c)`'s representative agrees with that of `g`.
  have key : (PRegularConjClass.representative (classOfCode (code c))).1.cycleType = g.cycleType := by
    rcases cycleType_of_isPRegular g hreg with h | h | h | h
    · have hc : code c = 0 := by rw [code, if_pos (by rw [← hg_def]; exact h)]
      rw [hc, classOfCode, cycleType_representative_ofSubtype, one_cycleType, h]
    · have hne0 : g.cycleType ≠ 0 := by rw [h]; decide
      have hc : code c = 1 := by
        rw [code, if_neg (by rw [← hg_def]; exact hne0), if_pos (by rw [← hg_def]; exact h)]
      rw [hc, classOfCode, cycleType_representative_ofSubtype, transp_cycleType, h]
    · have hne0 : g.cycleType ≠ 0 := by rw [h]; decide
      have hne2 : g.cycleType ≠ {2} := by rw [h]; decide
      have hc : code c = 2 := by
        rw [code, if_neg (by rw [← hg_def]; exact hne0), if_neg (by rw [← hg_def]; exact hne2),
          if_pos (by rw [← hg_def]; exact h)]
      rw [hc, classOfCode, cycleType_representative_ofSubtype, dbl_cycleType, h]
    · have hne0 : g.cycleType ≠ 0 := by rw [h]; decide
      have hne2 : g.cycleType ≠ {2} := by rw [h]; decide
      have hne22 : g.cycleType ≠ {2, 2} := by rw [h]; decide
      have hc : code c = 3 := by
        rw [code, if_neg (by rw [← hg_def]; exact hne0), if_neg (by rw [← hg_def]; exact hne2),
          if_neg (by rw [← hg_def]; exact hne22)]
      rw [hc, classOfCode, cycleType_representative_ofSubtype, four_cycleType, h]
  -- Equal cycle types ⟹ conjugate ⟹ the same conjugacy class.
  have hconj :
      IsConj (PRegularConjClass.representative (classOfCode (code c))).1 g :=
    Equiv.Perm.isConj_iff_cycleType_eq.2 key
  apply Subtype.ext
  calc
    (classOfCode (code c) : ConjClasses S4)
        = ConjClasses.mk (PRegularConjClass.representative (classOfCode (code c))).1 :=
          (PRegularConjClass.mk_representative (G := S4) (p := 3) (classOfCode (code c))).symm
    _ = ConjClasses.mk g := (ConjClasses.mk_eq_mk_iff_isConj).2 hconj
    _ = c.1 := by rw [hg_def]; exact PRegularConjClass.mk_representative (G := S4) (p := 3) c

/-- The bijection between the `3`-regular conjugacy classes of `S₄` and `Fin 4`. -/
noncomputable def equivFinFour : RegClasses ≃ Fin 4 where
  toFun := code
  invFun := classOfCode
  left_inv := classOfCode_code
  right_inv := code_classOfCode

end Exercise_18_18_5_2

/-- `S₄ = Equiv.Perm (Fin 4)` has exactly four `3`-regular conjugacy classes: the identity,
the transpositions, the double transpositions, and the four-cycles (the 3-cycles are the only
non-regular class). -/
theorem nat_card_pRegularConjClass_s4_three :
    Nat.card (Representation.PRegularConjClass (Equiv.Perm (Fin 4)) 3) = 4 := by
  simpa using Nat.card_congr Exercise_18_18_5_2.equivFinFour

end
