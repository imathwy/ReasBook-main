/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xuran Sun, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part1

open scoped Matrix Topology

section Chap01
section Section04

/-- Prop 4.4.1: The effective domain of a convex function is a convex set in `ℝ^n`. -/
lemma effectiveDomain_convex {n : Nat} {S : Set (Fin n -> Real)}
    {f : (Fin n -> Real) -> EReal} (hf : ConvexFunctionOn S f) :
    Convex ℝ (effectiveDomain S f) := by
  have hconv :
      Convex ℝ ((LinearMap.fst ℝ (Fin n -> Real) Real) '' epigraph S f) :=
    convex_image_fst_epigraph (S := S) (f := f) hf
  simpa [effectiveDomain_eq_image_fst] using hconv

/-- The effective domain is contained in the original set. -/
lemma effectiveDomain_subset {n : Nat} (S : Set (Fin n -> Real))
    (f : (Fin n -> Real) -> EReal) :
    effectiveDomain S f ⊆ S := by
  intro x hx
  rcases hx with ⟨μ, hμ⟩
  exact hμ.1

/-- The epigraph is unchanged by restricting to the effective domain. -/
lemma epigraph_effectiveDomain_eq {n : Nat} (S : Set (Fin n -> Real))
    (f : (Fin n -> Real) -> EReal) :
    epigraph (effectiveDomain S f) f = epigraph S f := by
  ext p; constructor
  · intro hp
    rcases hp with ⟨hp_dom, hp_le⟩
    have hp_S : S p.1 := (effectiveDomain_subset (S := S) (f := f)) hp_dom
    exact And.intro hp_S hp_le
  · intro hp
    rcases hp with ⟨hp_S, hp_le⟩
    have hp_dom : p.1 ∈ effectiveDomain S f := by
      refine ⟨p.2, ?_⟩
      exact And.intro hp_S hp_le
    exact And.intro hp_dom hp_le

/-- Prop 4.4.2: Trivially, the convexity of `f` is equivalent to that of the restriction
of `f` to `dom f` (the effective domain). All the interest really centers on this
restriction, and `S` has little role of its own. -/
lemma convexFunctionOn_iff_convexFunctionOn_effectiveDomain {n : Nat}
    (S : Set (Fin n -> Real)) (f : (Fin n -> Real) -> EReal) :
    ConvexFunctionOn S f ↔ ConvexFunctionOn (effectiveDomain S f) f := by
  simp [ConvexFunctionOn, epigraph_effectiveDomain_eq]

/-- The inequality `⊤ ≤ (r : EReal)` never holds for real `r`. -/
lemma not_top_le_coe (r : Real) : ¬ ((⊤ : EReal) ≤ (r : EReal)) := by
  simp [top_le_iff]

/-- The constant `⊤` function is convex on any set. -/
lemma convexFunctionOn_const_top {n : Nat} (C : Set (Fin n -> Real)) :
    ConvexFunctionOn C (fun _ => (⊤ : EReal)) := by
  have h_empty :
      epigraph C (fun _ => (⊤ : EReal)) = (∅ : Set ((Fin n -> Real) × Real)) := by
    ext p; constructor
    · intro hp
      rcases hp with ⟨_, hp⟩
      exact (not_top_le_coe p.2 hp).elim
    · intro hp; cases hp
  simpa [ConvexFunctionOn, h_empty] using
    (convex_empty : Convex ℝ (∅ : Set ((Fin n -> Real) × Real)))

/-- The effective domain of the constant `⊤` function is empty. -/
lemma effectiveDomain_const_top {n : Nat} (C : Set (Fin n -> Real)) :
    effectiveDomain C (fun _ => (⊤ : EReal)) = (∅ : Set (Fin n -> Real)) := by
  ext x; constructor
  · intro hx
    rcases hx with ⟨μ, hx⟩
    rcases hx with ⟨_, hxμ⟩
    exact (not_top_le_coe μ hxμ).elim
  · intro hx; cases hx

/-- Remark 4.4.5: There are weighty reasons, soon apparent, why one does not want to consider
merely the class of all convex functions having a fixed set `C` as their common effective domain. -/
lemma fixedEffectiveDomain_restriction_not_preferred {n : Nat} (C : Set (Fin n -> Real))
    (hC : Set.Nonempty C) :
    ¬ (∀ f : (Fin n -> Real) → EReal, ConvexFunctionOn C f → effectiveDomain C f = C) := by
  intro hforall
  have hdom :
      effectiveDomain C (fun _ => (⊤ : EReal)) = C :=
    hforall (fun _ => (⊤ : EReal)) (convexFunctionOn_const_top (C := C))
  have h_empty :
      effectiveDomain C (fun _ => (⊤ : EReal)) = (∅ : Set (Fin n → Real)) :=
    effectiveDomain_const_top (C := C)
  exact hC.ne_empty (hdom.symm.trans h_empty)

/-- Defintion 4.4.6: The forbidden sums are `⊤ + ⊥` (that is, `⊤ - ⊤`) and `⊥ + ⊤`
in the extended real line. -/
def ERealForbiddenSum (a b : EReal) : Prop :=
  (a = ⊤ ∧ b = ⊥) ∨ (a = ⊥ ∧ b = ⊤)

/-- Defintion 4.4.6: Conventions for arithmetic on `EReal` include
`α + ⊤ = ⊤ + α = ⊤` for `⊥ < α`, `α - ⊤ = ⊥ + α = ⊥` for `α < ⊤`, rules for
multiplication by `⊤` or `⊥` depending on the sign of `α`, the identities
`0 * ⊤ = ⊤ * 0 = 0 = 0 * ⊥ = ⊥ * 0`, `-⊥ = ⊤`, and
`sInf ∅ = ⊤`, `sSup ∅ = ⊥`. -/
def ERealArithmeticConventions : Prop :=
  (∀ α : EReal, ⊥ < α → α + ⊤ = ⊤ ∧ ⊤ + α = ⊤) ∧
    (∀ α : EReal, α < ⊤ → α - ⊤ = ⊥ ∧ ⊥ + α = ⊥) ∧
    (∀ α : EReal, 0 < α → α * ⊤ = ⊤ ∧ ⊤ * α = ⊤) ∧
    (∀ α : EReal, 0 < α → α * ⊥ = ⊥ ∧ ⊥ * α = ⊥) ∧
    (∀ α : EReal, α < 0 → α * ⊤ = ⊥ ∧ ⊤ * α = ⊥) ∧
    (∀ α : EReal, α < 0 → α * ⊥ = ⊤ ∧ ⊥ * α = ⊤) ∧
    (0 * (⊤ : EReal) = 0 ∧ (⊤ : EReal) * 0 = 0 ∧ 0 * (⊥ : EReal) = 0 ∧
        (⊥ : EReal) * 0 = 0) ∧
    (-(⊥ : EReal) = ⊤) ∧
    (sInf (∅ : Set EReal) = (⊤ : EReal) ∧ sSup (∅ : Set EReal) = (⊥ : EReal))

/-- Negating both arguments preserves the forbidden-sum condition. -/
lemma ereal_forbiddenSum_neg_iff {a b : EReal} :
    ERealForbiddenSum (-a) (-b) ↔ ERealForbiddenSum a b := by
  constructor
  · intro h
    rcases h with h | h
    · rcases h with ⟨ha, hb⟩
      have ha' : a = ⊥ := (EReal.neg_eq_top_iff).1 ha
      have hb' : b = ⊤ := (EReal.neg_eq_bot_iff).1 hb
      exact Or.inr ⟨ha', hb'⟩
    · rcases h with ⟨ha, hb⟩
      have ha' : a = ⊤ := (EReal.neg_eq_bot_iff).1 ha
      have hb' : b = ⊥ := (EReal.neg_eq_top_iff).1 hb
      exact Or.inl ⟨ha', hb'⟩
  · intro h
    rcases h with h | h
    · rcases h with ⟨ha, hb⟩
      simp [ERealForbiddenSum, ha, hb]
    · rcases h with ⟨ha, hb⟩
      simp [ERealForbiddenSum, ha, hb]

/-- Disjunctions needed to apply `EReal.neg_add` from a non-forbidden sum. -/
lemma ereal_no_forbidden_neg_add {a b : EReal} (h : ¬ ERealForbiddenSum a b) :
    (a ≠ ⊥ ∨ b ≠ ⊤) ∧ (a ≠ ⊤ ∨ b ≠ ⊥) := by
  constructor
  · by_cases ha : a = ⊥
    · right
      intro hb
      apply h
      exact Or.inr ⟨ha, hb⟩
    · left
      exact ha
  · by_cases ha : a = ⊤
    · right
      intro hb
      apply h
      exact Or.inl ⟨ha, hb⟩
    · left
      exact ha

/-- Left distributivity for multiplication by `⊤` under a non-forbidden sum. -/
lemma ereal_top_mul_add_of_no_forbidden {x1 x2 : EReal}
    (h : ¬ ERealForbiddenSum ((⊤ : EReal) * x1) ((⊤ : EReal) * x2)) :
    (⊤ : EReal) * (x1 + x2) = (⊤ : EReal) * x1 + (⊤ : EReal) * x2 := by
  cases x1 using EReal.rec <;> cases x2 using EReal.rec
  · simp
  · simp
  · simp
  · simp
  · rename_i a b
    rcases lt_trichotomy a 0 with (ha_neg | ha_zero | ha_pos)
    · rcases lt_trichotomy b 0 with (hb_neg | hb_zero | hb_pos)
      · have hsum : a + b < 0 := by linarith
        simp [← EReal.coe_add, EReal.top_mul_coe_of_neg, ha_neg, hb_neg, hsum]
      · have hsum : a + b < 0 := by simpa [hb_zero] using ha_neg
        simp [hb_zero, EReal.top_mul_coe_of_neg, ha_neg]
      · exfalso
        apply h
        simp [ERealForbiddenSum, EReal.top_mul_coe_of_neg, EReal.top_mul_coe_of_pos, ha_neg, hb_pos]
    · rcases lt_trichotomy b 0 with (hb_neg | hb_zero | hb_pos)
      · have hsum : a + b < 0 := by simpa [ha_zero] using hb_neg
        simp [ha_zero, EReal.top_mul_coe_of_neg, hb_neg]
      · simp [ha_zero, hb_zero]
      · have hsum : 0 < a + b := by simpa [ha_zero] using hb_pos
        simp [ha_zero, EReal.top_mul_coe_of_pos, hb_pos]
    · rcases lt_trichotomy b 0 with (hb_neg | hb_zero | hb_pos)
      · exfalso
        apply h
        simp [ERealForbiddenSum, EReal.top_mul_coe_of_pos, EReal.top_mul_coe_of_neg, ha_pos, hb_neg]
      · have hsum : 0 < a + b := by simpa [hb_zero] using ha_pos
        simp [hb_zero, EReal.top_mul_coe_of_pos, ha_pos]
      · have hsum : 0 < a + b := by linarith
        simp [← EReal.coe_add, EReal.top_mul_coe_of_pos, ha_pos, hb_pos, hsum]
  · rename_i a
    rcases lt_trichotomy a 0 with (ha_neg | ha_zero | ha_pos)
    · exfalso
      apply h
      simp [ERealForbiddenSum, EReal.top_mul_coe_of_neg, ha_neg]
    · simp [ha_zero]
    · simp [EReal.top_mul_coe_of_pos, ha_pos]
  · simp
  · rename_i b
    rcases lt_trichotomy b 0 with (hb_neg | hb_zero | hb_pos)
    · exfalso
      apply h
      simp [ERealForbiddenSum, EReal.top_mul_coe_of_neg, hb_neg]
    · simp [hb_zero]
    · simp [EReal.top_mul_coe_of_pos, hb_pos]
  · simp

end Section04
end Chap01
