/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part8

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise
open scoped InnerProductSpace

/-- Text 16.4.4: Let `f : ℝⁿ → ℝ ∪ {+∞}` be defined by

`f(ξ₁, …, ξₙ) = ξ₁ log ξ₁ + ⋯ + ξₙ log ξₙ` if `ξⱼ ≥ 0` for all `j` and `∑ᵢ ξᵢ = 1`, and `f = +∞`
otherwise (with the convention `0 log 0 = 0`).

Then the Fenchel conjugate satisfies `f^*(x^*) = log (exp(λ₁^*) + ⋯ + exp(λₙ^*))`. -/
theorem section16_fenchelConjugate_sum_mul_log_eq_log_sum_exp {n : ℕ} (hn : 0 < n) :
    let f : (Fin n → ℝ) → EReal := by
      classical
      exact fun ξ =>
        if 0 ≤ ξ ∧ (∑ j : Fin n, ξ j) = (1 : ℝ) then
          ((∑ j : Fin n, ξ j * Real.log (ξ j) : ℝ) : EReal)
        else (⊤ : EReal)
    fenchelConjugate n f =
      fun xStar : Fin n → ℝ => (Real.log (∑ j : Fin n, Real.exp (xStar j)) : EReal) := by
  classical
  let f : (Fin n → ℝ) → EReal := by
    classical
    exact fun ξ =>
      if 0 ≤ ξ ∧ (∑ j : Fin n, ξ j) = (1 : ℝ) then
        ((∑ j : Fin n, ξ j * Real.log (ξ j) : ℝ) : EReal)
      else (⊤ : EReal)
  have h :
      fenchelConjugate n f =
        fun xStar : Fin n → ℝ => (Real.log (∑ j : Fin n, Real.exp (xStar j)) : EReal) := by
    funext xStar
    let Z : ℝ := ∑ j : Fin n, Real.exp (xStar j)
    have hupper : fenchelConjugate n f xStar ≤ (Real.log Z : EReal) := by
      unfold fenchelConjugate
      refine sSup_le ?_
      rintro _ ⟨ξ, rfl⟩
      by_cases hfeas : 0 ≤ ξ ∧ (∑ j : Fin n, ξ j) = (1 : ℝ)
      · have hineq :
            dotProduct ξ xStar - ∑ j, ξ j * Real.log (ξ j) ≤ Real.log Z :=
          section16_entropy_rangeTerm_le_log_sum_exp (hn := hn) (ξ := ξ) (hξ := hfeas.1)
            (hsum := hfeas.2) (xStar := xStar)
        have hineq' :
            ((dotProduct ξ xStar - ∑ j, ξ j * Real.log (ξ j) : ℝ) : EReal) ≤
              (Real.log Z : EReal) := by
          exact_mod_cast hineq
        have hterm :
            ((ξ ⬝ᵥ xStar : ℝ) : EReal) - f ξ =
              ((dotProduct ξ xStar - ∑ j, ξ j * Real.log (ξ j) : ℝ) : EReal) := by
          simp [f, hfeas, dotProduct, EReal.coe_sub]
        simpa [hterm] using hineq'
      · simp [f, hfeas]
    have hlower : (Real.log Z : EReal) ≤ fenchelConjugate n f xStar := by
      let ξ0 : Fin n → ℝ := fun j => Real.exp (xStar j) / Z
      have hsoft : (0 ≤ ξ0) ∧ (∑ j, ξ0 j = 1) ∧ 0 < Z := by
        simpa [Z, ξ0] using (section16_softmax_mem_simplex (n := n) hn xStar)
      rcases hsoft with ⟨hξ0, hsum, hZpos⟩
      have hval :
          dotProduct ξ0 xStar - ∑ j, ξ0 j * Real.log (ξ0 j) = Real.log Z := by
        simpa [Z, ξ0] using
          (section16_entropy_rangeTerm_eq_log_sum_exp_at_softmax (n := n) hn xStar)
      unfold fenchelConjugate
      have hle' :
          ((ξ0 ⬝ᵥ xStar : ℝ) : EReal) - f ξ0 ≤
            sSup (Set.range fun ξ : Fin n → ℝ => ((ξ ⬝ᵥ xStar : ℝ) : EReal) - f ξ) := by
        exact le_sSup ⟨ξ0, rfl⟩
      have hterm :
          ((ξ0 ⬝ᵥ xStar : ℝ) : EReal) - f ξ0 = (Real.log Z : EReal) := by
        have hterm' :
            ((ξ0 ⬝ᵥ xStar : ℝ) : EReal) - f ξ0 =
              ((dotProduct ξ0 xStar - ∑ j, ξ0 j * Real.log (ξ0 j) : ℝ) : EReal) := by
          simp [f, hξ0, hsum, dotProduct, EReal.coe_sub]
        have hval' :
            ((dotProduct ξ0 xStar - ∑ j, ξ0 j * Real.log (ξ0 j) : ℝ) : EReal) =
              (Real.log Z : EReal) := by
          exact_mod_cast hval
        simpa [hterm'] using hval'
      simpa [hterm] using hle'
    have hEq : fenchelConjugate n f xStar = (Real.log Z : EReal) :=
      le_antisymm hupper hlower
    simpa [Z] using hEq
  simpa [f] using h

/-- The affine functional `x ↦ ⟪x,b⟫ - μ` is convex as an `EReal`-valued function. -/
lemma section16_convexFunctionOn_dotProduct_sub_const {n : ℕ} (b : Fin n → ℝ) (μ : ℝ) :
    ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun x => ((x ⬝ᵥ b - μ : ℝ) : EReal)) := by
  refine convexFunctionOn_of_convexOn_real (S := (Set.univ : Set (Fin n → ℝ))) ?_
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a c _ _ hac
  have hlin :
      (a • x + c • y) ⬝ᵥ b = a * (x ⬝ᵥ b) + c * (y ⬝ᵥ b) := by
    calc
      (a • x + c • y) ⬝ᵥ b = b ⬝ᵥ (a • x + c • y) := by
        exact dotProduct_comm (a • x + c • y) b
      _ = b ⬝ᵥ (a • x) + b ⬝ᵥ (c • y) := by
        exact dotProduct_add b (a • x) (c • y)
      _ = a * (x ⬝ᵥ b) + c * (y ⬝ᵥ b) := by
        simp [dotProduct_smul, smul_eq_mul, dotProduct_comm]
  have hcalc :
      a * (x ⬝ᵥ b - μ) + c * (y ⬝ᵥ b - μ) =
        a * (x ⬝ᵥ b) + c * (y ⬝ᵥ b) - μ := by
    calc
      a * (x ⬝ᵥ b - μ) + c * (y ⬝ᵥ b - μ) =
          a * (x ⬝ᵥ b) + c * (y ⬝ᵥ b) - (a + c) * μ := by ring
      _ = a * (x ⬝ᵥ b) + c * (y ⬝ᵥ b) - μ := by simp [hac]
  have h_eq :
      (a • x + c • y) ⬝ᵥ b - μ =
        a * (x ⬝ᵥ b - μ) + c * (y ⬝ᵥ b - μ) := by
    calc
      (a • x + c • y) ⬝ᵥ b - μ =
          a * (x ⬝ᵥ b) + c * (y ⬝ᵥ b) - μ := by
            simp [hlin]
      _ = a * (x ⬝ᵥ b - μ) + c * (y ⬝ᵥ b - μ) := by
            symm
            exact hcalc
  exact le_of_eq h_eq

/-- Affine minorants of the convex hull coincide with affine minorants of each family member. -/
lemma section16_affine_le_convexHullFunctionFamily_iff_forall_le {n : ℕ} {ι : Sort _}
    (f : ι → (Fin n → ℝ) → EReal) (b : Fin n → ℝ) (μ : ℝ) :
    (∀ x, ((x ⬝ᵥ b - μ : ℝ) : EReal) ≤ convexHullFunctionFamily f x) ↔
      (∀ i x, ((x ⬝ᵥ b - μ : ℝ) : EReal) ≤ f i x) := by
  classical
  have hminor :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (convexHullFunctionFamily f) ∧
        (∀ i, convexHullFunctionFamily f ≤ f i) ∧
        ∀ h : (Fin n → ℝ) → EReal,
          ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h →
          (∀ i, h ≤ f i) → h ≤ convexHullFunctionFamily f := by
    simpa using (convexHullFunctionFamily_greatest_convex_minorant (f := f))
  have hgi : ∀ i, convexHullFunctionFamily f ≤ f i := hminor.2.1
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => ((x ⬝ᵥ b - μ : ℝ) : EReal)) := by
    simpa using (section16_convexFunctionOn_dotProduct_sub_const (b := b) (μ := μ))
  constructor
  · intro hle i x
    exact le_trans (hle x) (hgi i x)
  · intro hforall
    have hforall' :
        ∀ i, (fun x => ((x ⬝ᵥ b - μ : ℝ) : EReal)) ≤ f i := by
      intro i x
      exact hforall i x
    have hle' :
        (fun x => ((x ⬝ᵥ b - μ : ℝ) : EReal)) ≤ convexHullFunctionFamily f :=
      hminor.2.2 _ hconv hforall'
    intro x
    exact hle' x

/-- The epigraph inequality for the convex hull reduces to the family componentwise. -/
lemma section16_fenchelConjugate_convexHullFunctionFamily_le_coe_iff_forall {n : ℕ} {ι : Sort _}
    (f : ι → (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) (μ : ℝ) :
    fenchelConjugate n (convexHullFunctionFamily f) xStar ≤ (μ : EReal) ↔
      ∀ i, fenchelConjugate n (f i) xStar ≤ (μ : EReal) := by
  constructor
  · intro hμ i
    have h_aff :
        ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ convexHullFunctionFamily f x :=
      (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := convexHullFunctionFamily f)
            (b := xStar) (μ := μ)).1 hμ
    have hforall :
        ∀ i x, ((x ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ f i x :=
      (section16_affine_le_convexHullFunctionFamily_iff_forall_le (f := f) (b := xStar)
            (μ := μ)).1 h_aff
    exact (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f i) (b := xStar)
        (μ := μ)).2 (hforall i)
  · intro hμ
    have hforall :
        ∀ i x, ((x ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ f i x := by
      intro i
      exact (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f i) (b := xStar)
        (μ := μ)).1 (hμ i)
    have h_aff :
        ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ convexHullFunctionFamily f x :=
      (section16_affine_le_convexHullFunctionFamily_iff_forall_le (f := f) (b := xStar)
            (μ := μ)).2 hforall
    exact (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := convexHullFunctionFamily f)
        (b := xStar) (μ := μ)).2 h_aff

/-- Nonempty families yield a non-`⊥` supremum of conjugates. -/
lemma section16_sSup_range_fenchelConjugate_ne_bot_of_nonempty {n : ℕ} {ι : Sort _} [Nonempty ι]
    (f : ι → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (xStar : Fin n → ℝ) :
    sSup (Set.range fun i => fenchelConjugate n (f i) xStar) ≠ (⊥ : EReal) := by
  classical
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  have hnotbot :
      fenchelConjugate n (f i0) xStar ≠ (⊥ : EReal) := by
    have hproper :=
      proper_fenchelConjugate_of_proper (n := n) (f := f i0) (hf i0)
    exact hproper.2.2 xStar (by trivial)
  intro hbot
  have hle :
      fenchelConjugate n (f i0) xStar ≤ (⊥ : EReal) := by
    have hle' :
        fenchelConjugate n (f i0) xStar ≤
          sSup (Set.range fun i => fenchelConjugate n (f i) xStar) := by
      exact le_sSup ⟨i0, rfl⟩
    simpa [hbot] using hle'
  exact hnotbot (le_bot_iff.mp hle)

/-- Theorem 16.5.1: Let `f i` be a proper convex function on `ℝ^n` for each `i` in an (arbitrary)
index set. Then the Fenchel conjugate of the convex hull of the family is the pointwise supremum
of the conjugates:

`(conv {f_i | i ∈ I})^* = sup {f_i^* | i ∈ I}`.

Here `conv {f_i | i ∈ I}` is represented by `convexHullFunctionFamily f`, and `f_i^*` is
`fenchelConjugate n (f i)`. -/
theorem section16_fenchelConjugate_convexHullFunctionFamily {n : ℕ} {ι : Sort _}
    (f : ι → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    fenchelConjugate n (convexHullFunctionFamily f) =
      fun xStar => sSup (Set.range fun i => fenchelConjugate n (f i) xStar) := by
  classical
  funext xStar
  by_cases hI : IsEmpty ι
  · haveI : IsEmpty ι := hI
    have hconv : convexHullFunctionFamily f = fun _ : Fin n → ℝ => (⊤ : EReal) := by
      funext x
      simp [convexHullFunctionFamily]
    have hrange :
        Set.range (fun i : ι => fenchelConjugate n (f i) xStar) = (∅ : Set EReal) := by
      simpa using
        (Set.range_eq_empty (f := fun i : ι => fenchelConjugate n (f i) xStar))
    have hleft :
        fenchelConjugate n (convexHullFunctionFamily f) xStar = (⊥ : EReal) := by
      simp [hconv, fenchelConjugate]
    have hright :
        sSup (Set.range fun i => fenchelConjugate n (f i) xStar) = (⊥ : EReal) := by
      simp [hrange]
    simp [hleft, hright]
  · haveI : Nonempty ι := (not_isEmpty_iff.1 hI)
    set s : EReal := sSup (Set.range fun i => fenchelConjugate n (f i) xStar) with hs
    have hsup_le :
        s ≤ fenchelConjugate n (convexHullFunctionFamily f) xStar := by
      have hminor :
          ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (convexHullFunctionFamily f) ∧
            (∀ i, convexHullFunctionFamily f ≤ f i) ∧
            ∀ h : (Fin n → ℝ) → EReal,
              ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h →
              (∀ i, h ≤ f i) → h ≤ convexHullFunctionFamily f := by
        simpa using (convexHullFunctionFamily_greatest_convex_minorant (f := f))
      have hgi : ∀ i, convexHullFunctionFamily f ≤ f i := hminor.2.1
      refine sSup_le ?_
      rintro _ ⟨i, rfl⟩
      have hanti := (fenchelConjugate_antitone n) (hgi i)
      exact hanti xStar
    have hle_sup :
        fenchelConjugate n (convexHullFunctionFamily f) xStar ≤ s := by
      by_cases htop : s = (⊤ : EReal)
      · simp [htop]
      · have hbot :
          s ≠ (⊥ : EReal) :=
          section16_sSup_range_fenchelConjugate_ne_bot_of_nonempty (f := f) hf xStar
        have hcoe : ((s.toReal) : EReal) = s := EReal.coe_toReal htop hbot
        have hforall :
            ∀ i, fenchelConjugate n (f i) xStar ≤ (s.toReal : EReal) := by
          intro i
          have hle :
              fenchelConjugate n (f i) xStar ≤ s := by
            exact le_sSup ⟨i, rfl⟩
          simpa [hcoe] using hle
        have hle_toReal :
            fenchelConjugate n (convexHullFunctionFamily f) xStar ≤ (s.toReal : EReal) :=
          (section16_fenchelConjugate_convexHullFunctionFamily_le_coe_iff_forall
                (f := f) (xStar := xStar) (μ := s.toReal)).2 hforall
        simpa [hcoe] using hle_toReal
    have hEq : fenchelConjugate n (convexHullFunctionFamily f) xStar = s :=
      le_antisymm hle_sup hsup_le
    simpa [hs] using hEq

end Section16
end Chap03
