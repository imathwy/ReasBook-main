/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part8

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise

/-- Taking the convex-function closure does not change the Fenchel conjugate. -/
lemma section16_fenchelConjugate_convexFunctionClosure_eq {n : Nat}
    (g : (Fin n → ℝ) → EReal) :
    fenchelConjugate n (convexFunctionClosure g) = fenchelConjugate n g := by
  simpa using (fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := g))

/-- The Fenchel conjugate is closed and convex. -/
lemma section16_closedConvexFunction_fenchelConjugate {n : Nat}
    (g : (Fin n → ℝ) → EReal) :
    ClosedConvexFunction (fenchelConjugate n g) := by
  have h := fenchelConjugate_closedConvex (n := n) (f := g)
  exact ⟨h.2, h.1⟩

/-- The recession function of a Fenchel conjugate is proper and positively homogeneous. -/
lemma section16_recessionFunction_fenchelConjugate_proper_posHom {n : Nat}
    (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (recessionFunction (fenchelConjugate n f)) ∧
      PositivelyHomogeneous (recessionFunction (fenchelConjugate n f)) := by
  classical
  have hsupp :
      supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) =
        recessionFunction (fenchelConjugate n f) := by
    simpa [recessionFunction] using
      (supportFunctionEReal_effectiveDomain_eq_recession_fenchelConjugate
        (n := n) (f := f) (hf := hf)
        (fStar0_plus := recessionFunction (fenchelConjugate n f))
        (by intro y; rfl))
  have hdom_ne :
      Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
    section13_effectiveDomain_nonempty_of_proper (n := n) (f := f) hf
  have hdom_conv :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
    have hconv_on : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := hf.1
    simpa using
      (effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f) (hf := hconv_on))
  have hsupp_props :=
    section13_supportFunctionEReal_closedProperConvex_posHom
      (n := n) (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) hdom_ne hdom_conv
  refine ⟨?_, ?_⟩
  · simpa [hsupp] using hsupp_props.2.1
  · simpa [hsupp] using hsupp_props.2.2

/-- The epigraph recession cone of a Fenchel conjugate is the epigraph of its recession function. -/
lemma section16_recessionCone_epigraph_eq_epigraph_recessionFunction_fenchelConjugate {n : Nat}
    (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    Set.recessionCone (epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) =
      epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction (fenchelConjugate n f)) := by
  classical
  let g : Fin 1 → (Fin n → ℝ) → EReal := fun _ => fenchelConjugate n f
  have hconv : ∀ i : Fin 1,
      Convex ℝ (epigraph (Set.univ : Set (Fin n → ℝ)) (g i)) := by
    intro i
    have hconvStar : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
      have hconv : ConvexFunction (fenchelConjugate n f) :=
        (fenchelConjugate_closedConvex (n := n) (f := f)).2
      simpa [ConvexFunction] using hconv
    simpa [g] using (convex_epigraph_of_convexFunctionOn (hf := hconvStar))
  have hproper : ∀ i : Fin 1,
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (g i) := by
    intro i
    simpa [g] using (proper_fenchelConjugate_of_proper (n := n) (f := f) hf)
  have hk :
      ∀ (i : Fin 1) (y : Fin n → ℝ),
        recessionFunction (fenchelConjugate n f) y =
          sSup { r : EReal | ∃ x : Fin n → ℝ, r = g i (x + y) - g i x } := by
    intro i y
    simpa [g] using
      (section16_recessionFunction_eq_sSup_unrestricted (f := fenchelConjugate n f) y)
  have hrec :=
    recessionCone_epigraph_eq_epigraph_k (f := g)
      (k := recessionFunction (fenchelConjugate n f)) hconv hproper hk
  simpa [g] using hrec (i := 0)

/-- Closedness and attainment for the infimal convolution of conjugates under the `ri` condition. -/
lemma section16_infimalConvolutionFamily_fenchelConjugate_closed_and_attained_of_nonempty_iInter_ri
    {n m : Nat} (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hri :
      Set.Nonempty
        (⋂ i : Fin m,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))) :
    (convexFunctionClosure (infimalConvolutionFamily fun i => fenchelConjugate n (f i)) =
        infimalConvolutionFamily fun i => fenchelConjugate n (f i)) ∧
      ∀ xStar : Fin n → ℝ,
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar = ⊤ ∨
          ∃ xStarFamily : Fin m → Fin n → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
                infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar := by
  classical
  let fStar : Fin m → (Fin n → ℝ) → EReal := fun i => fenchelConjugate n (f i)
  let f0_plus : Fin m → (Fin n → ℝ) → EReal := fun i => recessionFunction (fStar i)
  have hnot_exists :
      ¬ ∃ xStar : Fin m → Fin n → ℝ,
          (∑ i, xStar i) = 0 ∧
            (∑ i, f0_plus i (xStar i)) ≤ (0 : EReal) ∧
              (∑ i, f0_plus i (-xStar i)) > (0 : EReal) := by
    simpa [fStar, f0_plus] using
      (section16_nonempty_iInter_ri_effectiveDomain_iff_not_exists_sum_eq_zero_recession_ineq
        (f := f) hf).2 hri
  have hzero :
      ∀ z : Fin m → Fin n → ℝ,
        (∑ i, f0_plus i (z i)) ≤ (0 : EReal) →
        (∑ i, f0_plus i (-(z i))) > (0 : EReal) →
        (∑ i, z i) ≠ (0 : Fin n → ℝ) := by
    intro z hzle hzgt hsum
    exact (hnot_exists ⟨z, hsum, hzle, hzgt⟩).elim
  cases m with
  | zero =>
      have hInf :
          infimalConvolutionFamily (fun i : Fin 0 => fenchelConjugate n (f i)) =
            indicatorFunction ({0} : Set (Fin n → ℝ)) := by
        funext xStar
        by_cases hx : xStar = 0
        · subst hx
          simp [infimalConvolutionFamily, indicatorFunction, Set.mem_singleton_iff]
        · simp [infimalConvolutionFamily, indicatorFunction, Set.mem_singleton_iff, hx, eq_comm]
      have hclosed_indicator :
          ClosedConvexFunction (indicatorFunction ({0} : Set (Fin n → ℝ))) := by
        have h :=
          closedConvexFunction_indicator_neg (n := n) (C := ({0} : Set (Fin n → ℝ)))
            (by simp)
            (by simp)
            (by simp)
        simpa using h.1
      have hnotbot :
          ∀ x : Fin n → ℝ, indicatorFunction ({0} : Set (Fin n → ℝ)) x ≠ (⊥ : EReal) := by
        intro x
        by_cases hx : x = 0
        · simp [indicatorFunction, Set.mem_singleton_iff, hx]
        · simp [indicatorFunction, Set.mem_singleton_iff, hx]
      have hclosure_indicator :
          convexFunctionClosure (indicatorFunction ({0} : Set (Fin n → ℝ))) =
            indicatorFunction ({0} : Set (Fin n → ℝ)) :=
        convexFunctionClosure_eq_of_closedConvexFunction
          (f := indicatorFunction ({0} : Set (Fin n → ℝ))) hclosed_indicator hnotbot
      have hclosure :
          convexFunctionClosure
              (infimalConvolutionFamily (fun i : Fin 0 => fenchelConjugate n (f i))) =
            infimalConvolutionFamily (fun i : Fin 0 => fenchelConjugate n (f i)) := by
        simpa [hInf] using hclosure_indicator
      refine ⟨?_, ?_⟩
      · simpa [hInf] using hclosure
      · intro xStar
        by_cases hx : xStar = 0
        · subst hx
          right
          refine ⟨fun _ => (0 : Fin n → ℝ), ?_, ?_⟩
          · simp
          · simp [hInf, indicatorFunction, Set.mem_singleton_iff]
        · left
          simp [hInf, indicatorFunction, Set.mem_singleton_iff, hx]
  | succ m' =>
      have hm : 0 < Nat.succ m' := Nat.succ_pos m'
      have hclosed :
          ∀ i : Fin (Nat.succ m'),
            ClosedConvexFunction (fStar i) := by
        intro i
        simpa [fStar] using
          (section16_closedConvexFunction_fenchelConjugate (n := n) (g := f i))
      have hproper :
          ∀ i : Fin (Nat.succ m'),
            ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fStar i) := by
        intro i
        simpa [fStar] using
          (proper_fenchelConjugate_of_proper (n := n) (f := f i) (hf i))
      have hrec :
          ∀ i : Fin (Nat.succ m'),
            Set.recessionCone (epigraph (Set.univ : Set (Fin n → ℝ)) (fStar i)) =
              epigraph (Set.univ : Set (Fin n → ℝ)) (f0_plus i) := by
        intro i
        simpa [fStar, f0_plus] using
          (section16_recessionCone_epigraph_eq_epigraph_recessionFunction_fenchelConjugate
            (n := n) (f := f i) (hf := hf i))
      have hprops :
          ∀ i : Fin (Nat.succ m'),
            ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f0_plus i) ∧
              PositivelyHomogeneous (f0_plus i) := by
        intro i
        simpa [fStar, f0_plus] using
          (section16_recessionFunction_fenchelConjugate_proper_posHom (n := n) (f := f i) (hf := hf i))
      have hproper0 :
          ∀ i : Fin (Nat.succ m'),
            ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f0_plus i) := by
        intro i
        exact (hprops i).1
      have hpos :
          ∀ i : Fin (Nat.succ m'),
            PositivelyHomogeneous (f0_plus i) := by
        intro i
        exact (hprops i).2
      let fInf : (Fin n → ℝ) → EReal := infimalConvolutionFamily fStar
      have hmain :=
        infimalConvolutionFamily_closed_proper_convex_recession
          (f := fStar) (f0_plus := f0_plus)
          hclosed hproper hrec hpos hproper0 hzero hm
      have hclosedInf : ClosedConvexFunction fInf := by
        simpa [fInf] using hmain.1
      have hproperInf :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fInf := by
        simpa [fInf] using hmain.2.1
      have hnotbot : ∀ x : Fin n → ℝ, fInf x ≠ (⊥ : EReal) := by
        intro x
        exact hproperInf.2.2 x (by simp)
      have hclosure : convexFunctionClosure fInf = fInf :=
        convexFunctionClosure_eq_of_closedConvexFunction (f := fInf) hclosedInf hnotbot
      have hatt :
          ∀ x : Fin n → ℝ,
            ∃ x' : Fin (Nat.succ m') → Fin n → ℝ,
              (∑ i, x' i) = x ∧ fInf x = ∑ i, fStar i (x' i) := by
        simpa [fInf, fStar] using hmain.2.2.1
      refine ⟨?_, ?_⟩
      · simpa [fInf] using hclosure
      · intro xStar
        right
        rcases hatt xStar with ⟨xStarFamily, hsum, hval⟩
        refine ⟨xStarFamily, hsum, ?_⟩
        simpa [fInf, fStar] using hval.symm

end Section16
end Chap03
