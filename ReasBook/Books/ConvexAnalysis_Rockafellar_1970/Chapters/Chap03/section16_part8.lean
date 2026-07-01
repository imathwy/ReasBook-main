/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part7

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise

/-- Taking the convex-function closure does not change the Fenchel conjugate. -/
private lemma section16_fenchelConjugate_convexFunctionClosure_eq {n : Nat}
    (g : (Fin n → ℝ) → EReal) :
    fenchelConjugate n (convexFunctionClosure g) = fenchelConjugate n g := by
  simpa using (fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := g))

/-- The Fenchel conjugate is closed and convex. -/
private lemma section16_closedConvexFunction_fenchelConjugate {n : Nat}
    (g : (Fin n → ℝ) → EReal) :
    ClosedConvexFunction (fenchelConjugate n g) := by
  have h := fenchelConjugate_closedConvex (n := n) (f := g)
  exact ⟨h.2, h.1⟩

/-- The recession function of a Fenchel conjugate is proper and positively homogeneous. -/
private lemma section16_recessionFunction_fenchelConjugate_proper_posHom {n : Nat}
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
private lemma section16_recessionCone_epigraph_eq_epigraph_recessionFunction_fenchelConjugate
    {n : Nat} (f : (Fin n → ℝ) → EReal)
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
private lemma section16_infimalConvolutionFamily_fenchelConjugate_closed_and_attained_of_nonempty_iInter_ri
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

/-- Remove both closures under the `ri` hypothesis and record attainment. -/
private lemma section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain_proof_step
    {n m : Nat} (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hri :
      Set.Nonempty
        (⋂ i : Fin m,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))) :
    (fenchelConjugate n (fun x => ∑ i, f i x) =
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) ∧
      ∀ xStar : Fin n → ℝ,
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar = ⊤ ∨
          ∃ xStarFamily : Fin m → Fin n → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
                infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar := by
  classical
  have hsum :
      (fun x => ∑ i, convexFunctionClosure (f i) x) =
        convexFunctionClosure (fun x => ∑ i, f i x) :=
    section16_sum_convexFunctionClosure_eq_convexFunctionClosure_sum_of_nonempty_iInter_ri_effectiveDomain
      (f := f) hf hri
  have hEq0 :
      fenchelConjugate n (convexFunctionClosure (fun x => ∑ i, f i x)) =
        convexFunctionClosure (infimalConvolutionFamily fun i => fenchelConjugate n (f i)) := by
    simpa [hsum] using
      (section16_fenchelConjugate_sum_convexFunctionClosure_eq_convexFunctionClosure_infimalConvolutionFamily
        (f := f) hf)
  have hEq1 :
      fenchelConjugate n (fun x => ∑ i, f i x) =
        convexFunctionClosure (infimalConvolutionFamily fun i => fenchelConjugate n (f i)) := by
    calc
      fenchelConjugate n (fun x => ∑ i, f i x) =
          fenchelConjugate n (convexFunctionClosure (fun x => ∑ i, f i x)) := by
            symm
            simpa using
              (section16_fenchelConjugate_convexFunctionClosure_eq
                (n := n) (g := fun x => ∑ i, f i x))
      _ = convexFunctionClosure (infimalConvolutionFamily fun i => fenchelConjugate n (f i)) := hEq0
  have hclosed_att :
      (convexFunctionClosure (infimalConvolutionFamily fun i => fenchelConjugate n (f i)) =
          infimalConvolutionFamily fun i => fenchelConjugate n (f i)) ∧
        ∀ xStar : Fin n → ℝ,
          infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar = ⊤ ∨
            ∃ xStarFamily : Fin m → Fin n → ℝ,
              (∑ i, xStarFamily i) = xStar ∧
                (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
                  infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar :=
    section16_infimalConvolutionFamily_fenchelConjugate_closed_and_attained_of_nonempty_iInter_ri
      (f := f) hf hri
  have hEq2 :
      fenchelConjugate n (fun x => ∑ i, f i x) =
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) := by
    simpa [hclosed_att.1] using hEq1
  exact ⟨hEq2, hclosed_att.2⟩

/-- Theorem 16.4.3 (sum vs infimal convolution without closures). -/
private theorem section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain
    {n m : Nat} (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hri :
      Set.Nonempty
        (⋂ i : Fin m,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))) :
    (fenchelConjugate n (fun x => ∑ i, f i x) =
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) ∧
      ∀ xStar : Fin n → ℝ,
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar = ⊤ ∨
          ∃ xStarFamily : Fin m → Fin n → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
                infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar := by
  simpa using
    (section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain_proof_step
      (f := f) hf hri)

/-- Specializing Theorem 16.4.3 to indicator functions yields the support-function identity and
the usual attainment/`⊤` disjunction. -/
lemma section16_supportFunctionEReal_iInter_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_proof_step
    {n m : Nat} (C : Fin m → Set (Fin n → ℝ)) (hC : ∀ i, Convex ℝ (C i))
    (hCne : ∀ i, (C i).Nonempty)
    (hri :
      Set.Nonempty
        (⋂ i : Fin m,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' (C i)))) :
    supportFunctionEReal (⋂ i, C i) =
        infimalConvolutionFamily (fun i => supportFunctionEReal (C i)) ∧
      ∀ xStar : Fin n → ℝ,
        infimalConvolutionFamily (fun i => supportFunctionEReal (C i)) xStar = ⊤ ∨
          ∃ xStarFamily : Fin m → Fin n → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              (∑ i, supportFunctionEReal (C i) (xStarFamily i)) =
                infimalConvolutionFamily (fun i => supportFunctionEReal (C i)) xStar := by
  classical
  let f : Fin m → (Fin n → ℝ) → EReal := fun i => indicatorFunction (C i)
  have hproper :
      ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i) := by
    intro i
    simpa [f] using
      (properConvexFunctionOn_indicator_of_convex_of_nonempty (C := C i) (hC i) (hCne i))
  have hri' :
      Set.Nonempty
        (⋂ i : Fin m,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) := by
    simpa [f, effectiveDomain_indicatorFunction_eq] using hri
  have hmain :=
    section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain
      (f := f) hproper hri'
  have hsum : (fun x => ∑ i, f i x) = indicatorFunction (⋂ i, C i) := by
    simpa [f] using
      (section16_sum_indicatorFunction_eq_indicatorFunction_iInter (C := C))
  have hEq :
      supportFunctionEReal (⋂ i, C i) =
        infimalConvolutionFamily (fun i => supportFunctionEReal (C i)) := by
    have hEq' :
        fenchelConjugate n (indicatorFunction (⋂ i, C i)) =
          infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) := by
      simpa [hsum] using hmain.1
    simpa [f, section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal] using hEq'
  have hdisj :
      ∀ xStar : Fin n → ℝ,
        infimalConvolutionFamily (fun i => supportFunctionEReal (C i)) xStar = ⊤ ∨
          ∃ xStarFamily : Fin m → Fin n → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              (∑ i, supportFunctionEReal (C i) (xStarFamily i)) =
                infimalConvolutionFamily (fun i => supportFunctionEReal (C i)) xStar := by
    intro xStar
    simpa [f, section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal] using
      hmain.2 xStar
  exact ⟨hEq, hdisj⟩

/-- When `m > 0`, any `xStar` admits a family summing to `xStar`. -/
lemma section16_exists_xStarFamily_sum_eq_of_pos {n m : Nat} (hm : 0 < m)
    (xStar : Fin n → ℝ) :
    ∃ xStarFamily : Fin m → Fin n → ℝ, (∑ i, xStarFamily i) = xStar := by
  classical
  let i0 : Fin m := ⟨0, hm⟩
  let xStarFamily : Fin m → Fin n → ℝ := fun i => if i = i0 then xStar else 0
  refine ⟨xStarFamily, ?_⟩
  simp [xStarFamily]

/-- If the infimal convolution is `⊤` and `m > 0`, any fixed decomposition attains `⊤`. -/
lemma section16_attainment_when_infimalConvolutionFamily_eq_top_of_pos {n m : Nat} (hm : 0 < m)
    (g : Fin m → (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ)
    (htop : infimalConvolutionFamily g xStar = ⊤) :
    ∃ xStarFamily : Fin m → Fin n → ℝ,
      (∑ i, xStarFamily i) = xStar ∧
        (∑ i, g i (xStarFamily i)) = infimalConvolutionFamily g xStar := by
  classical
  obtain ⟨xStarFamily, hsum⟩ :=
    section16_exists_xStarFamily_sum_eq_of_pos (n := n) (m := m) hm xStar
  refine ⟨xStarFamily, hsum, ?_⟩
  have hle : infimalConvolutionFamily g xStar ≤ ∑ i, g i (xStarFamily i) := by
    unfold infimalConvolutionFamily
    exact sInf_le ⟨xStarFamily, hsum, rfl⟩
  have htop' : (⊤ : EReal) ≤ ∑ i, g i (xStarFamily i) := by
    simpa [htop] using hle
  have hsum_top : (∑ i, g i (xStarFamily i)) = (⊤ : EReal) :=
    le_antisymm le_top htop'
  simpa [htop] using hsum_top

/-- Corollary 16.4.1.3: Let `C₁, …, Cₘ` be non-empty convex sets in `ℝⁿ`. If the sets `ri Cᵢ`
have a point in common, then the closure operation can be omitted from Corollary 16.4.1.2, and

`δ^*(· | C₁ ∩ ⋯ ∩ Cₘ) = inf { δ^*(· | C₁) + ⋯ + δ^*(· | Cₘ) | x₁⋆ + ⋯ + xₘ⋆ = x⋆ }`,

where for each `x⋆` the infimum is attained.

In this development, `δ^*` is `supportFunctionEReal`, `ri` is `euclideanRelativeInterior`, and the
right-hand side is modeled by `infimalConvolutionFamily`. -/
theorem section16_supportFunctionEReal_iInter_eq_infimalConvolutionFamily_of_nonempty_iInter_ri
    {n m : Nat} (C : Fin m → Set (Fin n → ℝ)) (hC : ∀ i, Convex ℝ (C i))
    (hCne : ∀ i, (C i).Nonempty)
    (hri :
      Set.Nonempty
        (⋂ i : Fin m,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' (C i))))
    (hm : 0 < m) :
    supportFunctionEReal (⋂ i, C i) = infimalConvolutionFamily (fun i => supportFunctionEReal (C i)) ∧
      ∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin m → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            (∑ i, supportFunctionEReal (C i) (xStarFamily i)) =
              infimalConvolutionFamily (fun i => supportFunctionEReal (C i)) xStar := by
  classical
  have hmain :=
    section16_supportFunctionEReal_iInter_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_proof_step
      (C := C) hC hCne hri
  refine ⟨hmain.1, ?_⟩
  intro xStar
  rcases hmain.2 xStar with htop | hatt
  · exact
      section16_attainment_when_infimalConvolutionFamily_eq_top_of_pos (n := n) (m := m) hm
        (g := fun i => supportFunctionEReal (C i)) (xStar := xStar) htop
  · exact hatt

end Section16
end Chap03
