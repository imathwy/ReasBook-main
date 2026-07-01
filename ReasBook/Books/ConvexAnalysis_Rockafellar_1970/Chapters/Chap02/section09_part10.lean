/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section08_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section08_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part9

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology
open scoped RealInnerProductSpace
open Filter

section Chap02
section Section09

/-- Precomposition with a linear map preserves closedness of convex functions. -/
lemma closedConvexFunction_precomp_linearMap {n m : Nat} {g : (Fin m → Real) → EReal}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) :
    ClosedConvexFunction g → ClosedConvexFunction (fun x => g (A x)) := by
  intro hg
  have hconv_on : ConvexFunctionOn (Set.univ : Set (Fin m → Real)) g := by
    simpa [ConvexFunction] using hg.1
  have hconv_on' :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => g (A x)) :=
    convexFunctionOn_precomp_linearMap (A := A) g hconv_on
  have hconv : ConvexFunction (fun x => g (A x)) := by
    simpa [ConvexFunction] using hconv_on'
  have hls : LowerSemicontinuous (fun x => g (A x)) :=
    hg.2.comp A.continuous_of_finiteDimensional
  exact ⟨hconv, hls⟩

/-- Effective domain of a precomposition is a preimage. -/
lemma effectiveDomain_precomp_linearMap {n m : Nat} {g : (Fin m → Real) → EReal}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) :
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x)) =
      A ⁻¹' effectiveDomain (Set.univ : Set (Fin m → Real)) g := by
  ext x
  simp [effectiveDomain_eq]

/-- Relative interior of the effective domain under a linear preimage. -/
lemma ri_effectiveDomain_preimage_linearMap
    {n m : Nat} {g : (Fin m → Real) → EReal}
    (hgproper : ProperConvexFunctionOn (Set.univ : Set (Fin m → Real)) g)
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (hri :
      ∃ x : Fin n → Real,
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm (A x) ∈
          euclideanRelativeInterior m
            (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm
              (effectiveDomain (Set.univ : Set (Fin m → Real)) g))) :
    let e_n := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
    let e_m := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m))
    let A_e : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m) :=
      (e_m.symm.toLinearMap).comp (A.comp e_n.toLinearMap)
    euclideanRelativeInterior n
        (Set.image e_n.symm
          (effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x)))) =
      A_e ⁻¹' euclideanRelativeInterior m
        (Set.image e_m.symm (effectiveDomain (Set.univ : Set (Fin m → Real)) g)) := by
  classical
  intro e_n e_m A_e
  have hconv_dom :
      Convex Real (effectiveDomain (Set.univ : Set (Fin m → Real)) g) :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin m → Real))) (f := g) hgproper.1
  have hconv_C :
      Convex Real
        (Set.image e_m.symm (effectiveDomain (Set.univ : Set (Fin m → Real)) g)) := by
    simpa using hconv_dom.linear_image (e_m.symm.toLinearMap)
  have hri' :
      (A_e ⁻¹' euclideanRelativeInterior m
        (Set.image e_m.symm (effectiveDomain (Set.univ : Set (Fin m → Real)) g))).Nonempty := by
    rcases hri with ⟨x, hx⟩
    refine ⟨e_n.symm x, ?_⟩
    simpa [A_e, e_n, e_m] using hx
  have hpre :
      A_e ⁻¹' Set.image e_m.symm (effectiveDomain (Set.univ : Set (Fin m → Real)) g) =
        Set.image e_n.symm
          (effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x))) := by
    have himage_m :
        Set.image e_m.symm (effectiveDomain (Set.univ : Set (Fin m → Real)) g) =
          e_m ⁻¹' effectiveDomain (Set.univ : Set (Fin m → Real)) g := by
      simpa using
        (ContinuousLinearEquiv.image_eq_preimage_symm
          (e := e_m.symm)
          (s := effectiveDomain (Set.univ : Set (Fin m → Real)) g))
    have himage_n :
        Set.image e_n.symm
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x))) =
          e_n ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x)) := by
      simpa using
        (ContinuousLinearEquiv.image_eq_preimage_symm
          (e := e_n.symm)
          (s := effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x))))
    calc
      A_e ⁻¹' Set.image e_m.symm (effectiveDomain (Set.univ : Set (Fin m → Real)) g) =
          A_e ⁻¹' (e_m ⁻¹' effectiveDomain (Set.univ : Set (Fin m → Real)) g) := by
            simp [himage_m]
      _ = (fun y => e_m (A_e y)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → Real)) g := by
            simp [Set.preimage_preimage]
      _ = (fun y => A (e_n y)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → Real)) g := by
            ext y
            simp [A_e, LinearMap.comp_apply]
      _ = e_n ⁻¹' (A ⁻¹' effectiveDomain (Set.univ : Set (Fin m → Real)) g) := by
            simp [Set.preimage_preimage]
      _ = e_n ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x)) := by
            simp [effectiveDomain_precomp_linearMap (A := A)]
      _ = Set.image e_n.symm
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x))) := by
            simp [himage_n]
  have hri_eq :=
    (euclideanRelativeInterior_preimage_linearMap_eq_and_closure_preimage
      (n := n) (m := m) (A := A_e)
      (C := Set.image e_m.symm (effectiveDomain (Set.univ : Set (Fin m → Real)) g))
      hconv_C hri').1
  simpa [hpre] using hri_eq

/-- Relative interior of the effective domain in preimage form under a linear map. -/
lemma ri_effectiveDomain_preimage_linearMap_preimage
    {n m : Nat} {g : (Fin m → Real) → EReal}
    (hgproper : ProperConvexFunctionOn (Set.univ : Set (Fin m → Real)) g)
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (hri :
      ∃ x : Fin n → Real,
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm (A x) ∈
          euclideanRelativeInterior m
            (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm
              (effectiveDomain (Set.univ : Set (Fin m → Real)) g))) :
    let e_n := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
    let e_m := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m))
    let A_e : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m) :=
      (e_m.symm.toLinearMap).comp (A.comp e_n.toLinearMap)
    euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x))) =
      A_e ⁻¹' euclideanRelativeInterior m
        ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin m → Real)) g) := by
  classical
  intro e_n e_m A_e
  have hri' :
      euclideanRelativeInterior n
          (Set.image e_n.symm
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x)))) =
        A_e ⁻¹' euclideanRelativeInterior m
          (Set.image e_m.symm (effectiveDomain (Set.univ : Set (Fin m → Real)) g)) := by
    simpa [e_n, e_m, A_e] using
      (ri_effectiveDomain_preimage_linearMap (hgproper := hgproper) (A := A) hri)
  have himage_n :
      Set.image e_n.symm
          (effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x))) =
        e_n ⁻¹' effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x)) := by
    simpa using
      (ContinuousLinearEquiv.image_eq_preimage_symm
        (e := e_n.symm)
        (s := effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x))))
  have himage_m :
      Set.image e_m.symm
          (effectiveDomain (Set.univ : Set (Fin m → Real)) g) =
        e_m ⁻¹' effectiveDomain (Set.univ : Set (Fin m → Real)) g := by
    simpa using
      (ContinuousLinearEquiv.image_eq_preimage_symm
        (e := e_m.symm)
        (s := effectiveDomain (Set.univ : Set (Fin m → Real)) g))
  simpa [himage_n, himage_m] using hri'

/-- Relative interior of the effective domain is preserved by convex closure. -/
lemma ri_effectiveDomain_closure_eq {m : Nat} {g : (Fin m → Real) → EReal}
    (hgproper : ProperConvexFunctionOn (Set.univ : Set (Fin m → Real)) g) :
    euclideanRelativeInterior m
        ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin m → Real)) (convexFunctionClosure g)) =
      euclideanRelativeInterior m
        ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin m → Real)) g) := by
  simpa using
    (convexFunctionClosure_effectiveDomain_subset_relativeBoundary_and_same_closure_ri_dim
      (f := g) hgproper).2.2.2.1

/-- Closure commutes with linear precomposition under a relative-interior preimage point. -/
lemma convexFunctionClosure_precomp_linearMap_eq
    {n m : Nat} {g : (Fin m → Real) → EReal}
    (hgproper : ProperConvexFunctionOn (Set.univ : Set (Fin m → Real)) g)
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (hri :
      ∃ x : Fin n → Real,
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm (A x) ∈
          euclideanRelativeInterior m
            (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm
              (effectiveDomain (Set.univ : Set (Fin m → Real)) g))) :
    convexFunctionClosure (fun x => g (A x)) = fun x => convexFunctionClosure g (A x) := by
  classical
  let e_n := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  let e_m := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m))
  let A_e : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m) :=
    (e_m.symm.toLinearMap).comp (A.comp e_n.toLinearMap)
  have hconv_on : ConvexFunctionOn (Set.univ : Set (Fin m → Real)) g := hgproper.1
  have hconvA_on :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => g (A x)) :=
    convexFunctionOn_precomp_linearMap (A := A) g hconv_on
  have hconvA : ConvexFunction (fun x => g (A x)) := by
    simpa [ConvexFunction] using hconvA_on
  have hproper_cl :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → Real)) (convexFunctionClosure g) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri (f := g) hgproper).1.2
  have hconv_cl_on :
      ConvexFunctionOn (Set.univ : Set (Fin m → Real)) (convexFunctionClosure g) :=
    hproper_cl.1
  have hconv_clA_on :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun x => convexFunctionClosure g (A x)) :=
    convexFunctionOn_precomp_linearMap (A := A) (convexFunctionClosure g) hconv_cl_on
  have hconv_clA : ConvexFunction (fun x => convexFunctionClosure g (A x)) := by
    simpa [ConvexFunction] using hconv_clA_on
  have hri_pre :
      euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x))) =
        A_e ⁻¹' euclideanRelativeInterior m
          ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → Real)) g) := by
    simpa [e_n, e_m, A_e] using
      (ri_effectiveDomain_preimage_linearMap_preimage (hgproper := hgproper) (A := A) hri)
  have hri_cl :
      euclideanRelativeInterior m
          ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → Real)) (convexFunctionClosure g)) =
        euclideanRelativeInterior m
          ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → Real)) g) :=
    ri_effectiveDomain_closure_eq (hgproper := hgproper)
  have hri_closure :
      ∃ x : Fin n → Real,
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm (A x) ∈
          euclideanRelativeInterior m
            (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm
              (effectiveDomain (Set.univ : Set (Fin m → Real)) (convexFunctionClosure g))) := by
    rcases hri with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have himage_m :
        Set.image e_m.symm
            (effectiveDomain (Set.univ : Set (Fin m → Real)) g) =
          ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → Real)) g) := by
      simpa [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using
        (ContinuousLinearEquiv.image_eq_preimage_symm
          (e := e_m.symm)
          (s := effectiveDomain (Set.univ : Set (Fin m → Real)) g))
    have himage_m_cl :
        Set.image e_m.symm
            (effectiveDomain (Set.univ : Set (Fin m → Real)) (convexFunctionClosure g)) =
          ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → Real)) (convexFunctionClosure g)) := by
      simpa [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using
        (ContinuousLinearEquiv.image_eq_preimage_symm
          (e := e_m.symm)
          (s := effectiveDomain (Set.univ : Set (Fin m → Real)) (convexFunctionClosure g)))
    have hx_pre :
        e_m.symm (A x) ∈
          euclideanRelativeInterior m
            ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → Real)) g) := by
      have hx' :
          e_m.symm (A x) ∈
            euclideanRelativeInterior m
              (Set.image e_m.symm
                (effectiveDomain (Set.univ : Set (Fin m → Real)) g)) := by
        simpa using hx
      simpa [himage_m] using hx'
    have hx_pre_cl :
        e_m.symm (A x) ∈
          euclideanRelativeInterior m
            ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → Real)) (convexFunctionClosure g)) := by
      simpa [hri_cl] using hx_pre
    simpa [←himage_m_cl] using hx_pre_cl
  have hri_pre_cl :
      euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real))
              (fun x => convexFunctionClosure g (A x))) =
        A_e ⁻¹' euclideanRelativeInterior m
          ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → Real)) (convexFunctionClosure g)) := by
    simpa [e_n, e_m, A_e] using
      (ri_effectiveDomain_preimage_linearMap_preimage
        (hgproper := hproper_cl) (A := A) hri_closure)
  have hri_eq :
      euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x))) =
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real))
              (fun x => convexFunctionClosure g (A x))) := by
    calc
      euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x))) =
          A_e ⁻¹' euclideanRelativeInterior m
            ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → Real)) g) := hri_pre
      _ = A_e ⁻¹' euclideanRelativeInterior m
            ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → Real)) (convexFunctionClosure g)) := by
            simpa using (congrArg (fun s => A_e ⁻¹' s) hri_cl.symm)
      _ = euclideanRelativeInterior n
            ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → Real))
                (fun x => convexFunctionClosure g (A x))) := by
            symm
            exact hri_pre_cl
  have hagree :
      ∀ x ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => g (A x))),
        (fun x => g (A x)) x = (fun x => convexFunctionClosure g (A x)) x := by
    intro x hx
    have hx' :
        x ∈ A_e ⁻¹' euclideanRelativeInterior m
          ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → Real)) g) := by
      simpa [hri_pre] using hx
    have hxA :
        A_e x ∈ euclideanRelativeInterior m
          ((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → Real)) g) := by
      simpa [Set.mem_preimage] using hx'
    have hcl := convexFunctionClosure_eq_on_ri (f := g) hgproper (A_e x) hxA
    simpa [A_e, e_n, e_m] using hcl.symm
  have hcl_eq :
      convexFunctionClosure (fun x => g (A x)) =
        convexFunctionClosure (fun x => convexFunctionClosure g (A x)) :=
    convexFunctionClosure_eq_of_agree_on_ri_effectiveDomain
      (n := n) (f := fun x => g (A x))
      (g := fun x => convexFunctionClosure g (A x))
      hconvA hconv_clA hri_eq hagree
  have hclosed_cl :
      ClosedConvexFunction (convexFunctionClosure g) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri (f := g) hgproper).1.1
  have hclosed_clA :
      ClosedConvexFunction (fun x => convexFunctionClosure g (A x)) := by
    simpa using
      (closedConvexFunction_precomp_linearMap (A := A) (g := convexFunctionClosure g) hclosed_cl)
  have hbot_clA :
      ∀ x, (fun x => convexFunctionClosure g (A x)) x ≠ (⊥ : EReal) := by
    intro x
    have hbot := hproper_cl.2.2 (A x) (by simp)
    simpa using hbot
  have hclA :
      convexFunctionClosure (fun x => convexFunctionClosure g (A x)) =
        fun x => convexFunctionClosure g (A x) :=
    convexFunctionClosure_eq_of_closedConvexFunction (f := fun x => convexFunctionClosure g (A x))
      hclosed_clA hbot_clA
  calc
    convexFunctionClosure (fun x => g (A x)) =
        convexFunctionClosure (fun x => convexFunctionClosure g (A x)) := hcl_eq
    _ = fun x => convexFunctionClosure g (A x) := hclA

/-- Theorem 9.5. Let `A` be a linear transformation from `ℝ^n` to `ℝ^m`, and let `g` be a
proper convex function on `ℝ^m` such that `g ∘ A` is not identically `+∞`. If `g` is closed,
then `g ∘ A` is closed and `(g ∘ A)0^+ = (g0^+) ∘ A`. If `g` is not closed, but `A x` lies in
`ri (dom g)` for some `x`, then `cl (g ∘ A) = (cl g) ∘ A`. -/
theorem linearMap_comp_closed_recession_and_closure
    {n m : Nat} {g g0_plus : (Fin m → Real) → EReal}
    (hgproper : ProperConvexFunctionOn (Set.univ : Set (Fin m → Real)) g)
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (_hfinite : ∃ x : Fin n → Real, g (A x) ≠ (⊤ : EReal)) :
    let gA : (Fin n → Real) → EReal := fun x => g (A x)
    let gA0_plus : (Fin n → Real) → EReal := fun x => g0_plus (A x)
    (ClosedConvexFunction g →
        ClosedConvexFunction gA ∧ gA0_plus = fun x => g0_plus (A x)) ∧
      ((¬ ClosedConvexFunction g) →
        (∃ x : Fin n → Real,
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm (A x) ∈
            euclideanRelativeInterior m
              (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm
                (effectiveDomain (Set.univ : Set (Fin m → Real)) g))) →
        convexFunctionClosure gA = fun x => convexFunctionClosure g (A x)) := by
  intro gA gA0_plus
  constructor
  · intro hclosed
    have hclosedA : ClosedConvexFunction gA := by
      simpa [gA] using (closedConvexFunction_precomp_linearMap (A := A) hclosed)
    refine ⟨hclosedA, ?_⟩
    rfl
  · intro _hnotclosed hri
    simpa [gA] using
      (convexFunctionClosure_precomp_linearMap_eq (hgproper := hgproper) (A := A) hri)

/-- In the lifted cone, a closure point with zero tail must be the origin. -/
lemma tail_kernel_closure_cone_zero {n : Nat} {C : Set (Fin n → Real)}
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCconv : Convex Real C)
    (hC0 : (0 : Fin n → Real) ∉ C) :
    let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
    let C' : Set (EuclideanSpace Real (Fin n)) := Set.image e.symm C
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C'}
    let K : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
    ∀ v, v ∈ closure K → tail v = 0 → v = 0 := by
  classical
  intro e C' coords first tail S K v hv htail0
  have hC'ne : C'.Nonempty := hCne.image e.symm
  have hC'conv : Convex Real C' := by
    simpa using hCconv.linear_image (e.symm.toLinearMap)
  have hC'closed : IsClosed C' := by
    have himage :
        Set.image e.symm C = e ⁻¹' C := by
      simpa using
        (ContinuousLinearEquiv.image_eq_preimage_symm (e := e.symm) (s := C))
    have hpre : IsClosed (e ⁻¹' C) := hCclosed.preimage e.continuous
    simpa [C', himage] using hpre
  have hclosure :
      closure K = K ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone C'} := by
    simpa [coords, first, tail, S, K] using
      (closure_cone_eq_union_recession (n := n) (C := C') hC'ne hC'closed hC'conv)
  have hv' :
      v ∈ K ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone C'} := by
    simpa [hclosure] using hv
  cases hv' with
  | inl hvK =>
      have hmem :
          0 < first v ∧ tail v ∈ (first v) • C' := by
        simpa [coords, first, tail, S, K] using
          (mem_K_iff_first_tail (n := n) (C := C') hC'conv v).1 hvK
      rcases hmem with ⟨hpos, htailmem⟩
      rcases htailmem with ⟨c, hcC, htail_eq⟩
      have hsmul : (first v : Real) • c = 0 := by
        calc
          (first v : Real) • c = tail v := by simp [htail_eq]
          _ = 0 := by simp [htail0]
      have hc0 : c = 0 := by
        rcases (smul_eq_zero.mp hsmul) with hzero | hc0
        · exact (False.elim ((ne_of_gt hpos) hzero))
        · exact hc0
      have hC0' : (0 : EuclideanSpace Real (Fin n)) ∈ C' := by
        simpa [hc0] using hcC
      have hC0'' : (0 : Fin n → Real) ∈ C := by
        rcases hC0' with ⟨x, hxC, hx0⟩
        have hx0' : x = 0 := by
          exact e.symm.injective hx0
        simpa [hx0'] using hxC
      exact (hC0 hC0'').elim
  | inr hvrec =>
      rcases hvrec with ⟨hfirst0, _⟩
      have hEq :
          ∀ u v, first u = first v → tail u = tail v → u = v := by
        simpa [coords, first, tail] using (eq_of_first_tail_eq (n := n))
      have hfirst0' : first v = first (0 : EuclideanSpace Real (Fin (1 + n))) := by
        have hzero : first (0 : EuclideanSpace Real (Fin (1 + n))) = 0 := by
          simp [first, coords]
        simp [hzero, hfirst0]
      have htail0' : tail v = tail (0 : EuclideanSpace Real (Fin (1 + n))) := by
        have hzero : tail (0 : EuclideanSpace Real (Fin (1 + n))) = 0 := by
          ext i; simp [tail, coords]
        simp [hzero, htail0]
      exact hEq v 0 hfirst0' htail0'

/-- The tail image of the lifted cone closes by adjoining recession directions. -/
lemma closure_tail_image_cone_eq_union_recession {n : Nat} {C : Set (Fin n → Real)}
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCconv : Convex Real C)
    (hC0 : (0 : Fin n → Real) ∉ C) :
    let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
    let C' : Set (EuclideanSpace Real (Fin n)) := Set.image e.symm C
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C'}
    let K : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
    let A : EuclideanSpace Real (Fin (1 + n)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
      (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin 1))
          (M₂ := EuclideanSpace Real (Fin n))).comp
        (appendAffineEquiv 1 n).symm.linear.toLinearMap
    closure (A '' K) = (A '' K) ∪ Set.recessionCone C' := by
  classical
  intro e C' coords first tail S K A
  have hC'ne : C'.Nonempty := hCne.image e.symm
  have hC'conv : Convex Real C' := by
    simpa using hCconv.linear_image (e.symm.toLinearMap)
  have hC'closed : IsClosed C' := by
    have himage :
        Set.image e.symm C = e ⁻¹' C := by
      simpa using
        (ContinuousLinearEquiv.image_eq_preimage_symm (e := e.symm) (s := C))
    have hpre : IsClosed (e ⁻¹' C) := hCclosed.preimage e.continuous
    simpa [C', himage] using hpre
  have hA : ∀ v, A v = tail v := by
    simpa [coords, tail, A] using (tail_linearMap_apply (n := n))
  have hKne : Set.Nonempty K := by
    rcases hC'ne with ⟨x0, hx0⟩
    let y0 : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (1 : ℝ))
    let append :
        EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
          EuclideanSpace Real (Fin (1 + n)) :=
      fun y z =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
          ((Fin.appendIsometry 1 n)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
             (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
    let v : EuclideanSpace Real (Fin (1 + n)) := append y0 x0
    have hfirst_tail :
        first v = 1 ∧ tail v = x0 := by
      have h :=
        (first_tail_append (n := n) (y := y0) (z := x0))
      simpa [coords, first, tail, append, v, y0] using h
    have hvS : v ∈ S := by
      refine ⟨hfirst_tail.1, ?_⟩
      simpa [hfirst_tail.2] using hx0
    have hvK : v ∈ K := by
      exact (ConvexCone.subset_hull (s := S) hvS)
    exact ⟨v, hvK⟩
  have hKconv : Convex Real K := by
    simpa [K] using (ConvexCone.convex (C := ConvexCone.hull Real S))
  have hlineal :
      ∀ z, z ≠ 0 → z ∈ Set.recessionCone (closure K) → A z = 0 →
        z ∈ Set.linealitySpace (closure K) := by
    intro z hz0 hzrec hAz
    have hclosure :
        closure K = K ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone C'} := by
      simpa [coords, first, tail, S, K] using
        (closure_cone_eq_union_recession (n := n) (C := C') hC'ne hC'closed hC'conv)
    have hzero_rec : (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone C' := by
      intro x hx t ht
      simpa [zero_smul, add_zero] using hx
    have hzero : (0 : EuclideanSpace Real (Fin (1 + n))) ∈ closure K := by
      have hfirst0 : first (0 : EuclideanSpace Real (Fin (1 + n))) = 0 := by
        simp [first, coords]
      have htail0 : tail (0 : EuclideanSpace Real (Fin (1 + n))) = 0 := by
        ext i; simp [tail, coords]
      have hzero' :
          (0 : EuclideanSpace Real (Fin (1 + n))) ∈
            {v | first v = 0 ∧ tail v ∈ Set.recessionCone C'} := by
        refine ⟨hfirst0, ?_⟩
        simpa [htail0] using hzero_rec
      have : (0 : EuclideanSpace Real (Fin (1 + n))) ∈
          K ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone C'} := by
        exact Or.inr hzero'
      simpa [hclosure] using this
    have hz_closure : z ∈ closure K := by
      have hz' :=
        hzrec (x := (0 : EuclideanSpace Real (Fin (1 + n)))) hzero (t := (1 : Real))
          (by linarith)
      simpa using hz'
    have htailz : tail z = 0 := by
      simpa [hA z] using hAz
    have hz0' : z = 0 := by
      have htk :=
        (tail_kernel_closure_cone_zero (hCne := hCne) (hCclosed := hCclosed)
          (hCconv := hCconv) (hC0 := hC0))
      simpa [e, C', coords, first, tail, S, K] using (htk (v := z) hz_closure htailz)
    exact (False.elim (hz0 hz0'))
  have hcl :
      closure (A '' K) = A '' closure K := by
    exact
      (linearMap_closure_image_eq_image_closure_of_recessionCone_kernel_lineality
        (hCne := hKne) (hCconv := hKconv) (A := A) hlineal).1
  have hclosureK :
      closure K = K ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone C'} := by
    simpa [coords, first, tail, S, K] using
      (closure_cone_eq_union_recession (n := n) (C := C') hC'ne hC'closed hC'conv)
  have hAboundary :
      A '' {v | first v = 0 ∧ tail v ∈ Set.recessionCone C'} =
        Set.recessionCone C' := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      rcases hv with ⟨hfirst0, htailrec⟩
      simpa [hA v] using htailrec
    · intro hw
      let y0 : EuclideanSpace Real (Fin 1) :=
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ))
      let append :
          EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
            EuclideanSpace Real (Fin (1 + n)) :=
        fun y z =>
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
            ((Fin.appendIsometry 1 n)
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
               (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
      let v : EuclideanSpace Real (Fin (1 + n)) := append y0 w
      have hfirst_tail :
          first v = 0 ∧ tail v = w := by
        have h :=
          (first_tail_append (n := n) (y := y0) (z := w))
        simpa [coords, first, tail, append, v, y0] using h
      have hv :
          v ∈ {v | first v = 0 ∧ tail v ∈ Set.recessionCone C'} := by
        refine ⟨hfirst_tail.1, ?_⟩
        simpa [hfirst_tail.2] using hw
      refine ⟨v, hv, ?_⟩
      simp [hA v, hfirst_tail.2]
  calc
    closure (A '' K) = A '' closure K := hcl
    _ = A '' (K ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone C'}) := by
      simp [hclosureK]
    _ = A '' K ∪ A '' {v | first v = 0 ∧ tail v ∈ Set.recessionCone C'} := by
      simp [Set.image_union]
    _ = A '' K ∪ Set.recessionCone C' := by
      simp [hAboundary]

/-- The generated cone equals positive scalings, up to union with a set containing `0`. -/
lemma convexConeGenerated_union_recession_eq_iUnion_pos {n : Nat}
    {C : Set (Fin n → Real)} (hCconv : Convex Real C) {recC : Set (Fin n → Real)}
    (hrec0 : (0 : Fin n → Real) ∈ recC) :
    let K : Set (Fin n → Real) := convexConeGenerated n C
    K ∪ recC = (⋃ (t : Real) (_ : 0 < t), (t • C)) ∪ recC := by
  classical
  intro K
  ext x
  constructor
  · intro hx
    rcases hx with hxK | hxrec
    · have hx' : x = 0 ∨ x ∈ (ConvexCone.hull Real C : Set _) := by
        simpa [K, convexConeGenerated, Set.mem_insert_iff] using hxK
      cases hx' with
      | inl hx0 =>
          right
          simpa [hx0] using hrec0
      | inr hxHull =>
          rcases (ConvexCone.mem_hull_of_convex (s := C) hCconv).1 hxHull with ⟨t, htpos, htmem⟩
          left
          refine Set.mem_iUnion.2 ?_
          refine ⟨t, ?_⟩
          refine Set.mem_iUnion.2 ?_
          refine ⟨htpos, ?_⟩
          simpa using htmem
    · exact Or.inr hxrec
  · intro hx
    rcases hx with hxpos | hxrec
    · rcases (Set.mem_iUnion).1 hxpos with ⟨t, ht⟩
      rcases (Set.mem_iUnion).1 ht with ⟨htpos, hxmem⟩
      have hxHull : x ∈ (ConvexCone.hull Real C : Set _) :=
        (ConvexCone.mem_hull_of_convex (s := C) hCconv).2 ⟨t, htpos, hxmem⟩
      have hxK : x ∈ K := by
        have : x = 0 ∨ x ∈ (ConvexCone.hull Real C : Set _) := Or.inr hxHull
        simpa [K, convexConeGenerated, Set.mem_insert_iff] using this
      exact Or.inl hxK
    · exact Or.inr hxrec

/-- Theorem 9.6. Let `C` be a non-empty closed convex set not containing the origin, and let
`K` be the convex cone generated by `C`. Then `closure K = K ∪ 0^+ C`, and this set equals
`⋃ { λ C | λ > 0 or λ = 0^+ }`. -/
theorem closure_convexConeGenerated_eq_union_recessionCone
    {n : Nat} {C : Set (Fin n → Real)}
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCconv : Convex Real C)
    (hC0 : (0 : Fin n → Real) ∉ C) :
    let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
    let C' : Set (EuclideanSpace Real (Fin n)) := Set.image e.symm C
    let recC : Set (Fin n → Real) := Set.image e (Set.recessionCone C')
    let K : Set (Fin n → Real) := convexConeGenerated n C
    closure K = K ∪ recC ∧
      K ∪ recC =
        (⋃ (t : Real) (_ : 0 < t), (t • C)) ∪ recC := by
  classical
  intro e C' recC K
  let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
  let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
  let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
    fun v =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
        (fun i => coords v (Fin.natAdd 1 i))
  let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C'}
  let K' : Set (EuclideanSpace Real (Fin (1 + n))) :=
    (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
  let A : EuclideanSpace Real (Fin (1 + n)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
    (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin 1))
        (M₂ := EuclideanSpace Real (Fin n))).comp
      (appendAffineEquiv 1 n).symm.linear.toLinearMap
  have hC'conv : Convex Real C' := by
    simpa using hCconv.linear_image (e.symm.toLinearMap)
  have hclosure_image :
      closure (A '' K') = (A '' K') ∪ Set.recessionCone C' := by
    simpa [e, C', coords, first, tail, S, K', A] using
      (closure_tail_image_cone_eq_union_recession (hCne := hCne) (hCclosed := hCclosed)
        (hCconv := hCconv) (hC0 := hC0))
  have hAimage :
      A '' K' = (ConvexCone.hull Real C' : Set _) := by
    simpa [coords, first, tail, S, K', A] using
      (tail_image_cone_eq_convexCone_hull (n := n) (C := C') hC'conv)
  have hclosure_hull :
      closure (ConvexCone.hull Real C' : Set _) =
        (ConvexCone.hull Real C' : Set _) ∪ Set.recessionCone C' := by
    simpa [hAimage] using hclosure_image
  have himage_hull :
      e '' (ConvexCone.hull Real C' : Set _) = (ConvexCone.hull Real C : Set _) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases (ConvexCone.mem_hull_of_convex (s := C') hC'conv).1 hy with ⟨r, hr, hrC⟩
      rcases hrC with ⟨c', hc'C, rfl⟩
      rcases hc'C with ⟨c, hcC, hc_eq⟩
      have hc' : e c' = c := by
        have := congrArg e hc_eq
        simpa [eq_comm] using this
      have hx : e (r • c') ∈ r • C := by
        refine ⟨c, hcC, ?_⟩
        have hx' : e (r • c') = r • c := by
          calc
            e (r • c') = r • e c' := by
              simp
            _ = r • c := by simp [hc']
        simpa [eq_comm] using hx'
      exact (ConvexCone.mem_hull_of_convex (s := C) hCconv).2 ⟨r, hr, hx⟩
    · intro hx
      rcases (ConvexCone.mem_hull_of_convex (s := C) hCconv).1 hx with ⟨r, hr, hrC⟩
      rcases hrC with ⟨c, hcC, rfl⟩
      have hcC' : e.symm c ∈ C' := by
        exact ⟨c, hcC, rfl⟩
      have hx' : e.symm (r • c) ∈ (ConvexCone.hull Real C' : Set _) := by
        have hmem : e.symm (r • c) ∈ r • C' := by
          refine ⟨e.symm c, hcC', ?_⟩
          simp
        exact (ConvexCone.mem_hull_of_convex (s := C') hC'conv).2 ⟨r, hr, hmem⟩
      refine ⟨e.symm (r • c), hx', ?_⟩
      simp
  have hclosure_hull_C :
      closure (ConvexCone.hull Real C : Set _) =
        (ConvexCone.hull Real C : Set _) ∪ recC := by
    have himage_closure :
        closure (e '' (ConvexCone.hull Real C' : Set _)) =
          e '' closure (ConvexCone.hull Real C' : Set _) := by
      symm
      simpa using
        (ContinuousLinearEquiv.image_closure (e := e)
          (s := (ConvexCone.hull Real C' : Set _)))
    calc
      closure (ConvexCone.hull Real C : Set _) =
          closure (e '' (ConvexCone.hull Real C' : Set _)) := by
            simp [himage_hull]
      _ = e '' closure (ConvexCone.hull Real C' : Set _) := himage_closure
      _ = e '' ((ConvexCone.hull Real C' : Set _) ∪ Set.recessionCone C') := by
            simp [hclosure_hull]
      _ = e '' (ConvexCone.hull Real C' : Set _) ∪ e '' Set.recessionCone C' := by
            simp [Set.image_union]
      _ = (ConvexCone.hull Real C : Set _) ∪ recC := by
            simp [himage_hull, recC]
  have hrec0 : (0 : Fin n → Real) ∈ recC := by
    have hzero_rec : (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone C' := by
      intro x hx t ht
      simpa [zero_smul, add_zero] using hx
    refine ⟨0, hzero_rec, ?_⟩
    simp
  have hK_union : K ∪ recC = (ConvexCone.hull Real C : Set _) ∪ recC := by
    ext x
    constructor
    · intro hx
      rcases hx with hxK | hxrec
      · have hx' : x = 0 ∨ x ∈ (ConvexCone.hull Real C : Set _) := by
          simpa [K, convexConeGenerated, Set.mem_insert_iff] using hxK
        cases hx' with
        | inl hx0 =>
            right
            simpa [hx0] using hrec0
        | inr hxHull =>
            left
            exact hxHull
      · exact Or.inr hxrec
    · intro hx
      rcases hx with hxHull | hxrec
      · have hxK : x ∈ K := by
          have : x = 0 ∨ x ∈ (ConvexCone.hull Real C : Set _) := Or.inr hxHull
          simpa [K, convexConeGenerated, Set.mem_insert_iff] using this
        exact Or.inl hxK
      · exact Or.inr hxrec
  have hclosureK : closure K = K ∪ recC := by
    have hzero_closure_hull :
        (0 : Fin n → Real) ∈ closure (ConvexCone.hull Real C : Set _) := by
      have : (0 : Fin n → Real) ∈ (ConvexCone.hull Real C : Set _) ∪ recC := by
        exact Or.inr hrec0
      simpa [hclosure_hull_C] using this
    have hKdef : K = (ConvexCone.hull Real C : Set _) ∪ {0} := by
      ext x
      constructor
      · intro hx
        have hx' : x = 0 ∨ x ∈ (ConvexCone.hull Real C : Set _) := by
          simpa [K, convexConeGenerated, Set.mem_insert_iff] using hx
        rcases hx' with hx0 | hxHull
        · right
          simp [hx0]
        · left
          exact hxHull
      · intro hx
        rcases hx with hxHull | hx0
        · have : x = 0 ∨ x ∈ (ConvexCone.hull Real C : Set _) := Or.inr hxHull
          simpa [K, convexConeGenerated, Set.mem_insert_iff] using this
        · have : x = 0 ∨ x ∈ (ConvexCone.hull Real C : Set _) := Or.inl (by simpa using hx0)
          simpa [K, convexConeGenerated, Set.mem_insert_iff] using this
    have hclosureK' :
        closure K = closure (ConvexCone.hull Real C : Set _) := by
      calc
        closure K = closure ((ConvexCone.hull Real C : Set _) ∪ {0}) := by
          simp [hKdef]
        _ = closure (ConvexCone.hull Real C : Set _) ∪ closure ({0} : Set (Fin n → Real)) := by
          simpa using
            (closure_union
              (s := (ConvexCone.hull Real C : Set (Fin n → Real)))
              (t := ({0} : Set (Fin n → Real))))
        _ = closure (ConvexCone.hull Real C : Set _) := by
          apply Set.union_eq_left.mpr
          intro x hx
          have hx0 : x = 0 := by
            have hx' : x ∈ ({0} : Set (Fin n → Real)) := by
              simpa [closure_singleton] using hx
            simpa [Set.mem_singleton_iff] using hx'
          simpa [hx0] using hzero_closure_hull
    calc
      closure K = closure (ConvexCone.hull Real C : Set _) := hclosureK'
      _ = (ConvexCone.hull Real C : Set _) ∪ recC := hclosure_hull_C
      _ = K ∪ recC := by
          symm
          exact hK_union
  have hK_union_pos :
      K ∪ recC = (⋃ (t : Real) (h : 0 < t), (t • C)) ∪ recC := by
    simpa [K] using
      (convexConeGenerated_union_recession_eq_iUnion_pos (C := C) hCconv
        (recC := recC) hrec0)
  exact ⟨hclosureK, hK_union_pos⟩

/-- Boundedness forces the recession cone of the Euclidean image to be `{0}`. -/
lemma recCone_eq_singleton_zero_of_bounded_image {n : Nat} {C : Set (Fin n → Real)}
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCconv : Convex Real C)
    (hCbdd : Bornology.IsBounded C) :
    let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
    let C' : Set (EuclideanSpace Real (Fin n)) := Set.image e.symm C
    Set.recessionCone C' = {0} := by
  intro e C'
  have hC'ne : C'.Nonempty := hCne.image e.symm
  have hC'conv : Convex Real C' := by
    simpa using hCconv.linear_image (e.symm.toLinearMap)
  have hC'closed : IsClosed C' := by
    have himage :
        Set.image e.symm C = e ⁻¹' C := by
      simpa using
        (ContinuousLinearEquiv.image_eq_preimage_symm (e := e.symm) (s := C))
    have hpre : IsClosed (e ⁻¹' C) := hCclosed.preimage e.continuous
    simpa [C', himage] using hpre
  have hC'bounded : Bornology.IsBounded C' := by
    simpa [C'] using (e.symm.lipschitz.isBounded_image hCbdd)
  exact
    (bounded_iff_recessionCone_eq_singleton_zero (C := C') hC'ne hC'closed hC'conv).1
      hC'bounded

/-- Corollary 9.6.1. If `C` is a non-empty closed bounded convex set not containing the
origin, then the convex cone `K` generated by `C` is closed. -/
theorem closed_convexConeGenerated_of_bounded {n : Nat} {C : Set (Fin n → Real)}
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCbdd : Bornology.IsBounded C)
    (hCconv : Convex Real C) (hC0 : (0 : Fin n → Real) ∉ C) :
    IsClosed (convexConeGenerated n C) := by
  classical
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  let C' : Set (EuclideanSpace Real (Fin n)) := Set.image e.symm C
  let recC : Set (Fin n → Real) := Set.image e (Set.recessionCone C')
  let K : Set (Fin n → Real) := convexConeGenerated n C
  have hrecC :
      Set.recessionCone C' = ({0} : Set (EuclideanSpace Real (Fin n))) := by
    simpa [e, C'] using
      (recCone_eq_singleton_zero_of_bounded_image (C := C) hCne hCclosed hCconv hCbdd)
  have hclosure :
      closure K = K ∪ recC := by
    simpa [e, C', recC, K] using
      (closure_convexConeGenerated_eq_union_recessionCone
        (C := C) hCne hCclosed hCconv hC0).1
  have hrecC' : recC = ({0} : Set (Fin n → Real)) := by
    simp [recC, hrecC]
  have h0 : (0 : Fin n → Real) ∈ K := by
    have h0' :
        (0 : Fin n → Real) ∈
          Set.insert (0 : Fin n → Real) (ConvexCone.hull Real C : Set (Fin n → Real)) :=
      (Set.mem_insert_iff).2 (Or.inl rfl)
    simpa [K, convexConeGenerated] using h0'
  have hclosureK : closure K = K := by
    calc
      closure K = K ∪ recC := hclosure
      _ = K ∪ {0} := by simp [hrecC']
      _ = K := by
        apply Set.union_eq_left.mpr
        intro x hx
        have hx0 : x = 0 := by simpa [Set.mem_singleton_iff] using hx
        simpa [hx0] using h0
  exact (closure_eq_iff_isClosed (s := K)).1 hclosureK

/-- The vertical line through `![1, 0]` is the set of points with first coordinate `1`. -/
lemma lineSet_eq_first_coord :
    {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]} =
      {x : Fin 2 → Real | x 0 = 1} := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    simp
  · intro hx
    refine ⟨x 1, ?_⟩
    ext i; fin_cases i
    · simpa using hx
    · simp

/-- The vertical line `{(1, t)}` is closed. -/
lemma closed_lineSet :
    IsClosed {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]} := by
  have hclosed : IsClosed {x : Fin 2 → Real | x 0 = (1 : Real)} := by
    simpa using (isClosed_eq (continuous_apply 0) continuous_const)
  rw [lineSet_eq_first_coord]
  exact hclosed

/-- The vertical line `{(1, t)}` is convex. -/
lemma convex_lineSet :
    Convex Real {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]} := by
  have hconv : Convex Real {x : Fin 2 → Real | x 0 = (1 : Real)} := by
    intro x hx y hy a b ha hb hab
    have hx0 : x 0 = 1 := hx
    have hy0 : y 0 = 1 := hy
    simp [hx0, hy0, hab]
  rw [lineSet_eq_first_coord]
  exact hconv

/-- Nonzero points in the cone over the vertical line have positive first coordinate. -/
lemma cone_line_pos_first {x : Fin 2 → Real}
    (hx : x ∈ convexConeGenerated 2 {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]})
    (hx0 : x ≠ 0) : 0 < x 0 := by
  have hx' : x = 0 ∨
      x ∈ (ConvexCone.hull Real
        {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]} : Set (Fin 2 → Real)) := by
    simpa [convexConeGenerated, Set.mem_insert_iff] using hx
  rcases hx' with hx0' | hxHull
  · exact (hx0 hx0').elim
  · rcases (ConvexCone.mem_hull_of_convex
        (s := {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]})
        convex_lineSet).1 hxHull with ⟨t, htpos, htmem⟩
    rcases htmem with ⟨c, hcC, rfl⟩
    have hc0 : c 0 = 1 := by
      rcases hcC with ⟨t, rfl⟩
      simp
    simpa [hc0] using htpos

/-- Points with positive first coordinate lie in the cone over the vertical line. -/
lemma pos_first_mem_cone_line {x : Fin 2 → Real} (hx : 0 < x 0) :
    x ∈ convexConeGenerated 2 {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]} := by
  have hxHull :
      x ∈ (ConvexCone.hull Real
        {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]} : Set (Fin 2 → Real)) := by
    refine (ConvexCone.mem_hull_of_convex
      (s := {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]})
      convex_lineSet).2 ?_
    refine ⟨x 0, hx, ?_⟩
    refine ⟨![1, x 1 / x 0], ?_, ?_⟩
    · refine ⟨x 1 / x 0, ?_⟩
      ext i; fin_cases i
      · simp
      · simp
    · have hxne : x 0 ≠ 0 := ne_of_gt hx
      ext i; fin_cases i
      · simp
      · have h : x 0 * (x 1 / x 0) = x 1 := by
          field_simp [hxne]
        simpa using h
  have hxK : x = 0 ∨
      x ∈ (ConvexCone.hull Real
        {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]} : Set (Fin 2 → Real)) :=
    Or.inr hxHull
  simpa [convexConeGenerated, Set.mem_insert_iff] using hxK

/-- The point `(0, 1)` lies in the closure of the cone over the vertical line. -/
lemma closure_cone_line_has_point :
    (![0, 1] : Fin 2 → Real) ∈
      closure (convexConeGenerated 2
        {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]}) := by
  refine (mem_closure_iff_seq_limit).2 ?_
  refine ⟨fun n : ℕ => ![(1 : Real) / (n + 1), 1], ?_, ?_⟩
  · intro n
    have hpos : 0 < (1 : Real) / (n + 1) := by
      have : 0 < (n + 1 : Real) := by
        exact_mod_cast (Nat.succ_pos n)
      exact one_div_pos.mpr this
    simpa using (pos_first_mem_cone_line (x := ![(1 : Real) / (n + 1), 1]) hpos)
  · refine (tendsto_pi_nhds.2 ?_)
    intro i
    fin_cases i
    · have h :
        Tendsto (fun n : ℕ => (1 : Real) / ((n : Real) + 1)) atTop (𝓝 (0 : Real)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [one_div, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using h
    · simp

end Section09
end Chap02
