/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part10

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise
open scoped InnerProductSpace

/-- Theorem 16.4.3: Let `f₁, …, fₘ` be proper convex functions on `ℝⁿ`. For any convex set
`D ⊆ ℝᵐ`, if there exists `x` such that `A x ∈ ri D`, then the closure operation can be omitted
in Theorem 16.4.2, and

`δ^*(xStar | A⁻¹ D) = inf { δ^*(yStar | D) | A^* yStar = xStar }`,

where the infimum is attained (or is `+∞` vacuously).

In this development, `δ^*` is represented by `supportFunctionEReal`, `ri` is
`euclideanRelativeInterior`, and the right-hand side is modeled by an `sInf` over the affine
fiber `{yStar | A^* yStar = xStar}`. -/
theorem section16_supportFunctionEReal_preimage_eq_sInf_of_exists_mem_ri {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (D : Set (Fin m → ℝ)) (hD : Convex ℝ D)
    (hri :
      ∃ x : EuclideanSpace ℝ (Fin n),
        A x ∈
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹' D)) :
    let Aadj : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      ((LinearMap.adjoint :
              (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
            A)
    ((supportFunctionEReal
          (Set.preimage (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) D) =
        fun xStar : Fin n → ℝ =>
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  supportFunctionEReal D (yStar : Fin m → ℝ)) ''
              {yStar | Aadj yStar = WithLp.toLp 2 xStar})) ∧
      ∀ xStar : Fin n → ℝ,
        sInf
              ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                    supportFunctionEReal D (yStar : Fin m → ℝ)) ''
                {yStar | Aadj yStar = WithLp.toLp 2 xStar}) =
            ⊤ ∨
          ∃ yStar : EuclideanSpace ℝ (Fin m),
            Aadj yStar = WithLp.toLp 2 xStar ∧
              supportFunctionEReal D (yStar : Fin m → ℝ) =
                sInf
                  ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                        supportFunctionEReal D (yStar : Fin m → ℝ)) ''
                    {yStar | Aadj yStar = WithLp.toLp 2 xStar})) := by
  simpa using
    (section16_supportFunctionEReal_preimage_eq_adjoint_image_of_exists_mem_ri
      (A := A) (D := D) hD hri)

/-- Rewriting the distance function as an infimal convolution of the norm and indicator. -/
lemma section16_infDist_as_infimalConvolution_norm_indicator {n : Nat} {C : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) :
    (fun x : Fin n → ℝ => ((Metric.infDist x C : ℝ) : EReal)) =
      infimalConvolution (fun y : Fin n → ℝ => ((‖y‖ : ℝ) : EReal)) (indicatorFunction C) := by
  funext x
  symm
  simpa using (infimalConvolution_norm_indicator_eq_infDist (C := C) hCne x)

/-- The Fenchel conjugate of the norm is the indicator of the `ℓ¹` unit ball. -/
lemma section16_fenchelConjugate_norm_eq_indicator_unitBall {n : ℕ} :
    fenchelConjugate n (fun x : Fin n → ℝ => ((‖x‖ : ℝ) : EReal)) =
      fun xStar : Fin n → ℝ =>
        if l1Norm xStar ≤ (1 : ℝ) then (0 : EReal) else (⊤ : EReal) := by
  classical
  funext xStar
  by_cases hxs : l1Norm xStar ≤ (1 : ℝ)
  · have hle :
        fenchelConjugate n (fun x : Fin n → ℝ => ((‖x‖ : ℝ) : EReal)) xStar ≤ (0 : EReal) := by
      have hbound :
          ∀ x : Fin n → ℝ,
            ((x ⬝ᵥ xStar - (0 : ℝ) : ℝ) : EReal) ≤ ((‖x‖ : ℝ) : EReal) := by
        intro x
        have hdot' :
            dotProduct xStar x ≤ l1Norm xStar * ‖x‖ :=
          section13_dotProduct_le_l1Norm_mul_norm (n := n) (x := xStar) (y := x)
        have hdot : dotProduct x xStar ≤ l1Norm xStar * ‖x‖ := by
          simpa [dotProduct_comm] using hdot'
        have hmul :
            l1Norm xStar * ‖x‖ ≤ ‖x‖ := by
          have hnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
          have hmul' := mul_le_mul_of_nonneg_right hxs hnorm_nonneg
          simpa using hmul'
        have hle_real : dotProduct x xStar ≤ ‖x‖ := le_trans hdot hmul
        have hle_ereal :
            ((dotProduct x xStar : ℝ) : EReal) ≤ ((‖x‖ : ℝ) : EReal) := by
          exact_mod_cast hle_real
        simpa using hle_ereal
      exact
        (fenchelConjugate_le_coe_iff_affine_le (n := n)
              (f := fun x : Fin n → ℝ => ((‖x‖ : ℝ) : EReal)) (b := xStar) (μ := 0)).2 hbound
    have hge :
        (0 : EReal) ≤ fenchelConjugate n (fun x : Fin n → ℝ => ((‖x‖ : ℝ) : EReal)) xStar := by
      unfold fenchelConjugate
      have hle :
          ((0 ⬝ᵥ xStar : ℝ) : EReal) -
              ((‖(0 : Fin n → ℝ)‖ : ℝ) : EReal) ≤
            sSup
              (Set.range fun x : Fin n → ℝ =>
                ((x ⬝ᵥ xStar : ℝ) : EReal) - ((‖x‖ : ℝ) : EReal)) := by
        exact le_sSup ⟨0, rfl⟩
      simpa using hle
    have hzero :
        fenchelConjugate n (fun x : Fin n → ℝ => ((‖x‖ : ℝ) : EReal)) xStar = (0 : EReal) :=
      le_antisymm hle hge
    simp [hxs, hzero]
  · have hfinite :
        ∀ z : Fin n → ℝ,
          (fun x : Fin n → ℝ => ((‖x‖ : ℝ) : EReal)) z ≠ ⊤ ∧
            (fun x : Fin n → ℝ => ((‖x‖ : ℝ) : EReal)) z ≠ ⊥ := by
      intro z
      exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
    have hLip :
        LipschitzCondition (fun x : Fin n → ℝ => ((‖x‖ : ℝ) : EReal)) (1 : ℝ) := by
      intro z x
      simpa [LipschitzCondition, one_mul] using (abs_norm_sub_norm_le z x)
    have htop :
        fenchelConjugate n (fun x : Fin n → ℝ => ((‖x‖ : ℝ) : EReal)) xStar = ⊤ := by
      refine
        section13_fenchelConjugate_eq_top_of_LipschitzCondition_lt_l1Norm (n := n)
          (f := fun x : Fin n → ℝ => ((‖x‖ : ℝ) : EReal)) (α := 1) hfinite (by norm_num) hLip
          xStar (lt_of_not_ge hxs)
    simp [hxs, htop]

/-- The Fenchel conjugate of the distance function splits into the norm conjugate and the support
function. -/
lemma section16_fenchelConjugate_infDist_eq_indicatorBall_add_supportFunctionEReal {n : ℕ}
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C) (hCne : C.Nonempty) :
    fenchelConjugate n (fun x : Fin n → ℝ => ((Metric.infDist x C : ℝ) : EReal)) =
      fun xStar : Fin n → ℝ =>
        (if l1Norm xStar ≤ (1 : ℝ) then (0 : EReal) else (⊤ : EReal)) +
          supportFunctionEReal C xStar := by
  classical
  let f1 : (Fin n → ℝ) → EReal := fun x => ((‖x‖ : ℝ) : EReal)
  let f2 : (Fin n → ℝ) → EReal := indicatorFunction C
  let f : Fin 2 → (Fin n → ℝ) → EReal := fun i => if i = 0 then f1 else f2
  have hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i) := by
    intro i
    fin_cases i <;> simp [f, f1, f2, properConvexFunctionOn_norm,
      properConvexFunctionOn_indicator_of_convex_of_nonempty, hC, hCne]
  have hInf :
      infimalConvolution f1 f2 = infimalConvolutionFamily f := by
    simpa [f, f1, f2] using
      (infimalConvolution_eq_infimalConvolutionFamily_two (f := f1) (g := f2))
  have hInfDist :
      (fun x : Fin n → ℝ => ((Metric.infDist x C : ℝ) : EReal)) =
        infimalConvolution f1 f2 :=
    (section16_infDist_as_infimalConvolution_norm_indicator (C := C) hCne)
  calc
    fenchelConjugate n (fun x : Fin n → ℝ => ((Metric.infDist x C : ℝ) : EReal)) =
        fenchelConjugate n (infimalConvolution f1 f2) := by
          simp [hInfDist, f1, f2]
    _ = fenchelConjugate n (infimalConvolutionFamily f) := by
          simp [hInf, f, f1, f2]
    _ = fun xStar => ∑ i, fenchelConjugate n (f i) xStar :=
          section16_fenchelConjugate_infimalConvolutionFamily (f := f) hf
    _ = fun xStar : Fin n → ℝ =>
          (if l1Norm xStar ≤ (1 : ℝ) then (0 : EReal) else (⊤ : EReal)) +
            supportFunctionEReal C xStar := by
          funext xStar
          simp [f, f1, f2, Fin.sum_univ_two,
            section16_fenchelConjugate_norm_eq_indicator_unitBall,
            section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal]

/-- Text 16.4.1: Let `f(x) = d(x, C) = inf {‖x - y‖ | y ∈ C}` be the distance function, where `C`
is a given nonempty convex set. Then

`f^*(x^*) = δ^*(x^* | C)` if `‖x^*‖₁ ≤ 1`, and `f^*(x^*) = +∞` otherwise.

In this development, `f^*` is represented by `fenchelConjugate n f`, `d(x, C)` is `Metric.infDist`,
and `δ^*(· | C)` is the support function `supportFunctionEReal C`. -/
theorem section16_fenchelConjugate_infDist {n : ℕ} (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCne : C.Nonempty) :
    fenchelConjugate n (fun x : Fin n → ℝ => ((Metric.infDist x C : ℝ) : EReal)) =
      fun xStar : Fin n → ℝ =>
        if l1Norm xStar ≤ (1 : ℝ) then supportFunctionEReal C xStar else (⊤ : EReal) := by
  classical
  have hsum :=
    section16_fenchelConjugate_infDist_eq_indicatorBall_add_supportFunctionEReal (C := C) hC hCne
  funext xStar
  by_cases hxs : l1Norm xStar ≤ (1 : ℝ)
  · simp [hsum, hxs]
  · have hne_bot : supportFunctionEReal C xStar ≠ (⊥ : EReal) :=
      section13_supportFunctionEReal_ne_bot (C := C) hCne hC xStar
    simp [hsum, hxs, hne_bot]

/-- The span of a finite family agrees with the range of its linear-combination map. -/
lemma section16_span_range_eq_linearMap_range_sum_smul {n m : Nat} (a : Fin m → Fin n → ℝ) :
    let A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      { toFun := fun ξ => ∑ t, (ξ t) • a t
        map_add' := by
          intro ξ η
          ext j
          simp [Finset.sum_add_distrib, add_smul]
        map_smul' := by
          intro c ξ
          ext j
          simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin m)))
              (f := fun x => a x j * ξ x) (a := c)).symm }
    Submodule.span ℝ (Set.range a) = LinearMap.range A := by
  classical
  let A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun ξ => ∑ t, (ξ t) • a t
      map_add' := by
        intro ξ η
        ext j
        simp [Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro c ξ
        ext j
        simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          (Finset.mul_sum (s := (Finset.univ : Finset (Fin m)))
            (f := fun x => a x j * ξ x) (a := c)).symm }
  have hspan : Submodule.span ℝ (Set.range a) = LinearMap.range A := by
    refine le_antisymm ?_ ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨t, rfl⟩
      refine ⟨(fun s => if s = t then 1 else 0), ?_⟩
      simp [A, ite_smul, Finset.sum_ite_eq', Finset.mem_univ]
    · rintro _ ⟨ξ, rfl⟩
      have hmem :
          ∀ t ∈ (Finset.univ : Finset (Fin m)), (ξ t) • a t ∈ Submodule.span ℝ (Set.range a) := by
        intro t ht
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
      have hsum :
          Finset.sum (Finset.univ : Finset (Fin m)) (fun t => (ξ t) • a t) ∈
            Submodule.span ℝ (Set.range a) :=
        Submodule.sum_mem (Submodule.span ℝ (Set.range a)) hmem
      simpa [A] using hsum
  simpa [A] using hspan

/-- The infimum over all coefficient vectors is the distance to the range. -/
lemma section16_sInf_range_norm_sub_eq_infDist_range {n m : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (x : Fin n → ℝ) :
    sInf (Set.range fun ξ : Fin m → ℝ => ‖x - A ξ‖) =
      Metric.infDist x (Set.range A) := by
  classical
  have hleft :
      sInf (Set.range fun ξ : Fin m → ℝ => ‖x - A ξ‖) =
        iInf (fun ξ : Fin m → ℝ => ‖x - A ξ‖) := by
    simpa using (sInf_range (f := fun ξ : Fin m → ℝ => ‖x - A ξ‖))
  have hsurj :
      Function.Surjective (fun ξ : Fin m → ℝ => (⟨A ξ, ⟨ξ, rfl⟩⟩ : Set.range A)) := by
    intro y
    rcases y with ⟨y, ⟨ξ, rfl⟩⟩
    exact ⟨ξ, rfl⟩
  have hright :
      iInf (fun ξ : Fin m → ℝ => ‖x - A ξ‖) =
        iInf (fun y : Set.range A => ‖x - y‖) := by
    simpa using
      (Function.Surjective.iInf_comp hsurj (fun y : Set.range A => ‖x - y‖))
  have hdist :
      Metric.infDist x (Set.range A) = iInf (fun y : Set.range A => dist x y) := by
    simpa using (Metric.infDist_eq_iInf (x := x) (s := (Set.range A)))
  calc
    sInf (Set.range fun ξ : Fin m → ℝ => ‖x - A ξ‖) =
        iInf (fun ξ : Fin m → ℝ => ‖x - A ξ‖) := hleft
    _ = iInf (fun y : Set.range A => ‖x - y‖) := hright
    _ = iInf (fun y : Set.range A => dist x y) := by
          simp [dist_eq_norm]
    _ = Metric.infDist x (Set.range A) := by
          simpa using hdist.symm

/-- The distance to a submodule is closed, proper, and convex. -/
lemma section16_closedProperConvex_coe_infDist_submodule {n : Nat}
    (L : Submodule ℝ (Fin n → ℝ)) :
    ClosedConvexFunction
        (fun x : Fin n → ℝ => ((Metric.infDist x (L : Set (Fin n → ℝ)) : ℝ) : EReal)) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x : Fin n → ℝ => ((Metric.infDist x (L : Set (Fin n → ℝ)) : ℝ) : EReal)) := by
  classical
  have hC : Convex ℝ (L : Set (Fin n → ℝ)) := by
    simpa using L.convex
  have hCne : (L : Set (Fin n → ℝ)).Nonempty := ⟨0, by simp⟩
  have hproper_norm :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x : Fin n → ℝ => ((‖x‖ : ℝ) : EReal)) :=
    properConvexFunctionOn_norm (n := n)
  have hproper_indicator :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (indicatorFunction (L : Set (Fin n → ℝ))) :=
    properConvexFunctionOn_indicator_of_convex_of_nonempty (C := (L : Set (Fin n → ℝ))) hC hCne
  have hconv_ereal :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (infimalConvolution (fun y : Fin n → ℝ => ((‖y‖ : ℝ) : EReal))
          (indicatorFunction (L : Set (Fin n → ℝ)))) := by
    exact
      convexFunctionOn_infimalConvolution_of_proper
        (f := fun y : Fin n → ℝ => ((‖y‖ : ℝ) : EReal))
        (g := indicatorFunction (L : Set (Fin n → ℝ))) hproper_norm hproper_indicator
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x : Fin n → ℝ => ((Metric.infDist x (L : Set (Fin n → ℝ)) : ℝ) : EReal)) := by
    have hEq :
        infimalConvolution (fun y : Fin n → ℝ => ((‖y‖ : ℝ) : EReal))
            (indicatorFunction (L : Set (Fin n → ℝ))) =
          fun x : Fin n → ℝ => ((Metric.infDist x (L : Set (Fin n → ℝ)) : ℝ) : EReal) := by
      funext x
      simpa using
        (infimalConvolution_norm_indicator_eq_infDist (C := (L : Set (Fin n → ℝ))) hCne x)
    simpa [hEq] using hconv_ereal
  have hconv_fun :
      ConvexFunction
        (fun x : Fin n → ℝ => ((Metric.infDist x (L : Set (Fin n → ℝ)) : ℝ) : EReal)) := by
    simpa [ConvexFunction] using hconv
  have hls :
      LowerSemicontinuous
        (fun x : Fin n → ℝ => ((Metric.infDist x (L : Set (Fin n → ℝ)) : ℝ) : EReal)) := by
    have hcont :
        Continuous (fun x : Fin n → ℝ => Metric.infDist x (L : Set (Fin n → ℝ))) := by
      simpa using (Metric.continuous_infDist_pt (s := (L : Set (Fin n → ℝ))))
    exact lowerSemicontinuous_coe_real_toEReal hcont.lowerSemicontinuous
  have hclosed :
      ClosedConvexFunction
        (fun x : Fin n → ℝ => ((Metric.infDist x (L : Set (Fin n → ℝ)) : ℝ) : EReal)) :=
    ⟨hconv_fun, hls⟩
  have hne_epi :
      Set.Nonempty
        (epigraph (Set.univ : Set (Fin n → ℝ))
          (fun x : Fin n → ℝ => ((Metric.infDist x (L : Set (Fin n → ℝ)) : ℝ) : EReal))) := by
    refine ⟨(0, Metric.infDist (0 : Fin n → ℝ) (L : Set (Fin n → ℝ))), ?_⟩
    refine And.intro ?_ ?_
    · change True
      trivial
    · exact le_rfl
  have hnotbot :
      ∀ x ∈ (Set.univ : Set (Fin n → ℝ)),
        ((Metric.infDist x (L : Set (Fin n → ℝ)) : ℝ) : EReal) ≠ (⊥ : EReal) := by
    intro x hx
    exact EReal.coe_ne_bot (Metric.infDist x (L : Set (Fin n → ℝ)))
  refine ⟨hclosed, ?_⟩
  exact ⟨hconv, hne_epi, hnotbot⟩

attribute [local instance] Classical.propDecidable

/-- The support function of a submodule is the indicator of its orthogonal complement. -/
lemma section16_supportFunctionEReal_submodule {n : Nat} (L : Submodule ℝ (Fin n → ℝ)) :
    supportFunctionEReal (L : Set (Fin n → ℝ)) =
      fun b : Fin n → ℝ =>
        if b ∈ orthogonalComplement n L then (0 : EReal) else (⊤ : EReal) := by
  classical
  funext b
  have hSup :=
    (section16_sInf_sSup_image_dotProduct_submodule (L := L) (b := b)).2
  have hset :
      {z : EReal | ∃ x ∈ (L : Set (Fin n → ℝ)), z = ((dotProduct x b : ℝ) : EReal)} =
        (fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' (L : Set (Fin n → ℝ)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [supportFunctionEReal, hset]
  simpa using hSup

/-- The conjugate of the distance to a submodule is an indicator on `D ∩ Lᗮ`. -/
lemma section16_fenchelConjugate_coe_infDist_submodule_eq_indicator_D_inter_orth {n : Nat}
    (L : Submodule ℝ (Fin n → ℝ)) :
    fenchelConjugate n
        (fun x : Fin n → ℝ =>
          ((Metric.infDist x (L : Set (Fin n → ℝ)) : ℝ) : EReal)) =
      indicatorFunction
        ({b : Fin n → ℝ | l1Norm b ≤ (1 : ℝ)} ∩
          (orthogonalComplement n L : Set (Fin n → ℝ))) := by
  classical
  have hC : Convex ℝ (L : Set (Fin n → ℝ)) := by
    simpa using L.convex
  have hCne : (L : Set (Fin n → ℝ)).Nonempty := ⟨0, by simp⟩
  have hfenchel :=
    section16_fenchelConjugate_infDist (C := (L : Set (Fin n → ℝ))) hC hCne
  have hSupp := section16_supportFunctionEReal_submodule (L := L)
  funext b
  by_cases hD : l1Norm b ≤ (1 : ℝ)
  · by_cases hO : b ∈ orthogonalComplement n L
    · simp [hfenchel, hSupp, hD, hO, indicatorFunction]
    · simp [hfenchel, hSupp, hD, hO, indicatorFunction]
  · simp [hfenchel, hD, indicatorFunction]

/-- Dot products over `D ∩ Lᗮ` are bounded above. -/
lemma section16_bddAbove_dotProduct_D_inter_orth {n : Nat} (L : Submodule ℝ (Fin n → ℝ))
    (x : Fin n → ℝ) :
    BddAbove
      (Set.image (fun y : Fin n → ℝ => dotProduct y x)
        ({y : Fin n → ℝ | l1Norm y ≤ (1 : ℝ)} ∩
          (orthogonalComplement n L : Set (Fin n → ℝ)))) := by
  classical
  refine ⟨‖x‖, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hyD : l1Norm y ≤ (1 : ℝ) := hy.1
  have hdot :
      dotProduct y x ≤ l1Norm y * ‖x‖ :=
    section13_dotProduct_le_l1Norm_mul_norm (n := n) (x := y) (y := x)
  have hmul :
      l1Norm y * ‖x‖ ≤ ‖x‖ := by
    have hxnonneg : 0 ≤ ‖x‖ := norm_nonneg _
    have hmul' := mul_le_mul_of_nonneg_right hyD hxnonneg
    simpa using hmul'
  exact le_trans hdot hmul

/-- Text 16.4.2: Consider the function

`f(x) = inf { ‖x - ξ₁ a₁ - ⋯ - ξₘ aₘ‖∞ | ξₜ ∈ ℝ }`,

where `a₁, …, aₘ ∈ ℝⁿ` are given and `‖x‖∞ = max_j |x j|` for `x ∈ ℝⁿ`. Then `f` is the support
function of the (polyhedral) convex set `D ∩ L^⊥`, where `L` is the subspace spanned by
`a₁, …, aₘ` and

`D = {xStar | |xStar 1| + ⋯ + |xStar n| ≤ 1}`. -/
theorem section16_infNorm_sub_lincomb_eq_deltaStar_inter_orthogonalComplement {n m : Nat}
    (a : Fin m → Fin n → ℝ) :
    let L : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ (Set.range a)
    let D : Set (Fin n → ℝ) := {xStar | (∑ j, |xStar j|) ≤ (1 : ℝ)}
    let f : (Fin n → ℝ) → ℝ :=
      fun x => sInf (Set.range fun ξ : Fin m → ℝ => ‖x - ∑ t, (ξ t) • a t‖)
    f = deltaStar (D ∩ (orthogonalComplement n L : Set (Fin n → ℝ))) := by
  classical
  let L : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ (Set.range a)
  let D : Set (Fin n → ℝ) := {xStar | (∑ j, |xStar j|) ≤ (1 : ℝ)}
  let f : (Fin n → ℝ) → ℝ :=
    fun x => sInf (Set.range fun ξ : Fin m → ℝ => ‖x - ∑ t, (ξ t) • a t‖)
  have hD : D = {xStar : Fin n → ℝ | l1Norm xStar ≤ (1 : ℝ)} := by
    ext xStar
    simp [D, l1Norm]
  let A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun ξ => ∑ t, (ξ t) • a t
      map_add' := by
        intro ξ η
        ext j
        simp [Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro c ξ
        ext j
        simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          (Finset.mul_sum (s := (Finset.univ : Finset (Fin m)))
            (f := fun x => a x j * ξ x) (a := c)).symm }
  have hL : L = LinearMap.range A := by
    simpa [A] using (section16_span_range_eq_linearMap_range_sum_smul (a := a))
  have hdist : f = fun x => Metric.infDist x (L : Set (Fin n → ℝ)) := by
    funext x
    have hInf :
        sInf (Set.range fun ξ : Fin m → ℝ => ‖x - A ξ‖) =
          Metric.infDist x (Set.range A) :=
      section16_sInf_range_norm_sub_eq_infDist_range (A := A) x
    have hset : (Set.range A) = (L : Set (Fin n → ℝ)) := by
      ext y
      constructor
      · rintro ⟨ξ, rfl⟩
        have : A ξ ∈ LinearMap.range A := ⟨ξ, rfl⟩
        simp [hL]
      · intro hy
        have : y ∈ LinearMap.range A := by simpa [hL] using hy
        rcases this with ⟨ξ, rfl⟩
        exact ⟨ξ, rfl⟩
    calc
      f x = sInf (Set.range fun ξ : Fin m → ℝ => ‖x - A ξ‖) := by
        simp [f, A]
      _ = Metric.infDist x (Set.range A) := hInf
      _ = Metric.infDist x (L : Set (Fin n → ℝ)) := by
            simp [hset]
  let S : Set (Fin n → ℝ) :=
    {xStar : Fin n → ℝ | l1Norm xStar ≤ (1 : ℝ)} ∩
      (orthogonalComplement n L : Set (Fin n → ℝ))
  let fE : (Fin n → ℝ) → EReal := fun x => (f x : EReal)
  have hstar : fenchelConjugate n fE = indicatorFunction S := by
    simpa [S, fE, hdist] using
      (section16_fenchelConjugate_coe_infDist_submodule_eq_indicator_D_inter_orth (L := L))
  have hclosed :
      ClosedConvexFunction fE ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fE := by
    simpa [fE, hdist] using (section16_closedProperConvex_coe_infDist_submodule (L := L))
  have hbiconj : fenchelConjugate n (fenchelConjugate n fE) = fE := by
    have hb :
        fenchelConjugate n (fenchelConjugate n fE) = clConv n fE := by
      simpa using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := fE))
    have hcl :
        clConv n fE = fE :=
      clConv_eq_of_closedProperConvex (n := n) (f := fE)
        (hf_closed := hclosed.1.2) (hf_proper := hclosed.2)
    simpa [hcl] using hb
  have hfenchel_indicator : fenchelConjugate n (indicatorFunction S) = fE := by
    simpa [hstar] using hbiconj
  have hS_ne : S.Nonempty := by
    refine ⟨0, ?_⟩
    have hD0 : (0 : Fin n → ℝ) ∈ {xStar : Fin n → ℝ | l1Norm xStar ≤ (1 : ℝ)} := by
      simp [l1Norm]
    have hO0 : (0 : Fin n → ℝ) ∈ (orthogonalComplement n L : Set (Fin n → ℝ)) := by
      simp
    exact ⟨hD0, hO0⟩
  have hS_bdd :
      ∀ xStar : Fin n → ℝ,
        BddAbove (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) S) := by
    intro xStar
    simpa [S] using (section16_bddAbove_dotProduct_D_inter_orth (L := L) (x := xStar))
  have hindicator :
      fenchelConjugate n (indicatorFunction S) =
        fun xStar : Fin n → ℝ => ((deltaStar S xStar : ℝ) : EReal) := by
    simpa using
      (section13_fenchelConjugate_indicatorFunction_eq_deltaStar_fun (C := S) hS_ne hS_bdd)
  have hfinalE : fE = fun xStar : Fin n → ℝ => ((deltaStar S xStar : ℝ) : EReal) := by
    calc
      fE = fenchelConjugate n (indicatorFunction S) := by
            simpa using hfenchel_indicator.symm
      _ = fun xStar : Fin n → ℝ => ((deltaStar S xStar : ℝ) : EReal) := hindicator
  have hfinal : f = deltaStar S := by
    funext xStar
    have hx :
        (f xStar : EReal) = ((deltaStar S xStar : ℝ) : EReal) := by
      have := congrArg (fun g => g xStar) hfinalE
      simpa [fE] using this
    exact EReal.coe_injective hx
  simpa [S, hD] using hfinal

/-- Rewriting the piecewise nonnegative extension as a sum with the indicator. -/
lemma section16_piecewise_nonneg_eq_add_indicator_nonnegOrthant {n : Nat}
    (h : (Fin n → ℝ) → EReal) (hnotbot : ∀ x, h x ≠ (⊥ : EReal)) :
    (fun x : Fin n → ℝ => if 0 ≤ x then h x else (⊤ : EReal)) =
      fun x => h x + indicatorFunction {x : Fin n → ℝ | 0 ≤ x} x := by
  classical
  funext x
  by_cases hx : 0 ≤ x
  · simp [indicatorFunction, hx]
  · simp [indicatorFunction, hx, hnotbot x]

/-- The dot-product polar of the nonnegative orthant is the nonpositive orthant. -/
lemma section16_polar_nonnegOrthant_eq_nonpos {n : Nat} :
    {xStar : Fin n → ℝ |
        ∀ x ∈ {x : Fin n → ℝ | 0 ≤ x}, dotProduct x xStar ≤ 0} =
      {xStar : Fin n → ℝ | xStar ≤ 0} := by
  classical
  ext xStar
  constructor
  · intro hx i
    have hxmem : Pi.single i (1 : ℝ) ∈ {x : Fin n → ℝ | 0 ≤ x} := by
      intro j
      by_cases hji : j = i
      · subst hji
        simp
      · simp [Pi.single, hji]
    have hdot : dotProduct (Pi.single i (1 : ℝ)) xStar ≤ 0 := hx _ hxmem
    simpa using hdot
  · intro hxStar x hx
    have hx' : 0 ≤ x := by simpa using hx
    have hsum : ∑ i : Fin n, x i * xStar i ≤ (0 : ℝ) := by
      classical
      refine Finset.sum_nonpos ?_
      intro i hi
      exact mul_nonpos_of_nonneg_of_nonpos (hx' i) (hxStar i)
    simpa [dotProduct] using hsum

/-- The Fenchel conjugate of the nonnegative-orthant indicator is the nonpositive-orthant indicator. -/
lemma section16_fenchelConjugate_indicator_nonnegOrthant_eq_indicator_nonposOrthant {n : Nat} :
    fenchelConjugate n (indicatorFunction {x : Fin n → ℝ | 0 ≤ x}) =
      indicatorFunction {xStar : Fin n → ℝ | xStar ≤ 0} := by
  classical
  let K : ConvexCone ℝ (Fin n → ℝ) :=
    { carrier := {x : Fin n → ℝ | 0 ≤ x}
      smul_mem' := by
        intro c hc x hx
        have hx' : 0 ≤ x := by simpa using hx
        intro i
        have hx_i : 0 ≤ x i := hx' i
        have hc0 : 0 ≤ c := le_of_lt hc
        simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg hc0 hx_i
      add_mem' := by
        intro x hx y hy
        have hx' : 0 ≤ x := by simpa using hx
        have hy' : 0 ≤ y := by simpa using hy
        intro i
        have hx_i : 0 ≤ x i := hx' i
        have hy_i : 0 ≤ y i := hy' i
        simpa [Pi.add_apply] using add_nonneg hx_i hy_i }
  have hKne : (K : Set (Fin n → ℝ)).Nonempty := by
    refine ⟨0, ?_⟩
    simp [K]
  have hsupport :
      supportFunctionEReal (K : Set (Fin n → ℝ)) =
        indicatorFunction
          {xStar : Fin n → ℝ | ∀ x ∈ (K : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0} :=
    section16_supportFunctionEReal_convexCone_eq_indicatorFunction_polar (K := K) hKne
  have hpolar :
      {xStar : Fin n → ℝ | ∀ x ∈ (K : Set (Fin n → ℝ)), dotProduct x xStar ≤ 0} =
        {xStar : Fin n → ℝ | xStar ≤ 0} := by
    simpa [K] using (section16_polar_nonnegOrthant_eq_nonpos (n := n))
  have hpolar' :
      {xStar : Fin n → ℝ | ∀ x, 0 ≤ x → dotProduct x xStar ≤ 0} =
        {xStar : Fin n → ℝ | xStar ≤ 0} := by
    simpa [Set.mem_setOf_eq] using hpolar
  calc
    fenchelConjugate n (indicatorFunction {x : Fin n → ℝ | 0 ≤ x}) =
        supportFunctionEReal ({x : Fin n → ℝ | 0 ≤ x}) :=
      section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal
        (C := {x : Fin n → ℝ | 0 ≤ x})
    _ = indicatorFunction {xStar : Fin n → ℝ | xStar ≤ 0} := by
        have hsupport' :
            supportFunctionEReal ({x : Fin n → ℝ | 0 ≤ x}) =
              indicatorFunction
                {xStar : Fin n → ℝ |
                  ∀ x, 0 ≤ x → dotProduct x xStar ≤ 0} := by
          simpa [K] using hsupport
        simpa [hpolar'] using hsupport'

/-- Infimal convolution with the nonpositive orthant indicator is an infimum over upper bounds. -/
lemma section16_infimalConvolution_with_indicator_nonpos_eq_sInf_image_ge {n : Nat}
    (p : (Fin n → ℝ) → EReal) (hp : ∀ z, p z ≠ (⊥ : EReal)) :
    infimalConvolution p (indicatorFunction {u : Fin n → ℝ | u ≤ 0}) =
      fun xStar => sInf (p '' {zStar : Fin n → ℝ | xStar ≤ zStar}) := by
  classical
  funext xStar
  have hparam :=
    infimalConvolution_eq_sInf_param (f := p)
      (g := indicatorFunction {u : Fin n → ℝ | u ≤ 0}) xStar
  set S1 : Set EReal :=
    { r : EReal |
      ∃ z : Fin n → ℝ, r = indicatorFunction {u : Fin n → ℝ | u ≤ 0} z + p (xStar - z) } with
    hS1
  set S2 : Set EReal := p '' {zStar : Fin n → ℝ | xStar ≤ zStar} with hS2
  have h1 : sInf S1 ≤ sInf S2 := by
    refine le_sInf ?_
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    have hz : xStar - y ≤ 0 := by
      intro i
      exact sub_nonpos.mpr (hy i)
    have hmem : p y ∈ S1 := by
      refine ⟨xStar - y, ?_⟩
      have hxy : xStar - (xStar - y) = y := by
        simp
      simp [indicatorFunction, hz, hxy]
    exact sInf_le hmem
  have h2 : sInf S2 ≤ sInf S1 := by
    refine le_sInf ?_
    intro r hr
    rcases hr with ⟨z, rfl⟩
    by_cases hz : z ≤ 0
    · have hx : xStar ≤ xStar - z := by
        intro i
        have hz_i : z i ≤ 0 := hz i
        have hnonneg : 0 ≤ -z i := by exact neg_nonneg.mpr hz_i
        have hle : xStar i ≤ xStar i + (-z i) := le_add_of_nonneg_right hnonneg
        simpa [sub_eq_add_neg] using hle
      have hmem : p (xStar - z) ∈ S2 := ⟨xStar - z, hx, rfl⟩
      have hle : sInf S2 ≤ p (xStar - z) := sInf_le hmem
      simpa [indicatorFunction, hz] using hle
    · have htop : indicatorFunction {u : Fin n → ℝ | u ≤ 0} z + p (xStar - z) = (⊤ : EReal) := by
        simp [indicatorFunction, hz, hp (xStar - z)]
      simp [htop]
  have hEq : sInf S1 = sInf S2 := le_antisymm h1 h2
  calc
    infimalConvolution p (indicatorFunction {u : Fin n → ℝ | u ≤ 0}) xStar = sInf S1 := by
      simpa [hS1] using hparam
    _ = sInf S2 := hEq

/-- Text 16.4.3: Let `h` be a closed proper convex function on `ℝⁿ`. Define `f` by

`f x = h x` if `x ≥ 0`, and `f x = +∞` otherwise,

where `x ≥ 0` is the coordinatewise order (the non-negative orthant). Then the Fenchel conjugate
`f^*` is the closure of the convex function

`g xStar = inf { h^* zStar | zStar ≥ xStar }`,

again with respect to the coordinatewise order. Here `h^*` is `fenchelConjugate n h` and the
closure is `convexFunctionClosure`. -/
theorem section16_fenchelConjugate_piecewise_nonneg_eq_convexFunctionClosure_sInf_ge {n : ℕ}
    (h : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h) :
    let f : (Fin n → ℝ) → EReal := by
      classical
      exact fun x => if 0 ≤ x then h x else (⊤ : EReal)
    let g : (Fin n → ℝ) → EReal :=
      fun xStar => sInf ((fun zStar => fenchelConjugate n h zStar) '' {zStar | xStar ≤ zStar})
    fenchelConjugate n f = convexFunctionClosure g := by
  classical
  let Kset : Set (Fin n → ℝ) := {x : Fin n → ℝ | 0 ≤ x}
  let Nset : Set (Fin n → ℝ) := {x : Fin n → ℝ | x ≤ 0}
  let f' : (Fin n → ℝ) → EReal := fun x => if 0 ≤ x then h x else (⊤ : EReal)
  let g' : (Fin n → ℝ) → EReal :=
    fun xStar => sInf ((fun zStar => fenchelConjugate n h zStar) '' {zStar | xStar ≤ zStar})
  have hnotbot : ∀ x, h x ≠ (⊥ : EReal) := by
    intro x
    exact hproper.2.2 x (by simp)
  have hf_eq : f' = fun x => h x + indicatorFunction Kset x := by
    simpa [Kset] using
      (section16_piecewise_nonneg_eq_add_indicator_nonnegOrthant (h := h) hnotbot)
  have hKconv : Convex ℝ Kset := by
    simpa [Kset, Set.Ici] using (convex_Ici (r := (0 : Fin n → ℝ)))
  have hKne : Kset.Nonempty := by
    refine ⟨0, ?_⟩
    simp [Kset]
  have hproper_indicator :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (indicatorFunction Kset) :=
    properConvexFunctionOn_indicator_of_convex_of_nonempty (C := Kset) hKconv hKne
  have hclosure_h : convexFunctionClosure h = h :=
    convexFunctionClosure_eq_of_closedConvexFunction (f := h) hclosed hnotbot
  have hNne : Nset.Nonempty := by
    refine ⟨0, ?_⟩
    simp [Nset]
  have hNclosed : IsClosed Nset := by
    simpa [Nset, Set.Iic] using (isClosed_Iic (a := (0 : Fin n → ℝ)))
  have hNconv : Convex ℝ Nset := by
    simpa [Nset, Set.Iic] using (convex_Iic (r := (0 : Fin n → ℝ)))
  have hneg : -Nset = Kset := by
    ext x
    constructor
    · intro hx
      have hx' : -x ≤ 0 := by simpa [Nset] using hx
      have hle : 0 ≤ x := by
        intro i
        have hx_i : (-x) i ≤ 0 := by simpa using (hx' i)
        exact neg_nonpos.mp hx_i
      simpa [Kset] using hle
    · intro hx
      have hx' : 0 ≤ x := by simpa [Kset] using hx
      have hle : -x ≤ 0 := by
        intro i
        exact neg_nonpos.mpr (hx' i)
      simpa [Nset] using hle
  have hclosed_indicator : ClosedConvexFunction (indicatorFunction Kset) := by
    have h :=
      closedConvexFunction_indicator_neg (C := Nset) hNne hNclosed hNconv
    simpa [hneg] using h.1
  have hnotbot_indicator : ∀ x, indicatorFunction Kset x ≠ (⊥ : EReal) := by
    intro x
    by_cases hx : x ∈ Kset <;> simp [indicatorFunction, hx]
  have hclosure_indicator :
      convexFunctionClosure (indicatorFunction Kset) = indicatorFunction Kset :=
    convexFunctionClosure_eq_of_closedConvexFunction
      (f := indicatorFunction Kset) hclosed_indicator hnotbot_indicator
  let F : Fin 2 → (Fin n → ℝ) → EReal := fun i => if i = 0 then h else indicatorFunction Kset
  have hproperF : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (F i) := by
    intro i
    fin_cases i
    · simpa [F] using hproper
    · simpa [F] using hproper_indicator
  have hfenchel :=
    section16_fenchelConjugate_sum_convexFunctionClosure_eq_convexFunctionClosure_infimalConvolutionFamily
      (f := F) hproperF
  have hInf :
      infimalConvolutionFamily (fun i => fenchelConjugate n (F i)) =
        infimalConvolution (fenchelConjugate n h)
          (fenchelConjugate n (indicatorFunction Kset)) := by
    symm
    simpa [F] using
      (infimalConvolution_eq_infimalConvolutionFamily_two
        (f := fenchelConjugate n h)
        (g := fenchelConjugate n (indicatorFunction Kset)))
  have hfenchel' :
      fenchelConjugate n (fun x => h x + indicatorFunction Kset x) =
        convexFunctionClosure
          (infimalConvolution (fenchelConjugate n h)
            (fenchelConjugate n (indicatorFunction Kset))) := by
    simpa [F, Fin.sum_univ_two, hclosure_h, hclosure_indicator, hInf] using hfenchel
  have hindicator :
      fenchelConjugate n (indicatorFunction Kset) = indicatorFunction Nset := by
    simpa [Kset, Nset] using
      (section16_fenchelConjugate_indicator_nonnegOrthant_eq_indicator_nonposOrthant (n := n))
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n h) :=
    proper_fenchelConjugate_of_proper (n := n) (f := h) hproper
  have hstar_notbot : ∀ z, fenchelConjugate n h z ≠ (⊥ : EReal) := by
    intro z
    exact hproperStar.2.2 z (by simp)
  have hinf :
      infimalConvolution (fenchelConjugate n h) (indicatorFunction Nset) =
        fun xStar => sInf ((fun zStar => fenchelConjugate n h zStar) '' {zStar | xStar ≤ zStar}) := by
    simpa [Nset] using
      (section16_infimalConvolution_with_indicator_nonpos_eq_sInf_image_ge
        (p := fenchelConjugate n h) hstar_notbot)
  have hfinal : fenchelConjugate n f' = convexFunctionClosure g' := by
    calc
      fenchelConjugate n f' =
          fenchelConjugate n (fun x => h x + indicatorFunction Kset x) := by
            simp [hf_eq]
      _ =
          convexFunctionClosure
            (infimalConvolution (fenchelConjugate n h)
              (fenchelConjugate n (indicatorFunction Kset))) := hfenchel'
      _ =
          convexFunctionClosure
            (infimalConvolution (fenchelConjugate n h) (indicatorFunction Nset)) := by
            simp [hindicator]
      _ = convexFunctionClosure g' := by
            simp [g', hinf]
  simpa [f', g'] using hfinal

/-- Softmax lies in the simplex and has a positive normalizer. -/
lemma section16_softmax_mem_simplex {n : Nat} (hn : 0 < n) (xStar : Fin n → ℝ) :
    let Z := ∑ j : Fin n, Real.exp (xStar j)
    let ξ0 : Fin n → ℝ := fun j => Real.exp (xStar j) / Z
    (0 ≤ ξ0) ∧ (∑ j, ξ0 j = 1) ∧ 0 < Z := by
  classical
  let Z : ℝ := ∑ j : Fin n, Real.exp (xStar j)
  let ξ0 : Fin n → ℝ := fun j => Real.exp (xStar j) / Z
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    simp
  have hpos' :
      0 < ∑ j, Real.exp (xStar j) := by
    have hpos : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 < Real.exp (xStar j) := by
      intro j hj
      exact Real.exp_pos _
    have hsum :
        0 < ∑ j ∈ (Finset.univ : Finset (Fin n)), Real.exp (xStar j) :=
      Finset.sum_pos hpos hne
    simpa using hsum
  have hZpos : 0 < Z := by
    simpa [Z] using hpos'
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  have hnonneg' : ∀ j, 0 ≤ ξ0 j := by
    intro j
    have hnum : 0 ≤ Real.exp (xStar j) := le_of_lt (Real.exp_pos _)
    have hden : 0 ≤ Z := le_of_lt hZpos
    exact div_nonneg hnum hden
  have hnonneg : 0 ≤ ξ0 := by
    simpa [Pi.le_def] using hnonneg'
  have hsum : ∑ j, ξ0 j = 1 := by
    calc
      ∑ j, ξ0 j = ∑ j, Real.exp (xStar j) / Z := by
        simp [ξ0]
      _ = ∑ j, Real.exp (xStar j) * (1 / Z) := by
        simp [div_eq_mul_inv]
      _ = (∑ j, Real.exp (xStar j)) * (1 / Z) := by
        simpa using
          (Finset.sum_mul (s := Finset.univ) (f := fun j => Real.exp (xStar j)) (a := (1 / Z))).symm
      _ = 1 := by
        simp [Z, div_eq_mul_inv, hZne]
  exact ⟨hnonneg, hsum, hZpos⟩

/-- A weighted exponential term is bounded by the unweighted exponential. -/
lemma section16_mul_exp_sub_log_le_exp {ξ a : ℝ} (hξ : 0 ≤ ξ) :
    ξ * Real.exp (a - Real.log ξ) ≤ Real.exp a := by
  by_cases hξ0 : ξ = 0
  · simpa [hξ0] using (le_of_lt (Real.exp_pos a))
  · have hξpos : 0 < ξ := lt_of_le_of_ne hξ (Ne.symm hξ0)
    have hrewrite : ξ * Real.exp (a - Real.log ξ) = Real.exp a := by
      calc
        ξ * Real.exp (a - Real.log ξ)
            = ξ * (Real.exp a / Real.exp (Real.log ξ)) := by simp [Real.exp_sub]
        _ = ξ * (Real.exp a / ξ) := by simp [Real.exp_log hξpos]
        _ = Real.exp a := by
            field_simp [hξ0]
    simp [hrewrite]

/-- Gibbs inequality for entropy on the simplex. -/
lemma section16_entropy_rangeTerm_le_log_sum_exp {n : Nat} (hn : 0 < n) (ξ : Fin n → ℝ)
    (hξ : 0 ≤ ξ) (hsum : ∑ j, ξ j = (1 : ℝ)) (xStar : Fin n → ℝ) :
    dotProduct ξ xStar - ∑ j, ξ j * Real.log (ξ j) ≤
      Real.log (∑ j, Real.exp (xStar j)) := by
  classical
  have hξ' : ∀ j, 0 ≤ ξ j := by
    simpa [Pi.le_def] using hξ
  have hconv : ConvexOn ℝ (Set.univ : Set ℝ) Real.exp := convexOn_exp
  have hJensen :
      Real.exp (∑ j, ξ j * (xStar j - Real.log (ξ j))) ≤
        ∑ j, ξ j * Real.exp (xStar j - Real.log (ξ j)) := by
    have h0 : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ ξ j := by
      intro j hj
      exact hξ' j
    have h1 : ∑ j ∈ (Finset.univ : Finset (Fin n)), ξ j = 1 := by
      simpa using hsum
    have hmem :
        ∀ j ∈ (Finset.univ : Finset (Fin n)),
          (xStar j - Real.log (ξ j)) ∈ (Set.univ : Set ℝ) := by
      intro j hj
      exact Set.mem_univ _
    have hJ := ConvexOn.map_sum_le (t := (Finset.univ : Finset (Fin n)))
      (w := ξ) (p := fun j => xStar j - Real.log (ξ j)) hconv h0 h1 hmem
    simpa [smul_eq_mul] using hJ
  have hsum_exp :
      ∑ j, ξ j * Real.exp (xStar j - Real.log (ξ j)) ≤
        ∑ j, Real.exp (xStar j) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact section16_mul_exp_sub_log_le_exp (ξ := ξ j) (a := xStar j) (hξ := hξ' j)
  have hle_exp :
      Real.exp (∑ j, ξ j * (xStar j - Real.log (ξ j))) ≤
        ∑ j, Real.exp (xStar j) :=
    le_trans hJensen hsum_exp
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    simp
  have hpos : 0 < ∑ j, Real.exp (xStar j) := by
    have hpos' : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 < Real.exp (xStar j) := by
      intro j hj
      exact Real.exp_pos _
    have hsum_pos : 0 < ∑ j ∈ (Finset.univ : Finset (Fin n)), Real.exp (xStar j) :=
      Finset.sum_pos hpos' hne
    simpa using hsum_pos
  have hlog := (Real.le_log_iff_exp_le hpos).2 hle_exp
  have hsum_eq :
      dotProduct ξ xStar - ∑ j, ξ j * Real.log (ξ j) =
        ∑ j, ξ j * (xStar j - Real.log (ξ j)) := by
    calc
      dotProduct ξ xStar - ∑ j, ξ j * Real.log (ξ j) =
          (∑ j, ξ j * xStar j) - ∑ j, ξ j * Real.log (ξ j) := by
        simp [dotProduct]
      _ = ∑ j, (ξ j * xStar j - ξ j * Real.log (ξ j)) := by
        symm
        simp [Finset.sum_sub_distrib]
      _ = ∑ j, ξ j * (xStar j - Real.log (ξ j)) := by
        simp [mul_sub]
  simpa [hsum_eq] using hlog

/-- The entropy range term attains `log (∑ exp)` at the softmax point. -/
lemma section16_entropy_rangeTerm_eq_log_sum_exp_at_softmax {n : Nat} (hn : 0 < n)
    (xStar : Fin n → ℝ) :
    let Z := ∑ j : Fin n, Real.exp (xStar j)
    let ξ0 : Fin n → ℝ := fun j => Real.exp (xStar j) / Z
    dotProduct ξ0 xStar - ∑ j, ξ0 j * Real.log (ξ0 j) = Real.log Z := by
  classical
  let Z : ℝ := ∑ j : Fin n, Real.exp (xStar j)
  let ξ0 : Fin n → ℝ := fun j => Real.exp (xStar j) / Z
  have hsoft : (0 ≤ ξ0) ∧ (∑ j, ξ0 j = 1) ∧ 0 < Z := by
    simpa [Z, ξ0] using (section16_softmax_mem_simplex (n := n) hn xStar)
  rcases hsoft with ⟨hξ0, hsum, hZpos⟩
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  have hlogξ : ∀ j, Real.log (ξ0 j) = xStar j - Real.log Z := by
    intro j
    have hExpNe : Real.exp (xStar j) ≠ 0 := by exact ne_of_gt (Real.exp_pos _)
    simp [ξ0, Real.log_div, hExpNe, hZne, Real.log_exp]
  have hsumlog :
      ∑ j, ξ0 j * Real.log (ξ0 j) =
        (∑ j, ξ0 j * xStar j) - (∑ j, ξ0 j) * Real.log Z := by
    calc
      ∑ j, ξ0 j * Real.log (ξ0 j) =
          ∑ j, ξ0 j * (xStar j - Real.log Z) := by
        simp [hlogξ]
      _ = ∑ j, (ξ0 j * xStar j - ξ0 j * Real.log Z) := by
        simp [mul_sub]
      _ = (∑ j, ξ0 j * xStar j) - ∑ j, ξ0 j * Real.log Z := by
        simp [Finset.sum_sub_distrib]
      _ = (∑ j, ξ0 j * xStar j) - (∑ j, ξ0 j) * Real.log Z := by
        simpa using
          (Finset.sum_mul (s := (Finset.univ : Finset (Fin n)))
            (f := fun j => ξ0 j) (a := Real.log Z)).symm
  calc
    dotProduct ξ0 xStar - ∑ j, ξ0 j * Real.log (ξ0 j) =
        (∑ j, ξ0 j * xStar j) - ∑ j, ξ0 j * Real.log (ξ0 j) := by
      simp [dotProduct]
    _ = (∑ j, ξ0 j * xStar j) -
          ((∑ j, ξ0 j * xStar j) - (∑ j, ξ0 j) * Real.log Z) := by
      simp [hsumlog]
    _ = (∑ j, ξ0 j) * Real.log Z := by ring
    _ = Real.log Z := by simp [hsum]

end Section16
end Chap03
