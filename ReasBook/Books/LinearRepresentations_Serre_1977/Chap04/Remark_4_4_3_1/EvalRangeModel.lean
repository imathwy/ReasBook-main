import Serre.Chap04.Remark_4_4_3_1.GeneratedCopyContinuous

open MeasureTheory
open DomMulAct
open scoped ENNReal MonoidAlgebra
open scoped ComplexStarModule
open scoped Representation.ExplicitDecomposition

noncomputable section

universe u v

namespace Representation

open Remark_4_4_3_1
local notation "L²(" G ")" => G →₂[(Measure.haar : Measure G)] ℂ

section PeterWeyl

variable {G : Type u} [MeasurableSpace G] [Group G] [TopologicalSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [Finite G]
variable {W : Type v} [TopologicalSpace W] [AddCommGroup W] [Module ℂ W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]

theorem matrixCoefficient_codRestrict_scalar_evaluation_iff_mem_evalRange
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (r : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule) :
    (∃ ell : Module.Dual ℂ W, ∃ c : ℂ, c ≠ 0 ∧
        matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ ell = c • r) ↔
      r ∈ LinearMap.range
        (matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ) := by
  let E := matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ
  constructor
  · rintro ⟨ell, c, hc, hEval⟩
    refine ⟨c⁻¹ • ell, ?_⟩
    -- Rescale the coefficient witness by `c⁻¹` to recover the exact vector `r`.
    calc
      E (c⁻¹ • ell) = c⁻¹ • E ell := by
        simp [E]
      _ = c⁻¹ • (c • r) := by rw [hEval]
      _ = r := by simp [hc]
  · rintro ⟨ell, hEll⟩
    -- Exact range-membership is the special case `c = 1` of the scalar witness.
    refine ⟨ell, 1, one_ne_zero, ?_⟩
    simpa [E] using hEll

/-- Helper for Remark 4-4.3-1: once the exact first-coordinate vector `r` already lies in the
evaluated coefficient range, the previously isolated scalar-line and continuous-model steps build
the full continuous `C(G, ℂ)` realization of the generated copy `W(r)`. This shrinks the
remaining blocker to the pure source Proposition 8 range-membership statement. -/
theorem
    matrixCoefficient_codRestrict_generated_copy_continuous_regular_model_of_mem_evalRange
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ)
    (r : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hr : r ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (hr0 : r ≠ 0)
    (hEvalRange :
      r ∈ LinearMap.range
        (matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ)) :
    let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨r, hr⟩
    let U := W⟮τ,σ,basis,oneIndex⟯ x₁
    ∃ R : U.toSubmodule →ₗ[ℂ] C(G, ℂ),
      (ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ).toLinearMap.comp
          R =
        (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype).comp
          U.toSubmodule.subtype) ∧
      (∀ g : G, ∀ u : U.toSubmodule,
        R (U.toRepresentation g u) =
          (R u).comp ⟨fun t : G ↦ g⁻¹ * t, continuous_const.mul continuous_id⟩) := by
  have hnonzero_eval :
      ∃ ell : Module.Dual ℂ W, ∃ c : ℂ, c ≠ 0 ∧
        matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ ell = c • r := by
    -- Repackage exact evaluated-range membership as the nonzero scalar witness needed by the
    -- already-isolated continuous-model constructor.
    exact
      (matrixCoefficient_codRestrict_scalar_evaluation_iff_mem_evalRange
        (G := G) (σ := σ) (hσ := hσ) (r := r)).2 hEvalRange
  -- The remaining work is exactly the scalar-evaluation-to-continuous-model bridge already
  -- packaged above.
  exact
    matrixCoefficient_codRestrict_generated_copy_continuous_regular_model_of_scalar_evaluation
      (G := G) (σ := σ) (hσ := hσ) (basis := basis) (oneIndex := oneIndex)
      hbasis (r := r) (hr := hr) (hr0 := hr0) hnonzero_eval

/-- Helper for Remark 4-4.3-1: for the canonical Exercise 2-2.7-2 inverse attached to
`r ∈ V_{i,1}`, asking for a coefficient-image preimage on the chosen source vector is equivalent
to asking that `r` itself already lie in the evaluated coefficient range. This isolates the
remaining blocker to exact first-coordinate range-membership. -/
theorem
    matrixCoefficient_codRestrict_evalSymm_fixedVector_preimage_iff_mem_evalRange
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ)
    (r : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hr : r ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex) :
    let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨r, hr⟩
    let D : σ.IntertwiningMap τ :=
      (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁
    (∃ T : σ.IntertwiningMap τ,
        T ∈ LinearMap.range
            (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ) ∧
          T (chosen_irreducible_vector (G := G) σ) = r) ↔
      r ∈ LinearMap.range
        (matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ) := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨r, hr⟩
  let D : σ.IntertwiningMap τ :=
    (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁
  rw [matrixCoefficient_codRestrict_exists_range_preimage_of_fixedVector_iff_mem_evalRange
    (G := G) (σ := σ) (hσ := hσ) (D := D)]
  have hDx₀ : D (chosen_irreducible_vector (G := G) σ) = r := by
    -- Evaluate the canonical inverse at the chosen source vector to recover `r`.
    simpa [τ, x₁] using
      matrixCoefficient_codRestrict_evalSymm_apply_chosen
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (hbasis := hbasis) (y := r) (hy := hr)
  constructor
  · rintro hpreimage
    simpa [hDx₀] using hpreimage
  · intro hrange
    simpa [hDx₀] using hrange

/-- Helper for Remark 4-4.3-1: the remaining open source-local bridge is to produce a genuine
coefficient intertwiner already supported on the single generated copy `W(r)` and nonzero on the
chosen source vector. Once this witness exists, the scalar-line argument above finishes
Proposition 8(c). -/
theorem
    matrixCoefficient_codRestrict_generated_copy_continuous_regular_model_iff_mem_evalRange
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ)
    (r : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hr : r ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (hr0 : r ≠ 0) :
    let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨r, hr⟩
    let U := W⟮τ,σ,basis,oneIndex⟯ x₁
    (∃ R : U.toSubmodule →ₗ[ℂ] C(G, ℂ),
      (ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ).toLinearMap.comp
          R =
        (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype).comp
          U.toSubmodule.subtype) ∧
      (∀ g : G, ∀ u : U.toSubmodule,
        R (U.toRepresentation g u) =
          (R u).comp ⟨fun t : G ↦ g⁻¹ * t, continuous_const.mul continuous_id⟩)) ↔
      r ∈ LinearMap.range
        (matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ) := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨r, hr⟩
  let U := W⟮τ,σ,basis,oneIndex⟯ x₁
  constructor
  · intro hmodel
    rcases hmodel with ⟨R, hR_toLp, hR_cov⟩
    let e :=
      ExplicitDecomposition.generatedSubrepresentationEquiv τ σ basis oneIndex x₁
        (by simpa [x₁] using hr0)
    let F : W →ₗ[ℂ] C(G, ℂ) := R.comp e.toLinearEquiv.toLinearMap
    let inclLin :
        U.toSubmodule →ₗ[ℂ]
          (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule :=
      U.toSubmodule.subtype
    let incl :
        U.toRepresentation.IntertwiningMap τ :=
      inclLin.intertwiningMap_of_isIntertwiningMap U.toRepresentation τ
        (fun g u ↦ by
          apply Subtype.ext
          rfl)
    let D : σ.IntertwiningMap τ :=
      (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁
    have hD_eq : incl.comp e.toIntertwiningMap = D := by
      -- The canonical generated-copy inclusion is already the Exercise 2-2.7-2 inverse.
      simpa [τ, x₁, U, e, inclLin, incl, D] using
        matrixCoefficient_codRestrict_generated_copy_ambient_intertwiner_eq_evalSymm
          (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
          (y := r) (hy := hr) (hy0 := hr0)
    have hF_toLp :
        (ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ).toLinearMap.comp
            F =
          ((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype).comp
            D.toLinearMap := by
      -- Transport the copy-local `C(G, ℂ)` model back across the generated-copy equivalence.
      ext x
      have hRx :
          ((ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ).toLinearMap
              (R (e x))) =
            (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype)
              (U.toSubmodule.subtype (e x))) := by
        exact congrArg (fun L : U.toSubmodule →ₗ[ℂ] L²(G) ↦ L (e x)) hR_toLp
      have hDx :
          (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype)
            (U.toSubmodule.subtype (e x))) =
          (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype) (D x)) := by
        exact
          congrArg
            (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype))
            (congrArg (fun T : σ.IntertwiningMap τ ↦ T x) hD_eq)
      calc
        ((ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ).toLinearMap
            (F x))
            =
          ((ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ).toLinearMap
            (R (e x))) := rfl
        _ =
          (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype)
            (U.toSubmodule.subtype (e x))) := hRx
        _ =
          (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype) (D x)) := hDx
    have hF_cov :
        ∀ g : G, ∀ x : W,
          F (σ g x) =
            (F x).comp ⟨fun t : G ↦ g⁻¹ * t, continuous_const.mul continuous_id⟩ := by
      -- Covariance is preserved by precomposition with the generated-copy equivalence.
      intro g x
      calc
        F (σ g x) = R (e (σ g x)) := rfl
        _ = R (U.toRepresentation g (e x)) := by
              simpa using congr($(e.isIntertwining' g) x)
        _ = (R (e x)).comp
              ⟨fun t : G ↦ g⁻¹ * t, continuous_const.mul continuous_id⟩ := hR_cov g (e x)
        _ = (F x).comp
              ⟨fun t : G ↦ g⁻¹ * t, continuous_const.mul continuous_id⟩ := rfl
    have hD_range :
        D ∈ LinearMap.range
          (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
            (G := G) σ hσ) := by
      -- The transported continuous model realizes the canonical inverse as a coefficient image.
      exact
        matrixCoefficient_codRestrict_mem_range_of_continuous_model
          (G := G) (σ := σ) (hσ := hσ) D F hF_toLp hF_cov
    have hpreimage :
        ∃ T : σ.IntertwiningMap τ,
          T ∈ LinearMap.range
              (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
                (G := G) σ hσ) ∧
            T (chosen_irreducible_vector (G := G) σ) = r := by
      refine ⟨D, hD_range, ?_⟩
      -- Evaluate the canonical Exercise 2-2.7-2 inverse on the chosen source vector.
      simpa [τ, x₁] using
        matrixCoefficient_codRestrict_evalSymm_apply_chosen
          (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
          (hbasis := hbasis) (y := r) (hy := hr)
    -- The fixed-vector preimage criterion is equivalent to exact membership in the evaluated
    -- coefficient range.
    exact
      (matrixCoefficient_codRestrict_evalSymm_fixedVector_preimage_iff_mem_evalRange
        (G := G) (σ := σ) (hσ := hσ) (basis := basis) (oneIndex := oneIndex)
        (hbasis := hbasis) (r := r) (hr := hr)).1 hpreimage
  · intro hEvalRange
    -- The reverse implication is the already isolated source-faithful range-to-model step.
    exact
      matrixCoefficient_codRestrict_generated_copy_continuous_regular_model_of_mem_evalRange
        (G := G) (σ := σ) (hσ := hσ) (basis := basis) (oneIndex := oneIndex)
        hbasis (r := r) (hr := hr) (hr0 := hr0) hEvalRange

/-- Helper for Remark 4-4.3-1: the remaining open source-local bridge is to produce a genuine
coefficient intertwiner already supported on the single generated copy `W(r)` and nonzero on the
chosen source vector. Once this witness exists, the scalar-line argument above finishes
Proposition 8(c). -/
theorem
    matrixCoefficient_codRestrict_generated_copy_continuous_regular_model
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ)
    (r : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hr : r ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (hr0 : r ≠ 0) :
    let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨r, hr⟩
    let U := W⟮τ,σ,basis,oneIndex⟯ x₁
    ∃ R : U.toSubmodule →ₗ[ℂ] C(G, ℂ),
      (ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ).toLinearMap.comp
          R =
        (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype).comp
          U.toSubmodule.subtype) ∧
      (∀ g : G, ∀ u : U.toSubmodule,
        R (U.toRepresentation g u) =
          (R u).comp ⟨fun t : G ↦ g⁻¹ * t, continuous_const.mul continuous_id⟩) := by
  -- Route correction: the transport/coercion part is now isolated in the previous helper.
  -- Route correction: the scalar-line postprocessing and the continuous-model transport are now
  -- packaged in the helper above. The sole remaining source-faithful blocker is the compact
  -- Proposition 8 statement that every nonzero `r ∈ V_{i,1}` already lies in the evaluated
  -- coefficient range.
  have hEvalRange :
      r ∈ LinearMap.range
        (matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ) := by
    -- The compact Proposition 8 spanning step has already been isolated as the exact equality
    -- between the evaluated coefficient range and the first-coordinate copy `V_{i,1}`.
    rw [matrixCoefficient_codRestrict_evalRange_eq_coordinateSubspace
      (G := G) (σ := σ) (hσ := hσ) (basis := basis) (oneIndex := oneIndex)
      hbasis]
    exact hr
  -- The source-faithful bridge has now been reduced exactly to the range-membership statement
  -- above; the transport from that statement to the `C(G, ℂ)` model is packaged separately.
  exact
    (matrixCoefficient_codRestrict_generated_copy_continuous_regular_model_iff_mem_evalRange
      (G := G) (σ := σ) (hσ := hσ) (basis := basis) (oneIndex := oneIndex)
      hbasis (r := r) (hr := hr) (hr0 := hr0)).2 hEvalRange

/-- Helper for Remark 4-4.3-1: once the single generated copy `W(r)` is realized inside
`C(G, ℂ)`, transport that realization back across the canonical generated-copy equivalence to get
the continuous model needed for the canonical Exercise 2-2.7-2 inverse. -/
theorem
    matrixCoefficient_codRestrict_evalSymm_continuous_model_from_generated_copy
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (r : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hr : r ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (hr0 : r ≠ 0) :
    ∃ F : W →ₗ[ℂ] C(G, ℂ),
      let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
      let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨r, hr⟩
      let D : σ.IntertwiningMap τ :=
        (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁
      (ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ).toLinearMap.comp
          F =
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype).comp D.toLinearMap
        ∧
      (∀ g : G, ∀ x : W,
        F (σ g x) =
          (F x).comp ⟨fun t : G ↦ g⁻¹ * t, continuous_const.mul continuous_id⟩) := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨r, hr⟩
  let U := W⟮τ,σ,basis,oneIndex⟯ x₁
  let e :=
    ExplicitDecomposition.generatedSubrepresentationEquiv τ σ basis oneIndex x₁
      (by simpa [x₁] using hr0)
  rcases
      matrixCoefficient_codRestrict_generated_copy_continuous_regular_model
        (G := G) (σ := σ) (hσ := hσ) (basis := basis) (oneIndex := oneIndex)
        hbasis (r := r) (hr := hr) (hr0 := hr0) with
    ⟨R, hR_toLp, hR_cov⟩
  let F : W →ₗ[ℂ] C(G, ℂ) := R.comp e.toLinearEquiv.toLinearMap
  refine ⟨F, ?_, ?_⟩
  · -- Rewrite the transported continuous model through the canonical generated-copy inclusion.
    let inclLin :
        U.toSubmodule →ₗ[ℂ]
          (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule :=
      U.toSubmodule.subtype
    let incl :
        U.toRepresentation.IntertwiningMap τ :=
      inclLin.intertwiningMap_of_isIntertwiningMap U.toRepresentation τ
        (fun g u ↦ by
          apply Subtype.ext
          rfl)
    let D : σ.IntertwiningMap τ :=
      (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁
    have hD_eq : incl.comp e.toIntertwiningMap = D := by
      -- The canonical generated-copy inclusion is already the Exercise 2-2.7-2 inverse.
      simpa [τ, x₁, U, e, inclLin, incl, D] using
        matrixCoefficient_codRestrict_generated_copy_ambient_intertwiner_eq_evalSymm
          (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
          (y := r) (hy := hr) (hy0 := hr0)
    ext x
    have hRx :
        ((ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ).toLinearMap
            (R (e x))) =
          (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype)
            (U.toSubmodule.subtype (e x))) := by
      exact congrArg (fun L : U.toSubmodule →ₗ[ℂ] L²(G) ↦ L (e x)) hR_toLp
    have hDx :
        (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype)
          (U.toSubmodule.subtype (e x))) =
        (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype) (D x)) := by
      exact
        congrArg
          (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype))
          (congrArg (fun T : σ.IntertwiningMap τ ↦ T x) hD_eq)
    calc
      ((ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ).toLinearMap
          (F x))
          =
        ((ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ).toLinearMap
          (R (e x))) := rfl
      _ =
        (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype)
          (U.toSubmodule.subtype (e x))) := hRx
      _ =
        (((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype) (D x)) := hDx
  · -- Covariance is preserved by precomposition with the generated-copy equivalence `e`.
    intro g x
    calc
      F (σ g x) = R (e (σ g x)) := rfl
      _ = R (U.toRepresentation g (e x)) := by
            simpa using congr($(e.isIntertwining' g) x)
      _ = (R (e x)).comp
            ⟨fun t : G ↦ g⁻¹ * t, continuous_const.mul continuous_id⟩ := hR_cov g (e x)
      _ = (F x).comp
            ⟨fun t : G ↦ g⁻¹ * t, continuous_const.mul continuous_id⟩ := rfl

/-- Helper for Remark 4-4.3-1: the remaining open source-local bridge is to produce a genuine
coefficient intertwiner already supported on the single generated copy `W(r)` and nonzero on the
chosen source vector. Once this witness exists, the scalar-line argument above finishes
Proposition 8(c). -/
theorem
    matrixCoefficient_codRestrict_exists_copy_local_coefficient_witness_of_continuous_model
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ)
    (r : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hr : r ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (hr0 : r ≠ 0)
    (F : W →ₗ[ℂ] C(G, ℂ))
    (hF_toLp :
      let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
      let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨r, hr⟩
      let D : σ.IntertwiningMap τ :=
        (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁
      (ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ).toLinearMap.comp
          F =
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype).comp D.toLinearMap)
    (hF_cov :
      ∀ g : G, ∀ x : W,
        F (σ g x) =
          (F x).comp ⟨fun t : G ↦ g⁻¹ * t, continuous_const.mul continuous_id⟩) :
    ∃ T : σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),
      T ∈ LinearMap.range
          (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
            (G := G) σ hσ) ∧
        (∀ x : W,
          T x ∈
            (W⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis,
              oneIndex⟯ ⟨r, hr⟩).toSubmodule) ∧
        T (chosen_irreducible_vector (G := G) σ) ≠ 0 := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨r, hr⟩
  let D : σ.IntertwiningMap τ :=
    (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁
  have hD_range : D ∈ LinearMap.range Φ := by
    -- The generic continuous-model criterion turns the source-faithful `C(G, ℂ)` realization of
    -- the canonical generated-copy inverse into an actual coefficient image.
    exact
      matrixCoefficient_codRestrict_mem_range_of_continuous_model
        (G := G) (σ := σ) (hσ := hσ) D F
        (by simpa [τ, x₁, D] using hF_toLp) hF_cov
  -- Once `evalSymm` is in the coefficient-image range, the earlier packaging lemma produces the
  -- desired copy-local witness supported on `W(r)`.
  exact
    matrixCoefficient_codRestrict_exists_copy_local_coefficient_witness_of_evalSymm_mem_range
      (G := G) (σ := σ) (hσ := hσ) (basis := basis) (oneIndex := oneIndex)
      hbasis (r := r) (hr := hr) (hr0 := hr0) (by
        simpa [τ, Φ, x₁, D] using hD_range)

/-- Helper for Remark 4-4.3-1: the remaining open source-local bridge is to produce a genuine
coefficient intertwiner already supported on the single generated copy `W(r)` and nonzero on the
chosen source vector. Once this witness exists, the scalar-line argument above finishes
Proposition 8(c). -/

end PeterWeyl

end Representation
