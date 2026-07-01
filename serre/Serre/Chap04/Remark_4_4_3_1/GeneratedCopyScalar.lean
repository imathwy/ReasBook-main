import Serre.Chap04.Remark_4_4_3_1.GeneratedCopyLocal

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

theorem matrixCoefficient_codRestrict_generated_copy_ambient_intertwiner_eq_smul
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ)
    (y : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hy : y ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (hy0 : y ≠ 0) :
    let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
    let inclLin :
        (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule →ₗ[ℂ]
          (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule :=
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule.subtype
    let incl :
        ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation).IntertwiningMap τ :=
      inclLin.intertwiningMap_of_isIntertwiningMap
        ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation) τ
        (fun g x ↦ by
          apply Subtype.ext
          rfl)
    ∀ T : σ.IntertwiningMap (W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation,
      ∃ c : ℂ,
        incl.comp T =
          c • (incl.comp (ExplicitDecomposition.generatedSubrepresentationHom
            τ σ basis oneIndex x₁)) := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
  let inclLin :
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule →ₗ[ℂ]
        (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule :=
    (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule.subtype
  let incl :
      ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation).IntertwiningMap τ :=
    inclLin.intertwiningMap_of_isIntertwiningMap
      ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation) τ
      (fun g x ↦ by
        apply Subtype.ext
        rfl)
  intro T
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  let D : σ.IntertwiningMap τ := incl.comp T
  have hDx₀_mem_copy :
      D x₀ ∈ (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule := by
    -- Because `T` already lands in the generated copy, the ambient inclusion keeps its fixed
    -- vector inside `W(y)`.
    simpa [D, incl, inclLin, x₀] using (T x₀).2
  have hDx₀_mem_first :
      D x₀ ∈ V⟮τ,σ,basis⟯ oneIndex := by
    -- Exercise 2-2.7-2 still places the chosen-vector value in the distinguished first
    -- coordinate slice.
    simpa [D, x₀] using
      matrixCoefficient_codRestrict_fixedVector_mem_coordinateSubspace
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex) hbasis D
  rcases
      matrixCoefficient_codRestrict_first_coordinate_mem_smul_generated_vector
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (y := y) (hy := hy) (z := D x₀)
        hDx₀_mem_copy hDx₀_mem_first with
    ⟨c, hc⟩
  let Dcanon : σ.IntertwiningMap τ :=
    incl.comp (ExplicitDecomposition.generatedSubrepresentationHom τ σ basis oneIndex x₁)
  have hDcanon_eq :
      Dcanon =
        (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁ := by
    -- The canonical ambient inclusion of `W(y)` is already the Exercise 2-2.7-2 inverse.
    simpa [Dcanon, incl, inclLin, x₁,
      ExplicitDecomposition.generatedSubrepresentationEquiv,
      ExplicitDecomposition.generatedSubrepresentationHom] using
      matrixCoefficient_codRestrict_generated_copy_ambient_intertwiner_eq_evalSymm
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (y := y) (hy := hy) (hy0 := hy0)
  have hDcanon_x₀ : Dcanon x₀ = y := by
    have hDbasis : Dcanon (basis oneIndex) = y := by
      have hcoord :
          ((ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁)
              (basis oneIndex) = y := by
        exact
          congrArg Subtype.val
            (LinearEquiv.apply_symm_apply
              (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex) x₁)
      exact (congrArg (fun f : σ.IntertwiningMap τ ↦ f (basis oneIndex)) hDcanon_eq).trans hcoord
    -- Replace the distinguished basis vector by the chosen irreducible vector.
    simpa [x₀, hbasis] using hDbasis
  have hbasis_eval :
      D (basis oneIndex) = (c • Dcanon) (basis oneIndex) := by
    -- Both ambient maps take the distinguished basis vector to the same scalar multiple of `y`.
    simpa [x₀, hbasis, hDcanon_x₀] using hc
  have hEval_eq :
      (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex) D =
        (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex) (c • Dcanon) := by
    apply Subtype.ext
    simpa [ExplicitDecomposition.intertwiningMapEvaluationEquiv,
      ExplicitDecomposition.intertwiningMapEvaluation] using hbasis_eval
  -- The ambient evaluation equivalence on `V_{i,1}` identifies the two intertwiners.
  refine ⟨c, ?_⟩
  exact
    (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).injective hEval_eq

/-- Helper for Remark 4-4.3-1: once one coefficient intertwiner already lands in the single
generated copy `W(y)` and is nonzero on the chosen source vector, the scalar-uniqueness argument
upgrades that witness to the canonical generated-copy inclusion. This isolates the remaining
source blocker to constructing such a copy-local coefficient witness. -/
theorem
    matrixCoefficient_codRestrict_generated_copy_hom_mem_range_of_nonzero_witness
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ)
    (y : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hy : y ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (hy0 : y ≠ 0)
    (T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (hT_range :
      T ∈ LinearMap.range
        (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
          (G := G) σ hσ))
    (hT_mem :
      ∀ x : W,
        T x ∈
          (W⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis,
            oneIndex⟯ ⟨y, hy⟩).toSubmodule)
    (hTx₀_ne : T (chosen_irreducible_vector (G := G) σ) ≠ 0) :
    let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
    let inclLin :
        (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule →ₗ[ℂ]
          (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule :=
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule.subtype
    let incl :
        ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation).IntertwiningMap τ :=
      inclLin.intertwiningMap_of_isIntertwiningMap
        ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation) τ
        (fun g x ↦ by
          apply Subtype.ext
          rfl)
    incl.comp (ExplicitDecomposition.generatedSubrepresentationHom τ σ basis oneIndex x₁) ∈
      LinearMap.range
        (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
          (G := G) σ hσ) := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let inclLin :
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule →ₗ[ℂ]
        (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule :=
    (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule.subtype
  let incl :
      ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation).IntertwiningMap τ :=
    inclLin.intertwiningMap_of_isIntertwiningMap
      ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation) τ
      (fun g x ↦ by
        apply Subtype.ext
        rfl)
  let TcopyLin :
      W →ₗ[ℂ] (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule :=
    T.toLinearMap.codRestrict
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule
      hT_mem
  let Tcopy :
      σ.IntertwiningMap (W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation :=
    TcopyLin.intertwiningMap_of_isIntertwiningMap σ
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation
      (fun g x ↦ by
        apply Subtype.ext
        simpa [TcopyLin] using congr($(T.isIntertwining' g) x))
  let Dcanon : σ.IntertwiningMap τ :=
    incl.comp (ExplicitDecomposition.generatedSubrepresentationHom τ σ basis oneIndex x₁)
  have hT_eq : incl.comp Tcopy = T := by
    -- Re-including the codomain restriction recovers the original copy-local ambient intertwiner.
    apply Representation.IntertwiningMap.ext
    intro x
    apply Subtype.ext
    rfl
  rcases
      matrixCoefficient_codRestrict_generated_copy_ambient_intertwiner_eq_smul
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        hbasis (y := y) (hy := hy) (hy0 := hy0) Tcopy with
    ⟨c, hc⟩
  have hT_scalar : T = c • Dcanon := by
    -- Scalar uniqueness on the generated copy expresses the witness as a multiple of `Dcanon`.
    simpa [Dcanon] using hT_eq.symm.trans hc
  have hDcanon_eq :
      Dcanon =
        (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁ := by
    -- The canonical generated-copy inclusion is already the Exercise 2-2.7-2 inverse.
    simpa [Dcanon, incl, inclLin, x₁,
      ExplicitDecomposition.generatedSubrepresentationEquiv,
      ExplicitDecomposition.generatedSubrepresentationHom] using
      matrixCoefficient_codRestrict_generated_copy_ambient_intertwiner_eq_evalSymm
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (y := y) (hy := hy) (hy0 := hy0)
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  have hDcanon_x₀ : Dcanon x₀ = y := by
    have hDbasis : Dcanon (basis oneIndex) = y := by
      -- Evaluate the canonical inverse at the distinguished basis vector to recover `y`.
      have hcoord :
          ((ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁)
              (basis oneIndex) = y := by
        exact
          congrArg Subtype.val
            (LinearEquiv.apply_symm_apply
              (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex) x₁)
      exact (congrArg (fun f : σ.IntertwiningMap τ ↦ f (basis oneIndex)) hDcanon_eq).trans hcoord
    -- Replace the distinguished basis vector by the chosen irreducible vector `x₀`.
    simpa [x₀, hbasis] using hDbasis
  have hTx₀_eq : T x₀ = c • y := by
    -- Evaluate the scalar-comparison at the chosen source generator to read off the scalar.
    simpa [x₀, hDcanon_x₀] using
      congrArg (fun f : σ.IntertwiningMap τ ↦ f x₀) hT_scalar
  have hc_ne : c ≠ 0 := by
    -- Because the witness is nonzero on `x₀` and `y ≠ 0`, the comparison scalar is nonzero.
    intro hc0
    apply hTx₀_ne
    rw [hTx₀_eq, hc0, zero_smul]
  have hscaled_range : c⁻¹ • T ∈ LinearMap.range Φ := by
    -- The matrix-coefficient range is a submodule, so it is closed under scalar rescaling.
    exact smul_mem (LinearMap.range Φ) _ hT_range
  have hcanon_eq : c⁻¹ • T = Dcanon := by
    -- Invert the nonzero scalar to recover the canonical generated-copy inclusion itself.
    calc
      c⁻¹ • T = c⁻¹ • (c • Dcanon) := by rw [hT_scalar]
      _ = Dcanon := by simp [hc_ne, Dcanon]
  exact hcanon_eq ▸ hscaled_range

/-- Helper for Remark 4-4.3-1: once every first-coordinate vector orthogonal to the evaluated
coefficient range is known to vanish, the orthogonal-projection decomposition already produces a
coefficient preimage of the canonical Exercise 2-2.7-2 inverse on the chosen source vector. This
shrinks the blocker from a copy-local witness with several side conditions to one pure
orthogonality statement in `V_{i,1}`. -/
theorem
    matrixCoefficient_codRestrict_exists_range_preimage_of_firstCoordinate_orthogonal_zero
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ)
    (y : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hy : y ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (hy0 : y ≠ 0)
    (horth_zero :
      ∀ r : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule,
        r ∈
          V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯
            oneIndex →
        (∀ z ∈ LinearMap.range
            (matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ),
          inner ℂ z r = 0) →
        r = 0) :
    ∃ T : σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),
      T ∈ LinearMap.range
          (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
            (G := G) σ hσ) ∧
        T (chosen_irreducible_vector (G := G) σ) = y := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
  let D : σ.IntertwiningMap τ :=
    (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let E := matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  obtain ⟨T, hT_range, horth⟩ :=
    matrixCoefficient_codRestrict_exists_range_preimage_with_orthogonal_residual
      (G := G) (σ := σ) (hσ := hσ) D
  let r : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule := (D - T) x₀
  have hDx₀ : D x₀ = y := by
    -- The canonical inverse recovers the prescribed first-coordinate vector on `x₀`.
    simpa [D, τ, x₁] using
      matrixCoefficient_codRestrict_evalSymm_apply_chosen
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (hbasis := hbasis) (y := y) (hy := hy)
  have hTx₀_mem :
      T x₀ ∈ V⟮τ,σ,basis⟯ oneIndex := by
    -- Every coefficient intertwiner still evaluates into the distinguished coordinate slice.
    simpa [x₀] using
      matrixCoefficient_codRestrict_fixedVector_mem_coordinateSubspace
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex) hbasis T
  have hr_mem :
      r ∈ V⟮τ,σ,basis⟯ oneIndex := by
    -- The residual stays in `V_{i,1}` because both `D x₀ = y` and `T x₀` do.
    have hDx₀_mem : D x₀ ∈ V⟮τ,σ,basis⟯ oneIndex := by
      simpa [hDx₀] using hy
    exact sub_mem _ hDx₀_mem hTx₀_mem
  have hr_orth :
      ∀ z ∈ LinearMap.range E, inner ℂ z r = 0 := by
    intro z hz
    rcases hz with ⟨ℓ, rfl⟩
    -- The orthogonal-projection witness already kills all evaluated coefficient vectors.
    simpa [E, Φ, x₀, r, D] using horth (Φ ℓ) ⟨ℓ, rfl⟩
  have hr_zero : r = 0 := horth_zero r hr_mem hr_orth
  refine ⟨T, hT_range, ?_⟩
  have hDx₀_eq_Tx₀ : D x₀ = T x₀ := by
    -- Vanishing of the residual identifies the coefficient witness with the canonical inverse on
    -- the chosen source vector.
    exact sub_eq_zero.mp (by simpa [r] using hr_zero)
  exact hDx₀_eq_Tx₀.symm.trans hDx₀

/-- Helper for Remark 4-4.3-1: once a coefficient intertwiner already hits the prescribed
first-coordinate vector `y`, its range is forced into the single generated copy `W(y)` by the
cyclic-subrepresentation collapse `V(y) = W(y)`. The scalar-uniqueness argument can then upgrade
that witness to the canonical generated-copy inclusion. -/
theorem
    matrixCoefficient_codRestrict_generated_copy_hom_mem_range_of_fixedVector_preimage
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ)
    (y : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hy : y ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (hy0 : y ≠ 0)
    (T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (hT_range :
      T ∈ LinearMap.range
        (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
          (G := G) σ hσ))
    (hTx₀ : T (chosen_irreducible_vector (G := G) σ) = y) :
    let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
    let inclLin :
        (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule →ₗ[ℂ]
          (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule :=
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule.subtype
    let incl :
        ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation).IntertwiningMap τ :=
      inclLin.intertwiningMap_of_isIntertwiningMap
        ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation) τ
        (fun g x ↦ by
          apply Subtype.ext
          rfl)
    incl.comp (ExplicitDecomposition.generatedSubrepresentationHom τ σ basis oneIndex x₁) ∈
      LinearMap.range
        (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
          (G := G) σ hσ) := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
  let inclLin :
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule →ₗ[ℂ]
        (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule :=
    (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule.subtype
  let incl :
      ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation).IntertwiningMap τ :=
    inclLin.intertwiningMap_of_isIntertwiningMap
      ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation) τ
      (fun g x ↦ by
        apply Subtype.ext
        rfl)
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  have hT_mem :
      ∀ x : W, T x ∈ (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule := by
    intro x
    have hcyc_mem :
        T x ∈ (V⟮τ⟯ y).toSubmodule := by
      -- Because `x₀` generates `σ`, the whole range of `T` sits inside the cyclic
      -- subrepresentation generated by `T x₀ = y`.
      simpa [x₀, hTx₀] using
        intertwiningMap_range_le_cyclicSubrepresentation_of_apply_chosen
          (G := G) (τ := τ) (σ := σ) T
          (LinearMap.mem_range.mpr ⟨x, rfl⟩)
    have hcyc_eq :
        V⟮τ⟯ y = W⟮τ,σ,basis,oneIndex⟯ x₁ := by
      -- The Exercise 2-2.7.4 collapse turns the cyclic representation of `y` into the single
      -- generated copy `W(y)`.
      simpa [τ, x₁] using
        matrixCoefficient_codRestrict_first_coordinate_cyclicSubrepresentation_eq_generated_copy
          (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
          hbasis (y := y) (hy := hy) (hy0 := hy0)
    simpa [hcyc_eq] using hcyc_mem
  have hTx₀_ne : T x₀ ≠ 0 := by
    -- The prescribed evaluation is the nonzero vector `y`.
    simpa [x₀, hTx₀] using hy0
  exact
    matrixCoefficient_codRestrict_generated_copy_hom_mem_range_of_nonzero_witness
      (G := G) (σ := σ) (hσ := hσ) (basis := basis) (oneIndex := oneIndex)
      hbasis (y := y) (hy := hy) (hy0 := hy0) T hT_range hT_mem hTx₀_ne

/-- Helper for Remark 4-4.3-1: once a coefficient intertwiner already lands in the single
generated copy `W(r)` and is nonzero on the chosen source vector `x₀`, its chosen-vector
evaluation is automatically a nonzero scalar multiple of `r`. This packages the easy scalar-line
part of Proposition 8(c), so the only remaining blocker is producing the copy-local coefficient
witness itself. -/
theorem
    matrixCoefficient_codRestrict_copy_local_witness_yields_nonzero_smul_eval
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ)
    (r : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hr : r ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (hT_range :
      T ∈ LinearMap.range
        (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
          (G := G) σ hσ))
    (hT_mem :
      ∀ x : W,
        T x ∈
          (W⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis,
            oneIndex⟯ ⟨r, hr⟩).toSubmodule)
    (hTx₀_ne : T (chosen_irreducible_vector (G := G) σ) ≠ 0) :
    ∃ ell : Module.Dual ℂ W, ∃ c : ℂ, c ≠ 0 ∧
      matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ ell = c • r := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨r, hr⟩
  let E := matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  rcases hT_range with ⟨ell, rfl⟩
  have hEval_mem_copy :
      E ell ∈ (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule := by
    -- Evaluating the copy-local coefficient witness at `x₀` keeps the image inside `W(r)`.
    simpa [E, x₀, τ, x₁] using hT_mem x₀
  have hEval_mem_first :
      E ell ∈ V⟮τ,σ,basis⟯ oneIndex := by
    -- Every evaluated coefficient vector still lies in the distinguished first-coordinate copy.
    simpa [E, x₀, τ] using
      matrixCoefficient_codRestrict_fixedVector_mem_coordinateSubspace
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex) hbasis
        ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
          (G := G) σ hσ) ell)
  rcases
      matrixCoefficient_codRestrict_first_coordinate_mem_smul_generated_vector
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (y := r) (hy := hr) (z := E ell) hEval_mem_copy hEval_mem_first with
    ⟨c, hc⟩
  have hc_ne : c ≠ 0 := by
    intro hc0
    apply hTx₀_ne
    have hzero : E ell = 0 := by simpa [hc0] using hc
    simpa [E, x₀] using hzero
  refine ⟨ell, c, hc_ne, hc⟩

/-- Helper for Remark 4-4.3-1: scaling a nonzero vector in the distinguished first-coordinate
copy does not change the generated copy `W(r)`. This is the source-level fact that
`W(c • r) = W(r)` for `c ≠ 0`, expressed in the theorem-local `Exercise 2-2.7.4` API. -/

end PeterWeyl

end Representation
