import LinearRepresentations_Serre_1977.Chap04.Remark_4_4_3_1.CoordinateSubspace

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

/-- Helper for Remark 4-4.3-1: once every first-coordinate vector orthogonal to the evaluated
coefficient range is known to vanish, the orthogonal-projection decomposition already produces a
coefficient preimage of the prescribed first-coordinate vector on the chosen source vector. -/
theorem matrixCoefficient_codRestrict_exists_range_preimage_of_firstCoordinate_orthogonal_zero
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
    -- Exercise 2-2.7-2 reconstructs the unique intertwiner whose chosen coordinate is `y`.
    simpa [D, τ, x₁] using
      matrixCoefficient_codRestrict_evalSymm_apply_chosen
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (hbasis := hbasis) (y := y) (hy := hy)
  have hTx₀_mem :
      T x₀ ∈ V⟮τ,σ,basis⟯ oneIndex := by
    -- Every evaluated coefficient vector already lies in the distinguished first-coordinate copy.
    simpa [x₀] using
      matrixCoefficient_codRestrict_fixedVector_mem_coordinateSubspace
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex) hbasis T
  have hr_mem :
      r ∈ V⟮τ,σ,basis⟯ oneIndex := by
    -- The orthogonal residual stays in the same first-coordinate copy as both summands.
    have hDx₀_mem : D x₀ ∈ V⟮τ,σ,basis⟯ oneIndex := by
      simpa [hDx₀] using hy
    exact sub_mem _ hDx₀_mem hTx₀_mem
  have hr_orth :
      ∀ z ∈ LinearMap.range E, inner ℂ z r = 0 := by
    intro z hz
    rcases hz with ⟨ℓ, rfl⟩
    -- The orthogonal-projection witness already kills every evaluated coefficient vector.
    simpa [E, Φ, x₀, r, D] using horth (Φ ℓ) ⟨ℓ, rfl⟩
  have hr_zero : r = 0 := horth_zero r hr_mem hr_orth
  refine ⟨T, hT_range, ?_⟩
  have hDx₀_eq_Tx₀ : D x₀ = T x₀ := by
    -- Vanishing of the residual identifies the coefficient witness with the canonical inverse on
    -- the chosen source vector.
    exact sub_eq_zero.mp (by simpa [r] using hr_zero)
  exact hDx₀_eq_Tx₀.symm.trans hDx₀

/-- Helper for Remark 4-4.3-1: a vector in the distinguished first-coordinate copy that is
orthogonal to every evaluated coefficient vector must vanish. -/
theorem matrixCoefficient_codRestrict_firstCoordinate_orthogonal_zero
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ) :
    ∀ y :
        (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule,
      y ∈ V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex →
      (∀ z ∈ LinearMap.range
          (matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ),
        inner ℂ z y = 0) →
      y = 0 := by
  intro y hy horth
  by_contra hy0
  rcases matrixCoefficient_codRestrict_exists_range_preimage_of_firstCoordinate_orthogonal_zero
      (G := G) (σ := σ) (hσ := hσ) (basis := basis) (oneIndex := oneIndex)
      hbasis (y := y) (hy := hy) (hy0 := hy0) (horth_zero := fun r hr horth_r ↦ by
        exact matrixCoefficient_codRestrict_firstCoordinate_orthogonal_zero
          (G := G) (σ := σ) (hσ := hσ) (basis := basis) (oneIndex := oneIndex)
          hbasis r hr horth_r)
    with ⟨T, hT_range, hTx₀⟩
  let E := matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ
  have hself : inner ℂ y y = 0 := by
    rcases hT_range with ⟨ℓ, rfl⟩
    -- Apply the orthogonality hypothesis to the coefficient witness whose chosen value is `y`.
    simpa [E, hTx₀] using horth (E ℓ) ⟨ℓ, rfl⟩
  exact hy0 (inner_self_eq_zero.mp hself)

end PeterWeyl

end Representation
