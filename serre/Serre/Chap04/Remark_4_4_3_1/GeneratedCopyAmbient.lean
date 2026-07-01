import Serre.Chap04.Remark_4_4_3_1.CoordinateSubspace
import Serre.Chap04.Remark_4_4_3_1.EvalSymmApply

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

theorem matrixCoefficient_codRestrict_generated_copy_ambient_intertwiner_eq_evalSymm
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (y : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hy : y ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (hy0 : y ≠ 0) :
    let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    let x₁ :
        V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex :=
      ⟨y, hy⟩
    let e :=
      ExplicitDecomposition.generatedSubrepresentationEquiv τ σ basis oneIndex x₁
        (by simpa [x₁] using hy0)
    let inclLin :
        (W⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis,
          oneIndex⟯ x₁).toSubmodule →ₗ[ℂ]
          (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule :=
      (W⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis,
        oneIndex⟯ x₁).toSubmodule.subtype
    let incl :
        ((W⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis,
            oneIndex⟯ x₁).toRepresentation).IntertwiningMap τ :=
      inclLin.intertwiningMap_of_isIntertwiningMap
        ((W⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis,
            oneIndex⟯ x₁).toRepresentation) τ
        (fun g x ↦ by
          apply Subtype.ext
          rfl)
    let D : σ.IntertwiningMap τ := incl.comp e.toIntertwiningMap
    D =
      (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁ := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
  let e :=
    ExplicitDecomposition.generatedSubrepresentationEquiv τ σ basis oneIndex x₁
      (by simpa [x₁] using hy0)
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
  let D : σ.IntertwiningMap τ := incl.comp e.toIntertwiningMap
  have hDbasis : D (basis oneIndex) = y := by
    -- The generated-copy ambient map and the Exercise 2-2.7-2 inverse both evaluate to `y` on
    -- the distinguished basis vector, so they represent the same intertwiner.
    have hcoord :
        ((ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁)
            (basis oneIndex) = y := by
      exact
        congrArg Subtype.val
          (LinearEquiv.apply_symm_apply
            (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex) x₁)
    simpa [D, incl, inclLin, e, x₁,
      ExplicitDecomposition.generatedSubrepresentationEquiv,
      ExplicitDecomposition.generatedSubrepresentationHom] using hcoord
  have hEval :
      (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex) D =
        (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex)
          ((ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁) := by
    -- Route correction: pin the comparison down by the unique `Exercise 2-2.7-2` evaluation
    -- equivalence instead of re-expanding the generated copy throughout the later proof.
    calc
      (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex) D = x₁ := by
        apply Subtype.ext
        simpa [x₁, ExplicitDecomposition.intertwiningMapEvaluationEquiv,
          ExplicitDecomposition.intertwiningMapEvaluation] using hDbasis
      _ =
          (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex)
            ((ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁) := by
          symm
          exact LinearEquiv.apply_symm_apply
            (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex) x₁
  exact
    (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).injective
      hEval

/-- Helper for Remark 4-4.3-1: the generated copy `W(y)` comes with a canonical ambient
intertwiner from `σ` into the full `σ`-isotypic summand, and this intertwiner sends the chosen
source vector `x₀` to the original first-coordinate vector `y`. This isolates the remaining
blocker to showing that this copy-local ambient intertwiner is realized by a matrix coefficient.
-/
theorem matrixCoefficient_codRestrict_generated_copy_exists_ambient_intertwiner
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ)
    (y : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hy : y ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (hy0 : y ≠ 0) :
    ∃ D : σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),
      D (chosen_irreducible_vector (G := G) σ) = y ∧
        ∀ x : W,
          D x ∈
            (W⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis,
              oneIndex⟯ ⟨y, hy⟩).toSubmodule := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ :
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex :=
    ⟨y, hy⟩
  let e :=
    ExplicitDecomposition.generatedSubrepresentationEquiv τ σ basis oneIndex x₁
      (by simpa [x₁] using hy0)
  let inclLin :
      (W⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis,
        oneIndex⟯ x₁).toSubmodule →ₗ[ℂ]
        (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule :=
    (W⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis,
      oneIndex⟯ x₁).toSubmodule.subtype
  let incl :
      ((W⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis,
          oneIndex⟯ x₁).toRepresentation).IntertwiningMap τ :=
    inclLin.intertwiningMap_of_isIntertwiningMap
      ((W⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis,
          oneIndex⟯ x₁).toRepresentation) τ
      (fun g x ↦ by
        apply Subtype.ext
        rfl)
  let D : σ.IntertwiningMap τ := incl.comp e.toIntertwiningMap
  have hD_eq :
      D = (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁ := by
    -- Reuse the unique evaluation-characterization of the generated-copy inclusion to keep the
    -- source comparison localized.
    simpa [τ, x₁, e, inclLin, incl, D] using
      matrixCoefficient_codRestrict_generated_copy_ambient_intertwiner_eq_evalSymm
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (y := y) (hy := hy) (hy0 := hy0)
  refine ⟨D, ?_, ?_⟩
  · have hDbasis : D (basis oneIndex) = y := by
      -- Evaluate the canonical comparison at the distinguished basis vector to recover `y`.
      have hDbasis_eq :
          D (basis oneIndex) =
            ((ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁)
              (basis oneIndex) := by
        exact congrArg (fun f : σ.IntertwiningMap τ ↦ f (basis oneIndex)) hD_eq
      have hcoord :
          ((ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁)
              (basis oneIndex) = y := by
        exact
          congrArg Subtype.val
            (LinearEquiv.apply_symm_apply
              (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex) x₁)
      exact hDbasis_eq.trans hcoord
    -- Replace the distinguished basis vector by the chosen irreducible vector `x₀`.
    simpa [hbasis] using hDbasis
  · intro x
    -- By construction the ambient intertwiner factors through the generated copy `W(y)`.
    change (incl (e x)) ∈ (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule
    exact (e x).property

end PeterWeyl

end Representation
