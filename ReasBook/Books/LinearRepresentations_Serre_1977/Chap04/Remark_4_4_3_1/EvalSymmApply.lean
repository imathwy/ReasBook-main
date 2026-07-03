import Serre.Chap04.Remark_4_4_3_1.CyclicRegular
import Serre.Chap04.Remark_4_4_3_1.FixedVectorRangeBridge

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

/-- Helper for Remark 4-4.3-1: the canonical Exercise 2-2.7-2 inverse attached to a vector
`y ∈ V_{i,1}` sends the chosen irreducible source vector `x₀` back to `y`. This keeps the
remaining blocker focused only on range-membership of that canonical intertwiner. -/
theorem matrixCoefficient_codRestrict_evalSymm_apply_chosen
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ)
    (y : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hy : y ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex) :
    let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
    ((ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁)
        (chosen_irreducible_vector (G := G) σ) = y := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
  have hDbasis :
      ((ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁)
          (basis oneIndex) = y := by
    -- Evaluate the canonical inverse at the distinguished basis vector to recover its coordinate.
    exact congrArg Subtype.val
      (LinearEquiv.apply_symm_apply
        (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex) x₁)
  -- Replace the distinguished basis vector by the chosen irreducible vector `x₀`.
  simpa [τ, x₁, hbasis] using hDbasis

end PeterWeyl

end Representation
