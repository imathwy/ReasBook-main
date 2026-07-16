import Mathlib.Tactic.Recall
import LinearRepresentations_Serre_1977.Serre.Chap04.Proposition_4_34
import LinearRepresentations_Serre_1977.Serre.Chap04.Proposition_4_35

noncomputable section

open scoped MonoidAlgebra Representation

-- Semantic recall: `lean_leansearch` surfaced only general isotypic-component API, so this item
-- stays on the Chapter 4 matrix-coefficient projection owners introduced in Proposition 4-34.

universe u v w x y

namespace Representation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V]
variable {Hπ : Type w} [NormedAddCommGroup Hπ] [InnerProductSpace ℂ Hπ]
  [FiniteDimensional ℂ Hπ]
variable {Hσ : Type x} [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ]
  [FiniteDimensional ℂ Hσ]
variable {ι : Type y} [Fintype ι]

/-- Proposition 4-36 (1): if `π` and `σ` are nonisomorphic irreducible unitary
representations, then `p[ρ, π, b; α, β]` vanishes on the canonical `σ`-isotypic component
`(ρ.isotypicSubrepresentation σ).toSubmodule` of `ρ`. -/
theorem matrixCoefficientProjection_apply_eq_zero_of_mem_otherIsotypicComponent
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ] [Representation.IsIrreducible σ]
    [Representation.IsUnitary π] [Representation.IsUnitary σ]
    (bπ : OrthonormalBasis ι ℂ Hπ)
    (α β : ι) {v : V} (hπσ : ¬ Nonempty (π.Equiv σ))
    (hv : v ∈ (ρ.isotypicSubrepresentation σ).toSubmodule) :
    p[ρ, π, bπ; α, β] v = 0 := by
  -- Rewrite the subrepresentation-membership hypothesis in the owner form used by Proposition 4-35.
  have hv' : v ∈ ρ.moduleIsotypicComponent σ := by
    simpa using hv
  -- The diagonal projector with index `β` already vanishes on the `σ`-isotypic component.
  have hdiag : p[ρ, π, bπ; β, β] v = 0 := by
    exact
      matrixCoefficientProjection_apply_eq_zero_of_mem_otherIsotypicComponent_diag
        ρ π σ bπ β hπσ hv'
  -- Specialize the matrix-unit relation to the right-diagonal factor `p[ρ, π, bπ; β, β]`.
  have hcomp : (p[ρ, π, bπ; α, β]).comp (p[ρ, π, bπ; β, β]) = p[ρ, π, bπ; α, β] := by
    classical
    simpa using matrixCoefficientProjection_comp ρ π bπ α β β β
  -- Evaluate the specialized composition identity at `v` and rewrite with the diagonal vanishing.
  have happly :
      ((p[ρ, π, bπ; α, β]).comp (p[ρ, π, bπ; β, β])) v = p[ρ, π, bπ; α, β] v := by
    exact congrArg (fun f : V →L[ℂ] V ↦ f v) hcomp
  calc
    p[ρ, π, bπ; α, β] v = ((p[ρ, π, bπ; α, β]).comp (p[ρ, π, bπ; β, β])) v := by
      simpa using happly.symm
    _ = p[ρ, π, bπ; α, β] (p[ρ, π, bπ; β, β] v) := by
      rfl
    _ = 0 := by
      rw [hdiag]
      simp

/- Proposition 4-36 (2): for one irreducible representation `π`, the operator `p_{αβ}^{(i)}`
vanishes on `V_{i,γ}` whenever `γ ≠ β`. This is the canonical theorem
`matrixCoefficientProjection_apply_eq_zero_of_mem_otherSubspace` from Proposition 4-34. -/
recall matrixCoefficientProjection_apply_eq_zero_of_mem_otherSubspace

/- Proposition 4-36 (3): the operator `p_{αβ}^{(i)}` induces an isomorphism
`V_{i,β} ≃ₗ[ℂ] V_{i,α}`. This is the concrete linear equivalence
`matrixCoefficientProjectionSubspaceLinearEquiv` from Proposition 4-34. -/
recall matrixCoefficientProjectionSubspaceLinearEquiv

end

end Representation
