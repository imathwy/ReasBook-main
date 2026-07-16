import Mathlib.Tactic.Recall
import LinearRepresentations_Serre_1977.Serre.Chap04.Proposition_4_34

noncomputable section

open scoped MonoidAlgebra Representation

-- Semantic recall: `lean_leansearch` confirms `isotypicComponent` as the canonical owner, and
-- this item uses the local matrix-coefficient projection API from Proposition 4-34 directly.

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

/- Proposition 4-35 (1): the diagonal matrix-coefficient operator `p_{αα}^{(i)}` is a
projection. This is the canonical theorem `matrixCoefficientProjection_isProj` from
Proposition 4-34. -/
recall matrixCoefficientProjection_isProj

/-- Helper for Proposition 4-35: a diagonal `π`-matrix-coefficient projector annihilates the
`σ`-isotypic character average when `π` and `σ` are nonisomorphic. -/
private theorem matrixCoefficientProjection_comp_isotypicCharacterAverage_eq_zero_of_not_isomorphic
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ] [Representation.IsIrreducible σ]
    [Representation.IsUnitary π] [Representation.IsUnitary σ]
    (bπ : OrthonormalBasis ι ℂ Hπ)
    (α : ι) (hπσ : ¬ Nonempty (π.Equiv σ)) :
    (p[ρ, π, bπ; α, α]).toLinearMap.comp (isotypicCharacterAverage ρ σ) = 0 := by
  let bσ : OrthonormalBasis (Fin (Module.finrank ℂ Hσ)) ℂ Hσ := stdOrthonormalBasis ℂ Hσ
  -- Rewrite the basis-free isotypic projector as the diagonal sum from Proposition 4-34.
  rw [← sum_matrixCoefficientProjection_diag_eq_isotypicCharacterAverage (ρ := ρ) (π := σ)
    (b := bσ)]
  ext v
  -- Each diagonal `σ`-summand vanishes because nonisomorphic irreducibles have zero product.
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum, LinearMap.zero_apply]
  refine Finset.sum_eq_zero ?_
  intro η hη
  have hterm :
      (p[ρ, π, bπ; α, α]).toLinearMap.comp (p[ρ, σ, bσ; η, η]).toLinearMap = 0 := by
    exact congrArg ContinuousLinearMap.toLinearMap
      (matrixCoefficientProjection_comp_eq_zero_of_not_isomorphic
        ρ π σ bπ bσ α α η η hπσ)
  simpa [LinearMap.comp_apply] using congrArg (fun f : V →ₗ[ℂ] V ↦ f v) hterm

/-- Proposition 4-35 (1): textbook clause (2). If `π` and `σ` are nonisomorphic irreducible
unitary representations, then the diagonal operator `p_{αα}^{(i)}` vanishes on the
`σ`-isotypic component `V_j` of `ρ`. -/
theorem matrixCoefficientProjection_apply_eq_zero_of_mem_otherIsotypicComponent_diag
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ] [Representation.IsIrreducible σ]
    [Representation.IsUnitary π] [Representation.IsUnitary σ]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α : ι) {v : V} (hπσ : ¬ Nonempty (π.Equiv σ))
    (hv : v ∈ ρ.moduleIsotypicComponent σ) :
    p[ρ, π, b; α, α] v = 0 := by
  -- Vectors in the `σ`-isotypic component are fixed by the basis-free isotypic projector.
  have hfixσ : isotypicCharacterAverage ρ σ v = v := by
    exact
      (LinearMap.IsProj.mem_iff_map_id (ρ.piIsotypicCharacterAverage_isProj σ)).1
        (by simpa using hv)
  -- Route correction: instead of unfolding `ρ.moduleIsotypicComponent σ`, kill the basis-free
  -- `σ`-projector first and then apply that zero composite to `v`.
  have hzeroComp :
      (p[ρ, π, b; α, α]).toLinearMap.comp (isotypicCharacterAverage ρ σ) = 0 := by
    exact
      matrixCoefficientProjection_comp_isotypicCharacterAverage_eq_zero_of_not_isomorphic
        ρ π σ b α hπσ
  -- Evaluate the vanishing composite on `v` and rewrite `isotypicCharacterAverage ρ σ v` to `v`.
  have hzeroApply : (p[ρ, π, b; α, α]).toLinearMap (isotypicCharacterAverage ρ σ v) = 0 := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : V →ₗ[ℂ] V ↦ f v) hzeroComp
  simpa [hfixσ] using hzeroApply

/- Proposition 4-35 (2): textbook clause (3). The image `V_{i,α}` of the diagonal projector
`p_{αα}^{(i)}` is contained in the `π`-isotypic component `V_i`. This is the canonical theorem
`matrixCoefficientProjectionSubspace_le_piIsotypicComponent` from Proposition 4-34. -/
recall matrixCoefficientProjectionSubspace_le_piIsotypicComponent

/- Proposition 4-35 (4): the `π`-isotypic component is the direct sum of the subspaces
`V_{i,α}`. In the canonical API from Proposition 4-34, this is recorded by the independence
theorem `iSupIndep_matrixCoefficientProjectionSubspaces` together with the equality
`iSup_matrixCoefficientProjectionSubspaces_eq_piIsotypicComponent`. -/
recall iSupIndep_matrixCoefficientProjectionSubspaces

recall iSup_matrixCoefficientProjectionSubspaces_eq_piIsotypicComponent

/- Proposition 4-35 (5): the sum of the diagonal matrix-coefficient projections is the projection
onto the `π`-isotypic component. This is the canonical theorem
`sum_matrixCoefficientProjection_diag_isProj_piIsotypicComponent` from Proposition 4-34. -/
recall sum_matrixCoefficientProjection_diag_isProj_piIsotypicComponent

end

end Representation
