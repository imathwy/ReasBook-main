import StacksProject_2024.Chap17.Definition_17_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Semantic recall: `lean_leansearch` surfaced the canonical finite-morphism owner
`AlgebraicGeometry.IsFinite` and the finite-fiber helper
`AlgebraicGeometry.IsFinite.finite_preimage_singleton`. Local Chapter 17 precedent names
trivial module sheaves by `RingedSpace.IsTrivial`, and Chapter 31 precedent expresses
restriction to an open subscheme as `Scheme.Modules.pullback` along `X.ofRestrict`. The Stacks
tag evidence is consistent: tag `0BUT` comes from `https://stacks.math.columbia.edu/tag/0BUT`. -/

/-- Lemma 31.17.1: let `π : X ⟶ Y` be a finite morphism of schemes and let `\mathcal L` be an
invertible `\mathcal O_X`-module. For every point `y ∈ Y`, there is an open neighbourhood
`V` of `y` such that `\mathcal L` restricted to `π⁻¹(V)` is trivial. -/
@[stacks 0BUT]
theorem exists_open_neighborhood_isTrivial_pullback_of_isFinite
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π]
    [MonoidalCategory X.Modules]
    (ℒ : X.Modules) [Functor.IsEquivalence (tensorRight ℒ)]
    (y : Y) :
    ∃ V : Y.Opens, y ∈ V ∧
      RingedSpace.IsTrivial
        ((Scheme.Modules.pullback (X.ofRestrict (π ⁻¹ᵁ V).isOpenEmbedding)).obj ℒ) := sorry

end AlgebraicGeometry.Scheme
