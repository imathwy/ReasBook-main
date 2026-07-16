import Mathlib
import StacksProject_2024.stacks_project.Chap07.Lemma_7_28_1
import StacksProject_2024.stacks_project.Chap25.Lemma_25_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u₁ u₂

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [HasPullbacks C] [HasPullbacks D]

-- Semantic search note: `lean_leansearch` recalled the continuous-functor owners in
-- `CategoryTheory.Sites.Continuous`; the source-faithful owner for this item is still the local
-- Chapter 25 fixed-target `Hypercovering (J := J) X`, transported degreewise by
-- `SemiRepresentableFamily.map (Over.post u)` on slice categories.

namespace Functor

open SemiRepresentableFamily.Over

/-- Applying `u` degreewise to the simplicial fixed-target family underlying a hypercovering of
`Y`. -/
abbrev mapOverHypercoveringSimplicial
    (u : D ⥤ C) {Y : D} (K : @Hypercovering D _ JD Y) :
    SimplicialObject (SR(C, u.obj Y)) :=
  K.toSimplicialObject ⋙ SemiRepresentableFamily.map (Over.post u)

/-- Unfolding `mapOverHypercoveringSimplicial` identifies each simplicial degree with the image of
the corresponding fixed-target family under `SemiRepresentableFamily.map (Over.post u)`. -/
theorem mapOverHypercoveringSimplicial_obj
    (u : D ⥤ C) {Y : D} (K : @Hypercovering D _ JD Y)
    (Δ : SimplexCategoryᵒᵖ) :
    (mapOverHypercoveringSimplicial u K).obj Δ =
      (SemiRepresentableFamily.map (Over.post u)).obj (K.toSimplicialObject.obj Δ) := sorry

/-- Helper for Lemma 25.12.5: the degree-`0` covering family of a hypercovering remains covering
after applying a continuous functor that preserves fibre products. -/
theorem mapOverHypercovering_zero_isCovering
    (u : D ⥤ C) [u.IsContinuous JD JC]
    [PreservesLimitsOfShape WalkingCospan u]
    {Y : D} (K : @Hypercovering D _ JD Y) :
    ((mapOverHypercoveringSimplicial u K).obj (op <| SimplexCategory.mk 0)).toSieve ∈
      JC (u.obj Y) := sorry

/-- Helper for Lemma 25.12.5: each mapped matching morphism remains covering after applying a
continuous functor that preserves fibre products. -/
theorem mapOverHypercovering_succ_isCovering
    (u : D ⥤ C) [u.IsContinuous JD JC]
    [PreservesLimitsOfShape WalkingCospan u]
    {Y : D} (K : @Hypercovering D _ JD Y) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, u.obj Y),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    Hom.IsCovering JC
      (matchingMap (mapOverHypercoveringSimplicial u K) n) := sorry

/-- Lemma 25.12.5: let `\mathcal{C}`, `\mathcal{D}` be sites, let `u : \mathcal{D} \to
\mathcal{C}` be a continuous functor, and assume `\mathcal{D}` and `\mathcal{C}` have fibre
products and `u` commutes with them. If `K` is a hypercovering of `Y`, then the degreewise image
`u(K)` is a hypercovering of `u(Y)`. -/
def mapOverHypercovering
    (u : D ⥤ C) [u.IsContinuous JD JC]
    [PreservesLimitsOfShape WalkingCospan u]
    {Y : D} (K : @Hypercovering D _ JD Y) :
    @Hypercovering C _ JC (u.obj Y) where
  toSimplicialObject := mapOverHypercoveringSimplicial u K
  zero_isCovering := mapOverHypercovering_zero_isCovering u K
  succ_isCovering n := mapOverHypercovering_succ_isCovering u K n

/-- The hypercovering produced by `mapOverHypercovering` has the expected degreewise image
simplicial object. -/
theorem mapOverHypercovering_toSimplicialObject
    (u : D ⥤ C) [u.IsContinuous JD JC]
    [PreservesLimitsOfShape WalkingCospan u]
    {Y : D} (K : @Hypercovering D _ JD Y) :
    (show @Hypercovering C _ JC (u.obj Y) from mapOverHypercovering u K).toSimplicialObject =
      mapOverHypercoveringSimplicial u K := sorry

end Functor

end CategoryTheory
