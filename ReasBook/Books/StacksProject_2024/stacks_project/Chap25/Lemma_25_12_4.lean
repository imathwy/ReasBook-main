import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_14_1
import StacksProject_2024.stacks_project.Chap25.Remark_25_12_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u₁ u₂

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily
open scoped Simplicial
open scoped TerminalPresheaf

namespace Functor

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [HasEqualizers C] [HasPullbacks C]
variable [HasEqualizers D] [HasPullbacks D]
variable [HasWeakSheafify JC (Type (max w v))]
variable [HasWeakSheafify JD (Type (max w v))]

-- Semantic search note: `lean_leansearch` recalled mathlib's one-hypercover preservation API in
-- `CategoryTheory.Sites.Continuous`, but this Stacks item is about the local Chapter 25 owner
-- `HypercoveringOf.Terminal` built from simplicial objects in `SR(C)`, so the statement is
-- phrased by
-- mapping those degreewise families along `SemiRepresentableFamily.map u`.

/-- Applying `u` degreewise to the simplicial semi-representable family underlying a hypercovering.
-/
abbrev mapHypercoveringSimplicial (u : D ⥤ C) (K : HypercoveringOf.Terminal JD) :
    SimplicialObject (SR(C)) :=
  K.simplicial ⋙ SemiRepresentableFamily.map u

/-- Unfolding `mapHypercoveringSimplicial` identifies each degree with the image of the
corresponding semi-representable family under `SemiRepresentableFamily.map u`. -/
theorem mapHypercoveringSimplicial_obj
    (u : D ⥤ C) (K : HypercoveringOf.Terminal JD) (Δ : SimplexCategoryᵒᵖ) :
    (mapHypercoveringSimplicial u K).obj Δ =
      (SemiRepresentableFamily.map u).obj (K.simplicial.obj Δ) := sorry

/-- The mapped simplicial object carries the canonical augmentation to the terminal presheaf on
`C`. -/
private abbrev mapHypercoveringAugmentation
    (u : D ⥤ C) (K : HypercoveringOf.Terminal JD) :
    mapHypercoveringSimplicial u K ⋙ SemiRepresentableFamily.toPresheaf ⟶
      (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj *ₚ[C] :=
  HypercoveringOf.terminalAugmentation (mapHypercoveringSimplicial u K)

/-- If `u` presents a morphism of sites and preserves the site-level equalizer and pullback data,
then the mapped degree-`0` augmentation is locally surjective after sheafification. -/
theorem mapHypercovering_zero_locallySurjective
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [PreservesLimitsOfShape WalkingCospan u]
    (K : HypercoveringOf.Terminal JD) :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf JC (Type (max w v))).map
        (hypercoveringZeroMap
          (mapHypercoveringSimplicial u K)
          (mapHypercoveringAugmentation u K))) := sorry

/-- If `u` presents a morphism of sites and preserves the site-level equalizer and pullback data,
then the mapped degree-`1` matching map is locally surjective after sheafification. -/
theorem mapHypercovering_one_locallySurjective
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [PreservesLimitsOfShape WalkingCospan u]
    (K : HypercoveringOf.Terminal JD) :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf JC (Type (max w v))).map
        (hypercoveringOneMap
          (mapHypercoveringSimplicial u K)
          (mapHypercoveringAugmentation u K))) := sorry

/-- If `u` presents a morphism of sites and preserves the site-level equalizer and pullback data,
then every higher mapped matching map is locally surjective after sheafification. -/
theorem mapHypercovering_higher_locallySurjective
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [PreservesLimitsOfShape WalkingCospan u]
    (K : HypercoveringOf.Terminal JD) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated (n + 1))ᵒᵖ ⥤ SR(C),
      (SimplexCategory.Truncated.inclusion (n + 1)).op.HasRightKanExtension F] :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf JC (Type (max w v))).map
        (hypercoveringHigherMap
          (mapHypercoveringSimplicial u K) (n + 1))) := sorry

/-- Lemma 25.12.4: let `f : \mathcal{C} \to \mathcal{D}` be the morphism of sites given by
`u : \mathcal{D} \to \mathcal{C}`. Assume `\mathcal{D}` and `\mathcal{C}` have equalizers and
fibre products and `u` commutes with them. If `K` is a hypercovering of `\mathcal{D}`, then the
degreewise image simplicial family `u(K)` is a hypercovering of `\mathcal{C}`. -/
def mapHypercovering
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [PreservesLimitsOfShape WalkingCospan u]
    (K : HypercoveringOf.Terminal JD) :
    HypercoveringOf.Terminal JC :=
  HypercoveringOf.Terminal.ofSimplicial JC (mapHypercoveringSimplicial u K)
    (mapHypercovering_zero_locallySurjective u K)
    (mapHypercovering_one_locallySurjective u K)
    (fun n ↦ mapHypercovering_higher_locallySurjective u K n)

/-- The hypercovering produced by `mapHypercovering` has the expected degreewise image simplicial
object. -/
theorem mapHypercovering_simplicial
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [PreservesLimitsOfShape WalkingCospan u]
    (K : HypercoveringOf.Terminal JD) :
    (mapHypercovering u K).simplicial = mapHypercoveringSimplicial u K := sorry

end Functor

end CategoryTheory
