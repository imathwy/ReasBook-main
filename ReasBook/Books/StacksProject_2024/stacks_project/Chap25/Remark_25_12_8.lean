import Mathlib
import StacksProject_2024.stacks_project.Chap25.Definition_25_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily
open scoped Simplicial

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasEqualizers C] [HasPullbacks C]
variable [HasWeakSheafify J (Type (max w v))]

-- Semantic search note: `lean_leansearch` recalled
-- `Presheaf.isLocallySurjective_presheafToSheaf_map_iff`; the owner choice here follows the local
-- `HypercoveringOf` API from Definition 25.6.1, together with a degreewise singleton-coproduct
-- replacement of families in `SR(C)`.

namespace SemiRepresentableFamily

/-- The singleton semi-representable family obtained by replacing a family with the coproduct of
its components. -/
abbrev coproductSingleton (K : SR(C)) [HasCoproduct K.obj] : SR(C) where
  index := PUnit
  obj := fun _ ↦ ∐ K.obj

/-- Unfolding `coproductSingleton` gives the singleton family on the coproduct object. -/
theorem coproductSingleton_def (K : SR(C)) [HasCoproduct K.obj] :
    coproductSingleton K =
      { index := PUnit
        obj := fun _ ↦ ∐ K.obj } := sorry

/-- The canonical morphism from a family to its singleton coproduct family is given by the
coproduct inclusions. -/
def toCoproductSingleton (K : SR(C)) [HasCoproduct K.obj] :
    K ⟶ coproductSingleton K where
  α := fun _ ↦ PUnit.unit
  f := fun i ↦ Sigma.ι K.obj i

/-- On each component, `toCoproductSingleton` is the corresponding coproduct inclusion. -/
theorem toCoproductSingleton_f (K : SR(C)) [HasCoproduct K.obj] (i : K.index) :
    (toCoproductSingleton K).f i = Sigma.ι K.obj i := sorry

/-- If a chosen family is identified with the singleton coproduct family, the canonical map to that
chosen family is obtained by composing `toCoproductSingleton` with the equality transport. -/
abbrev toChosenCoproductSingleton (K L : SR(C)) [HasCoproduct K.obj]
    (hL : coproductSingleton K = L) :
    K ⟶ L :=
  toCoproductSingleton K ≫ eqToHom hL

/-- The presheaf comparison attached to a chosen singleton coproduct family is the sheafification
input used in Remark 25.12.8. -/
abbrev coproductSingletonComparison (K L : SR(C)) [HasCoproduct K.obj]
    (hL : coproductSingleton K = L) :
    SemiRepresentableFamily.toPresheaf.obj K ⟶ SemiRepresentableFamily.toPresheaf.obj L :=
  SemiRepresentableFamily.toPresheaf.map (toChosenCoproductSingleton K L hL)

/-- Unfolding `coproductSingletonComparison` shows that it is induced from
`toChosenCoproductSingleton`. -/
theorem coproductSingletonComparison_def (K L : SR(C)) [HasCoproduct K.obj]
    (hL : coproductSingleton K = L) :
    coproductSingletonComparison K L hL =
      SemiRepresentableFamily.toPresheaf.map (toChosenCoproductSingleton K L hL) := sorry

end SemiRepresentableFamily

namespace HypercoveringOf

/-- The degree-`0` hypercovering condition transfers from `K` to the degreewise singleton coproduct
replacement `L` when the sheafified comparison in degree `0` is an isomorphism. -/
theorem degreewiseCoproductSingleton_zero_locallySurjective
    (K : HypercoveringOf.Terminal J)
    (L : SimplicialObject (SR(C)))
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.simplicial.obj Δ).obj]
    (hobj : ∀ Δ : SimplexCategoryᵒᵖ,
      SemiRepresentableFamily.coproductSingleton (K.simplicial.obj Δ) = L.obj Δ)
    (hiso : ∀ Δ : SimplexCategoryᵒᵖ,
      IsIso
        ((presheafToSheaf J (Type (max w v))).map
          (SemiRepresentableFamily.coproductSingletonComparison
            (K.simplicial.obj Δ) (L.obj Δ) (hobj Δ)))) :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type (max w v))).map
        (hypercoveringZeroMap L (terminalAugmentation L))) := sorry

/-- The degree-`1` matching-map hypercovering condition transfers from `K` to the degreewise
singleton coproduct replacement `L` when the degreewise sheafified comparison maps are
isomorphisms. -/
theorem degreewiseCoproductSingleton_one_locallySurjective
    (K : HypercoveringOf.Terminal J)
    (L : SimplicialObject (SR(C)))
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.simplicial.obj Δ).obj]
    (hobj : ∀ Δ : SimplexCategoryᵒᵖ,
      SemiRepresentableFamily.coproductSingleton (K.simplicial.obj Δ) = L.obj Δ)
    (hiso : ∀ Δ : SimplexCategoryᵒᵖ,
      IsIso
        ((presheafToSheaf J (Type (max w v))).map
          (SemiRepresentableFamily.coproductSingletonComparison
            (K.simplicial.obj Δ) (L.obj Δ) (hobj Δ)))) :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type (max w v))).map
        (hypercoveringOneMap L (terminalAugmentation L))) := sorry

/-- The higher matching-map hypercovering conditions transfer from `K` to the degreewise singleton
coproduct replacement `L` when the degreewise sheafified comparison maps are isomorphisms. -/
theorem degreewiseCoproductSingleton_higher_locallySurjective
    (K : HypercoveringOf.Terminal J)
    (L : SimplicialObject (SR(C)))
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.simplicial.obj Δ).obj]
    (hobj : ∀ Δ : SimplexCategoryᵒᵖ,
      SemiRepresentableFamily.coproductSingleton (K.simplicial.obj Δ) = L.obj Δ)
    (hiso : ∀ Δ : SimplexCategoryᵒᵖ,
      IsIso
        ((presheafToSheaf J (Type (max w v))).map
          (SemiRepresentableFamily.coproductSingletonComparison
            (K.simplicial.obj Δ) (L.obj Δ) (hobj Δ))))
    (n : ℕ)
    [∀ F : (SimplexCategory.Truncated (n + 1))ᵒᵖ ⥤ SR(C),
      (SimplexCategory.Truncated.inclusion (n + 1)).op.HasRightKanExtension F] :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type (max w v))).map
        (hypercoveringHigherMap L (n + 1))) := sorry

/-- Remark 25.12.8: if `K` is a hypercovering and each degree of `L` is obtained by replacing the
components of the corresponding degree of `K` by their coproduct, with the induced presheaf map
becoming an isomorphism after sheafification in every simplicial degree, then `L` is again a
hypercovering. -/
def ofDegreewiseCoproductSingleton
    (K : HypercoveringOf.Terminal J)
    (L : SimplicialObject (SR(C)))
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.simplicial.obj Δ).obj]
    (hobj : ∀ Δ : SimplexCategoryᵒᵖ,
      SemiRepresentableFamily.coproductSingleton (K.simplicial.obj Δ) = L.obj Δ)
    (hiso : ∀ Δ : SimplexCategoryᵒᵖ,
      IsIso
        ((presheafToSheaf J (Type (max w v))).map
          (SemiRepresentableFamily.coproductSingletonComparison
            (K.simplicial.obj Δ) (L.obj Δ) (hobj Δ)))) :
    HypercoveringOf.Terminal J :=
  HypercoveringOf.Terminal.ofSimplicial J L
    (degreewiseCoproductSingleton_zero_locallySurjective K L hobj hiso)
    (degreewiseCoproductSingleton_one_locallySurjective K L hobj hiso)
    (fun n ↦ degreewiseCoproductSingleton_higher_locallySurjective K L hobj hiso n)

/-- The hypercovering produced by `ofDegreewiseCoproductSingleton` has underlying simplicial object
`L`. -/
theorem ofDegreewiseCoproductSingleton_simplicial
    (K : HypercoveringOf.Terminal J)
    (L : SimplicialObject (SR(C)))
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.simplicial.obj Δ).obj]
    (hobj : ∀ Δ : SimplexCategoryᵒᵖ,
      SemiRepresentableFamily.coproductSingleton (K.simplicial.obj Δ) = L.obj Δ)
    (hiso : ∀ Δ : SimplexCategoryᵒᵖ,
      IsIso
        ((presheafToSheaf J (Type (max w v))).map
          (SemiRepresentableFamily.coproductSingletonComparison
            (K.simplicial.obj Δ) (L.obj Δ) (hobj Δ)))) :
    (ofDegreewiseCoproductSingleton K L hobj hiso).simplicial = L := sorry

end HypercoveringOf

end CategoryTheory
