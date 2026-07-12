import Mathlib
import StacksProject_2024.Chap25.Lemma_25_7_3
import StacksProject_2024.Chap25.Definition_25_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily
open SemiRepresentableFamily.Over
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasPullbacks C] [HasWeakSheafify J (Type (max w v))]

-- Semantic search note: `lean_leansearch` again recalled only generic sheafification-local-
-- surjectivity and `OneHypercover` API. This item depends on the local Chapter 25 fixed-target
-- `Hypercovering` owner and the degreewise `SemiRepresentableFamily.toPresheaf` bridge, so the
-- source-facing statement stays on that surface.

namespace Hypercovering

/-- Local shorthand for the forgetful functor `SR(C, X) ⥤ SR(C)` in the degreewise statement. -/
private abbrev forgetOver {X : C} : SR(C, X) ⥤ SR(C) :=
  SemiRepresentableFamily.Over.forget

/-- Lemma 25.7.4: let `K` be a hypercovering of `X`, let `n ≥ 0`, and let
`u : ℱ ⟶ F(K_n)` be a morphism of presheaves whose sheafification is locally surjective. Then
there exists a hypercovering `L` of `X` and a morphism `f : L ⟶ K` of hypercoverings,
represented here by a simplicial morphism of the underlying simplicial objects, such that the
degree-`n` presheaf map `F(f_n) : F(L_n) ⟶ F(K_n)` factors through `u`. -/
@[stacks 01GK]
theorem existsRefinementFactoringDegreePresheafMap
    {X : C}
    (K : @Hypercovering C _ J X)
    (n : ℕ)
    (ℱ : Cᵒᵖ ⥤ Type (max w v))
    (u : ℱ ⟶ toPresheaf.obj
      (forgetOver.obj (K.toSimplicialObject.obj (op <| SimplexCategory.mk n))))
    (hu : Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type (max w v))).map u)) :
    ∃ (L : @Hypercovering C _ J X)
      (f : L.toSimplicialObject ⟶ K.toSimplicialObject)
      (g : toPresheaf.obj
          (forgetOver.obj (L.toSimplicialObject.obj (op <| SimplexCategory.mk n))) ⟶
        ℱ),
      toPresheaf.map
          (forgetOver.map (f.app (op <| SimplexCategory.mk n))) =
        g ≫ u := sorry

end Hypercovering

end CategoryTheory
