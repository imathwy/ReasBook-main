import Mathlib
import StacksProject_2024.stacks_project.Chap25.Lemma_25_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily.Over
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

-- Semantic search note: `lean_leansearch` recalled only mathlib's generic `OneHypercover` API.
-- This Stacks item is about the local Chapter 25 owner `Hypercovering` in `SR(C, X)`, so the
-- statement stays on that source-faithful surface.

namespace Hypercovering

/-- Lemma 25.7.3: let `K` be a hypercovering of `X`, let `k ≥ 0`, and let
`u : Z ⟶ K_k` be a covering morphism in `SR(C, X)`. Then there exists a hypercovering `L` of `X`
and a morphism `f : L ⟶ K` of hypercoverings, represented here by a simplicial morphism of the
underlying simplicial objects, such that the degree-`k` component `L_k ⟶ K_k` factors through
`u`. -/
@[stacks 01GJ]
theorem existsRefinementFactoringDegreeMap
    {X : C}
    (K : @CategoryTheory.Hypercovering C _ J X)
    (k : ℕ)
    (Z : SR(C, X))
    (u : Z ⟶ K.toSimplicialObject.obj (op <| SimplexCategory.mk k))
    (hu : Hom.IsCovering J u) :
    ∃ (L : @CategoryTheory.Hypercovering C _ J X)
      (f : L.toSimplicialObject ⟶ K.toSimplicialObject)
      (g : L.toSimplicialObject.obj (op <| SimplexCategory.mk k) ⟶ Z),
      f.app (op <| SimplexCategory.mk k) = g ≫ u := sorry

end Hypercovering

end CategoryTheory
