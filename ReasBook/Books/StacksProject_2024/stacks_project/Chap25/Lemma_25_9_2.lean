import Mathlib
import StacksProject_2024.stacks_project.Chap25.Lemma_25_7_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily.Over
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

-- Semantic search note: `lean_leansearch` only surfaced mathlib's generic `OneHypercover`
-- homotopy API. The local owner here is Chapter 25 `Hypercovering`, and repository precedent in
-- Chapter 14 confirms that directed simplicial homotopies are represented by
-- `CategoryTheory.SimplicialObject.Homotopy`.

namespace Hypercovering

/-- Lemma 25.9.2: let `K, L` be hypercoverings of `X` and let `a, b : K ⟶ L` be morphisms of
hypercoverings, represented here by simplicial morphisms of the underlying simplicial objects.
Then there exists a hypercovering `K'` of `X` and a morphism `c : K' ⟶ K` such that the
composites `a ∘ c` and `b ∘ c` are simplicially homotopic. -/
@[stacks 01GS]
theorem existsRefinementHomotopy
    {X : C}
    (K L : @Hypercovering C _ J X)
    (a b : K.toSimplicialObject ⟶ L.toSimplicialObject) :
    ∃ (K' : @Hypercovering C _ J X)
      (c : K'.toSimplicialObject ⟶ K.toSimplicialObject),
      Nonempty (CategoryTheory.SimplicialObject.Homotopy (c ≫ a) (c ≫ b)) := sorry

end Hypercovering

end CategoryTheory
