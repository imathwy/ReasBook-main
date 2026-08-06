import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Topology.Category.TopCat.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

-- Semantic recall: `CategoryTheory.Over`, `Over.homMk`, and `Over.w` in
-- `Mathlib.CategoryTheory.Comma.Over.Basic` give the canonical API for spaces over a fixed base.

universe u v

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  (p : C(E, B)) (p' : C(E', B))

/- Definition 3.7.4: a map of covering spaces over `B`, from `p : C(E, B)` to `p' : C(E', B)`,
is a morphism in the over-category `Over (TopCat.of B)`. Equivalently, it is a
continuous map `g : C(E, E')` such that `p' ∘ g = p`. -/
#check (Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))

/- An object of an over-category is given by a morphism with codomain `X`. -/
#check Over.mk

/- Equivalently, a morphism in an over-category is built from a commutative triangle. -/
#check Over.homMk

/- Every morphism in the over-category satisfies the defining commutative-triangle relation. -/
#check Over.w

namespace Over

/-- Evaluating the commutative triangle of a morphism of spaces over `B` at a point recovers the
relation `p' ∘ h.left = p` pointwise. -/
theorem w_apply {E E' B : Type u}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    {p : C(E, B)} {p' : C(E', B)}
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) (x : E) :
    p' (h.left.hom x) = p x := by
  have hx := congrArg (fun f : TopCat.of E ⟶ TopCat.of B ↦ f.hom x) (Over.w h)
  simpa [ContinuousMap.comp_apply] using hx

end Over
