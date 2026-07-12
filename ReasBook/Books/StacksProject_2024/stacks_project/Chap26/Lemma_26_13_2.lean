import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

-- Semantic recall: the canonical mathlib owner is `Scheme.range_fromSpecStalk`.

/- Lemma 26.13.2: for a point `x` of a scheme `X`, the image of the canonical morphism
`Spec(𝒪_{X, x}) ⟶ X` is exactly the set of generalizations of `x`. This is exactly the
canonical mathlib theorem `Scheme.range_fromSpecStalk`. -/
recall Scheme.range_fromSpecStalk

namespace AlgebraicGeometry.Scheme

/-- A point of `X` lies in the image of `Spec(𝒪_{X, x}) ⟶ X` exactly when it generalizes `x`. -/
@[simp] theorem mem_range_fromSpecStalk_iff (X : Scheme) (x y : X) :
    y ∈ Set.range (X.fromSpecStalk x) ↔ y ⤳ x := by
  simpa [Scheme.range_fromSpecStalk]

end AlgebraicGeometry.Scheme
