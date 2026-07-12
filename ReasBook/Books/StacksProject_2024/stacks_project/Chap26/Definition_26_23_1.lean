import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

-- Semantic recall: this Stacks item is a pure canonical owner recall.
-- Source/core/bridge triage:
-- - `source-facing`: a morphism of schemes is a monomorphism.
-- - `core/canonical`: the category-theoretic class `Mono`.
-- - `bridge/view`: none; the source item is exactly the canonical owner.
/- Definition 26.23.1: a morphism of schemes is a monomorphism exactly in the canonical
category-theoretic sense `Mono`. -/
recall Mono

namespace AlgebraicGeometry

/-- Definition 26.23.1: for a morphism of schemes `f : X ⟶ Y`, being a monomorphism is exactly
the right-cancellation property in the category of schemes. This is the source-facing
specialization of the canonical owner `Mono`. -/
@[stacks 01L2]
theorem Scheme.Hom.mono_iff_right_cancellation {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mono f ↔ ∀ ⦃Z : Scheme.{u}⦄ (g h : Z ⟶ X), g ≫ f = h ≫ f → g = h := by
  constructor
  · intro hf Z g h hgh
    exact hf.right_cancellation g h hgh
  · intro hf
    refine ⟨?_⟩
    intro Z g h hgh
    exact hf g h hgh

#check (Mono : {X Y : Scheme.{u}} → (X ⟶ Y) → Prop)

end AlgebraicGeometry
