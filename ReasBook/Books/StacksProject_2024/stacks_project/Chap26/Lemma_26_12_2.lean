import Mathlib.AlgebraicGeometry.Properties

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Source/core/bridge triage for Lemma 26.12.2:
-- - source-facing: the Stacks criterion that a scheme is reduced exactly when every open section
--   ring is reduced;
-- - core/canonical: the mathlib owner `IsReduced`, with the canonical open-sections directions
--   `IsReduced.component_reduced` and `IsReduced.mk`;
-- - bridge/view: this file keeps the reusable repository owner name `Scheme.isReduced_iff` while
--   presenting the criterion directly in the source language of section rings on opens.

/-- Lemma 26.12.2: a scheme `X` is reduced if and only if for every open subset `U ⊆ X` the ring
of sections `Γ(X, U)` is reduced. -/
@[stacks 01J1]
theorem isReduced_iff (X : Scheme.{u}) :
    IsReduced X ↔ ∀ U : X.Opens, _root_.IsReduced (Γ(X, U)) := by
  constructor
  · intro hX U
    letI := hX
    exact IsReduced.component_reduced U
  · intro hU
    exact ⟨hU⟩

end AlgebraicGeometry.Scheme
