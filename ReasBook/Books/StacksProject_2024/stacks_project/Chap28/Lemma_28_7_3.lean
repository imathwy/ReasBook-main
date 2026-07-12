import StacksProject_2024.Chap28.Definition_28_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Source-facing/main item: Lemma 28.7.3 is the Chapter-28 implication from the local normality
-- owner `Scheme.isNormal` to the canonical reducedness owner `IsReduced`.
-- Core/canonical reuse: Chapter 26 already provides the scheme-level bridge from stalkwise
-- reducedness to `IsReduced`, so this file keeps only the normality-to-reducedness stalk bridge
-- at the pointwise owner `Scheme.isNormalAt`, followed by the source-facing global theorem.

variable {X : Scheme.{u}}

/-- If a scheme is normal at `x`, then its stalk at `x` is reduced. -/
theorem isNormalAt.isReduced {x : X} (hx : X.isNormalAt x) :
    _root_.IsReduced (X.presheaf.stalk x) := by
  letI : _root_.IsNormalRing (X.presheaf.stalk x) := hx.isNormalRing
  exact inferInstance

/-- Lemma 28.7.3: a normal scheme is reduced. -/
theorem isReduced_of_isNormal (hX : X.isNormal) :
    IsReduced X := by
  let _ : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x ↦ (hX x).isReduced
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk X

end AlgebraicGeometry.Scheme
