import Mathlib.AlgebraicGeometry.Scheme
import StacksProject_2024.stacks_project.Chap10.Definition_10_37_11

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` did not surface a canonical scheme-level normality owner in
-- the current environment. Chapter-28 precedent packages pointwise scheme properties via
-- `X.presheaf.stalk x`, and the project's ring-level owner for the textbook phrase "normal
-- domain" is `_root_.IsNormalRing`.

variable (X : Scheme.{u})

/-- A scheme is normal at `x` if its stalk `X.presheaf.stalk x` is a normal ring. -/
abbrev isNormalAt (x : X) : Prop :=
  _root_.IsNormalRing (X.presheaf.stalk x)

/-- A scheme is normal at `x` iff its stalk at `x` is a normal ring. -/
theorem isNormalAt_def (x : X) :
    X.isNormalAt x ↔ _root_.IsNormalRing (X.presheaf.stalk x) :=
  Iff.rfl

/-- A scheme is normal at `x` iff its stalk at `x` is a normal ring. -/
@[simp] theorem isNormalAt_iff (x : X) :
    X.isNormalAt x ↔ _root_.IsNormalRing (X.presheaf.stalk x) :=
  Iff.rfl

/-- If `X` is normal at `x`, then the stalk `X.presheaf.stalk x` is a normal ring. -/
theorem isNormalAt.isNormalRing {x : X} (hx : X.isNormalAt x) :
    _root_.IsNormalRing (X.presheaf.stalk x) :=
  hx

/-- Definition 28.7.1: a scheme `X` is normal if and only if for all `x in X` the local ring
`O_{X, x}` is a normal domain; equivalently, each stalk `X.presheaf.stalk x` is a normal ring. -/
@[stacks 033I]
abbrev isNormal : Prop :=
  ∀ x : X, X.isNormalAt x

/-- A scheme is normal iff it is normal at each point. -/
theorem isNormal_def :
    X.isNormal ↔ ∀ x : X, X.isNormalAt x :=
  Iff.rfl

/-- If `X` is normal, then it is normal at each point. -/
theorem isNormal.isNormalAt (hX : X.isNormal) (x : X) :
    X.isNormalAt x :=
  hX x

/-- If `X` is normal, then each stalk `X.presheaf.stalk x` is a normal ring. -/
theorem isNormal.isNormalRing_stalk (hX : X.isNormal) (x : X) :
    _root_.IsNormalRing (X.presheaf.stalk x) :=
  hX x

/-- A scheme is normal iff each of its stalks is a normal ring. -/
@[simp] theorem isNormal_iff :
    X.isNormal ↔ ∀ x : X, _root_.IsNormalRing (X.presheaf.stalk x) :=
  Iff.rfl

end AlgebraicGeometry.Scheme
