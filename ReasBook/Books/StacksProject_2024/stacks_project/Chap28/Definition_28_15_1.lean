import StacksProject_2024.Chap15.Definition_15_107_1_Basic

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` pointed to the canonical stalk/local-ring owners on
-- `LocallyRingedSpace`, and the existing project owner for the ring-level notion is
-- `IsUnibranch` / `IsGeometricallyUnibranch`. The scheme-level API should therefore be stated
-- stalkwise on `Scheme`.

variable (X : Scheme.{u})

/-- Definition 28.15.1 (1): a scheme `X` is unibranch at a point `x` if the local ring
`X.presheaf.stalk x` is unibranch. -/
abbrev isUnibranchAt (x : X) : Prop :=
  _root_.IsUnibranch (X.presheaf.stalk x)

/-- A scheme is unibranch at `x` iff its stalk at `x` is unibranch. -/
@[simp] theorem isUnibranchAt_iff (x : X) :
    X.isUnibranchAt x ↔ _root_.IsUnibranch (X.presheaf.stalk x) :=
  Iff.rfl

/-- If `X` is unibranch at `x`, then the stalk `X.presheaf.stalk x` is unibranch. -/
theorem isUnibranchAt.isUnibranch {x : X} (hx : X.isUnibranchAt x) :
    _root_.IsUnibranch (X.presheaf.stalk x) :=
  hx

/-- Definition 28.15.1 (2): a scheme `X` is geometrically unibranch at a point `x` if the local
ring `X.presheaf.stalk x` is geometrically unibranch. -/
abbrev isGeometricallyUnibranchAt (x : X) : Prop :=
  _root_.IsGeometricallyUnibranch (X.presheaf.stalk x)

/-- A scheme is geometrically unibranch at `x` iff its stalk at `x` is geometrically unibranch.
-/
@[simp] theorem isGeometricallyUnibranchAt_iff (x : X) :
    X.isGeometricallyUnibranchAt x ↔
      _root_.IsGeometricallyUnibranch (X.presheaf.stalk x) :=
  Iff.rfl

/-- If `X` is geometrically unibranch at `x`, then the stalk `X.presheaf.stalk x` is
geometrically unibranch. -/
theorem isGeometricallyUnibranchAt.isGeometricallyUnibranch {x : X}
    (hx : X.isGeometricallyUnibranchAt x) :
    _root_.IsGeometricallyUnibranch (X.presheaf.stalk x) :=
  hx

/-- Geometrically unibranch schemes are unibranch at each point. -/
theorem isGeometricallyUnibranchAt.isUnibranchAt {x : X}
    (hx : X.isGeometricallyUnibranchAt x) :
    X.isUnibranchAt x :=
  hx.toIsUnibranch

/-- Definition 28.15.1 (3): a scheme `X` is unibranch if it is unibranch at every point. -/
abbrev isUnibranch : Prop :=
  ∀ x : X, X.isUnibranchAt x

/-- If `X` is unibranch, then it is unibranch at each point. -/
theorem isUnibranch.isUnibranchAt (hX : X.isUnibranch) (x : X) :
    X.isUnibranchAt x :=
  hX x

/-- If `X` is unibranch, then each stalk `X.presheaf.stalk x` is unibranch. -/
theorem isUnibranch.isUnibranch_stalk (hX : X.isUnibranch) (x : X) :
    _root_.IsUnibranch (X.presheaf.stalk x) :=
  hX x

/-- A scheme is unibranch iff each of its stalks is unibranch. -/
@[simp] theorem isUnibranch_iff :
    X.isUnibranch ↔ ∀ x : X, _root_.IsUnibranch (X.presheaf.stalk x) :=
  Iff.rfl

/-- Definition 28.15.1 (4): a scheme `X` is geometrically unibranch if it is geometrically
unibranch at every point. -/
abbrev isGeometricallyUnibranch : Prop :=
  ∀ x : X, X.isGeometricallyUnibranchAt x

/-- If `X` is geometrically unibranch, then it is geometrically unibranch at each point. -/
theorem isGeometricallyUnibranch.isGeometricallyUnibranchAt
    (hX : X.isGeometricallyUnibranch) (x : X) :
    X.isGeometricallyUnibranchAt x :=
  hX x

/-- If `X` is geometrically unibranch, then each stalk `X.presheaf.stalk x` is geometrically
unibranch. -/
theorem isGeometricallyUnibranch.isGeometricallyUnibranch_stalk
    (hX : X.isGeometricallyUnibranch) :
    ∀ x : X, _root_.IsGeometricallyUnibranch (X.presheaf.stalk x) :=
  hX

/-- A scheme is geometrically unibranch iff each of its stalks is geometrically unibranch. -/
@[simp] theorem isGeometricallyUnibranch_iff :
    X.isGeometricallyUnibranch ↔
      ∀ x : X, _root_.IsGeometricallyUnibranch (X.presheaf.stalk x) :=
  Iff.rfl

/-- Geometrically unibranch schemes are unibranch. -/
theorem isGeometricallyUnibranch.isUnibranch
    (hX : X.isGeometricallyUnibranch) :
    X.isUnibranch := fun x ↦
  (hX x).isUnibranchAt

end AlgebraicGeometry.Scheme
