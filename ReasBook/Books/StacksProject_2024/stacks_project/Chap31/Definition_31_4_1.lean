import StacksProject_2024.Chap31.Definition_31_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open Set TopologicalSpace

variable {X : Scheme.{u}} (ℱ : X.Modules)

-- Semantic recall: `lean_leansearch` surfaced the specialization relation `x ⤳ y`, while the
-- local Chapter 31 owner for associated points is `Scheme.Modules.associatedPoints`. No dedicated
-- embedded-point owner exists yet, so the source-facing notion is formalized as a thin predicate
-- on points together with the canonical specialization relation.

/-- Definition 31.4.1 (1): in the source this notion is introduced for a quasi-coherent
`\mathcal O_X`-module `\mathcal F`; the resulting predicate depends only on the associated points
of `\mathcal F`, so it is defined for any `\mathcal O_X`-module. A point `x : X` is embedded
associated if `x` is associated to `\mathcal F` and is the specialization of another associated
point of `\mathcal F`. -/
def embeddedAssociatedAt (x : X) : Prop :=
  x ∈ associatedPoints ℱ ∧
    ∃ y : X, y ∈ associatedPoints ℱ ∧ y ≠ x ∧ y ⤳ x

theorem embeddedAssociatedAt.mem_associatedPoints {x : X} (hx : ℱ.embeddedAssociatedAt x) :
    x ∈ associatedPoints ℱ :=
  hx.1

theorem embeddedAssociatedAt.exists_specializing_associated {x : X}
    (hx : ℱ.embeddedAssociatedAt x) :
    ∃ y : X, y ∈ associatedPoints ℱ ∧ y ≠ x ∧ y ⤳ x :=
  hx.2

/-- Being embedded associated at `x` means that `x` is associated to `\mathcal F` and is the
specialization of a distinct associated point of `\mathcal F`. -/
theorem embeddedAssociatedAt_iff (x : X) :
    ℱ.embeddedAssociatedAt x ↔
      x ∈ associatedPoints ℱ ∧
        ∃ y : X, y ∈ associatedPoints ℱ ∧ y ≠ x ∧ y ⤳ x :=
  Iff.rfl

/-- The set of embedded associated points of an `\mathcal O_X`-module `\mathcal F`. -/
def embeddedAssociatedPoints : Set X :=
  ℱ.embeddedAssociatedAt

/-- Membership in `embeddedAssociatedPoints` is exactly the embedded-associated-point predicate. -/
@[simp] theorem mem_embeddedAssociatedPoints_iff (x : X) :
    x ∈ ℱ.embeddedAssociatedPoints ↔ ℱ.embeddedAssociatedAt x :=
  Iff.rfl

/-- An `\mathcal O_X`-module has no embedded associated points exactly when no point is embedded
associated for it. -/
theorem embeddedAssociatedPoints_eq_empty_iff :
    ℱ.embeddedAssociatedPoints = (∅ : Set X) ↔ ∀ x : X, ¬ ℱ.embeddedAssociatedAt x := by
  constructor
  · intro h x hx
    have : x ∈ ℱ.embeddedAssociatedPoints := hx
    simpa [h] using this
  · intro h
    ext x
    simpa [embeddedAssociatedPoints] using h x

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

open Set TopologicalSpace

variable (X : Scheme.{u})

local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : X.Modules)

/-- Definition 31.4.1 (2): a point `x` of a scheme `X` is an embedded point if it is an embedded
associated point of the structure sheaf `\mathcal O_X`. -/
abbrev embeddedPoint (x : X) : Prop :=
  Scheme.Modules.embeddedAssociatedAt 𝒪X x

/-- A point of `X` is embedded exactly when it is an embedded associated point of the structure
sheaf. -/
theorem embeddedPoint_iff (x : X) :
    X.embeddedPoint x ↔ Scheme.Modules.embeddedAssociatedAt 𝒪X x :=
  Iff.rfl

/-- Being an embedded point of `X` means being an associated point of `X` that is the
specialization of a distinct associated point of `X`. -/
theorem embeddedPoint_iff_mem_associatedPoints_and_exists_specializing_associated (x : X) :
    X.embeddedPoint x ↔
      x ∈ X.associatedPoints ∧
        ∃ y : X, y ∈ X.associatedPoints ∧ y ≠ x ∧ y ⤳ x :=
  Iff.rfl

/-- An embedded point of `X` is an associated point of `X`. -/
theorem embeddedPoint.mem_associatedPoints {x : X} (hx : X.embeddedPoint x) :
    x ∈ X.associatedPoints :=
  hx.1

/-- An embedded point of `X` is the specialization of a distinct associated point of `X`. -/
theorem embeddedPoint.exists_specializing_associated {x : X} (hx : X.embeddedPoint x) :
    ∃ y : X, y ∈ X.associatedPoints ∧ y ≠ x ∧ y ⤳ x :=
  hx.2

/-- The set of embedded points of a scheme `X`. -/
abbrev embeddedPoints : Set X :=
  X.embeddedPoint

/-- Membership in `embeddedPoints` is exactly the embedded-point predicate. -/
@[simp] theorem mem_embeddedPoints_iff (x : X) :
    x ∈ X.embeddedPoints ↔ X.embeddedPoint x :=
  Iff.rfl

/-- A scheme has no embedded points exactly when none of its points is embedded. -/
theorem embeddedPoints_eq_empty_iff :
    X.embeddedPoints = (∅ : Set X) ↔ ∀ x : X, ¬ X.embeddedPoint x := by
  constructor
  · intro h x hx
    have : x ∈ X.embeddedPoints := hx
    simpa [h] using this
  · intro h
    ext x
    simpa [embeddedPoints] using h x

/-- Definition 31.4.1 (3): an embedded component of a scheme `X` is an irreducible closed subset
of the form `closure {x}` for an embedded point `x` of `X`. -/
def isEmbeddedComponent (Z : TopologicalSpace.IrreducibleCloseds X) : Prop :=
  ∃ x : X, X.embeddedPoint x ∧ (Z : Set X) = closure ({x} : Set X)

/-- A bundled irreducible closed subset of `X` is an embedded component exactly when it is the
closure of an embedded point of `X`. -/
theorem isEmbeddedComponent_iff (Z : TopologicalSpace.IrreducibleCloseds X) :
    X.isEmbeddedComponent Z ↔
      ∃ x : X, X.embeddedPoint x ∧ (Z : Set X) = closure ({x} : Set X) :=
  Iff.rfl

/-- An embedded component is the closure of an embedded point. -/
theorem isEmbeddedComponent.exists_embeddedPoint {Z : TopologicalSpace.IrreducibleCloseds X}
    (hZ : X.isEmbeddedComponent Z) :
    ∃ x : X, X.embeddedPoint x ∧ (Z : Set X) = closure ({x} : Set X) :=
  hZ

end AlgebraicGeometry.Scheme
