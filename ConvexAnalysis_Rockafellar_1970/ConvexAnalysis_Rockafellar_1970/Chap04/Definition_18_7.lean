import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_3_2

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*} {V : Type*}
variable [CommRing 𝕜] [LE 𝕜]
variable [TopologicalSpace V]
variable [AddCommGroup V] [Module 𝕜 V]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 18.7 introduces the pointwise notion that a supporting hyperplane
  to `C` through `x` is unique, and then defines a tangent half-space by asking its boundary
  hyperplane to be tangent at some point.
- `core/canonical`: the owner abstractions already present in the project are
  `AffineSubspace.IsSupportingHyperplane` for hyperplanes and `Set.IsSupportingHalfSpace` for
  half-spaces.
- `bridge/view`: the textbook phrase "supporting hyperplane to `C` at `x`" is rendered by adding
  the point-incidence condition `x ∈ H` to the imported supporting-hyperplane owner
  predicate.

Domain-style sampling used here:
- `AffineSubspace.IsSupportingHyperplane`;
- `Set.IsSupportingHalfSpace`;
- the `SetLike` coercion from `AffineSubspace 𝕜 V` to `Set V`;
- the boundary operator `frontier`.

Primitive data vs derived API:
- the primitive owner data are still the candidate hyperplane `H`, the supported set `C`, the
  contact point `x`, and the candidate half-space `s`;
- tangency is a derived `Prop` asserting uniqueness among supporting hyperplanes through `x`,
  while tangent-half-space status is the derived existence of such a tangent boundary over the
  owner half-space `s`, reusing `AffineSubspace.IsTangentHyperplaneAt` rather than re-expanding
  its point-incidence and uniqueness fields.

Layer target: `source-facing`.

Ambient refinement:
- the declarations in this file use only the Chapter 11 owner predicates, `frontier`, affine
  subspaces, and the ambient pairing-space structure;
- no norm, inner-product, or finite-dimensional data are used locally;
- the public API therefore belongs on the weaker owner layer
  `[CommRing 𝕜] [LE 𝕜] [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]`,
  leaving later Chapter 4 theorems free to specialize to real inner-product spaces only where
  those stronger hypotheses are actually needed.
-/

namespace AffineSubspace

variable (Y : Type*)
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]

variable {H : AffineSubspace 𝕜 V} {C : Set V} {x : V}

/-- Definition 18.7 (1): a hyperplane `H` is tangent to `C` at `x` when `x` lies in `C ∩ H`,
`H` supports `C`, and every supporting hyperplane to `C` through `x` coincides with `H`. -/
def IsTangentHyperplaneAt (H : AffineSubspace 𝕜 V) (C : Set V) (x : V) : Prop :=
  (H supportsHyperplane[Y] C) ∧ x ∈ C ∧ x ∈ H ∧
    ∀ ⦃H' : AffineSubspace 𝕜 V⦄, (H' supportsHyperplane[Y] C) → x ∈ H' → H' = H

/-- Textbook-facing notation for "hyperplane `H` tangent to `C` at `x`". -/
scoped[Rockafellar] notation:50 H " tangent[" Y "] " C " at " x =>
  AffineSubspace.IsTangentHyperplaneAt Y H C x

/-- A tangent hyperplane at `x` is, in particular, a supporting hyperplane to `C`. -/
theorem IsTangentHyperplaneAt.isSupportingHyperplane
    (h : H tangent[Y] C at x) : H supportsHyperplane[Y] C :=
  h.1

/-- The tangency point of a tangent hyperplane lies in the supported set. -/
theorem IsTangentHyperplaneAt.mem (h : H tangent[Y] C at x) : x ∈ C :=
  h.2.1

/-- The tangency point of a tangent hyperplane lies on the hyperplane. -/
theorem IsTangentHyperplaneAt.mem_hyperplane (h : H tangent[Y] C at x) : x ∈ H :=
  h.2.2.1

/-- A tangent hyperplane at `x` is the unique supporting hyperplane through `x`. -/
theorem IsTangentHyperplaneAt.eq
    (h : H tangent[Y] C at x) {H' : AffineSubspace 𝕜 V}
    (hH' : H' supportsHyperplane[Y] C) (hxH' : x ∈ H') :
    H' = H :=
  h.2.2.2 hH' hxH'

end AffineSubspace

namespace Set

/-- Definition 18.7 (2): a half-space `s` is tangent to `C` when `s` is a supporting half-space
to `C` and the boundary hyperplane `frontier s` is tangent to `C` at some point. -/
def IsTangentHalfSpace {𝕜 : Type*} [CommRing 𝕜] [LE 𝕜]
    {V Y : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]
    (s C : Set V) : Prop :=
  (s supports[Y,𝕜] C) ∧
    ∃ x : V, ∃ H : AffineSubspace 𝕜 V,
      frontier s = H ∧ H tangent[Y] C at x

/-- Textbook-facing notation for tangent half-spaces from Definition 18.7 (2). -/
scoped[Rockafellar] notation:50 s " tangent[" Y "," R "] " C =>
  @Set.IsTangentHalfSpace R _ _ _ Y _ _ _ _ _ _ s C

section

variable {Y 𝕜 V : Type*}
variable [CommRing 𝕜] [LE 𝕜]
variable [TopologicalSpace V]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]

variable {s C : Set V}

/-- A tangent half-space is, in particular, a supporting half-space. -/
theorem IsTangentHalfSpace.isSupportingHalfSpace
    (h : s tangent[Y,𝕜] C) :
    s supports[Y,𝕜] C :=
  h.1

/-- A tangent half-space has a tangent boundary hyperplane at some point. -/
theorem IsTangentHalfSpace.exists_tangentHyperplaneAt
    (h : s tangent[Y,𝕜] C) :
    ∃ x : V, ∃ H : AffineSubspace 𝕜 V,
      frontier s = H ∧ H tangent[Y] C at x :=
  h.2

end

end Set

end
