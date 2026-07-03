import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_0_1 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Definition 2.0.1 introduces convex subsets by closure under strict convex
  combinations `(1 - λ) x + λ y` for `0 < λ < 1`.
- `core/canonical`: the owner abstraction in mathlib is `Convex 𝕜 C`.
- `bridge/view`: primitive bridges are `convex_iff_segment_subset` (segment owner view) and
  `convex_iff_add_mem` (nonnegative affine-combination view at the weaker `SMul` layer), together
  with the set-level pointwise bridge `convex_iff_pointwise_add_subset` / `Convex.set_combo_subset`
  that avoids elementwise coefficient/coercion noise on theorem surfaces. The textbook
  strict-inequality formulation is the standard derived characterization `convex_iff_forall_pos`;
  its intrinsic owner-level coefficient form is `convex_iff_pairwise_pos`; the strict geometric
  form uses open segments via `convex_iff_openSegment_subset`, and owner-level
  open-segment closure is exposed by `Convex.openSegment_subset`.
- Domain-style sampling used here: `Convex`, `Convex.starConvex`, `convex_iff_segment_subset`,
  `convex_iff_add_mem`, `convex_iff_pointwise_add_subset`, `Convex.set_combo_subset`,
  `convex_iff_forall_pos`, `convex_iff_pairwise_pos`, `openSegment`,
  `convex_iff_openSegment_subset`,
  `Convex.segment_subset`, and `Convex.openSegment_subset`.
- Primitive data vs derived API: `Convex` is the primitive owner notion, and
  `Convex.starConvex` is its direct owner projection; the segment criterion and nonnegative
  affine-combination criteria (both elementwise and pointwise-set forms) are primitive bridge API
  at the canonical layer, while strict-coefficient and open-segment forms (including the intrinsic
  pairwise strict-coefficient bridge) are derived bridge API and should stay thin bridge theorems
  rather than parallel local owners.
- Layer target: `core/canonical`, with the source phrasing retained by canonical bridge theorems.

Abstraction audit (canonicalize):
- Codomain/ambient layer over-concrete? `No`: `Convex` is codomain-free and already at the
  canonical set/module owner layer.
- Scalar/ambient structure stronger than needed? `No`: the coefficient bridge is exposed at the
  weaker `SMul` layer via `convex_iff_add_mem`; strict-coefficient and open-segment forms are
  retained only as derived source-facing views.
- Owner tied to a concrete model? `No`: the owner is the intrinsic predicate `Convex 𝕜`.
- Ambient-vs-intrinsic topology mismatch? `No`: this surface avoids ambient closure/interior
  language entirely and uses affine-segment bridge theorems at the owner layer.
- Owner name/notation too heavy or too concrete? `No`: short canonical owner names are used
  directly (`Convex`, `Convex.openSegment_subset`) without local synonym wrappers.
- Need notation on theorem surfaces? `No extra notation needed`: existing segment/open-segment
  notation (`[x -[𝕜] y]`, `]x -[𝕜] y[`) already expresses the source-facing geometry.
-/

/- Definition 2.0.1: a subset is convex in the canonical mathlib sense of `Convex`,
meaning it contains every convex combination (hence in particular every strict convex
combination) of two of its points. -/
recall Convex

/- Direct owner bridge: from `x ∈ C`, convexity gives star-convexity of `C` at the center `x`.
This is the primitive elimination principle of the owner. -/
recall Convex.starConvex

/- Primitive bridge to the owner: convexity is exactly closure under all closed segments
`[x -[𝕜] y]` between points of the set. -/
recall convex_iff_segment_subset

/- Primitive coefficient bridge at the weaker abstraction layer: convexity is closure under all
nonnegative affine combinations `a • x + b • y` with `a + b = 1`. -/
recall convex_iff_add_mem

/- Primitive pointwise-set bridge at the same weak owner layer: convexity is equivalent to closure
under pointwise convex combinations `a • C + b • C` when `a,b ≥ 0` and `a + b = 1`. -/
recall convex_iff_pointwise_add_subset

/- Owner elimination in pointwise form: from convexity, each admissible pointwise convex
combination of the set is contained in the set. -/
recall Convex.set_combo_subset

/- The textbook formula `(1 - λ) x + λ y` with `0 < λ < 1` is the standard positive-coefficient
characterization of `Convex`. -/
recall convex_iff_forall_pos

/- Intrinsic strict-coefficient bridge on the owner itself: convexity is equivalent to pairwise
closure under positive affine combinations. -/
recall convex_iff_pairwise_pos

/- Source-facing strict-combination owner object: open segments `]x -[𝕜] y[` are the intrinsic
set-level strict interpolation surface. -/
recall openSegment

/- Intrinsic strict bridge: convexity is equivalent to closure under open segments. -/
recall convex_iff_openSegment_subset

/- Source-facing direct owner theorem: closed-segment membership is available from the owner
without introducing a chapter-local wrapper. -/
recall Convex.segment_subset

/- Source-facing direct owner theorem: membership in open segments is available without introducing
a parallel chapter-local wrapper. -/
recall Convex.openSegment_subset

/-! ### Definition_2_0_2 (from Chap01) -/
open scoped Convex

/- 
Source/core/bridge triage:
- `source-facing`: Definition 2.0.2 names the closed line segment between two points by the usual
  one-parameter convex-combination formula.
- `core/canonical`: mathlib's owner object for this notion is `segment`, written `[x -[𝕜] y]`.
- `bridge/view`: `segment_eq_image₂` is the primitive image bridge for `segment` at the
  ordered-semiring/`SMul` layer, while `segment_eq_image` is the standard source-facing
  one-parameter description at the ordered-ring affine-combination layer.
- Domain-style sampling used here: `segment`, `segment_eq_image₂`, `segment_eq_image`.
- Primitive data vs derived API: the closed segment itself is the owner-level notion; the explicit
  `λ`-parameter formula is derived API and should remain a bridge to `segment`, not a parallel local
  definition.
- Layer target: `core/canonical`, with the textbook formula retained only through the canonical
  bridge theorem.

Abstraction audit (canonicalize):
- Codomain/ambient layer over-concrete? `No`: the owner is the intrinsic set-level `segment`.
- Scalar/ambient structure stronger than needed? `No`: the primitive bridge is kept at the weaker
  ordered-semiring/`SMul` layer via `segment_eq_image₂`, while the textbook one-parameter formula
  is retained as derived API via `segment_eq_image`.
- Owner tied to a concrete model? `No`: no `ℝ^n`, `EuclideanSpace`, or coordinate model is fixed.
- Ambient-vs-intrinsic topology mismatch? `No`: this item is algebraic/affine, not an ambient
  topology reformulation.
- Owner name/notation too heavy or concrete? `No`: the canonical short owner notation
  `[x -[𝕜] y]` is used directly.
- Need extra local notation? `No`: existing canonical `segment` notation already matches the
  textbook surface.
-/

/- Definition 2.0.2: the closed line segment between two points is the canonical mathlib set
`segment 𝕜 x y` (notation `[x -[𝕜] y]`). -/
recall segment

/- Primitive bridge at the weakest canonical layer: `segment` is the image of two nonnegative
coefficients summing to `1`. -/
recall segment_eq_image₂

/- The textbook one-parameter formula for the closed line segment is the standard image
characterization of `segment` (without specializing the scalar in the public owner layer). -/
recall segment_eq_image

/-! ### Definition_2_0_3 (from Chap01) -/
section

open scoped Rockafellar

variable {X : Type*} {Y : Type*} {R : Type*}

/-
Source/core/bridge triage:
  half-spaces in finite-dimensional coordinate models, cut out by one nontrivial linear
  inequality. The owner layer here keeps
  only the primitive pairing data needed for those inequalities, rather than fixing an
  inner-product-space realization from the start.
- `core/canonical`: the owner abstractions are the interval preimages of the pairing functional
  `fun x ↦ ⟪x, b⟫ₚ`, equivalently of `HasLinearPairing.pairingLinear.flip b` in the linear layer.
- `bridge/view`: the four subset constructors `closedHalfSpaceLE`, `closedHalfSpaceGE`,
  `openHalfSpaceLT`, and `openHalfSpaceGT` are thin source-facing names for those interval
  preimages, while `Set.IsClosedHalfSpace Y 𝕜 s` and `Set.IsOpenHalfSpace Y 𝕜 s` classify subsets
  cut out by one nontrivial pairing functional in either textbook orientation.
- `intrinsic owner`: `Set.IsClosedLinearHalfSpace 𝕜 s` and
  `Set.IsOpenLinearHalfSpace 𝕜 s` are the pairing-free linear-functional owners (witnessed by
  `X →ₗ[𝕜] 𝕜`), with pairing-side predicates treated as bridge views into this intrinsic layer.
- Primitive data vs derived API: the primitive half-space data are the interval-preimage owner
  subsets, and the four named constructors are the source-facing bridge to that owner layer. The
  predicates saying that a set is a closed or open half-space are derived API. Their witness data
  should bundle a pairing functional that is genuinely
  nontrivial, because at the primitive pairing layer the mathematically relevant side condition is
  not `b ≠ 0` by itself but that the induced inequality is cut out by a nonconstant pairing
  functional.
- Domain-style sampling:
  `HasPairing` from `HasPairing.lean` isolates the primitive bilinear/evaluation data used by
  support-function and conjugate constructions later in the chapter, while `HasLinearPairing`
  is the canonical owner for genuinely linear-functional notions. Accordingly, the primitive set
  constructors stay at the raw pairing layer, but the textbook predicates `IsClosedHalfSpace` and
  `IsOpenHalfSpace` live on `HasLinearPairing`, with the pairing-side parameter `Y` and scalar
  parameter `𝕜` explicit in the owner surface and inner-product-space nonzero-normal bridges added
  only as companion theorems.
-/

section ClosedPrimitive

variable [LE R]
variable [HasPairing X Y R]
/-- The closed half-space `{x | ⟪x, b⟫ₚ ≤ β}` cut out by one pairing inequality. Specializing to
the inner-product pairing recovers the textbook coordinate form. -/
def closedHalfSpaceLE (b : Y) (β : R) : Set X :=
  {x : X | ⟪x, b⟫ₚ ≤ β}

/-- Membership in `closedHalfSpaceLE b β` is the inequality `⟪x, b⟫ₚ ≤ β`. -/
@[simp]
theorem mem_closedHalfSpaceLE_iff {b : Y} {x : X} {β : R} :
    x ∈ closedHalfSpaceLE b β ↔ ⟪x, b⟫ₚ ≤ β :=
  Iff.rfl

/-- The closed half-space `{x | β ≤ ⟪x, b⟫ₚ}` cut out by a pairing superlevel inequality. -/
abbrev closedHalfSpaceGE (b : Y) (β : R) : Set X :=
  {x : X | β ≤ ⟪x, b⟫ₚ}

/-- Membership in `closedHalfSpaceGE b β` is the inequality `β ≤ ⟪x, b⟫ₚ`. -/
@[simp]
theorem mem_closedHalfSpaceGE_iff {b : Y} {x : X} {β : R} :
    x ∈ closedHalfSpaceGE b β ↔ β ≤ ⟪x, b⟫ₚ :=
  Iff.rfl

end ClosedPrimitive

section ClosedOrder

variable [Preorder R]
variable [HasPairing X Y R]

/-- `closedHalfSpaceLE b β` is the `β`-sublevel preimage of the pairing functional
`x ↦ ⟪x, b⟫ₚ`. -/
theorem closedHalfSpaceLE_eq_preimage (b : Y) (β : R) :
    closedHalfSpaceLE b β = (fun x : X ↦ ⟪x, b⟫ₚ) ⁻¹' Set.Iic β :=
  by
    ext x
    rfl

/-- `closedHalfSpaceGE b β` is the `β`-superlevel preimage of the pairing functional
`x ↦ ⟪x, b⟫ₚ`. -/
theorem closedHalfSpaceGE_eq_preimage (b : Y) (β : R) :
    closedHalfSpaceGE b β = (fun x : X ↦ ⟪x, b⟫ₚ) ⁻¹' Set.Ici β :=
  by
    ext x
    rfl

end ClosedOrder

section OpenPrimitive

variable [LT R]
variable [HasPairing X Y R]

/-- The open half-space `{x | ⟪x, b⟫ₚ < β}` cut out by one pairing inequality. -/
def openHalfSpaceLT (b : Y) (β : R) : Set X :=
  {x : X | ⟪x, b⟫ₚ < β}

/-- Membership in `openHalfSpaceLT b β` is the inequality `⟪x, b⟫ₚ < β`. -/
@[simp]
theorem mem_openHalfSpaceLT_iff {b : Y} {x : X} {β : R} :
    x ∈ openHalfSpaceLT b β ↔ ⟪x, b⟫ₚ < β :=
  Iff.rfl

/-- The open half-space `{x | β < ⟪x, b⟫ₚ}` cut out by a pairing superlevel inequality. -/
abbrev openHalfSpaceGT (b : Y) (β : R) : Set X :=
  {x : X | β < ⟪x, b⟫ₚ}

/-- Membership in `openHalfSpaceGT b β` is the inequality `β < ⟪x, b⟫ₚ`. -/
@[simp]
theorem mem_openHalfSpaceGT_iff {b : Y} {x : X} {β : R} :
    x ∈ openHalfSpaceGT b β ↔ β < ⟪x, b⟫ₚ :=
  Iff.rfl

end OpenPrimitive

section OpenOrder

variable [Preorder R]
variable [HasPairing X Y R]

/-- `openHalfSpaceLT b β` is the strict `β`-sublevel preimage of the pairing functional
`x ↦ ⟪x, b⟫ₚ`. -/
theorem openHalfSpaceLT_eq_preimage (b : Y) (β : R) :
    openHalfSpaceLT b β = (fun x : X ↦ ⟪x, b⟫ₚ) ⁻¹' Set.Iio β :=
  by
    ext x
    rfl

/-- `openHalfSpaceGT b β` is the strict `β`-superlevel preimage of the pairing functional
`x ↦ ⟪x, b⟫ₚ`. -/
theorem openHalfSpaceGT_eq_preimage (b : Y) (β : R) :
    openHalfSpaceGT b β = (fun x : X ↦ ⟪x, b⟫ₚ) ⁻¹' Set.Ioi β :=
  by
    ext x
    rfl

end OpenOrder

namespace Set

section ClosedLinear

variable {𝕜 : Type*}
variable [LE 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable (Y) (𝕜)

/-- Definition 2.0.3: a subset is a closed half-space when it is cut out by one nontrivial
linear inequality, in either textbook orientation `⟪x, b⟫ₚ ≤ β` or `β ≤ ⟪x, b⟫ₚ`. The witness
normal stores the nontriviality of the induced linear functional
`HasLinearPairing.pairingLinear.flip b : X →ₗ[𝕜] 𝕜`. -/
def IsClosedHalfSpace (s : Set X) : Prop :=
  ∃ b : Y, ∃ β : 𝕜, HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜) ∧
    (s = closedHalfSpaceLE b β ∨ s = closedHalfSpaceGE b β)

variable {Y} {𝕜}

/-- The canonical linear half-space `closedHalfSpaceLE b β` is a closed half-space whenever the
cutting linear functional is nontrivial. -/
theorem closedHalfSpaceLE_isClosedHalfSpace {b : Y} {β : 𝕜}
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    Set.IsClosedHalfSpace Y 𝕜 (closedHalfSpaceLE b β : Set X) :=
  ⟨b, β, hb, Or.inl rfl⟩

/-- The canonical linear half-space `closedHalfSpaceGE b β` is a closed half-space whenever the
cutting linear functional is nontrivial. -/
theorem closedHalfSpaceGE_isClosedHalfSpace {b : Y} {β : 𝕜}
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    Set.IsClosedHalfSpace Y 𝕜 (closedHalfSpaceGE b β : Set X) :=
  ⟨b, β, hb, Or.inr rfl⟩

end ClosedLinear

section OpenLinear

variable {𝕜 : Type*}
variable [LT 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable (Y) (𝕜)

/-- Definition 2.0.3: a subset is an open half-space when it is cut out by one nontrivial linear
inequality, in either textbook orientation `⟪x, b⟫ₚ < β` or `β < ⟪x, b⟫ₚ`. -/
def IsOpenHalfSpace (s : Set X) : Prop :=
  ∃ b : Y, ∃ β : 𝕜, HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜) ∧
    (s = openHalfSpaceLT b β ∨ s = openHalfSpaceGT b β)

variable {Y} {𝕜}

/-- The canonical linear half-space `openHalfSpaceLT b β` is an open half-space whenever the
cutting linear functional is nontrivial. -/
theorem openHalfSpaceLT_isOpenHalfSpace {b : Y} {β : 𝕜}
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    Set.IsOpenHalfSpace Y 𝕜 (openHalfSpaceLT b β : Set X) :=
  ⟨b, β, hb, Or.inl rfl⟩

/-- The canonical linear half-space `openHalfSpaceGT b β` is an open half-space whenever the
cutting linear functional is nontrivial. -/
theorem openHalfSpaceGT_isOpenHalfSpace {b : Y} {β : 𝕜}
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    Set.IsOpenHalfSpace Y 𝕜 (openHalfSpaceGT b β : Set X) :=
  ⟨b, β, hb, Or.inr rfl⟩

end OpenLinear

section Linear

variable {𝕜 : Type*}
variable [LE 𝕜] [LT 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable (Y) (𝕜)

scoped[Rockafellar] notation3:max "closedHalfSpace[" Y "," 𝕜 "] " s =>
  Set.IsClosedHalfSpace Y 𝕜 s
scoped[Rockafellar] notation3:max "openHalfSpace[" Y "," 𝕜 "] " s =>
  Set.IsOpenHalfSpace Y 𝕜 s

/-- A subset is a half-space when it is either a closed half-space or an open half-space cut out
by one nontrivial linear inequality. This is the canonical source-facing owner for textbook
half-space statements that are independent of closed/open orientation. -/
def IsHalfSpace (s : Set X) : Prop :=
  Set.IsClosedHalfSpace Y 𝕜 s ∨ Set.IsOpenHalfSpace Y 𝕜 s

scoped[Rockafellar] notation3:max "halfSpace[" Y "," 𝕜 "] " s =>
  Set.IsHalfSpace Y 𝕜 s

variable {Y} {𝕜}

end Linear

section LinearFunctionalOwner

variable {𝕜 : Type*}
variable [Preorder 𝕜] [Semiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable (𝕜)

/-- Intrinsic linear-functional owner: a subset is a closed half-space when it is cut out by one
nonzero scalar-valued linear functional, in either orientation `f x ≤ β` or `β ≤ f x`. -/
def IsClosedLinearHalfSpace (s : Set X) : Prop :=
  ∃ f : X →ₗ[𝕜] 𝕜, ∃ β : 𝕜, f ≠ (0 : X →ₗ[𝕜] 𝕜) ∧
    (s = f ⁻¹' Set.Iic β ∨ s = f ⁻¹' Set.Ici β)

/-- Intrinsic linear-functional owner: a subset is an open half-space when it is cut out by one
nonzero scalar-valued linear functional, in either orientation `f x < β` or `β < f x`. -/
def IsOpenLinearHalfSpace (s : Set X) : Prop :=
  ∃ f : X →ₗ[𝕜] 𝕜, ∃ β : 𝕜, f ≠ (0 : X →ₗ[𝕜] 𝕜) ∧
    (s = f ⁻¹' Set.Iio β ∨ s = f ⁻¹' Set.Ioi β)

/-- Intrinsic linear-functional owner for half-spaces independent of closed/open orientation. -/
def IsLinearHalfSpace (s : Set X) : Prop :=
  IsClosedLinearHalfSpace 𝕜 s ∨ IsOpenLinearHalfSpace 𝕜 s

scoped[Rockafellar] notation3:max "closedLinearHalfSpace[" 𝕜 "] " s =>
  Set.IsClosedLinearHalfSpace 𝕜 s
scoped[Rockafellar] notation3:max "openLinearHalfSpace[" 𝕜 "] " s =>
  Set.IsOpenLinearHalfSpace 𝕜 s
scoped[Rockafellar] notation3:max "linearHalfSpace[" 𝕜 "] " s =>
  Set.IsLinearHalfSpace 𝕜 s

end LinearFunctionalOwner

section LinearFunctionalPairingBridge

variable {𝕜 : Type*}
variable [Preorder 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]

/-- Pairing-owner closed half-spaces are intrinsic linear-functional closed half-spaces. -/
theorem IsClosedHalfSpace.toClosedLinearHalfSpace {Y : Type*}
    [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    {s : Set X} (hs : closedHalfSpace[Y,𝕜] s) :
    closedLinearHalfSpace[𝕜] s := by
  rcases hs with ⟨b, β, hb, hs | hs⟩
  · refine ⟨HasLinearPairing.pairingLinear.flip b, β, hb, Or.inl ?_⟩
    calc
      s = closedHalfSpaceLE b β := hs
      _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iic β := by
        ext x
        simp [closedHalfSpaceLE, HasLinearPairing.pairing_eq_pairingLinear]
  · refine ⟨HasLinearPairing.pairingLinear.flip b, β, hb, Or.inr ?_⟩
    calc
      s = closedHalfSpaceGE b β := hs
      _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ici β := by
        ext x
        simp [closedHalfSpaceGE, HasLinearPairing.pairing_eq_pairingLinear]

/-- Pairing-owner open half-spaces are intrinsic linear-functional open half-spaces. -/
theorem IsOpenHalfSpace.toOpenLinearHalfSpace {Y : Type*}
    [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    {s : Set X} (hs : openHalfSpace[Y,𝕜] s) :
    openLinearHalfSpace[𝕜] s := by
  rcases hs with ⟨b, β, hb, hs | hs⟩
  · refine ⟨HasLinearPairing.pairingLinear.flip b, β, hb, Or.inl ?_⟩
    calc
      s = openHalfSpaceLT b β := hs
      _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iio β := by
        ext x
        simp [openHalfSpaceLT, HasLinearPairing.pairing_eq_pairingLinear]
  · refine ⟨HasLinearPairing.pairingLinear.flip b, β, hb, Or.inr ?_⟩
    calc
      s = openHalfSpaceGT b β := hs
      _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ioi β := by
        ext x
        simp [openHalfSpaceGT, HasLinearPairing.pairing_eq_pairingLinear]

/-- Pairing-owner half-spaces are intrinsic linear-functional half-spaces. -/
theorem IsHalfSpace.toLinearHalfSpace {Y : Type*}
    [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    {s : Set X} (hs : halfSpace[Y,𝕜] s) :
    linearHalfSpace[𝕜] s := by
  rcases hs with hs | hs
  · exact Or.inl hs.toClosedLinearHalfSpace
  · exact Or.inr hs.toOpenLinearHalfSpace

/-- Under surjectivity of `HasLinearPairing.pairingLinear.flip`, every intrinsic closed linear
half-space admits a pairing-owner witness. -/
theorem IsClosedLinearHalfSpace.toClosedHalfSpace_of_surjective_pairingLinear_flip
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    (hflip : Function.Surjective (HasLinearPairing.pairingLinear.flip : Y → X →ₗ[𝕜] 𝕜))
    {s : Set X} (hs : closedLinearHalfSpace[𝕜] s) :
    closedHalfSpace[Y,𝕜] s := by
  rcases hs with ⟨f, β, hf, hs | hs⟩
  · rcases hflip f with ⟨b, rfl⟩
    refine ⟨b, β, ?_, Or.inl ?_⟩
    · simpa using hf
    · calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iic β := hs
        _ = closedHalfSpaceLE b β := by
          ext x
          simp [closedHalfSpaceLE, HasLinearPairing.pairing_eq_pairingLinear]
  · rcases hflip f with ⟨b, rfl⟩
    refine ⟨b, β, ?_, Or.inr ?_⟩
    · simpa using hf
    · calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ici β := hs
        _ = closedHalfSpaceGE b β := by
          ext x
          simp [closedHalfSpaceGE, HasLinearPairing.pairing_eq_pairingLinear]

/-- Under surjectivity of `HasLinearPairing.pairingLinear.flip`, every intrinsic open linear
half-space admits a pairing-owner witness. -/
theorem IsOpenLinearHalfSpace.toOpenHalfSpace_of_surjective_pairingLinear_flip
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    (hflip : Function.Surjective (HasLinearPairing.pairingLinear.flip : Y → X →ₗ[𝕜] 𝕜))
    {s : Set X} (hs : openLinearHalfSpace[𝕜] s) :
    openHalfSpace[Y,𝕜] s := by
  rcases hs with ⟨f, β, hf, hs | hs⟩
  · rcases hflip f with ⟨b, rfl⟩
    refine ⟨b, β, ?_, Or.inl ?_⟩
    · simpa using hf
    · calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iio β := hs
        _ = openHalfSpaceLT b β := by
          ext x
          simp [openHalfSpaceLT, HasLinearPairing.pairing_eq_pairingLinear]
  · rcases hflip f with ⟨b, rfl⟩
    refine ⟨b, β, ?_, Or.inr ?_⟩
    · simpa using hf
    · calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ioi β := hs
        _ = openHalfSpaceGT b β := by
          ext x
          simp [openHalfSpaceGT, HasLinearPairing.pairing_eq_pairingLinear]

/-- Under surjectivity of `HasLinearPairing.pairingLinear.flip`, intrinsic linear half-spaces and
pairing-owner half-spaces coincide. -/
theorem IsLinearHalfSpace.toHalfSpace_of_surjective_pairingLinear_flip
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    (hflip : Function.Surjective (HasLinearPairing.pairingLinear.flip : Y → X →ₗ[𝕜] 𝕜))
    {s : Set X} (hs : linearHalfSpace[𝕜] s) :
    halfSpace[Y,𝕜] s := by
  rcases hs with hs | hs
  · exact Or.inl (hs.toClosedHalfSpace_of_surjective_pairingLinear_flip (Y := Y) hflip)
  · exact Or.inr (hs.toOpenHalfSpace_of_surjective_pairingLinear_flip (Y := Y) hflip)

/-- Under surjectivity of `HasLinearPairing.pairingLinear.flip`, pairing-owner and intrinsic
closed-half-space owners are equivalent. -/
theorem isClosedHalfSpace_iff_closedLinearHalfSpace_of_surjective_pairingLinear_flip
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    (hflip : Function.Surjective (HasLinearPairing.pairingLinear.flip : Y → X →ₗ[𝕜] 𝕜))
    {s : Set X} :
    IsClosedHalfSpace Y 𝕜 s ↔ IsClosedLinearHalfSpace 𝕜 s := by
  constructor
  · intro hs
    exact hs.toClosedLinearHalfSpace
  · intro hs
    exact hs.toClosedHalfSpace_of_surjective_pairingLinear_flip (Y := Y) hflip

/-- Under surjectivity of `HasLinearPairing.pairingLinear.flip`, pairing-owner and intrinsic
open-half-space owners are equivalent. -/
theorem isOpenHalfSpace_iff_openLinearHalfSpace_of_surjective_pairingLinear_flip
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    (hflip : Function.Surjective (HasLinearPairing.pairingLinear.flip : Y → X →ₗ[𝕜] 𝕜))
    {s : Set X} :
    IsOpenHalfSpace Y 𝕜 s ↔ IsOpenLinearHalfSpace 𝕜 s := by
  constructor
  · intro hs
    exact hs.toOpenLinearHalfSpace
  · intro hs
    exact hs.toOpenHalfSpace_of_surjective_pairingLinear_flip (Y := Y) hflip

/-- Under surjectivity of `HasLinearPairing.pairingLinear.flip`, pairing-owner and intrinsic
half-space owners are equivalent. -/
theorem isHalfSpace_iff_linearHalfSpace_of_surjective_pairingLinear_flip
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    (hflip : Function.Surjective (HasLinearPairing.pairingLinear.flip : Y → X →ₗ[𝕜] 𝕜))
    {s : Set X} :
    IsHalfSpace Y 𝕜 s ↔ IsLinearHalfSpace 𝕜 s := by
  constructor
  · intro hs
    exact hs.toLinearHalfSpace
  · intro hs
    exact hs.toHalfSpace_of_surjective_pairingLinear_flip (Y := Y) hflip

end LinearFunctionalPairingBridge

section ClosedLinearFunctionalCharacterization

variable {𝕜 : Type*}
variable [Preorder 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable {s : Set X}

/-- `IsClosedHalfSpace` is equivalent to a preimage description by the scalar-valued linear
functional `HasLinearPairing.pairingLinear.flip b`. -/
theorem isClosedHalfSpace_iff_exists_pairingLinear_preimage :
    (closedHalfSpace[Y,𝕜] s) ↔
      ∃ b : Y, ∃ β : 𝕜,
        HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜) ∧
          (s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iic β ∨
            s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ici β) := by
  constructor
  · intro hs
    rcases hs with ⟨b, β, hb, hs | hs⟩
    · refine ⟨b, β, hb, Or.inl ?_⟩
      calc
        s = closedHalfSpaceLE b β := hs
        _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iic β := by
          ext x
          simp [closedHalfSpaceLE, HasLinearPairing.pairing_eq_pairingLinear]
    · refine ⟨b, β, hb, Or.inr ?_⟩
      calc
        s = closedHalfSpaceGE b β := hs
        _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ici β := by
          ext x
          simp [closedHalfSpaceGE, HasLinearPairing.pairing_eq_pairingLinear]
  · intro hs
    rcases hs with ⟨b, β, hb, hs | hs⟩
    · refine ⟨b, β, hb, Or.inl ?_⟩
      calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iic β := hs
        _ = closedHalfSpaceLE b β := by
          ext x
          simp [closedHalfSpaceLE, HasLinearPairing.pairing_eq_pairingLinear]
    · refine ⟨b, β, hb, Or.inr ?_⟩
      calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ici β := hs
        _ = closedHalfSpaceGE b β := by
          ext x
          simp [closedHalfSpaceGE, HasLinearPairing.pairing_eq_pairingLinear]

end ClosedLinearFunctionalCharacterization

section OpenLinearFunctionalCharacterization

variable {𝕜 : Type*}
variable [Preorder 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable {s : Set X}

/-- `IsOpenHalfSpace` is equivalent to a strict-preimage description by the scalar-valued linear
functional `HasLinearPairing.pairingLinear.flip b`. -/
theorem isOpenHalfSpace_iff_exists_pairingLinear_preimage :
    (openHalfSpace[Y,𝕜] s) ↔
      ∃ b : Y, ∃ β : 𝕜,
        HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜) ∧
          (s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iio β ∨
            s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ioi β) := by
  constructor
  · intro hs
    rcases hs with ⟨b, β, hb, hs | hs⟩
    · refine ⟨b, β, hb, Or.inl ?_⟩
      calc
        s = openHalfSpaceLT b β := hs
        _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iio β := by
          ext x
          simp [openHalfSpaceLT, HasLinearPairing.pairing_eq_pairingLinear]
    · refine ⟨b, β, hb, Or.inr ?_⟩
      calc
        s = openHalfSpaceGT b β := hs
        _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ioi β := by
          ext x
          simp [openHalfSpaceGT, HasLinearPairing.pairing_eq_pairingLinear]
  · intro hs
    rcases hs with ⟨b, β, hb, hs | hs⟩
    · refine ⟨b, β, hb, Or.inl ?_⟩
      calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iio β := hs
        _ = openHalfSpaceLT b β := by
          ext x
          simp [openHalfSpaceLT, HasLinearPairing.pairing_eq_pairingLinear]
    · refine ⟨b, β, hb, Or.inr ?_⟩
      calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ioi β := hs
        _ = openHalfSpaceGT b β := by
          ext x
          simp [openHalfSpaceGT, HasLinearPairing.pairing_eq_pairingLinear]

end OpenLinearFunctionalCharacterization

section LinearPairingNontrivial

variable {𝕜 : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- In any linear-pairing ambient layer, a nonzero scalar-valued functional witness
`HasLinearPairing.pairingLinear.flip b ≠ 0` forces the normal parameter to be nonzero. -/
theorem ne_zero_of_pairingLinear_flip_ne_zero {b : Y}
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    b ≠ 0 := by
  intro hb0
  apply hb
  ext x
  simp [hb0]

end LinearPairingNontrivial

end Set

end

/-! ### Corollary_2_0_4 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.0.4 says that each of the four oriented half-spaces cut out by one
  pairing inequality is convex; the coordinate-free formulation here specializes to the textbook
  `ℝ^n` statement.
- `core/canonical`: the owner abstraction is `Convex 𝕜 s`; the canonical mathlib theorems are
  `convex_halfSpace_le`, `convex_halfSpace_ge`, `convex_halfSpace_lt`, and
  `convex_halfSpace_gt`, applied to the linear functional `x ↦ ⟪x, b⟫ₚ`.
- `bridge/view`: the chapter owner predicates `IsClosedHalfSpace` and `IsOpenHalfSpace` from
  Definition 2.0.3 package the textbook half-space presentations, while the owner subsets
  `closedHalfSpaceLE`, `closedHalfSpaceGE`, `openHalfSpaceLT`, and `openHalfSpaceGT` realize the
  four oriented textbook inequalities directly.
- Primitive data vs derived API: the actual half-space subsets are primitive data; convexity and
  closedness are derived theorem-level API. The primitive bridge theorems below are stated first
  with local linearity/continuity assumptions, then specialized to the chapter typeclass owners.
- Domain-style sampling:
  `closedHalfSpaceLE`/`openHalfSpaceLT` and `IsClosedHalfSpace`/`IsOpenHalfSpace` from
  `Definition_2_0_3`, and the mathlib owner theorems `convex_halfSpace_le`,
  `convex_halfSpace_ge`, `convex_halfSpace_lt`, and `convex_halfSpace_gt`.
-/

section

open scoped Rockafellar

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
variable [Module 𝕜 R] [PosSMulMono 𝕜 R]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [HasPairing X Y R]

/-- The left-oriented closed half-space is convex once the cutting pairing functional is linear. -/
theorem closedHalfSpaceLE_convex_of_isLinear (b : Y) (β : R)
    (hb : IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    Convex 𝕜 (closedHalfSpaceLE b β : Set X) := by
  simpa [closedHalfSpaceLE] using convex_halfSpace_le hb β

/-- The right-oriented closed half-space is convex once the cutting pairing functional is linear. -/
theorem closedHalfSpaceGE_convex_of_isLinear (b : Y) (β : R)
    (hb : IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    Convex 𝕜 (closedHalfSpaceGE b β : Set X) := by
  simpa [closedHalfSpaceGE] using convex_halfSpace_ge hb β

namespace Set

/-- A set presented as one oriented closed pairing half-space is convex when its cutting pairing
evaluation `x ↦ ⟪x, b⟫ₚ` is linear in `x`. -/
theorem convex_of_exists_eq_closedHalfSpace_of_forall_isLinear {s : Set X}
    (hs : ∃ b : Y, ∃ β : R,
      (s = closedHalfSpaceLE b β ∨ s = closedHalfSpaceGE b β) ∧
      IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    Convex 𝕜 s := by
  rcases hs with ⟨b, β, hs, hlin⟩
  rcases hs with rfl | rfl
  · exact closedHalfSpaceLE_convex_of_isLinear b β hlin
  · exact closedHalfSpaceGE_convex_of_isLinear b β hlin

end Set

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [PosSMulMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]

/-- Every intrinsic closed linear half-space is convex. -/
theorem Set.IsClosedLinearHalfSpace.convex {s : Set X}
    (hs : closedLinearHalfSpace[𝕜] s) :
    Convex 𝕜 s := by
  rcases hs with ⟨f, β, -, rfl | rfl⟩
  · simpa using (convex_halfSpace_le f.isLinear β)
  · simpa using (convex_halfSpace_ge f.isLinear β)

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedCancelAddMonoid 𝕜]
variable [PosSMulStrictMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]

/-- Every intrinsic open linear half-space is convex. -/
theorem Set.IsOpenLinearHalfSpace.convex {s : Set X}
    (hs : openLinearHalfSpace[𝕜] s) :
    Convex 𝕜 s := by
  rcases hs with ⟨f, β, -, rfl | rfl⟩
  · simpa using (convex_halfSpace_lt f.isLinear β)
  · simpa using (convex_halfSpace_gt f.isLinear β)

/-- Every intrinsic linear half-space (closed or open orientation) is convex. -/
theorem Set.IsLinearHalfSpace.convex {s : Set X}
    (hs : linearHalfSpace[𝕜] s) :
    Convex 𝕜 s := by
  rcases hs with hs | hs
  · exact Set.IsClosedLinearHalfSpace.convex hs
  · exact Set.IsOpenLinearHalfSpace.convex hs

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [PosSMulMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- The left-oriented closed half-space `closedHalfSpaceLE b β` is convex. -/
theorem closedHalfSpaceLE_convex (b : Y) (β : 𝕜) :
    Convex 𝕜 (closedHalfSpaceLE b β : Set X) := by
  exact
    closedHalfSpaceLE_convex_of_isLinear b β
      (HasLinearPairing.isLinear_pairing_left b)

/-- The right-oriented closed half-space `closedHalfSpaceGE b β` is convex. -/
theorem closedHalfSpaceGE_convex (b : Y) (β : 𝕜) :
    Convex 𝕜 (closedHalfSpaceGE b β : Set X) := by
  exact
    closedHalfSpaceGE_convex_of_isLinear b β
      (HasLinearPairing.isLinear_pairing_left b)

/-- Every closed half-space is convex. -/
theorem Set.IsClosedHalfSpace.convex {s : Set X}
    (hs : closedHalfSpace[Y,𝕜] s) :
    Convex 𝕜 s := by
  exact Set.IsClosedLinearHalfSpace.convex hs.toClosedLinearHalfSpace

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]
variable [Module 𝕜 R] [PosSMulStrictMono 𝕜 R]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [HasPairing X Y R]

/-- The left-oriented open half-space is convex once the cutting pairing functional is linear. -/
theorem openHalfSpaceLT_convex_of_isLinear (b : Y) (β : R)
    (hb : IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    Convex 𝕜 (openHalfSpaceLT b β : Set X) := by
  simpa [openHalfSpaceLT] using convex_halfSpace_lt hb β

/-- The right-oriented open half-space is convex once the cutting pairing functional is linear. -/
theorem openHalfSpaceGT_convex_of_isLinear (b : Y) (β : R)
    (hb : IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    Convex 𝕜 (openHalfSpaceGT b β : Set X) := by
  simpa [openHalfSpaceGT] using convex_halfSpace_gt hb β

namespace Set

/-- A set presented as one oriented open pairing half-space is convex when its cutting pairing
evaluation `x ↦ ⟪x, b⟫ₚ` is linear in `x`. -/
theorem convex_of_exists_eq_openHalfSpace_of_forall_isLinear {s : Set X}
    (hs : ∃ b : Y, ∃ β : R,
      (s = openHalfSpaceLT b β ∨ s = openHalfSpaceGT b β) ∧
      IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    Convex 𝕜 s := by
  rcases hs with ⟨b, β, hs, hlin⟩
  rcases hs with rfl | rfl
  · exact openHalfSpaceLT_convex_of_isLinear b β hlin
  · exact openHalfSpaceGT_convex_of_isLinear b β hlin

end Set

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedCancelAddMonoid 𝕜]
variable [PosSMulStrictMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- The left-oriented open half-space `openHalfSpaceLT b β` is convex. -/
theorem openHalfSpaceLT_convex (b : Y) (β : 𝕜) :
    Convex 𝕜 (openHalfSpaceLT b β : Set X) := by
  exact
    openHalfSpaceLT_convex_of_isLinear b β
      (HasLinearPairing.isLinear_pairing_left b)

/-- The right-oriented open half-space `openHalfSpaceGT b β` is convex. -/
theorem openHalfSpaceGT_convex (b : Y) (β : 𝕜) :
    Convex 𝕜 (openHalfSpaceGT b β : Set X) := by
  exact
    openHalfSpaceGT_convex_of_isLinear b β
      (HasLinearPairing.isLinear_pairing_left b)

/-- Every open half-space is convex. -/
theorem Set.IsOpenHalfSpace.convex {s : Set X}
    (hs : openHalfSpace[Y,𝕜] s) :
    Convex 𝕜 s := by
  exact Set.IsOpenLinearHalfSpace.convex hs.toOpenLinearHalfSpace

/-- Corollary 2.0.4: every textbook half-space, whether closed or open, is convex. -/
theorem Set.IsHalfSpace.convex {s : Set X}
    (hs : halfSpace[Y,𝕜] s) :
    Convex 𝕜 s := by
  exact Set.IsLinearHalfSpace.convex hs.toLinearHalfSpace

end

section

open scoped Rockafellar

variable {R : Type*} [Preorder R]
variable [TopologicalSpace R] [OrderClosedTopology R]
variable {X : Type*} [TopologicalSpace X]
variable {Y : Type*} [HasPairing X Y R]

/-- The left-oriented closed half-space is closed once `x ↦ ⟪x, b⟫ₚ` is continuous. -/
theorem closedHalfSpaceLE_closed_of_continuous (b : Y) (β : R)
    (hb : Continuous (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    IsClosed (closedHalfSpaceLE b β : Set X) := by
  simpa [closedHalfSpaceLE] using isClosed_le hb continuous_const

/-- The right-oriented closed half-space is closed once `x ↦ ⟪x, b⟫ₚ` is continuous. -/
theorem closedHalfSpaceGE_closed_of_continuous (b : Y) (β : R)
    (hb : Continuous (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    IsClosed (closedHalfSpaceGE b β : Set X) := by
  simpa [closedHalfSpaceGE] using isClosed_le continuous_const hb

namespace Set

/-- A set presented as one oriented closed pairing half-space is closed when its cutting pairing
evaluation `x ↦ ⟪x, b⟫ₚ` is continuous in `x`. -/
theorem isClosed_of_exists_eq_closedHalfSpace_of_forall_continuous {s : Set X}
    (hs : ∃ b : Y, ∃ β : R,
      (s = closedHalfSpaceLE b β ∨ s = closedHalfSpaceGE b β) ∧
      Continuous (fun x : X ↦ (⟪x, b⟫ₚ : R))) :
    IsClosed s := by
  rcases hs with ⟨b, β, hs, hcont⟩
  rcases hs with rfl | rfl
  · exact closedHalfSpaceLE_closed_of_continuous b β hcont
  · exact closedHalfSpaceGE_closed_of_continuous b β hcont

end Set

section

variable [HasContinuousPairing X Y R]

/-- The left-oriented closed half-space `closedHalfSpaceLE b β` is closed. -/
theorem closedHalfSpaceLE_closed (b : Y) (β : R) :
    IsClosed (closedHalfSpaceLE b β : Set X) := by
  exact closedHalfSpaceLE_closed_of_continuous b β
    (HasContinuousPairing.continuous_pairing_left b)

/-- The right-oriented closed half-space `closedHalfSpaceGE b β` is closed. -/
theorem closedHalfSpaceGE_closed (b : Y) (β : R) :
    IsClosed (closedHalfSpaceGE b β : Set X) := by
  exact closedHalfSpaceGE_closed_of_continuous b β
    (HasContinuousPairing.continuous_pairing_left b)

end

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [CommSemiring 𝕜] [Preorder 𝕜]
variable [TopologicalSpace 𝕜] [OrderClosedTopology 𝕜]
variable {X : Type*} [TopologicalSpace X] [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Every closed half-space is closed when each nontrivial pairing evaluation is continuous. -/
theorem Set.IsClosedHalfSpace.isClosed_of_forall_continuous {s : Set X}
    (hs : closedHalfSpace[Y,𝕜] s)
    (hcont : ∀ b : Y,
      HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜) →
        Continuous (fun x : X ↦ (⟪x, b⟫ₚ : 𝕜))) :
    IsClosed s := by
  rcases hs with ⟨b, β, hb, hs | hs⟩
  · rcases hs with rfl
    exact closedHalfSpaceLE_closed_of_continuous b β (hcont b hb)
  · rcases hs with rfl
    exact closedHalfSpaceGE_closed_of_continuous b β (hcont b hb)

section

variable [HasContinuousPairing X Y 𝕜]

/-- Every closed half-space is closed. -/
theorem Set.IsClosedHalfSpace.isClosed {s : Set X}
    (hs : closedHalfSpace[Y,𝕜] s) :
    IsClosed s := by
  exact Set.IsClosedHalfSpace.isClosed_of_forall_continuous hs
    (fun b _ ↦ HasContinuousPairing.continuous_pairing_left b)

end

end

/-! ### Proposition_2_0_5 (from Chap01) -/
open scoped Affine

variable {𝕜 : Type*} {V : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-
Source/core/bridge triage:
- `source-facing`: Proposition 2.0.5 says every affine subset, including `∅` and `Set.univ`,
  is convex. The formal statement is the coordinate-free ordered-ring module version.
- `core/canonical`: the owner abstraction is `AffineSubspace 𝕜 V`, with canonical convexity fact
  `AffineSubspace.convex`, and the source-facing set owner is `affine[𝕜] C`.
- `bridge/view`: the fixed-point criterion `C = affineSpan 𝕜 C` and the explicit carrier witness
  form `∃ S : AffineSubspace 𝕜 V, C = S` are retained as derived bridge corollaries.
- Domain-style sampling used here: `AffineSubspace.convex`, `affineSpan`,
  `Set.IsAffine`, `affine[𝕜]`, `isAffine_iff_affineSpan_eq_self`.
- Primitive data vs derived API: `AffineSubspace` and `AffineSubspace.convex` are primitive owner
  API; `Set.IsAffine` is the canonical set-level owner; affine-span and existential carrier forms
  are derived views.
- Layer target: `source-facing` owner form `affine[𝕜]`, with bridge lemmas for nearby set-level
  criteria.
-/

namespace Set

/- Proposition 2.0.5 is governed by the owner theorem `AffineSubspace.convex`; the primary
source-facing theorem below is the canonical set-owner notation `affine[𝕜]`. -/
recall AffineSubspace.convex

/- Canonicalization decision record (this pass):
- Codomain/ambient check: no extended-codomain object appears; this item is a set-level convexity
  statement in a module.
- Scalar/ambient structure check: keep the canonical `Convex`/`AffineSubspace.convex` layer
  assumptions `[Ring 𝕜] [PartialOrder 𝕜]`.
- Owner check: keep `affine[𝕜]` as the source-facing owner and derive convexity from the
  canonical owner theorem `AffineSubspace.convex`.
- Topology check: no topological operator is part of this statement.
- Owner-name check: no additional owner synonym is introduced.
- Notation check: no new notation is needed for this item.
-/

/-- The affine span of any set is convex. This is the direct set-level bridge of
`AffineSubspace.convex`. -/
theorem convex_affineSpan (C : Set V) :
    Convex 𝕜 (affineSpan 𝕜 C : Set V) := by
  simpa using (affineSpan 𝕜 C).convex

namespace IsAffine

variable {C : Set V}

/-- Proposition 2.0.5 in owner-method form: every affine set is convex. -/
theorem convex (hC : affine[𝕜] C) : Convex 𝕜 C := by
  -- Route correction: use the source proof directly by specializing affine-combination
  -- closure to coefficients in `[0, 1]`, instead of switching to the affine-subspace owner.
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  -- The affine hypothesis gives membership for the same binary affine combination at scalar `b`.
  have hline : AffineMap.lineMap x y b ∈ C := hC.lineMap_mem hx hy b
  -- Rewriting the affine combination with `a + b = 1` yields the required convex combination.
  have ha' : a = 1 - b := by
    rw [← hab]
    abel
  simpa [AffineMap.lineMap_apply_module, ha'] using hline

end IsAffine

/-- Proposition 2.0.5 in notation-first owner form: every affine set is convex. -/
theorem convex_of_affine {C : Set V} :
    (affine[𝕜] C) → Convex 𝕜 C :=
  IsAffine.convex

/-- Proposition 2.0.5 in affine-span fixed-point form: if `affineSpan 𝕜 C = C`, then `C` is
convex. This is a bridge corollary of `IsAffine.convex`. -/
theorem convex_of_affineSpan_eq {C : Set V} (hC : affineSpan 𝕜 C = C) :
    Convex 𝕜 C := by
  have hAffine : affine[𝕜] C := IsAffine.of_affineSpan_eq hC
  exact hAffine.convex

/-- Proposition 2.0.5 in existential owner form: if `C` is the carrier of an affine subspace,
then `C` is convex. This is a bridge corollary of `IsAffine.convex`. -/
theorem convex_of_exists_affineSubspace {C : Set V}
    (hC : ∃ S : AffineSubspace 𝕜 V, C = S) :
    Convex 𝕜 C := by
  have hAffine : affine[𝕜] C := IsAffine.of_exists_affineSubspace_eq hC
  exact hAffine.convex

end Set

/-! ### Proposition_2_0_6 (from Chap01) -/
section

open scoped Rockafellar

variable {𝕜 : Type*} [DivisionSemiring 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]

/-
Source/core/bridge triage:
- `source-facing`: Proposition 2.0.6 says that every textbook half-space, whether closed or open,
  contains a point.
- `core/canonical`: the primitive owner abstraction is a scalar-valued linear functional
  `f : X →ₗ[𝕜] 𝕜`; pairing-flip maps are bridge instances of that owner.
- `bridge/view`: the chapter constructors `closedHalfSpaceLE`, `closedHalfSpaceGE`,
  `openHalfSpaceLT`, and `openHalfSpaceGT`, together with the predicates `Set.IsClosedHalfSpace`
  and `Set.IsOpenHalfSpace`, are the source-facing half-space view of that owner layer.
- Primitive data vs derived API: the primitive data are the half-space constructors and the
  nontriviality witness on the cutting linear functional; nonemptiness is derived directly from
  surjectivity of a nonzero scalar-valued linear functional, combined with order-endpoint
  witnesses below and above the threshold for strict inequalities.
- Domain-style sampling: the relevant declarations are
  `Module.Dual.range_eq_top_of_ne_zero`, `LinearMap.range_eq_top`, and, at the bridge layer,
  `HasLinearPairing.pairingLinear.flip` with the chapter half-space owners.
- Layer target: `source-facing`, with the supporting API proved owner-first from the canonical
  intrinsic linear-functional owner layer rather than from downstream affine-hyperplane
  infrastructure.
-/

namespace LinearMap

/-- A nonzero scalar-valued linear functional is surjective. -/
theorem surjective_of_ne_zero_scalar (f : X →ₗ[𝕜] 𝕜)
    (hf : f ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    Function.Surjective f := by
  exact LinearMap.range_eq_top.mp <| Module.Dual.range_eq_top_of_ne_zero (f := f) hf

/-- Every scalar value is attained by a nonzero scalar-valued linear functional. -/
theorem exists_eq_of_ne_zero_scalar (f : X →ₗ[𝕜] 𝕜) (β : 𝕜)
    (hf : f ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    ∃ x : X, f x = β :=
  surjective_of_ne_zero_scalar (f := f) hf β

/-- The closed sublevel preimage of a nonzero scalar-valued linear functional is nonempty. -/
theorem preimage_Iic_nonempty_of_ne_zero_scalar [Preorder 𝕜]
    (f : X →ₗ[𝕜] 𝕜) (β : 𝕜)
    (hf : f ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    (f ⁻¹' Set.Iic β).Nonempty := by
  rcases exists_eq_of_ne_zero_scalar (f := f) β hf with ⟨x, hx⟩
  exact ⟨x, by simp [hx]⟩

/-- The closed superlevel preimage of a nonzero scalar-valued linear functional is nonempty. -/
theorem preimage_Ici_nonempty_of_ne_zero_scalar [Preorder 𝕜]
    (f : X →ₗ[𝕜] 𝕜) (β : 𝕜)
    (hf : f ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    (f ⁻¹' Set.Ici β).Nonempty := by
  rcases exists_eq_of_ne_zero_scalar (f := f) β hf with ⟨x, hx⟩
  exact ⟨x, by simp [hx]⟩

/-- The strict sublevel set of a nonzero scalar-valued linear functional is nonempty when the
codomain has no minimum. -/
theorem sublevel_lt_nonempty_of_ne_zero_scalar [LT 𝕜] [NoMinOrder 𝕜]
    (f : X →ₗ[𝕜] 𝕜) (β : 𝕜)
    (hf : f ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    {x : X | f x < β}.Nonempty := by
  rcases exists_lt β with ⟨γ, hγlt⟩
  rcases exists_eq_of_ne_zero_scalar (f := f) γ hf with ⟨x, hx⟩
  exact ⟨x, by simpa [hx] using hγlt⟩

/-- The strict superlevel set of a nonzero scalar-valued linear functional is nonempty when the
codomain has no maximum. -/
theorem superlevel_gt_nonempty_of_ne_zero_scalar [LT 𝕜] [NoMaxOrder 𝕜]
    (f : X →ₗ[𝕜] 𝕜) (β : 𝕜)
    (hf : f ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    {x : X | β < f x}.Nonempty := by
  rcases exists_gt β with ⟨γ, hβltγ⟩
  rcases exists_eq_of_ne_zero_scalar (f := f) γ hf with ⟨x, hx⟩
  exact ⟨x, by simpa [hx] using hβltγ⟩

end LinearMap

end

section LinearOwnerClosedOrder

open scoped Rockafellar

variable {𝕜 : Type*} [DivisionSemiring 𝕜] [Preorder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]

namespace Set

/-- Every intrinsic closed linear half-space is nonempty. -/
theorem IsClosedLinearHalfSpace.nonempty {s : Set X} (hs : closedLinearHalfSpace[𝕜] s) :
    s.Nonempty := by
  rcases hs with ⟨f, β, hf, rfl | rfl⟩
  · exact LinearMap.preimage_Iic_nonempty_of_ne_zero_scalar (f := f) β hf
  · exact LinearMap.preimage_Ici_nonempty_of_ne_zero_scalar (f := f) β hf

end Set

end LinearOwnerClosedOrder

section LinearOwnerOpenOrder

open scoped Rockafellar

variable {𝕜 : Type*} [DivisionSemiring 𝕜] [Preorder 𝕜]
variable [NoMinOrder 𝕜] [NoMaxOrder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]

namespace Set

/-- Every intrinsic open linear half-space is nonempty. -/
theorem IsOpenLinearHalfSpace.nonempty {s : Set X} (hs : openLinearHalfSpace[𝕜] s) :
    s.Nonempty := by
  rcases hs with ⟨f, β, hf, rfl | rfl⟩
  · exact LinearMap.sublevel_lt_nonempty_of_ne_zero_scalar (f := f) β hf
  · exact LinearMap.superlevel_gt_nonempty_of_ne_zero_scalar (f := f) β hf

/-- Every intrinsic linear half-space is nonempty. -/
theorem IsLinearHalfSpace.nonempty {s : Set X} (hs : linearHalfSpace[𝕜] s) :
    s.Nonempty := by
  rcases hs with hs | hs
  · exact hs.nonempty
  · exact hs.nonempty

end Set

end LinearOwnerOpenOrder

section ClosedOrder

open scoped Rockafellar

variable {𝕜 : Type*} [Semifield 𝕜] [Preorder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- The left-oriented closed half-space `closedHalfSpaceLE b β` is nonempty whenever the cutting
linear functional is nontrivial. -/
theorem closedHalfSpaceLE_nonempty (b : Y) (β : 𝕜)
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    (closedHalfSpaceLE b β : Set X).Nonempty := by
  rcases LinearMap.preimage_Iic_nonempty_of_ne_zero_scalar
      (f := HasLinearPairing.pairingLinear.flip b) β hb with ⟨x, hx⟩
  exact ⟨x, by simpa [mem_closedHalfSpaceLE_iff] using hx⟩

/-- The right-oriented closed half-space `closedHalfSpaceGE b β` is nonempty whenever the cutting
linear functional is nontrivial. -/
theorem closedHalfSpaceGE_nonempty (b : Y) (β : 𝕜)
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    (closedHalfSpaceGE b β : Set X).Nonempty := by
  rcases LinearMap.preimage_Ici_nonempty_of_ne_zero_scalar
      (f := HasLinearPairing.pairingLinear.flip b) β hb with ⟨x, hx⟩
  exact ⟨x, by simpa [mem_closedHalfSpaceGE_iff] using hx⟩

namespace Set

/-- Every closed half-space is nonempty. -/
theorem IsClosedHalfSpace.nonempty {s : Set X}
    (hs : closedHalfSpace[Y,𝕜] s) :
    s.Nonempty := by
  exact Set.IsClosedLinearHalfSpace.nonempty (hs.toClosedLinearHalfSpace)

end Set

end ClosedOrder

section OpenOrder

open scoped Rockafellar

variable {𝕜 : Type*} [Semifield 𝕜] [Preorder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- The left-oriented open half-space `openHalfSpaceLT b β` is nonempty whenever the cutting
linear functional is nontrivial. -/
theorem openHalfSpaceLT_nonempty (b : Y) (β : 𝕜)
    [NoMinOrder 𝕜]
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    (openHalfSpaceLT b β : Set X).Nonempty := by
  rcases LinearMap.sublevel_lt_nonempty_of_ne_zero_scalar
      (f := HasLinearPairing.pairingLinear.flip b) β hb with ⟨x, hx⟩
  exact ⟨x, by simpa [mem_openHalfSpaceLT_iff] using hx⟩

/-- The right-oriented open half-space `openHalfSpaceGT b β` is nonempty whenever the cutting
linear functional is nontrivial. -/
theorem openHalfSpaceGT_nonempty (b : Y) (β : 𝕜)
    [NoMaxOrder 𝕜]
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    (openHalfSpaceGT b β : Set X).Nonempty := by
  rcases LinearMap.superlevel_gt_nonempty_of_ne_zero_scalar
      (f := HasLinearPairing.pairingLinear.flip b) β hb with ⟨x, hx⟩
  exact ⟨x, by simpa [mem_openHalfSpaceGT_iff] using hx⟩

namespace Set

/-- Every open half-space is nonempty. -/
theorem IsOpenHalfSpace.nonempty {s : Set X}
    [NoMinOrder 𝕜] [NoMaxOrder 𝕜]
    (hs : openHalfSpace[Y,𝕜] s) :
    s.Nonempty := by
  exact Set.IsOpenLinearHalfSpace.nonempty (hs.toOpenLinearHalfSpace)

end Set

end OpenOrder

section Proposition

open scoped Rockafellar

variable {𝕜 : Type*} [Semifield 𝕜] [Preorder 𝕜]
variable [NoMinOrder 𝕜] [NoMaxOrder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

namespace Set

/-- Proposition 2.0.6: every textbook half-space is nonempty. -/
theorem IsHalfSpace.nonempty {s : Set X} (hs : halfSpace[Y,𝕜] s) :
    s.Nonempty := by
  exact Set.IsLinearHalfSpace.nonempty (hs.toLinearHalfSpace)

end Set

/-- Proposition 2.0.6: every textbook half-space, whether closed or open, is nonempty. -/
theorem nonempty_of_halfSpace {s : Set X} (hs : halfSpace[Y,𝕜] s) :
    s.Nonempty :=
  hs.nonempty

end Proposition
