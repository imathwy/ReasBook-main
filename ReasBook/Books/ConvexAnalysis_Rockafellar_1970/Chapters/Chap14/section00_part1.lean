import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_14_0_1 (from Chap03) -/
section

open scoped Rockafellar

universe u v w

variable {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {M : Type u} [AddCommMonoid M] [Module 𝕜 M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N]
variable [HasLinearPairing M N 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.1 defines the polar of a cone `K` by a pointwise pairing inequality.
- `core/canonical`: the ambient-level owner abstraction is mathlib's dual-cone construction
  `PointedCone.dual (HasLinearPairing.pairingLinear)`.
- `bridge/view`: `Kᵒ[𝕜]` in the `PolarCone` scope is Rockafellar's
  nonpositive-sign-convention view of that owner, implemented by applying the owner to the
  negated pairing map; the first derived API is the membership theorem `mem_polarCone_iff`.

Domain-style sampling used here:
- `PointedCone.dual`;
- `PointedCone.mem_dual`;
- `PointedCone.dual_anti`;
- `PointedCone.dual_hull`.

Primitive data vs derived API:
- primitive owner object:
  `PointedCone.dual (-(HasLinearPairing.pairingLinear : M →ₗ[𝕜] Module.Dual 𝕜 N)) K`;
- source-facing bridge/view: the notation `Kᵒ[𝕜]`;
- derived API: rewriting membership in its underlying set.

Layer target: `source-facing`, implemented as a thin sign-convention bridge/view over the owner
dual cone rather than as a second cone owner.

The source's nonemptiness and convex-cone hypotheses are redundant for the bare definition, since
the same formula defines a pointed cone for any `K : Set M`.
-/

end

-- The notation is scoped rather than global because the project also uses the same textbook glyph
-- `ᵒ` for the set polar `Set.polar : Set E → Set E`, so an unscoped postfix notation on `Set E`
-- would be ambiguous. The canonical source-facing surface keeps the scalar explicit as `Kᵒ[𝕜]`.
-- This owner-level notation sits at the minimal layer of `PointedCone.dual` with negated pairing:
-- `CommRing` is needed for `-HasLinearPairing.pairingLinear`, and `IsOrderedRing` is required by
-- the dual-cone owner itself.
namespace PolarCone

/-- Rockafellar's polar-cone owner with the chapter sign convention. This is the canonical owner
bridge over `PointedCone.dual` at negated pairing. -/
@[reducible] def polarCone
    {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
    {M : Type u} [AddCommMonoid M] [Module 𝕜 M]
    {N : Type v} [AddCommMonoid N] [Module 𝕜 N]
    [HasLinearPairing M N 𝕜] (K : Set M) : PointedCone 𝕜 N :=
  PointedCone.dual (-(HasLinearPairing.pairingLinear : M →ₗ[𝕜] Module.Dual 𝕜 N)) K

set_option quotPrecheck false in
scoped notation:max K "ᵒ[" k "]" =>
  (PolarCone.polarCone (𝕜 := k) K)

end PolarCone

section

open scoped Rockafellar

universe u v w

variable {𝕜 : Type w} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {M : Type u} [AddCommMonoid M] [Module 𝕜 M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N]
variable [HasLinearPairing M N 𝕜]

/-- Source-facing dual-cone owner with the nonnegative pairing convention. -/
@[reducible] def sourceDualCone (K : Set M) : PointedCone 𝕜 N :=
  PointedCone.dual (HasLinearPairing.pairingLinear : M →ₗ[𝕜] Module.Dual 𝕜 N) K

-- There is no bare postfix `∗` notation here, because Chapter 6 already uses `g∗` for concave
-- conjugates. The parameterized notation keeps the scalar explicit and avoids that conflict while
-- exposing the source inequality directly via the named owner `sourceDualCone`.
set_option quotPrecheck false in
scoped[Rockafellar] notation:max K "∗[" 𝕜 "]" =>
  (sourceDualCone (𝕜 := 𝕜) K)

end

section

open scoped Rockafellar

universe u v w

variable {𝕜 : Type w} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {M : Type u} [AddCommMonoid M] [Module 𝕜 M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N]
variable [HasLinearPairing M N 𝕜]

/-- Membership in `K∗[𝕜]` is exactly the source dual-cone pairing inequality. -/
@[simp] theorem mem_sourceDualCone_iff_pairing_nonneg {K : Set M} {xStar : N} :
    xStar ∈ K∗[𝕜] ↔ ∀ x ∈ K, (0 : 𝕜) ≤ ⟪x, xStar⟫ₚ :=
  by simp [sourceDualCone, PointedCone.mem_dual]

end

section

open scoped Rockafellar PolarCone

universe u v w

variable {𝕜 : Type w} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {M : Type u} [AddCommMonoid M] [Module 𝕜 M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N]
variable [HasLinearPairing M N 𝕜]

/-- The source dual-cone owner `K∗[𝕜]` is exactly the canonical owner `PointedCone.dual`
at the pairing layer. -/
@[simp] theorem sourceDualCone_eq_dual (K : Set M) :
    K∗[𝕜] =
      PointedCone.dual
        (HasLinearPairing.pairingLinear : M →ₗ[𝕜] Module.Dual 𝕜 N) K :=
  rfl

end

section

open scoped Rockafellar PolarCone

universe u v w

variable {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {M : Type u} [AddCommMonoid M] [Module 𝕜 M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N]
variable [HasLinearPairing M N 𝕜]

-- Proof sketch: unfold `Kᵒ[𝕜]`; membership is exactly the displayed universal
-- nonpositivity condition from the source-facing sign convention for the pairing dual cone.
/-- Membership in `Kᵒ[𝕜]` is exactly the defining pairing inequality. -/
@[simp]
theorem mem_polarCone_iff_pairing {K : Set M} {xStar : N} :
    xStar ∈ Kᵒ[𝕜] ↔ ∀ x ∈ K, ⟪x, xStar⟫ₚ ≤ (0 : 𝕜) :=
  by simp

/-- Membership in `Kᵒ[𝕜]` is exactly the defining pairing inequality. -/
@[simp] theorem mem_polarCone_iff {K : Set M} {xStar : N} :
    xStar ∈ Kᵒ[𝕜] ↔ ∀ x ∈ K, ⟪x, xStar⟫ₚ ≤ (0 : 𝕜) :=
  mem_polarCone_iff_pairing

end

section

open scoped PolarCone Rockafellar

universe u v w

variable {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {M : Type u} [AddCommMonoid M] [Module 𝕜 M]
variable {N : Type v} [AddCommGroup N] [Module 𝕜 N]
variable [HasLinearPairing M N 𝕜]

-- Proof sketch: unpack `K∗[𝕜]` by its direct inequality surface and `Kᵒ[𝕜]` by
-- `mem_polarCone_iff_pairing`; both directions are the same sign rewrite.
/-- Membership in the source dual cone is equivalent to membership of the negated point in
the chapter polar cone. -/
@[simp] theorem mem_sourceDualCone_iff_neg_mem_polarCone {K : Set M} {xStar : N} :
    xStar ∈ K∗[𝕜] ↔ -xStar ∈ Kᵒ[𝕜] := by
  constructor
  · intro hx
    refine (mem_polarCone_iff_pairing (K := K) (xStar := -xStar)).2 ?_
    intro x hxK
    have hpair' : -⟪x, xStar⟫ₚ ≤ (0 : 𝕜) := by
      exact neg_nonpos.mpr <|
        (mem_sourceDualCone_iff_pairing_nonneg (K := K) (xStar := xStar)).1 hx x hxK
    simpa using hpair'
  · intro hx
    refine (mem_sourceDualCone_iff_pairing_nonneg (K := K) (xStar := xStar)).2 ?_
    intro x hxK
    have hpair :=
      (mem_polarCone_iff_pairing (K := K) (xStar := -xStar)).1 hx x hxK
    have hpair' : -⟪x, xStar⟫ₚ ≤ (0 : 𝕜) := by
      simpa using hpair
    exact neg_nonpos.mp hpair'

end

/-! ### Text_14_0_2 (from Chap03) -/
open scoped RealInnerProductSpace PolarCone Rockafellar

universe u v w

section

variable {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {X : Type u} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type v} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.2 identifies the polar of a linear subspace of `R^n` with its
  orthogonal complement.
- `core/canonical`: the owner abstractions are the source-facing polar formula `polarCone` from
  `Text_14_0_1` and the chapter pairing-annihilator owner `Submodule.pairingOrthogonal` from
  `Text_1_6`, both at the primitive pairing layer.
- `bridge/view`: the textbook orthogonal complement `Submodule.orthogonal` is retained as the real
  inner-product specialization through `Submodule.pairingOrthogonal_eq_orthogonal_real`.

Domain-style sampling used here:
- `polarCone` and `mem_polarCone_iff_pairing` from `Text_14_0_1`;
- `Submodule.pairingOrthogonal` and `Submodule.mem_pairingOrthogonal_iff` from `Text_1_6`;
- `Submodule.pairingOrthogonal_eq_orthogonal_real` from `Text_1_6`.

Primitive data vs derived API:
- primitive datum: a subspace `K : Submodule 𝕜 X` in a paired module;
- derived API: first the canonical pairing-annihilator identity for the polar cone of `K`, then the
  source-facing real inner-product orthogonal-complement specialization.

Layer target: owner-first. The primary declaration is now at the primitive pairing layer; the
source-facing `R^n` orthogonal statement is a thin specialization bridge.
-/

namespace Submodule

@[simp] theorem mem_polarCone_submodule_iff {K : Submodule 𝕜 X} {y : Y} :
    y ∈ (K : Set X)ᵒ[𝕜] ↔ y ∈ Kᗮₚ := by
  rw [mem_polarCone_iff_pairing]
  rw [mem_pairingOrthogonal_iff]
  constructor
  · intro hy x hxK
    have hle : (⟪x, y⟫ₚ : 𝕜) ≤ 0 := hy x hxK
    have hge : (0 : 𝕜) ≤ ⟪x, y⟫ₚ := by
      have hxneg : (⟪(-1 : 𝕜) • x, y⟫ₚ : 𝕜) ≤ 0 :=
        hy (((-1 : 𝕜) • x)) (K.smul_mem (-1) hxK)
      have hxneg' : -(⟪x, y⟫ₚ : 𝕜) ≤ 0 := by
        simpa [HasLinearPairing.pairing_eq_pairingLinear] using hxneg
      exact neg_nonpos.mp hxneg'
    exact le_antisymm hle hge
  · intro hy x hxK
    simpa [HasLinearPairing.pairing_eq_pairingLinear] using (hy x hxK).le

/-- The polar of a subspace is exactly its pairing annihilator in the chapter owner sense. -/
theorem polarCone_eq_pairingOrthogonal (K : Submodule 𝕜 X) :
    ((K : Set X)ᵒ[𝕜] : PointedCone 𝕜 Y) = PointedCone.ofSubmodule Kᗮₚ := by
  ext y
  simpa using (mem_polarCone_submodule_iff (K := K) (y := y))

/-- Set-level view of `polarCone_eq_pairingOrthogonal`. -/
theorem polarCone_set_eq_pairingOrthogonal (K : Submodule 𝕜 X) :
    (((K : Set X)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) = ((Kᗮₚ : Submodule 𝕜 Y) : Set Y) := by
  simpa using congrArg
    (fun C : PointedCone 𝕜 Y => (C : Set Y))
    (polarCone_eq_pairingOrthogonal (K := K))

end Submodule

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Submodule

@[simp] theorem mem_polarCone_submodule_iff_orthogonal {K : Submodule ℝ E} {y : E} :
    y ∈ (K : Set E)ᵒ[ℝ] ↔ y ∈ Kᗮ := by
  simpa [pairingOrthogonal_eq_orthogonal_real] using
    (mem_polarCone_submodule_iff (K := K) (y := y))

/-- Text 14.0.2: if `K` is a linear subspace of a real inner-product space, specialized in the
source to `R^n`, then the polar `Kᵒ[ℝ]` of `K` coincides with its orthogonal complement. -/
@[simp] theorem polarCone_eq_orthogonal (K : Submodule ℝ E) :
    (K : Set E)ᵒ[ℝ] = PointedCone.ofSubmodule Kᗮ := by
  ext y
  simpa using (mem_polarCone_submodule_iff_orthogonal (K := K) (y := y))

/-- Set-level view of `polarCone_eq_orthogonal`. -/
theorem polarCone_set_eq_orthogonal (K : Submodule ℝ E) :
    (((K : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) = (Kᗮ : Set E) := by
  exact congrArg
    (fun C : PointedCone ℝ E => (C : Set E))
    (polarCone_eq_orthogonal (K := K))

end Submodule

end

/-! ### Text_14_0_3 (from Chap03) -/
section

open scoped PolarCone Rockafellar

universe u v w z

variable {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {X : Type u} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type v} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable {I : Type z}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.3 identifies the polar cone of the convex cone generated by a vector
  family `a : I → X` with the intersection of the half-spaces cut out by the generators.
- `core/canonical`: the owner abstractions are the generated convex cone
  `cone[𝕜] (Set.range a)` from Definition 2.6.10, with raw owner
  `PointedCone.hull 𝕜 (Set.range a)`, and the pairing-layer polar-cone operator
  `polarCone 𝕜` from Text 14.0.1.
- `bridge/view`: the source phrase “all non-negative linear combinations” is already canonically
  represented by `cone[𝕜] (Set.range a)`, while the generator inequalities are derived API from
  the owner-side polar membership formula.

Domain-style sampling used here:
- `cone[𝕜] S` / `PointedCone.hull`;
- `PointedCone.hull`;
- `PointedCone.dual_hull` from mathlib's cone-duality owner API;
- `PointedCone.mem_dual`;
- `polarCone` from Text 14.0.1.

Primitive data vs derived API:
- primitive owner-side input: a generating set `S : Set X`;
- source-facing specialization input: an indexed family `a : I → X` viewed via `Set.range a`;
- owner-side objects: the generated cone `cone[𝕜] S` and its polar;
- derived API: first, the set-level half-space characterization from
  `PointedCone.dual_hull`/`PointedCone.mem_dual`; then the range-family statement as a direct
  specialization.

Layer target: owner-first. The canonical theorem is set-based at `cone[𝕜] S`, with the textbook
family form recovered by specialization to `S = Set.range a`.

The source's nonemptiness assumption on the vector collection is redundant for this equality, so it
is omitted from the Lean header.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: this item is set/pairing valued and does not involve
  an extended codomain.
- Scalar/ambient check: the owner APIs used here (`cone`, `polar`) already live
  at the scalar-generic
  ordered-ring pairing layer, so no further scalar specialization is needed.
- Owner check: use the canonical owner theorem `PointedCone.dual_hull` first,
  then expose source-facing
  inequality forms as derived views.
- Topology check: this item is not topology-facing; no intrinsic/relative topology rewrite applies.
- Notation check: keep textbook notation on theorem surfaces (`cone[𝕜]`, `ᵒ[𝕜]`) and avoid raw
  `PointedCone.hull` spelling in public theorem names.
-/

/-- Owner-level bridge: taking the polar commutes with passage from a generating set `S` to the
generated cone `cone[𝕜] S`. -/
private theorem polarCone_cone_eq (S : Set X) :
    (cone[𝕜] S : Set X)ᵒ[𝕜] = (Sᵒ[𝕜] : PointedCone 𝕜 Y) := by
  change
    PointedCone.dual
        (-(HasLinearPairing.pairingLinear : X →ₗ[𝕜] Module.Dual 𝕜 Y))
        (↑(PointedCone.hull 𝕜 S)) =
      PointedCone.dual
        (-(HasLinearPairing.pairingLinear : X →ₗ[𝕜] Module.Dual 𝕜 Y))
        S
  exact
    PointedCone.dual_hull
      (p := (-(HasLinearPairing.pairingLinear : X →ₗ[𝕜] Module.Dual 𝕜 Y)))
      (s := S)

/-- Membership bridge for generated-cone polars: `xStar` lies in `(cone[𝕜] S)ᵒ[𝕜]` exactly when its
pairing with every generator in `S` is nonpositive. -/
@[simp] theorem mem_polarCone_cone_iff {S : Set X} {xStar : Y} :
    xStar ∈ ((cone[𝕜] S : Set X)ᵒ[𝕜]) ↔
      ∀ x ∈ S, ⟪x, xStar⟫ₚ ≤ (0 : 𝕜) := by
  rw [polarCone_cone_eq]
  exact mem_polarCone_iff_pairing (K := S) (xStar := xStar)

/-- Canonical cone-polar bridge in membership form: `xStar` lies in the polar of
`cone[𝕜] S` exactly when its pairing with every generator in `S` is nonpositive. -/
theorem polarCone_cone_eq_pairing_nonpositive {S : Set X} {xStar : Y} :
    xStar ∈ ((cone[𝕜] S : Set X)ᵒ[𝕜]) ↔
      ∀ x ∈ S, ⟪x, xStar⟫ₚ ≤ (0 : 𝕜) :=
  mem_polarCone_cone_iff (S := S) (xStar := xStar)

/-- Range-indexed membership bridge for generated-cone polars: `xStar` lies in the polar of
`cone[𝕜] (Set.range a)` exactly when it has nonpositive pairing with each generator `a i`. -/
@[simp] theorem mem_polarCone_cone_range_iff {a : I → X} {xStar : Y} :
    xStar ∈ ((cone[𝕜] (Set.range a) : Set X)ᵒ[𝕜]) ↔
      ∀ i, ⟪a i, xStar⟫ₚ ≤ (0 : 𝕜) := by
  constructor
  · intro hx i
    exact (mem_polarCone_cone_iff (S := Set.range a) (xStar := xStar)).1 hx (a i) ⟨i, rfl⟩
  · intro hx
    exact (mem_polarCone_cone_iff (S := Set.range a) (xStar := xStar)).2 <| by
      rintro x ⟨i, rfl⟩
      exact hx i

-- Proof sketch: specialize `polarCone_cone_eq_pairing_nonpositive` to `S = Set.range a` and
-- rewrite universal quantification over the range as quantification over indices.
/-- Text 14.0.3 in source-facing membership form: `xStar` lies in the polar cone of
`cone[𝕜] (Set.range a)` iff its pairing with each generator `a i` is nonpositive. -/
theorem polarCone_cone_range_eq_generator_inequalities {a : I → X} {xStar : Y} :
    xStar ∈ ((cone[𝕜] (Set.range a) : Set X)ᵒ[𝕜]) ↔
      ∀ i, ⟪a i, xStar⟫ₚ ≤ (0 : 𝕜) :=
  mem_polarCone_cone_range_iff (a := a) (xStar := xStar)

end

/-! ### Text_14_0_4 (from Chap03) -/
section

open scoped PolarCone

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
variable [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
variable [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ] [HasPairingSwap E E ℝ]
variable [((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)).IsContPerfPair]

local notation "pairingLinearMap" => (HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.4 states that the polar of the polar of a nonempty convex cone `K`
  is the closure of `K`.
- `core/canonical`: the owner abstractions are mathlib's bundled `ConvexCone ℝ E`, the bundled
  closure `ConvexCone.closure`, the set-duality owner `PointedCone.dual`, and its proper-cone
  closed owner `ProperCone.dual` for a continuous perfect pairing.
- `bridge/view`: `polarCone` is Rockafellar's nonpositive-sign-convention view of
  `PointedCone.dual (-(HasLinearPairing.pairingLinear))`, so the theorem remains source-facing
  while its proof factors through closure invariance of `polarCone`, the sign bridge between
  `polarCone` and `ProperCone.dual`, and the canonical proper-cone bipolar owner theorem
  `ProperCone.dual_flip_dual`.

Domain-style sampling used here:
- `ConvexCone ℝ E` as the canonical owner for convex-cone structure;
- `ConvexCone.closure` as the canonical closed-cone completion;
- `PointedCone.dual` as the owner/set bridge behind the source-facing sign convention;
- `polarCone_closure` as closure invariance at the source-facing owner;
- `ProperCone.dual_flip_dual` as the canonical bipolar theorem for proper cones.

Primitive data vs derived API:
- primitive input: a bundled pointed cone `K : PointedCone ℝ E`;
- derived API: the source-facing bipolar equality
  `((K : Set E)ᵒ[ℝ] : Set E)ᵒ[ℝ] = closure (K : Set E)`.

Scalar-layer note:
- this file remains specialized to `ℝ` because the upstream owner theorem
  `ProperCone.dual_flip_dual` used in the proof is currently available in mathlib only at the
  real locally convex layer.
-/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [HasContinuousPairing E E ℝ] [HasPairingSwap E E ℝ] in
private theorem polarCone_eq_neg_dual (K : Set E) :
    (((Kᵒ[ℝ] : PointedCone ℝ E) : Set E)) = (-(ProperCone.dual pairingLinearMap K : Set E)) := by
  ext y
  change y ∈ Kᵒ[ℝ] ↔ y ∈ (-(ProperCone.dual pairingLinearMap K : Set E))
  rw [mem_polarCone_iff]
  constructor
  · intro hy
    change -y ∈ ProperCone.dual pairingLinearMap K
    rw [ProperCone.mem_dual]
    intro x hx
    have hxle : (pairingLinearMap x) y ≤ (0 : ℝ) := hy x hx
    simpa [LinearMap.map_neg] using (neg_nonneg.mpr hxle)
  · intro hy
    change -y ∈ ProperCone.dual pairingLinearMap K at hy
    rw [ProperCone.mem_dual] at hy
    intro x hx
    have hxnonneg : (0 : ℝ) ≤ (pairingLinearMap x) (-y) := hy (x := x) hx
    have hxneg : (0 : ℝ) ≤ -((pairingLinearMap x) y) := by
      simpa [LinearMap.map_neg] using hxnonneg
    exact neg_nonneg.mp hxneg

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [HasContinuousPairing E E ℝ] [HasPairingSwap E E ℝ] in
private theorem dual_neg_eq_neg_dual (K : Set E) :
    ProperCone.dual pairingLinearMap (-K) = (-(ProperCone.dual pairingLinearMap K : Set E)) := by
  ext y
  constructor
  · intro hy
    change -y ∈ ProperCone.dual pairingLinearMap K
    have hy' : ∀ ⦃x : E⦄, x ∈ -K → 0 ≤ (pairingLinearMap x) y := by
      simpa [ProperCone.mem_dual] using hy
    rw [ProperCone.mem_dual]
    intro x hx
    have hneg : (0 : ℝ) ≤ (pairingLinearMap (-x)) y := hy' (x := -x) (by simpa using hx)
    have hxle : (pairingLinearMap x) y ≤ (0 : ℝ) := by
      have hxneg : (0 : ℝ) ≤ -((pairingLinearMap x) y) := by
        simpa [LinearMap.map_neg] using hneg
      exact neg_nonneg.mp hxneg
    simpa [LinearMap.map_neg] using (neg_nonneg.mpr hxle)
  · intro hy
    change -y ∈ ProperCone.dual pairingLinearMap K at hy
    have hy' : ∀ ⦃x : E⦄, x ∈ K → 0 ≤ (pairingLinearMap x) (-y) := by
      simpa [ProperCone.mem_dual] using hy
    have hdual : ∀ ⦃x : E⦄, x ∈ -K → 0 ≤ (pairingLinearMap x) y := by
      intro x hx
      have hxK : -x ∈ K := by simpa using hx
      have hneg : (0 : ℝ) ≤ (pairingLinearMap (-x)) (-y) := hy' (x := -x) hxK
      simpa [LinearMap.map_neg] using hneg
    exact (by simpa [ProperCone.mem_dual] using hdual)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [HasContinuousPairing E E ℝ] in
private theorem dual_eq_dual_flip (K : Set E) :
    (ProperCone.dual pairingLinearMap K : Set E) =
      (ProperCone.dual
        ((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ).flip) K : Set E) := by
  ext y
  constructor
  · intro hy
    have hy' : ∀ ⦃x : E⦄, x ∈ K → 0 ≤ (pairingLinearMap x) y := by
      simpa [ProperCone.mem_dual] using hy
    have hyflip : ∀ ⦃x : E⦄, x ∈ K →
        0 ≤ (((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ).flip) x) y := by
      intro x hx
      change (0 : ℝ) ≤ (pairingLinearMap y) x
      have hxy : (0 : ℝ) ≤ (pairingLinearMap x) y := hy' hx
      have hswap : (pairingLinearMap y) x = (pairingLinearMap x) y := by
        simpa [HasLinearPairing.pairing_eq_pairingLinear] using
          (HasPairingSwap.pairing_swap (x := y) (y := x))
      simpa [hswap] using hxy
    simpa [ProperCone.mem_dual] using hyflip
  · intro hy
    have hy' : ∀ ⦃x : E⦄, x ∈ K →
        0 ≤ (((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ).flip) x) y := by
      simpa [ProperCone.mem_dual] using hy
    have hyorig : ∀ ⦃x : E⦄, x ∈ K → 0 ≤ (pairingLinearMap x) y := by
      intro x hx
      have hyx : (0 : ℝ) ≤
          (((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ).flip) x) y := hy' hx
      change (0 : ℝ) ≤ (pairingLinearMap y) x at hyx
      have hswap : (pairingLinearMap y) x = (pairingLinearMap x) y := by
        simpa [HasLinearPairing.pairing_eq_pairingLinear] using
          (HasPairingSwap.pairing_swap (x := y) (y := x))
      simpa [hswap] using hyx
    simpa [ProperCone.mem_dual] using hyorig

-- Proof sketch: first replace `K` by its closure using the owner closure-invariance theorem for
-- `polarCone`. For the closed cone `K.closure`, the double source-facing polar is rewritten
-- through the sign bridge to `ProperCone.dual`, then reduced to the proper-cone bipolar owner
-- theorem `ProperCone.dual_flip_dual`.
/-- Text 14.0.4: the polar of the polar of a nonempty convex cone `K` is the closure of the
carrier of `K`. -/
private theorem polarCone_polarCone_eq_closure_of_nonempty_convexCone
    (K : ConvexCone ℝ E) (hK_nonempty : (K : Set E).Nonempty) :
    (((((K : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) =
      closure (K : Set E) := by
  have hpolarClosure :
      (((closure (K : Set E))ᵒ[ℝ] : PointedCone ℝ E) : Set E) =
        (((K : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) := by
    exact congrArg (fun P : PointedCone ℝ E => (P : Set E))
      (polarCone_closure (𝕜 := ℝ) (K := (K : Set E)))
  have hdoubleClosure :
      (((((K : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) =
        (((((closure (K : Set E))ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) :=
      by
    exact (congrArg (fun S : Set E ↦ ((Sᵒ[ℝ] : PointedCone ℝ E) : Set E)) hpolarClosure).symm
  have hKcl : (K.closure : Set E).Nonempty ∧ IsClosed (K.closure : Set E) := by
    constructor
    · exact Set.Nonempty.mono subset_closure hK_nonempty
    · simp [ConvexCone.coe_closure]
  let Kc : ProperCone ℝ E :=
    { toSubmodule :=
        (K.closure).toPointedCone (ConvexCone.Pointed.of_nonempty_of_isClosed hKcl.1 hKcl.2)
      isClosed' := hKcl.2 }
  have hKc_set : (Kc : Set E) = closure (K : Set E) := by
    change (K.closure : Set E) = closure (K : Set E)
    rfl
  calc
    (((((K : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) =
        (((((closure (K : Set E))ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) :=
        hdoubleClosure
    _ = (((((Kc : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) := by
          simp [hKc_set]
    _ = (-(ProperCone.dual pairingLinearMap
            (((Kc : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) : Set E)) := by
      rw [polarCone_eq_neg_dual]
    _ = (-(ProperCone.dual pairingLinearMap
            (-(ProperCone.dual pairingLinearMap (Kc : Set E) : Set E)) : Set E)) := by
      rw [polarCone_eq_neg_dual]
    _ = (-(-(ProperCone.dual pairingLinearMap
            ((ProperCone.dual pairingLinearMap (Kc : Set E) : Set E)) : Set E)) :
          Set E) := by
      rw [dual_neg_eq_neg_dual]
    _ = (ProperCone.dual pairingLinearMap
          ((ProperCone.dual pairingLinearMap (Kc : Set E) : Set E)) : Set E) := by
      rw [neg_neg]
    _ = (ProperCone.dual
          ((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ).flip)
          ((ProperCone.dual pairingLinearMap (Kc : Set E) : Set E)) : Set E) := by
      simpa using
        (dual_eq_dual_flip
          (K := (ProperCone.dual pairingLinearMap (Kc : Set E) : Set E)))
    _ = (Kc : Set E) := by
      exact congrArg ((↑) : ProperCone ℝ E → Set E)
        (ProperCone.dual_flip_dual pairingLinearMap Kc)
    _ = closure (K : Set E) := hKc_set

-- Proof sketch: apply the nonempty-convex-cone bridge theorem to the canonical pointed-cone
-- owner `(K : ConvexCone ℝ E)`, using `0 ∈ K` from pointedness.
/-- Text 14.0.4: for a pointed convex cone `K`, the polar of the polar of `K` is the closure of
its carrier. This owner form keeps nonemptiness in the cone owner (`PointedCone`) rather than as
an extra theorem argument. -/
theorem polarCone_polarCone_eq_closure
    (K : PointedCone ℝ E) :
    (((((K : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) =
      closure (K : Set E) := by
  exact polarCone_polarCone_eq_closure_of_nonempty_convexCone
    (K := (K : ConvexCone ℝ E))
    ⟨0, K.zero_mem⟩

/-- Nonempty-convex-cone bridge for Text 14.0.4. This keeps the source hypothesis form available
when an upstream declaration still packages the cone as `ConvexCone` plus explicit nonemptiness. -/
theorem polarCone_polarCone_eq_closure_of_nonempty
    (K : ConvexCone ℝ E) (hK_nonempty : (K : Set E).Nonempty) :
    (((((K : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) =
      closure (K : Set E) :=
  polarCone_polarCone_eq_closure_of_nonempty_convexCone K hK_nonempty

end

/-! ### Text_14_0_5 (from Chap03) -/
noncomputable section

open scoped Rockafellar

universe u v w

section

variable {X : Type u} {Y : Type v}
variable {α : Type w}
variable [Preorder α] [SupSet α] [One α]
variable [HasPairing Y X α]

/-
Source/core/bridge triage:
- `source-facing`: Text 14.0.5 defines the polar `Cᵒ[α]` by the support-function inequality
  `δ*(xStar | C) ≤ 1`.
- `core/canonical`: the owner abstraction is the support-function `1`-sublevel preimage.
- `bridge/view`: pointwise membership inequalities are derived from this owner by
  `supportFunction_def`.

Primitive data vs derived API:
- primitive owner: `Set.polar`, now at the pairing layer `C : Set X ↦ Set Y` rather than the
  over-concrete self-dual surface `Set E → Set E`;
- derived API: the pointwise membership criterion and closure invariance.
-/

namespace Set

/-- Text 14.0.5: the polar of a subset `C` is the support-function `1`-sublevel set. The owner is
kept at the pairing layer `Set X → Set Y`: only the primal set `C : Set X` and dual points
`xStar : Y` are primitive data. -/
def polar (α : Type w) [Preorder α] [SupSet α] [One α] [HasPairing Y X α]
    (C : Set X) : Set Y :=
  (δᵛ(· | C) : Y → WithTopBot α) ⁻¹' Set.Iic (1 : WithTopBot α)

scoped[Rockafellar] notation:max C "ᵒ[" 𝕜 "]" => (Set.polar 𝕜 C)

open scoped Rockafellar

end Set

end

section

variable {X : Type u} {Y : Type v}
variable {α : Type w}
variable [ConditionallyCompleteLattice α] [One α]
variable [HasPairing Y X α]

namespace Set

/-- Primitive support-function membership form of `Cᵒ[α]`: by definition,
`xStar ∈ Cᵒ[α]` iff `⟪xStar, x⟫ₚ ≤ 1` for every `x ∈ C`. -/
@[simp] theorem mem_polar_iff {C : Set X} {xStar : Y} :
    xStar ∈ Cᵒ[α] ↔ ∀ x ∈ C, (⟪xStar, x⟫ₚ : α) ≤ (1 : α) := by
  rw [polar]
  change
    (δᵛ(xStar | C) : WithTopBot α) ≤ (1 : WithTopBot α) ↔
      ∀ x ∈ C, (⟪xStar, x⟫ₚ : α) ≤ (1 : α)
  rw [supportFunction_def]
  constructor
  · intro hx x hxC
    have hxWithTopBot : (⟪xStar, x⟫ₚ : WithTopBot α) ≤ (1 : WithTopBot α) := by
      exact (le_iSup (fun z : C ↦ (⟪xStar, (z : X)⟫ₚ : WithTopBot α)) ⟨x, hxC⟩).trans hx
    have hxWithBot : ((⟪xStar, x⟫ₚ : α) : WithBot α) ≤ (1 : WithBot α) :=
      (WithTop.coe_le_coe).1 hxWithTopBot
    exact (WithBot.coe_le_coe).1 hxWithBot
  · intro hx
    refine iSup_le ?_
    intro x
    have hxWithBot : ((⟪xStar, (x : X)⟫ₚ : α) : WithBot α) ≤ (1 : WithBot α) :=
      (WithBot.coe_le_coe).2 (hx x x.2)
    exact (WithTop.coe_le_coe).2 hxWithBot

end Set

end

section

open scoped Rockafellar

variable {X : Type u} {Y : Type v} {α : Type w}
variable [ConditionallyCompleteLattice α] [One α]
variable [HasPairing Y X α] [HasPairing X Y α] [HasPairingSwap X Y α]

namespace Set

/-- Membership in `Cᵒ[α]` is equivalent to the pointwise inequality `⟪x, xStar⟫ ≤ 1` for every
`x ∈ C`, written in the swapped pairing orientation `(X, Y)`. -/
-- Proof sketch: first use the primitive pairing-orientation characterization
-- `mem_polar_iff`, then rewrite `⟪xStar, x⟫` as `⟪x, xStar⟫` via symmetry of the
-- bidirectional pairing (`HasPairingSwap`).
theorem mem_polar_iff_swap {C : Set X} {xStar : Y} :
    xStar ∈ Cᵒ[α] ↔ ∀ x ∈ C, (⟪x, xStar⟫ₚ : α) ≤ (1 : α) := by
  constructor
  · intro hx x hxC
    have hpair := (Set.mem_polar_iff (C := C) (xStar := xStar)).1 hx x hxC
    calc
      (⟪x, xStar⟫ₚ : α) = ⟪xStar, x⟫ₚ := HasPairingSwap.pairing_swap (x := x) (y := xStar)
      _ ≤ (1 : α) := hpair
  · intro hx
    refine (Set.mem_polar_iff (C := C) (xStar := xStar)).2 ?_
    intro x hxC
    have hsrc : (⟪x, xStar⟫ₚ : α) ≤ (1 : α) := hx x hxC
    calc
      (⟪xStar, x⟫ₚ : α) = ⟪x, xStar⟫ₚ := (HasPairingSwap.pairing_swap (x := x) (y := xStar)).symm
      _ ≤ (1 : α) := hsrc

end Set

end

section

open scoped Rockafellar

variable {E : Type u}
variable {Y : Type v}
variable {α : Type w}
variable [TopologicalSpace E]
variable [ConditionallyCompleteLattice α] [One α]
variable [TopologicalSpace α] [OrderClosedTopology α]
variable [HasPairing E Y α]
variable [HasContinuousPairing E Y α]

namespace Set

-- Use the canonical swapped pairing instance induced by the primal/dual pairing `HasPairing E Y α`.
local instance : HasPairing Y E α :=
  HasPairing.swap (X := E) (Y := Y) (L := α)

/-- Passing from `C` to `closure C` does not change its polar. -/
theorem polar_eq_of_closure_eq {C D : Set E} (hCD : closure C = closure D) :
    (Cᵒ[α] : Set Y) = Dᵒ[α] := by
  ext xStar
  have hsf :
      (δᵛ(xStar | C) : WithTopBot α) = (δᵛ(xStar | D) : WithTopBot α) := by
    exact congrArg (fun f : Y → WithTopBot α => f xStar)
      (supportFunction_eq_of_closure_eq (C := C) (D := D) hCD)
  simp [Set.polar, hsf]

/-- Passing from `C` to `closure C` does not change its polar. -/
@[simp] theorem polar_closure (C : Set E) :
    ((closure C)ᵒ[α] : Set Y) = Cᵒ[α] := by
  simpa using
    (polar_eq_of_closure_eq (C := C) (D := closure C) (by simp)).symm

end Set

end

/-! ### Text_14_0_6 (from Chap03) -/
noncomputable section

universe u v

open scoped Rockafellar
open Function

section

variable {𝕜 : Type*} {X : Type u} {Y : Type v}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasContinuousPairing X Y 𝕜]

local instance : HasPairing Y X 𝕜 := HasPairing.swap (X := X) (Y := Y)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.6 identifies the closure of the generated function of
  `δ[𝕜](· | C) + 1` for a nonempty convex set `C ⊆ X` with the support function
  `δᵛ[WithTopBot 𝕜](· | Cᵒ[𝕜])` of its polar subset `Cᵒ[𝕜] ⊆ Y`.
- `core/canonical`: the owner constructions in this domain are `sublinearHull`,
  `lowerSemicontinuousHull`, `supportFunction`, and `Set.polar`; the owner theorem driving the
  specialization is
  `lowerSemicontinuousHull_generatedBy_eq_supportFunction_nonpositiveSublevel_convexConjugate`.
- `bridge/view`: Text 5.4.11 provides the generated-function owner for `δ[𝕜](· | C) + 1`, and
  Text 14.0.5 identifies the corresponding nonpositive conjugate sublevel set with `Cᵒ[𝕜]`.

Domain-style sampling used here:
- `sublinearHull (δ[𝕜](· | C) + 1)` from `Text_5_4_11`;
- `lowerSemicontinuousHull` / the chapter notation `cl(·)` from `Text_7_0_4`;
- `Set.polar` / the chapter notation `Cᵒ[𝕜]` from `Text_14_0_5`;
- `lowerSemicontinuousHull_generatedBy_eq_supportFunction_nonpositiveSublevel_convexConjugate`
  from `Theorem_13_5`.

Primitive data vs derived API:
- primitive inputs: the set `C`, together with the source-essential hypotheses `Convex 𝕜 C` and
  `C.Nonempty`;
- derived output: the support-function description of the `WithTopBot 𝕜`-valued closure of the
  generated function of `δ[𝕜](· | C) + 1`, obtained by specializing the owner theorem from
  `Theorem_13_5` along `Text_5_4_11` and the chapter polar owner from `Text_14_0_5` (on the
  dual/primal swapped pairing orientation).

Ambient minimization: the theorem only uses the owner constructions above, so the public API lives
at the canonical ambient level of a finite-dimensional `𝕜`-module paired with a dual-side
`𝕜`-module by a continuous linear pairing, instead of a concrete real/self-dual model.

Layer target: `bridge/view`, stated directly in the chapter owners `cl(·)`, `δ[𝕜](· | ·)`,
`δᵛ[WithTopBot 𝕜](· | ·)`, and `Cᵒ[𝕜]`, without any local wrapper around the generated function or
polar constructions.
-/

-- Proof sketch: apply Text 5.4.11 to the source function `x ↦ δ(x | C) + 1`, whose generated
-- positively homogeneous convex function is the gauge-side owner used in the proof route. Then use
-- Theorem 13.5 for that generated function. Its conjugate is `δᵛ(· | C) - 1`, so the owner-side
-- nonpositive sublevel set is exactly `Cᵒ` by Text 14.0.5, yielding the support-function formula.
/-- Text 14.0.6: for a nonempty convex set in a finite-dimensional topological `𝕜`-module
carrying a continuous linear pairing to a dual-side module, the closure of the generated function
`sublinearHull (δ[𝕜](· | C) + 1)` is the support function
`δᵛ[WithTopBot 𝕜](· | Cᵒ[𝕜])` of its polar. -/
theorem lowerSemicontinuousHull_generatedBy_indicator_add_one_eq_supportFunction_polar
    (C : Set X) (hC_convex : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    cl(sublinearHull (δ[𝕜](· | C) + 1)) =
      (δᵛ(· | (Cᵒ[𝕜] : Set Y)) : X → WithTopBot 𝕜) := sorry

end

/-! ### Text_14_0_7 (from Chap03) -/
section

open scoped PolarCone

universe u v w

variable {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {M : Type u} [AddCommMonoid M] [Module 𝕜 M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N]
variable [HasLinearPairing M N 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.7 states that the polar cone `Kᵒ` from Text 14.0.1 is closed,
  convex, stable under nonnegative scalar multiplication, contains the origin, and hence is a cone
  in the chapter's set-level sense.
- `core/canonical`: the owner abstraction is `PointedCone.dual` at the primitive linear-pairing
  layer, used at the source-negated pairing map `-(HasLinearPairing.pairingLinear)`.
- `bridge/view`: `Kᵒ[𝕜]` is Rockafellar's nonpositive-sign-convention view of that owner. The
  public API should therefore expose only source-facing properties of `Kᵒ[𝕜]`, not a parallel local
  cone package.

Domain-style sampling used here:
- `polarCone` and `mem_polarCone_iff_pairing` from `Text_14_0_1`;
- `PointedCone.dual`;
- `PointedCone.convex`;
- `ConvexCone.isCone`;
- `PointedCone.smul_mem`.
- `Set.IsCone 𝕜`.

Primitive data vs derived API:
- primitive input: a subset `K : Set M`;
- primitive owner: `PointedCone.dual (-(HasLinearPairing.pairingLinear)) K`;
- derived source-facing API: convexity, membership of `0` in `Kᵒ[𝕜]`, the set-level cone predicate
  `Set.IsCone 𝕜 Kᵒ[𝕜]`, and nonnegative scalar stability of `Kᵒ[𝕜]`.

Layer target: `bridge/view`.
-/

/-- Text 14.0.7 (2): the polar cone of a set `K` is convex. This is a direct owner-side fact for
the dual cone and holds for arbitrary subsets. -/
theorem convex_polarCone (K : Set M) :
    Convex 𝕜 (↑(Kᵒ[𝕜] : PointedCone 𝕜 N) : Set N) := by
  simpa using PointedCone.convex (Kᵒ[𝕜] : PointedCone 𝕜 N)

/-- Text 14.0.7 (4): the polar cone `Kᵒ[𝕜]` contains the origin. -/
theorem zero_mem_polarCone (K : Set M) :
    (0 : N) ∈ Kᵒ[𝕜] := by
  simp

/-- Text 14.0.7, in the chapter's set-level cone vocabulary: the polar cone is a cone. -/
theorem isCone_polarCone (K : Set M) :
    Set.IsCone 𝕜 (↑(Kᵒ[𝕜] : PointedCone 𝕜 N) : Set N) := by
  simpa using ConvexCone.isCone ((Kᵒ[𝕜] : PointedCone 𝕜 N) : ConvexCone 𝕜 N)

/-- Text 14.0.7 (3): the polar cone is stable under nonnegative scalar multiplication. -/
theorem smul_mem_polarCone (K : Set M) {a : 𝕜} (ha : 0 ≤ a) {xStar : N}
    (hxStar : xStar ∈ Kᵒ[𝕜]) :
    a • xStar ∈ Kᵒ[𝕜] := by
  simpa using (Kᵒ[𝕜] : PointedCone 𝕜 N).smul_mem ha hxStar

end

section

open scoped Rockafellar PolarCone

universe u v w

variable {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [TopologicalSpace 𝕜] [ClosedIicTopology 𝕜]
  [IsOrderedRing 𝕜]
variable {M : Type u} [AddCommMonoid M] [Module 𝕜 M] [TopologicalSpace M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N]
variable [HasLinearPairing M N 𝕜]

/-!
Topology-layer note:
- the source-facing owner `K ↦ Kᵒ[𝕜]` has no extra carrier parameter on the source side, so its
  closure-invariance API is canonically ambient `closure`;
- intrinsic/relative closure formulations require additional carrier data and therefore belong to
  separate bridge theorems, not to this owner-level theorem.
-/

/-- Closure invariance for the chapter polar owner under continuity of left pairing evaluation, at
the canonical `PointedCone` owner layer. -/
@[simp] theorem polarCone_closure_of_continuous (K : Set M)
    (hcont : ∀ xStar : N, Continuous (fun x : M ↦ (⟪x, xStar⟫ₚ : 𝕜))) :
    ((closure K)ᵒ[𝕜] : PointedCone 𝕜 N) = (Kᵒ[𝕜] : PointedCone 𝕜 N) := by
  ext xStar
  constructor
  · intro hx
    refine (mem_polarCone_iff_pairing (K := K) (xStar := xStar)).2 ?_
    intro x hxK
    exact
      (mem_polarCone_iff_pairing (K := closure K) (xStar := xStar)).1 hx x
        (subset_closure hxK)
  · intro hx
    refine (mem_polarCone_iff_pairing (K := closure K) (xStar := xStar)).2 ?_
    have hsubset : K ⊆ {x : M | (⟪x, xStar⟫ₚ : 𝕜) ≤ 0} := by
      intro x hxK
      exact (mem_polarCone_iff_pairing (K := K) (xStar := xStar)).1 hx x hxK
    have hclosed : IsClosed {x : M | (⟪x, xStar⟫ₚ : 𝕜) ≤ 0} := by
      simpa using (isClosed_Iic.preimage (hcont xStar))
    intro x hxClosure
    exact closure_minimal hsubset hclosed hxClosure

/-- Set-level closure invariance corollary for the chapter polar owner under continuity of left
pairing evaluation. -/
@[simp] theorem polarCone_closure_eq_of_continuous (K : Set M)
    (hcont : ∀ xStar : N, Continuous (fun x : M ↦ (⟪x, xStar⟫ₚ : 𝕜))) :
    (↑((closure K)ᵒ[𝕜] : PointedCone 𝕜 N) : Set N) =
      (↑(Kᵒ[𝕜] : PointedCone 𝕜 N) : Set N) := by
  exact congrArg (fun P : PointedCone 𝕜 N ↦ (P : Set N))
    (polarCone_closure_of_continuous (K := K) hcont)

end

section

open scoped Rockafellar PolarCone

universe u v w

variable {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [TopologicalSpace 𝕜] [ClosedIicTopology 𝕜]
  [IsOrderedRing 𝕜]
variable {M : Type u} [AddCommMonoid M] [Module 𝕜 M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N] [TopologicalSpace N]
variable [HasLinearPairing M N 𝕜]

/-!
Topology-layer note:
- `isClosed_polarCone` is an owner-level closedness theorem for the ambient codomain topology on
  `N`;
- relative/intrinsic closedness statements for `Kᵒ[𝕜]` require an additional ambient subset in `N`,
  so they are downstream bridge results rather than the primitive source-facing API here.
-/

/-- Text 14.0.7 (1): the polar cone `Kᵒ[𝕜]` of a set `K` is closed at the pairing-continuity
layer. -/
theorem isClosed_polarCone (K : Set M)
    (hcont : ∀ x : M, Continuous (fun xStar : N ↦ (⟪x, xStar⟫ₚ : 𝕜))) :
    IsClosed (↑(Kᵒ[𝕜] : PointedCone 𝕜 N) : Set N) := by
  classical
  have hEq :
      (↑(Kᵒ[𝕜] : PointedCone 𝕜 N) : Set N) =
        ⋂ x : {x : M // x ∈ K}, {xStar : N | (⟪(x : M), xStar⟫ₚ : 𝕜) ≤ 0} := by
    ext xStar
    constructor
    · intro hx
      have hxall : ∀ x : {x : M // x ∈ K}, (⟪(x : M), xStar⟫ₚ : 𝕜) ≤ 0 := by
        intro x
        exact (mem_polarCone_iff_pairing (K := K) (xStar := xStar)).1 hx (x : M) x.2
      simpa [Set.mem_iInter] using hxall
    · intro hx
      have hxall : ∀ x : {x : M // x ∈ K}, (⟪(x : M), xStar⟫ₚ : 𝕜) ≤ 0 := by
        simpa [Set.mem_iInter] using hx
      exact (mem_polarCone_iff_pairing (K := K) (xStar := xStar)).2 <| by
        intro x hxK
        exact hxall ⟨x, hxK⟩
  rw [hEq]
  refine isClosed_iInter ?_
  intro x
  simpa using (isClosed_Iic.preimage (hcont (x : M)))

end

/-! ### Text_14_0_8 (from Chap03) -/
section

open scoped Rockafellar PolarCone

universe u v w

variable {𝕜 : Type w} [CommRing 𝕜] [TopologicalSpace 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
  [ClosedIicTopology 𝕜]
variable {M : Type u} [AddCommMonoid M] [Module 𝕜 M] [TopologicalSpace M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N]
variable [HasLinearPairing M N 𝕜] [HasContinuousPairing M N 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.8 states that taking the polar commutes with topological closure.
- `core/canonical`: the owner objects are `PointedCone.dual
  (-(HasLinearPairing.pairingLinear : M →ₗ[𝕜] Module.Dual 𝕜 N)) K` from Text 14.0.1 and the
  standard topological closure operator `closure`.
- `bridge/view`: the result is a direct equality between two source-visible set constructions, so
  no extra cone package or bridge wrapper is needed.

Domain-style sampling used here:
- `polarCone` and `mem_polarCone_iff_pairing` from `Text_14_0_1`;
- the standard closure operator `closure`;
- closed half-space preimages via `isClosed_Iic.preimage`.

Primitive data vs derived API:
- primitive input: a set `K : Set M`;
- primitive owner: `PointedCone.dual (-(HasLinearPairing.pairingLinear)) K`;
- derived source-facing content: the equality of the two polar sets obtained before and after
  closure.

Layer target: `bridge/view`.

Topology-layer note:
- the source owner here is `polarCone : Set M → PointedCone 𝕜 N`, with no distinguished ambient
  subset in
  its data;
- consequently, the canonical hull operation on the source side is ambient `closure`;
- intrinsic/relative closure statements require an extra carrier parameter and belong to a
  separate bridge theorem, not to this owner-level closure invariance API.

The source's nonempty and convex-cone hypotheses are redundant for this equality, since closure
invariance already holds for the owner dual cone of an arbitrary set.
-/

/-- Text 14.0.8 at the owner layer: taking the chapter polar commutes with closure. -/
@[simp] theorem polarCone_closure (K : Set M) :
    ((closure K)ᵒ[𝕜] : PointedCone 𝕜 N) = Kᵒ[𝕜] := by
  exact
    polarCone_closure_of_continuous (𝕜 := 𝕜) (M := M) (N := N) (K := K)
      (hcont := fun xStar : N =>
        HasContinuousPairing.continuous_pairing_left
          (X := M) (Y := N) (𝕜 := 𝕜) xStar)

end

/-! ### Text_14_0_9 (from Chap03) -/
section

open scoped PolarCone Rockafellar

universe u v w

variable {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {M : Type u} [AddCommGroup M] [Module 𝕜 M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N]
variable [HasLinearPairing M N 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.9 identifies the polar cone `Kᵒ` of a nonempty closed convex cone
  `K` with the normal cone to `K` at the origin, and then states the converse identification of
  `K` with the normal cone to `Kᵒ` at the origin.
- `core/canonical`: the owner abstractions already present in the project are the source-facing
  set-valued constructions `polarCone` and `normalCone`, together with the chapter owner predicate
  `Set.IsConvexCone ℝ K` for the converse bipolar clause.
- `bridge/view`: the theorem is already an equality between these two canonical source-level set
  constructions, with the chapter bipolar theorem `polarCone_polarCone_eq` providing the converse
  clause. No extra wrapper or packaged interface is mathematically justified.

Domain-style sampling used here:
- `polarCone` and `mem_polarCone_iff` from `Text_14_0_1`;
- `normalCone` and `mem_normalCone_iff` from `Definition_2_7_10`;
- `polarCone_polarCone_eq` from `Theorem_14_1` as the chapter bipolar owner behind the converse
  clause;
- the closure argument `IsClosed.closure_subset_iff` and the continuity owner
  `ContinuousWithinAt.mem_closure_image` used to recover `0 ∈ K` from nonemptiness, closedness,
  and the cone property.

Primitive data vs derived API:
- primitive input for the first clause: a set `K : Set M` together with the canonical datum
  `0 ∈ K`;
- textbook route to that primitive data: nonemptiness and closedness of the cone, used only to
  recover `0 ∈ K`;
- derived content: the two source-facing equalities identifying `Kᵒ` and `K` as normal cones at
  the origin.

Layer target: `source-facing`.

The public API is split into the two atomic source clauses and uses the chapter notation `Kᵒ`
directly on the theorem surface. The first clause is stated at the weakest canonical level
`0 ∈ K`; the textbook nonempty/closed-cone assumptions are kept only in a thin companion theorem
that derives this membership. The first clause therefore lives directly at the pairing owner layer
`[HasLinearPairing M N 𝕜]`, while the converse bipolar clause is isolated below in the stronger
real complete-inner-product setting forced by the currently available upstream theorem
`polarCone_polarCone_eq`.
-/

/-- Text 14.0.9 (1): if a cone `K` contains the origin, then its polar cone `Kᵒ` is the normal
cone to `K` at the origin. The textbook nonempty/closed-cone formulation is recovered by the
companion theorem `polarCone_eq_normalCone_at_zero_of_nonempty_closed_cone`. -/
-- Proof sketch: unfold `normalCone K 0`; once `0 ∈ K`, the defining inequalities reduce directly
-- to the polar inequalities from `polarCone`.
theorem polarCone_eq_normalCone_at_zero
    (K : Set M) (h0 : (0 : M) ∈ K) :
    (Kᵒ[𝕜] : Set N) = N[𝕜](0 | K) := by
  ext xStar
  rw [mem_polarCone_iff, mem_normalCone_iff]
  simp [h0]

end

section

open scoped PolarCone Rockafellar

universe u v

variable {M : Type u} [TopologicalSpace M] [AddCommGroup M] [Module ℝ M] [ContinuousSMul ℝ M]
variable {N : Type v} [AddCommMonoid N] [Module ℝ N]
variable [HasLinearPairing M N ℝ]

private theorem zero_mem_of_nonempty_closed_cone
    (K : Set M) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK_cone : Set.IsCone ℝ K) :
    (0 : M) ∈ K := by
  obtain ⟨x, hx⟩ := hK_nonempty
  let f : ℝ → M := fun t ↦ t • x
  have hfK : closure (f '' Set.Ioi (0 : ℝ)) ⊆ K :=
    hK_closed.closure_subset_iff.2 <| by
      rintro _ ⟨t, ht, rfl⟩
      exact hK_cone ht hx
  have hf_cont : ContinuousWithinAt f (Set.Ioi (0 : ℝ)) 0 := by
    fun_prop
  simpa [f] using hfK (hf_cont.mem_closure_image <| by simp)

/-- Text 14.0.9 (1), textbook hypothesis form: a nonempty closed cone contains the origin, so the
main origin-based normal-cone identification applies. -/
theorem polarCone_eq_normalCone_at_zero_of_nonempty_closed_cone
    (K : Set M) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK_cone : Set.IsCone ℝ K) :
    (Kᵒ[ℝ] : Set N) = N[ℝ](0 | K) := by
  exact polarCone_eq_normalCone_at_zero K
    (zero_mem_of_nonempty_closed_cone K hK_nonempty hK_closed hK_cone)

end

section

open scoped PolarCone Rockafellar

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Text 14.0.9 (2): for a nonempty closed convex cone `K ⊆ R^n`, the normal cone to `Kᵒ` at the
origin is `K`. -/
-- Proof sketch: rewrite `normalCone Kᵒ 0` as `Kᵒᵒ` using the first clause applied to `Kᵒ`, then
-- apply the bipolar theorem `polarCone_polarCone_eq`.
theorem normalCone_polarCone_at_zero_eq
    (K : Set E) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK : Set.IsConvexCone ℝ K) :
    N[ℝ]((0 : E) | Kᵒ[ℝ]) = K := by
  calc
    N[ℝ]((0 : E) | Kᵒ[ℝ]) = ((Kᵒ[ℝ] : Set E)ᵒ[ℝ] : Set E) := by
      symm
      exact polarCone_eq_normalCone_at_zero (K := (Kᵒ[ℝ] : Set E))
        (zero_mem_polarCone K)
    _ = K := polarCone_polarCone_eq K hK_nonempty hK_closed hK

end

/-! ### Text_14_0_10 (from Chap03) -/
section

open scoped Pointwise PolarCone Rockafellar

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]

local notation "E" => ι → 𝕜

/-!
Source/core/bridge triage:

- `source-facing`: Text 14.0.10 identifies the polar cone of the nonnegative orthant.
- `core/canonical`: the chapter owner surface is `K∗[𝕜]` (i.e., `sourceDualCone`) together with
  `orthant[𝕜](E)`; the raw owner `PointedCone.dual (HasLinearPairing.pairingLinear)` is retained
  as a bridge theorem.
- `bridge/view`: `polarCone` from Text 14.0.1 is the chapter sign-convention bridge over
  `PointedCone.dual`.
- `bridge/view`: the source-facing polar identity is the sign-convention bridge
  `orthant[𝕜](E)ᵒ[𝕜] = -orthant[𝕜](E)`.
- `scalar/ambient-strength decision`: the owner-level duality statements below only use the
  semiring layer required by `PointedCone.dual`; the source-facing polar statement is isolated in
  a downstream ring section because `Kᵒ[𝕜]` uses the sign-twisted dual owner.

Domain-style sampling used here:
- `sourceDualCone`, `mem_sourceDualCone_iff_pairing_nonneg`, and `sourceDualCone_eq_dual`;
- `orthant[𝕜](E)` and `mem_orthant_iff`;
- `dotProduct` and `single_one_dotProduct`.

Primitive data vs derived API:
- primitive owner data: `sourceDualCone` and `orthant[𝕜](E)`;
- source-facing bridge data: `polarCone` and pointwise negation;
- derived API: the owner-level orthant self-duality (plus its `PointedCone.dual` bridge form) and
  the source-facing equality identifying the source polar orthant with the negative orthant.

Layer target: `source-facing`.
-/

-- Proof sketch: the owner dual cone consists of vectors whose pairing evaluation with every vector
-- in the ambient positive cone is nonnegative. Testing this against the standard basis vectors
-- forces each coordinate to be nonnegative, while the converse follows because a sum of products of
-- nonnegative coordinates is nonnegative.
/-- At the source owner layer, the nonnegative orthant in `𝕜^ι` is self-dual for `K∗[𝕜]`. -/
@[simp] theorem sourceDualCone_nonnegativeOrthant_eq_nonnegativeOrthant :
    ((((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) : Set E) = orthant[𝕜](E)) := by
  classical
  ext x
  change x ∈ ((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) ↔ x ∈ orthant[𝕜](E)
  rw [mem_sourceDualCone_iff_pairing_nonneg, mem_orthant_iff]
  change
    (∀ y : E, y ∈ orthant[𝕜](E) → 0 ≤ y ⬝ᵥ x) ↔ ∀ i : ι, 0 ≤ x i
  constructor
  · intro hx i
    have hi : Pi.single i (1 : 𝕜) ∈ orthant[𝕜](E) := by
      change 0 ≤ (Pi.single i (1 : 𝕜) : E)
      intro j
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    have hdot : 0 ≤ (Pi.single i (1 : 𝕜) ⬝ᵥ x) := hx _ hi
    simpa [single_one_dotProduct] using hdot
  · intro hx y hy
    have hy' : ∀ i : ι, 0 ≤ y i := by
      change 0 ≤ y at hy
      exact hy
    simpa [dotProduct] using
      Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hy' i) (hx i))

/-- At the canonical owner layer, the dual cone of the ambient positive cone in `𝕜^ι` is
itself. -/
@[simp] theorem PointedCone.dual_nonnegativeOrthant_eq_nonnegativeOrthant :
    (PointedCone.dual
      (HasLinearPairing.pairingLinear : E →ₗ[𝕜] Module.Dual 𝕜 E)
      (orthant[𝕜](E)) : Set E) = orthant[𝕜](E) := by
  simpa [sourceDualCone_eq_dual] using
    (sourceDualCone_nonnegativeOrthant_eq_nonnegativeOrthant (ι := ι) (𝕜 := 𝕜))

end

section

open scoped Pointwise PolarCone Rockafellar

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]

local notation "E" => ι → 𝕜

/- The source-facing polar cone of the nonnegative orthant is the nonpositive orthant. This is the
sign-convention corollary of the owner-level self-duality of the orthant. -/
/-- Text 14.0.10 at the source-facing layer: the polar cone of the nonnegative orthant is its
pointwise negative. -/
@[simp] theorem polarCone_nonnegativeOrthant_eq_neg :
    {x : E | x ∈ (orthant[𝕜](E))ᵒ[𝕜]} = -orthant[𝕜](E) := by
  ext x
  change x ∈ (orthant[𝕜](E))ᵒ[𝕜] ↔ x ∈ -orthant[𝕜](E)
  constructor
  · intro hx
    have hxStar : -x ∈ ((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) := by
      exact (mem_sourceDualCone_iff_neg_mem_polarCone (K := orthant[𝕜](E)) (xStar := -x)).2 <| by
        simpa using hx
    have hstar_eq :
        (((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) : Set E) = orthant[𝕜](E) :=
      sourceDualCone_nonnegativeOrthant_eq_nonnegativeOrthant (ι := ι) (𝕜 := 𝕜)
    have hxStar' : -x ∈ orthant[𝕜](E) := by
      have hmem :
          (-x ∈ (((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) : Set E)) =
            (-x ∈ orthant[𝕜](E)) :=
        congrArg (fun S : Set E => -x ∈ S) hstar_eq
      exact hmem ▸ hxStar
    simpa using hxStar'
  · intro hx
    have hxStar : -x ∈ orthant[𝕜](E) := by simpa using hx
    have hstar_eq :
        (((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) : Set E) = orthant[𝕜](E) :=
      sourceDualCone_nonnegativeOrthant_eq_nonnegativeOrthant (ι := ι) (𝕜 := 𝕜)
    have hxStar' : -x ∈ ((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) := by
      have hmem :
          (-x ∈ (((orthant[𝕜](E))∗[𝕜] : PointedCone 𝕜 E) : Set E)) =
            (-x ∈ orthant[𝕜](E)) :=
        congrArg (fun S : Set E => -x ∈ S) hstar_eq
      exact hmem.symm ▸ hxStar
    have hxPolar :
        -(-x) ∈ (orthant[𝕜](E))ᵒ[𝕜] :=
      (mem_sourceDualCone_iff_neg_mem_polarCone (K := orthant[𝕜](E)) (xStar := -x)).1 <| by
        simpa using hxStar'
    simpa using hxPolar

end

/-! ### Text_14_0_11 (from Chap03) -/
section

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.11 says that polarity reverses inclusion for convex sets.
- `core/canonical`: the owner abstraction already present in the project is the source-facing set
  polar `Set.polar`, and the canonical order-theoretic formulation of the source sentence is the
  predicate `Antitone`.
- `bridge/view`: the textbook conclusion `C1ᵒ ⊇ C2ᵒ` is rendered canonically by the owner-side
  statement that `Set.polar` is antitone.

Domain-style sampling used here:
- `Set.polar` from `Text_14_0_5`;
- `Set.mem_polar_iff` from `Text_14_0_5`;
- the standard order-theoretic predicate `Antitone`.

Primitive data vs derived API:
- primitive owner: the map `Set.polar : Set E → Set E`;
- derived source-facing consequence: the reverse inclusion between the polars of comparable sets.

The source's closedness, convexity, and origin-membership hypotheses are redundant for this order
reversal, and the owner `Set.polar` already lives on arbitrary real inner-product spaces. The Lean
statement is therefore given at that ambient owner level instead of the display model `ℝ^n`.

Layer target: `core/canonical`.
-/

namespace Set

-- Proof sketch: if `xStar ∈ polar C2`, then `mem_polar_iff` gives
-- `⟪x, xStar⟫ ≤ 1` for every `x ∈ C2`. Along an inclusion `C1 ⊆ C2`, the same inequalities hold
-- for every `x ∈ C1`, so `xStar ∈ polar C1`. This is exactly the statement that `polar`
-- is antitone.
local notation "polar" => (Set.polar (α := ℝ) : Set E → Set E)

/-- Text 14.0.11: polarity is order-inverting. Equivalently, the source-facing polar map is
antitone. The source states this for closed convex sets containing the origin, but those
hypotheses are unnecessary for the inclusion itself. -/
theorem polar_antitone : Antitone polar := by
  intro C1 C2 hC xStar hxStar
  rw [mem_polar_iff] at hxStar ⊢
  exact fun x hx ↦ hxStar x (hC hx)

end Set

end

/-! ### Text_14_0_12 (from Chap03) -/
noncomputable section

open scoped BigOperators RealInnerProductSpace Rockafellar

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.12 defines the set `C₁` in `ℝ^n` by coordinatewise nonnegativity and
  the inequality `ξ₁ + ⋯ + ξ_n ≤ 1`, then identifies its polar.
- `core/canonical`: the project owner abstractions are `Set.polar` for polars of subsets of `ℝ^n`
  and `((ConvexCone.positive ℝ (EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n))))` for coordinatewise nonnegativity.
- `bridge/view`: the source-facing set is the intersection of `((ConvexCone.positive ℝ (EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n))))` with the
  affine half-space `∑ i, x i ≤ 1`; the companion lemma `mem_unitSimplexSet_iff` expands this back
  to the textbook coordinatewise description.

Domain-style sampling used here:
- `Set.polar` and `Set.mem_polar_iff` from Text 14.0.5;
- `((ConvexCone.positive ℝ (EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n))))` and `mem_nonnegativeOrthant_iff` from Definition 2.5.11;
- `stdSimplex` from Text 5.5.0.3 as the nearby exact-mass simplex owner, not reused here
  because the source set allows total mass at most `1`.

Primitive data vs derived API:
- primitive datum: the subset `unitSimplexSet n`, built from the owner `((ConvexCone.positive ℝ (EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n))))` and
  the half-space `∑ i, x i ≤ 1`;
- derived API: the coordinatewise membership expansion `mem_unitSimplexSet_iff` and the explicit
  coordinatewise description of `(unitSimplexSet n)ᵒ`.

Layer target: `source-facing`.
-/

/-- The example set `C₁` of points in `ℝ^n` with nonnegative coordinates whose coordinate sum is
at most `1`. -/
def unitSimplexSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  ((ConvexCone.positive ℝ (EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)))) ∩ {x : EuclideanSpace ℝ (Fin n) | ∑ i, x i ≤ 1}

/-- Membership in `unitSimplexSet n` is the textbook conjunction of coordinatewise nonnegativity
and the bound `∑ i, x i ≤ 1`. -/
theorem mem_unitSimplexSet_iff {x : E} :
    x ∈ unitSimplexSet n ↔ (∀ i : Fin n, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 := by
  rw [unitSimplexSet, Set.mem_inter_iff, mem_nonnegativeOrthant_iff, Set.mem_setOf_eq]
  constructor
  · intro hx
    exact ⟨fun i ↦ hx.1 i, hx.2⟩
  · intro hx
    exact ⟨fun i ↦ hx.1 i, hx.2⟩

-- Proof sketch: rewrite membership in `(unitSimplexSet n)ᵒ` using
-- `Set.mem_polar_iff_swap`.
-- Evaluating the defining inequality on the standard basis vectors yields `xStar i ≤ 1` for every
-- coordinate. Conversely, if every coordinate of `xStar` is at most `1`, then for any
-- `x ∈ unitSimplexSet n` one has `⟪x, xStar⟫ = ∑ i, x i * xStar i ≤ ∑ i, x i ≤ 1` by
-- `mem_unitSimplexSet_iff`.
/-- Text 14.0.12: if `C₁ = {x ∈ ℝ^n | 0 ≤ x i` for all `i` and `∑ i, x i ≤ 1}`, then
`C₁ᵒ = {xStar ∈ ℝ^n | xStar i ≤ 1` for all `i`}. -/
theorem polar_unitSimplexSet_eq_coordinatewise_le_one :
    (unitSimplexSet n)ᵒ[ℝ] = {xStar : E | ∀ i : Fin n, xStar i ≤ 1} := by
  ext xStar
  rw [Set.mem_setOf_eq, Set.mem_polar_iff_swap]
  constructor
  · intro hx i
    have hsingle : EuclideanSpace.single i (1 : ℝ) ∈ unitSimplexSet n := by
      rw [mem_unitSimplexSet_iff]
      constructor
      · intro j
        by_cases h : j = i
        · subst h
          simp [EuclideanSpace.single]
        · simp [EuclideanSpace.single, h]
      · simp [EuclideanSpace.single]
    have hinner := hx (EuclideanSpace.single i (1 : ℝ)) hsingle
    rw [show (⟪EuclideanSpace.single i (1 : ℝ), xStar⟫ₚ : ℝ) = xStar i by
      simpa [innerₗ_apply_apply] using EuclideanSpace.inner_single_left i (1 : ℝ) xStar] at hinner
    simpa using hinner
  · intro hcoord x hx
    rcases mem_unitSimplexSet_iff.mp hx with ⟨hx_nonneg, hx_sum⟩
    calc
      (⟪x, xStar⟫ₚ : ℝ) = ∑ i, xStar i * x i := by
        change inner ℝ x xStar = ∑ i, xStar i * x i
        simp [PiLp.inner_apply, real_inner_eq_re_inner]
      _ ≤ ∑ i, 1 * x i := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        exact mul_le_mul_of_nonneg_right (hcoord i) (hx_nonneg i)
      _ = ∑ i, x i := by simp
      _ ≤ 1 := hx_sum

end
