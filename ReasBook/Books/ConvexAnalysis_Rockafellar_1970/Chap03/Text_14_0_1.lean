import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing

-- Declarations for this item will be appended below by the statement pipeline.

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
