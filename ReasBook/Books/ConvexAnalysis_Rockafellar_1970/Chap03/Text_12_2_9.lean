import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u w

section

open LinearMap.BilinMap
open scoped Rockafellar

variable {𝕜 : Type w} [Field 𝕜] [Preorder 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [HasLinearPairing E E 𝕜]
variable [SupSet (WithTopBot 𝕜)]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.2.9 exhibits the Euclidean quadratic
  `x ↦ (1 / 2) ⟪x, x⟫` as a Fenchel-conjugation fixed point, specialized in the source to `R^n`.
- `core/canonical`: the owner constructions already present in the chapter are
  `convexConjugate`, its postfix notation `f⋆`, the canonical quadratic-form owner
  `LinearMap.halfPairingQuadratic`, and the quadratic conjugacy theorem
  `LinearMap.convexConjugate_halfPairingQuadratic_eq_if_mem_range_of_isRangePseudoinverse`.
- `bridge/view`: the textbook quadratic `x ↦ (1 / 2) ⟪x, x⟫` is the source-facing realization of
  the identity-endomorphism quadratic owner on inner-product spaces and is connected to that
  owner by the bridge `id_halfPairingQuadratic_eq_half_inner_self`; no public wrapper is
  introduced.

Domain-style sampling used here:
- `LinearMap.halfPairingQuadratic`;
- `LinearMap.convexConjugate_halfPairingQuadratic_eq_if_mem_range_of_isRangePseudoinverse`;
- `LinearMap.IsRangePseudoinverse`;
- `convexConjugate` with notation `f⋆`.

Primitive data vs derived API:
- primitive owner-side quadratic datum:
  `LinearMap.halfPairingQuadratic (LinearMap.id : E →ₗ[𝕜] E)`;
- primitive positivity side condition: `∀ x : E, 0 ≤ (⟪x, x⟫ₚ : 𝕜)`;
- derived bridge API: on real inner-product spaces, identify the owner with
  `x ↦ (1 / 2) ⟪x, x⟫`.

Layer target: owner-first canonicalization. The primary declarations are stated on the
pairing-level owner `halfPairingQuadratic` at scalar-generic layer `𝕜`; the textbook Euclidean
quadratic appears only as a downstream bridge specialization.
-/

local notation "halfPairingId" =>
  LinearMap.halfPairingQuadratic (LinearMap.id : E →ₗ[𝕜] E)

/-- The identity-endomorphism quadratic owner from `Text_12_3_2`, viewed in `WithTopBot 𝕜`,
is fixed by Fenchel conjugation. -/
theorem convexConjugate_id_halfPairingQuadratic :
    (hpair_nonneg : ∀ x : E, 0 ≤ (⟪x, x⟫ₚ : 𝕜)) →
    halfPairingId⋆ = halfPairingId := by
  intro hpair_nonneg
  have hnonneg : ∀ x : E, 0 ≤ (⟪x, (LinearMap.id : E →ₗ[𝕜] E) x⟫ₚ : 𝕜) := by
    simpa using hpair_nonneg
  have hIdRangePinv :
      (LinearMap.id : E →ₗ[𝕜] E).IsRangePseudoinverse (LinearMap.id : E →ₗ[𝕜] E) :=
    LinearMap.id_isRangePseudoinverse
  simpa using
    (LinearMap.convexConjugate_halfPairingQuadratic_eq_of_isRangePseudoinverse_of_range_eq_top
      (T := (LinearMap.id : E →ₗ[𝕜] E))
      (T' := (LinearMap.id : E →ₗ[𝕜] E))
      hnonneg
      hIdRangePinv
      (by simp))

/-- Any function definitionally equal to the identity-endomorphism pairing quadratic owner is
Fenchel-self-conjugate. -/
theorem convexConjugate_eq_self_of_eq_id_halfPairingQuadratic
    (hpair_nonneg : ∀ x : E, 0 ≤ (⟪x, x⟫ₚ : 𝕜))
    {f : E → WithTopBot 𝕜}
    (hf : f = halfPairingId) :
    f⋆ = f := by
  simpa [hf] using convexConjugate_id_halfPairingQuadratic (hpair_nonneg := hpair_nonneg)

end

section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "halfPairingId" =>
  LinearMap.halfPairingQuadratic (LinearMap.id : E →ₗ[ℝ] E)
local notation "halfInnerSelf" =>
  Function.toWithTopBot (fun x : E ↦ ((1 / 2 : ℝ) * ⟪x, x⟫ : ℝ))

/-- The identity-endomorphism pairing-quadratic owner from `Text_12_3_2`, in real inner-product
spaces, is exactly the textbook quadratic `x ↦ (1 / 2) ⟪x, x⟫`. -/
@[simp] theorem id_halfPairingQuadratic_eq_half_inner_self :
    halfPairingId = halfInnerSelf := sorry

/-- The textbook quadratic `x ↦ (1 / 2) ⟪x, x⟫`, viewed in `WithTopBot ℝ`, is fixed by Fenchel
conjugation. -/
theorem convexConjugate_half_inner_self :
    halfInnerSelf⋆ = halfInnerSelf := by
  have hpair_nonneg : ∀ x : E, 0 ≤ (⟪x, x⟫ₚ : ℝ) := by
    intro x
    change 0 ≤ inner ℝ x x
    exact real_inner_self_nonneg
  have hfixed : halfPairingId⋆ = halfPairingId :=
    convexConjugate_id_halfPairingQuadratic (E := E) (hpair_nonneg := hpair_nonneg)
  calc
    halfInnerSelf⋆ = halfPairingId⋆ := by rw [← id_halfPairingQuadratic_eq_half_inner_self]
    _ = halfPairingId := hfixed
    _ = halfInnerSelf := id_halfPairingQuadratic_eq_half_inner_self

/-- Any function definitionally equal to the textbook quadratic owner is Fenchel-self-conjugate.
-/
theorem convexConjugate_eq_self_of_eq_half_inner_self
    {f : E → WithTopBot ℝ}
    (hf : f = halfInnerSelf) :
    f⋆ = f := by
  simpa [hf] using convexConjugate_half_inner_self

end
