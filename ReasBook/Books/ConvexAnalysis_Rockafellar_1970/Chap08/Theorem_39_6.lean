import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_14
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_39_0_7

noncomputable section

open scoped Rockafellar SetRel

universe u v u' v' w

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 39.6 states that positive scalar multiplication of an oriented convex
  process commutes with passage to the adjoint process: `(λ A)^* = λ A^*`.
- `core/canonical`: this item now uses the existing Chapter 39 owners directly:
  the process-scaling notation `(λ : 𝕜) •ʳ A`, defined as `A ○ (λ • ·).graph`, and
  `A∗[XStar, UStar; 𝕜]` for the process adjoint.
- `bridge/view`: this item is a direct compatibility statement between those two owners, so no
  local wrapper owner is introduced.

Primary mathematical domain:
- convex processes and adjoint duality under positive rescaling.

Domain-style sampling used here:
- the source-facing process-scaling notation `a •ʳ A` from `Proposition_39_0_7`;
- process-adjoint notation `A∗[XStar, UStar; 𝕜]` from `Definition_39_0_14`;
- pairing owners `HasPairing`/`HasLinearPairing` from `Chap01.HasPairing`.

Primitive data vs derived API:
- primitive owners reused directly: a relation `A : SetRel U X`, a positive scalar `lam`,
  the process-scaling owner/notation `lam •ʳ A`, and `A∗[XStar, UStar; 𝕜]`;
- derived API: the process-level commutation identity between positive scaling and adjunction.

Layer target: `bridge/view`.
-/

section

variable {𝕜 : Type w} [Semifield 𝕜] [PartialOrder 𝕜] [PosMulMono 𝕜] [PosMulReflectLT 𝕜]
variable {U : Type u} [AddCommMonoid U] [Module 𝕜 U]
variable {X : Type v} [AddCommMonoid X] [Module 𝕜 X]
variable {UStar : Type u'} [AddCommMonoid UStar] [Module 𝕜 UStar]
variable {XStar : Type v'} [AddCommMonoid XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasLinearPairing X XStar 𝕜]

-- Proof sketch: unfold both relation owners. Membership in
-- `(lam •ʳ A)∗[XStar, UStar; 𝕜]` says
-- the defining pairing inequality holds for every point `(u, λ • y)` with `(u, y) ∈ A`; after
-- rewriting the pairing by bilinearity and using positivity of `λ`, this is equivalent to the
-- defining inequality for membership in `lam •ʳ (A∗[XStar, UStar; 𝕜])`.
/-- Theorem 39.6: for every positive scalar `λ`, the adjoint
of the scaled process `λ A` is the same scalar multiple of the adjoint process, rendered on the
canonical relation owners as `(λ A)^* = λ A^*`. -/
theorem adjoint_rightScalarMul
    (A : SetRel U X) {lam : 𝕜} (hlam : 0 < lam) :
    (lam •ʳ A)∗[XStar, UStar; 𝕜] =
      lam •ʳ (A∗[XStar, UStar; 𝕜]) := by
  ext p
  rcases p with ⟨xStar, uStar⟩
  rw [mem_adjoint_iff, mem_rightScalarMul_iff]
  constructor
  · intro huStar
    have hlam0 : lam ≠ 0 := ne_of_gt hlam
    refine ⟨lam⁻¹ • uStar, ?_, by simp [hlam0]⟩
    rw [mem_adjoint_iff]
    intro u x hux
    have hscaled : u ~[lam •ʳ A] (lam • x) :=
      mem_rightScalarMul_iff.mpr ⟨x, hux, rfl⟩
    have huStar_scaled := huStar hscaled
    have huStar_scaled' :=
      mul_le_mul_of_nonneg_left huStar_scaled (inv_nonneg.mpr hlam.le)
    have hpairing_left :
        (⟪(lam • x), xStar⟫ₚ : 𝕜) = lam * ⟪x, xStar⟫ₚ := by
      simp [HasLinearPairing.pairing_eq_pairingLinear]
    have hpairing_right :
        (⟪u, (lam⁻¹ • uStar)⟫ₚ : 𝕜) = lam⁻¹ * ⟪u, uStar⟫ₚ := by
      simp [HasLinearPairing.pairing_eq_pairingLinear]
    calc
      (⟪x, xStar⟫ₚ : 𝕜) = lam⁻¹ * (lam * ⟪x, xStar⟫ₚ) := by
        rw [← mul_assoc, inv_mul_cancel₀ hlam0, one_mul]
      _ = lam⁻¹ * ⟪(lam • x), xStar⟫ₚ := by rw [hpairing_left]
      _ ≤ lam⁻¹ * ⟪u, uStar⟫ₚ := huStar_scaled'
      _ = ⟪u, (lam⁻¹ • uStar)⟫ₚ := by rw [hpairing_right]
  · rintro ⟨uStar', huStar', rfl⟩
    intro u x hux
    rcases (mem_rightScalarMul_iff.mp hux) with ⟨y, hy, rfl⟩
    have hy' := huStar' hy
    have hy'' := mul_le_mul_of_nonneg_left hy' hlam.le
    calc
      (⟪(lam • y), xStar⟫ₚ : 𝕜) = lam * ⟪y, xStar⟫ₚ := by
        simp [HasLinearPairing.pairing_eq_pairingLinear]
      _ ≤ lam * ⟪u, uStar'⟫ₚ := hy''
      _ = ⟪u, lam • uStar'⟫ₚ := by
        simp [HasLinearPairing.pairing_eq_pairingLinear]

end

end SetRel
