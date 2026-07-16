import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_3

noncomputable section

open scoped Rockafellar

universe u v w

section

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

local instance : HasPairing X Y (WithTopBot 𝕜) := instHasPairingWithTopBot

omit [ConditionallyCompleteLattice 𝕜] in
@[simp] private theorem pairing_withTopBot_eq_coe (x : X) (y : Y) :
    (⟪x, y⟫ₚ : WithTopBot 𝕜) = ((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜) := rfl

omit [ConditionallyCompleteLattice 𝕜] in
@[simp] private theorem pairing_neg_left (x : X) (y : Y) :
    (⟪-x, y⟫ₚ : 𝕜) = -⟪x, y⟫ₚ := by
  simp [HasLinearPairing.pairing_eq_pairingLinear]

omit [ConditionallyCompleteLattice 𝕜] in
@[simp] private theorem pairing_neg_right (x : X) (y : Y) :
    (⟪x, -y⟫ₚ : 𝕜) = -⟪x, y⟫ₚ := by
  simp [HasLinearPairing.pairing_eq_pairingLinear]

/-!
Source/core/bridge triage:

- `source-facing`: Remark 31.4.3 introduces the translated-tilted function
  `x ↦ h (z + x) - ⟪x, z⋆⟫` and records the explicit formula for its Fenchel conjugate.
- `core/canonical`: the owner abstraction is the chapter affine-change theorem
  `convexConjugate_affineChange`, built on the pairing owner
  `HasLinearPairing`.
- `bridge/view`: this file keeps only the single source-facing combined formula as a specialization
  of that owner, without adding a second translated-duality wrapper. The later finite-valued
  duality specialization is delegated to the downstream corollary item.

Domain-style sampling used here:

- `convexConjugate`;
- `convexConjugate_eq_iSup_pairing_sub`;
- `convexConjugate_affineChange`;
- `convexConjugate_sub_pairing_const`.

Primitive data vs derived API:

- primitive inputs: the canonical `WithTopBot 𝕜`-valued function `h`, the primal translation
  vector `z`, and the dual shift vector `zStar`;
- owner-side primitive data already upstream: the affine-change conjugate owner and the linear
  pairing structure;
- derived API: the single explicit conjugate formula for the translated-tilted function. The
  pairing additivity used in the specialization is now derived from `HasLinearPairing`, not stored
  as primitive public data.

Layer target: `bridge/view`.
-/

-- Proof sketch: specialize the chapter affine-change owner with both bijections equal to
-- the identity, translation parameter `a = -z`, dual affine term `aStar = -zStar`, and zero
-- constant term. The pairing-side additivity and negation identities are discharged canonically
-- from `HasLinearPairing`.
/-- Remark 31.4.3: for the translated-tilted function `x ↦ h (z + x) - ⟪x, zStar⟫ₚ`, the
Fenchel conjugate is `xStar ↦ h⋆ (zStar + xStar) - ⟪z, xStar⟫ₚ - ⟪z, zStar⟫ₚ`. This is the
function-theoretic bridge used by the later finite-valued duality specialization. -/
theorem convexConjugate_translate_sub_pairing
    (h : X → WithTopBot 𝕜) (z : X) (zStar : Y) :
    (fun x : X ↦ h (z + x) - ⟪x, zStar⟫ₚ)⋆ =
      fun xStar : Y ↦ h⋆ (zStar + xStar) - ⟪z, xStar⟫ₚ - ⟪z, zStar⟫ₚ := by
  simpa [HasLinearPairing.pairing_eq_pairingLinear, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using
    (convexConjugate_affineChange h (Equiv.refl X)
      (Equiv.refl Y) (fun x xStar ↦ rfl) (-z) (-zStar) (0 : WithTopBot 𝕜))

end
