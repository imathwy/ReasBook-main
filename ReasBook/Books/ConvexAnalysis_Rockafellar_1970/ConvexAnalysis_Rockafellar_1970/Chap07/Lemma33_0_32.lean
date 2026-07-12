import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_8

noncomputable section

universe u v u' v' w

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Lemma33.0.32 records the primal identity
  `(inf F)(u) = -⟪F u, 0⟫ᶠ`, the dual identity `(sup F⋆)(x⋆) = -⟪0, F⋆ x⋆⟫ᶜ`, and the
  resulting equivalence between zero-point optimal-value equality and zero-point pairing equality.
- `core/canonical`: the chapter owners already in place are `perturbationFunction`,
  `upperPerturbationFunction`, `adjoint`, and the pairing notations `⟪·, ·⟫ᶠ` and `⟪·, ·⟫ᶜ`.
- `bridge/view`: this file keeps the source-facing equalities on those owners, rather than
  replacing them by a packaged wrapper.

Domain-style sampling inspected before drafting:
- `Bifunction.perturbationFunction` and `perturbationFunction_apply` from
  `Chap06.Definition_6_29_1`;
- `Bifunction.upperPerturbationFunction` and `upperPerturbationFunction_apply` from
  `Chap06.Definition_6_30_11`;
- `Bifunction.adjoint` from `Chap06.Definition_6_30_14`;
- the Chapter 33 pairing notations `⟪·, ·⟫ᶠ` and `⟪·, ·⟫ᶜ` from `Definition33_0_8`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → WithTopBot 𝕜`;
- reused chapter owners: `perturbationFunction F`, `upperPerturbationFunction F⋆`, and the two
  pairing evaluations at zero;
- derived API here: the two zero-pairing value identities and the final equivalence at `(0, 0)`.

Layer target: `source-facing`, stated directly in the textbook zero-pairing form.
-/

section ZeroPointEquality

section Primal

variable {𝕜 : Type w} {U : Type u} {X : Type v} {XStar : Type v'}
variable [AddCommGroup 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedAddMonoid 𝕜]
variable [HasPairing X XStar 𝕜] [Zero XStar] [HasPairingZeroRight X XStar 𝕜]
variable (F : U → X → WithTopBot 𝕜)

-- Proof sketch: unfold `perturbationFunction F u` as the indexed infimum of the slice `F u`,
-- rewrite the convex pairing `⟪F u, 0⟫ᶠ` by `convexConjugate_eq_neg_iInf_sub_pairing`, and then
-- use `pairing_zero_right` to remove the zero pairing term.
/-- The primal perturbation value at `u` is the negative of the convex pairing of the slice `F u`
with the zero dual parameter. -/
theorem perturbationFunction_eq_neg_convexPairing_zero
    (u : U) :
    infᵇ(F) u = -⟪F u, (0 : XStar)⟫ᶠ := sorry

end Primal

section Dual

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [AddCommGroup 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedAddMonoid 𝕜]
variable [Neg UStar] [HasPairing U UStar 𝕜] [Zero U] [HasPairingZeroLeft U UStar 𝕜]
variable [HasPairing (U × X) (UStar × XStar) 𝕜]
variable (F : U → X → WithTopBot 𝕜)

/-- The reversed pairing used to read the adjoint slice `F⋆ x⋆` by the concave pairing notation.
-/
local instance : HasPairing UStar U 𝕜 := HasPairing.swap

local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithTopBot 𝕜)

-- Proof sketch: unfold `upperPerturbationFunction F⋆ x⋆` as the indexed supremum of the adjoint
-- slice, rewrite `⟪0, F⋆ x⋆⟫ᶜ` by `concaveConjugate_eq_iInf_pairing_sub`, and then use
-- `pairing_zero_left` together with the order-dual identity `sup(-g) = - inf g`.
/-- The dual upper perturbation value at `x⋆` is the negative of the concave pairing of the
adjoint slice `F⋆ x⋆` with the zero primal parameter. -/
theorem upperPerturbationFunction_adjoint_eq_neg_concavePairing_zero
    (xStar : XStar) :
    supᵇ(F⋆) xStar = -⟪(0 : U), F⋆ xStar⟫ᶜ := sorry

end Dual

section Equivalence

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [AddCommGroup 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedAddMonoid 𝕜]
variable [Neg UStar] [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]
variable [Zero U] [Zero XStar]
variable [HasPairingZeroLeft U UStar 𝕜] [HasPairingZeroRight X XStar 𝕜]
variable [HasPairing (U × X) (UStar × XStar) 𝕜]
variable (F : U → X → WithTopBot 𝕜)

/-- The reversed pairing used to read the adjoint slice `F⋆ x⋆` by the concave pairing notation.
-/
local instance : HasPairing UStar U 𝕜 := HasPairing.swap

local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithTopBot 𝕜)

-- Proof sketch: specialize the primal and dual identities above to `u = 0` and `x⋆ = 0`, then
-- cancel the common outer minus signs to turn the zero-point value equality into the zero-point
-- pairing equality.
/-- Lemma33.0.32: the primal and dual optimal values at `0` agree exactly when the corresponding
zero-point pairing values agree. -/
theorem perturbationFunction_zero_eq_upperPerturbationFunction_adjoint_zero_iff_zero_pairing_eq
    infᵇ(F) 0 = supᵇ(F⋆) 0 ↔
      ⟪F 0, (0 : XStar)⟫ᶠ = ⟪(0 : U), F⋆ 0⟫ᶜ := sorry

end Equivalence

end ZeroPointEquality

end Bifunction
