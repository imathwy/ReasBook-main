import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_15
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_33
import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_34

noncomputable section

open scoped Rockafellar

universe u v u' v' z

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Lemma33.0.35 computes the primal and dual optimal values for the convex and
  concave programs attached to Rockafellar's translated pairing perturbation
  `H(v, y) = F (u + v) y - ⟪y, xStar⟫ₚ`.
- `core/canonical`: the chapter owners already present are `optimalValue`,
  `upperPerturbationFunction`, `adjoint`, `translatedSubPairing`, and the pairing
  notations `⟪·, ·⟫ᶠ` and `⟪·, ·⟫ᶜ`.
- `bridge/view`: this item is therefore formalized as two theorem-level value identities on those
  existing owners, without introducing a separate `(Q)` / `(Q*)` package.

Primary mathematical domain:
- convex duality for perturbation bifunctions and their adjoints.

Domain-style sampling used here:
- the owner `translatedSubPairing F u xStar` from `Definition33_0_33`;
- `Bifunction.optimalValue` from `Definition_6_29_15`;
- `Bifunction.upperPerturbationFunction` and `Bifunction.adjoint` from Chapter 6;
- `concaveConjugate_eq_iInf_pairing_sub` from `Chap06.Definition_6_30_4`, applied to the
  adjoint slice under the canonical swapped pairing `HasPairing.swap`;
- `Bifunction.adjoint_translatedSubPairing` from `Lemma33_0_34`.

Primitive data vs derived API:
- primitive source data: a bifunction `F`, a primal point `u`, and a dual point `xStar`;
- primitive translated kernel: `translatedSubPairing F u xStar`;
- derived API added here: the primal and dual optimal-value identities at the owner level.

Layer target: `source-facing`, expressed directly through the established pairing-based chapter
owners.
-/

section PrimalCore

variable {U : Type u} {X : Type v} {XStar : Type v'} {L : Type z}
variable [AddZeroClass U] [InfSet L] [HSub L L L]
variable [HasPairing X XStar L]

-- Proof sketch: unfold `optimalValue` on the zero slice of `translatedSubPairing F u xStar`.
/-- Lemma33.0.35 (1, owner form): the primal optimal value for the translated perturbation is the
direct infimum formula `inf_y (F u y - ⟪y, xStar⟫ₚ)`. -/
theorem optimalValue_translatedSubPairing_eq_iInf_sub_pairing
    (F : U → X → L) (u : U) (xStar : XStar) :
    optimalValue H[F | u, xStar] = ⨅ y : X, F u y - ⟪y, xStar⟫ₚ := by
  simpa [translatedSubPairing, add_zero] using
    (optimalValue_eq_iInf H[F | u, xStar])

end PrimalCore

section Primal

variable {α : Type z} {U : Type u} {X : Type v} {XStar : Type v'}
variable [AddZeroClass U]
variable [AddCommGroup α] [ConditionallyCompleteLattice α]
variable [IsOrderedAddMonoid α]
variable [HasPairing X XStar α]

-- Proof sketch: combine the owner-level infimum identity with
-- `convexConjugate_eq_neg_iInf_sub_pairing`.
/-- Lemma33.0.35 (1): the optimal value of the convex program associated with
Rockafellar's translated pairing perturbation `H(v, y) = F (u + v) y - ⟪y, xStar⟫ₚ` is the
negative of the convex pairing `⟪F u, xStar⟫ᶠ`; equivalently, it is
`inf_y (F u y - ⟪y, xStar⟫ₚ)`. -/
theorem optimalValue_translatedSubPairing_eq_neg_convex_slice_pairing
    (F : U → X → WithTopBot α) (u : U) (xStar : XStar) :
    optimalValue H[F | u, xStar] = -⟪F u, xStar⟫ᶠ := by
  rw [optimalValue_translatedSubPairing_eq_iInf_sub_pairing]
  rw [convexConjugate_eq_neg_iInf_sub_pairing (F u) xStar]
  simp

end Primal

section Dual

variable {𝕜 : Type z} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [CommRing 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup UStar] [Module 𝕜 UStar]
variable [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasLinearPairing X XStar 𝕜]

/-- The reversed pairing lets the adjoint slice `F⋆ xStar` be paired with a primal
point `u` using the chapter's concave-conjugate notation. -/
local instance instHasPairingSwapAdjointSlice : HasPairing UStar U 𝕜 := HasPairing.swap

variable (F : U → X → WithTopBot 𝕜) (u : U) (xStar : XStar)

local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithTopBot 𝕜)
local notation "H⋆" => (adjoint XStar UStar H[F | u, xStar] : XStar → UStar → WithTopBot 𝕜)

-- Proof sketch: unfold the upper perturbation owner and rewrite the translated adjoint slice at
-- `yStar = 0` with `adjoint_translatedSubPairing_apply`.
/-- Lemma33.0.35 (2, owner form): the dual optimal value for the translated perturbation is the
direct supremum formula `sup_{vStar} (F⋆ xStar vStar - ⟪u, vStar⟫ₚ)`. -/
theorem upperPerturbationFunction_adjoint_translatedSubPairing_zero_eq_iSup_sub_pairing
    :
    supᵇ(H⋆) (0 : XStar) =
      ⨆ uStar : UStar, F⋆ xStar uStar - ⟪u, uStar⟫ₚ := by
  rw [upperPerturbationFunction_apply]
  refine iSup_congr fun uStar ↦ ?_
  change ((H[F | u, xStar])⋆ : XStar → UStar → WithTopBot 𝕜) (0 : XStar) uStar =
      ((F⋆ : XStar → UStar → WithTopBot 𝕜) xStar uStar - ⟪u, uStar⟫ₚ)
  rw [adjoint_translatedSubPairing_apply (F := F) (u := u) (xStar := xStar)
    (yStar := (0 : XStar)) (vStar := uStar)]
  rw [add_zero]

variable [IsOrderedAddMonoid 𝕜]

-- Proof sketch: evaluate the dual optimal value as the supremum of the zero slice of the adjoint
-- of `translatedSubPairing F u xStar`, then compare the resulting supremum with the
-- canonical infimum formula for `⟪u, F⋆ xStar⟫ᶜ`.
/-- Lemma33.0.35 (2): the optimal value of the dual concave program associated with
Rockafellar's translated pairing perturbation `H(v, y) = F (u + v) y - ⟪y, xStar⟫ₚ` is the
negative of the concave pairing `⟪u, F^* xStar⟫ᶜ`; equivalently, it is
`sup_{vStar} (F⋆ xStar vStar - ⟪u, vStar⟫ₚ)`. -/
theorem upperPerturbationFunction_adjoint_translatedSubPairing_zero_eq_neg_adjoint_slice_pairing
    :
    supᵇ(H⋆) (0 : XStar) =
      -⟪u, F⋆ xStar⟫ᶜ := by
  rw [upperPerturbationFunction_adjoint_translatedSubPairing_zero_eq_iSup_sub_pairing]
  rw [concaveConjugate_eq_iInf_pairing_sub (F⋆ xStar) u]
  calc
    (⨆ uStar : UStar, F⋆ xStar uStar - ⟪u, uStar⟫ₚ) =
        -(⨅ uStar : UStar, ⟪u, uStar⟫ₚ - F⋆ xStar uStar) := by
      symm
      calc
        -(⨅ uStar : UStar, ⟪u, uStar⟫ₚ - F⋆ xStar uStar) =
            ⨆ uStar : UStar, -((⟪u, uStar⟫ₚ : 𝕜) - F⋆ xStar uStar) := by
          exact
            congrArg OrderDual.ofDual
              (WithBotTop.negOrderIso.map_iInf
                fun uStar ↦ ((⟪u, uStar⟫ₚ : 𝕜) : WithTopBot 𝕜) - F⋆ xStar uStar)
        _ = ⨆ uStar : UStar, F⋆ xStar uStar - ⟪u, uStar⟫ₚ := by
          refine iSup_congr fun uStar ↦ ?_
          let a : WithTopBot 𝕜 := (⟪u, uStar⟫ₚ : 𝕜)
          have htop : a ≠ ⊤ := WithBotTop.coe_ne_top (⟪u, uStar⟫ₚ : 𝕜)
          have hbot : a ≠ ⊥ := WithBotTop.coe_ne_bot (⟪u, uStar⟫ₚ : 𝕜)
          change -(a - F⋆ xStar uStar) = F⋆ xStar uStar - a
          rw [WithBotTop.neg_sub (Or.inl hbot) (Or.inl htop)]
          simp [add_comm]

end Dual

end Bifunction
