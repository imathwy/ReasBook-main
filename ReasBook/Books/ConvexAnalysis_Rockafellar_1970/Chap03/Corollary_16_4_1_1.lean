import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Pointwise Rockafellar

section

variable {𝕜 : Type*} [AddCommGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsOrderedAddMonoid 𝕜] [DenselyOrdered 𝕜]
variable {ι X Y : Type*}
variable [AddCommMonoid Y]
variable [HasPairing X Y 𝕜] [HasPairingAddRight X Y 𝕜]

@[simp] private theorem pairing_zero_right_finset
    {𝕜 X Y : Type*} [AddCommGroup 𝕜] [AddCommMonoid Y]
    [HasPairing X Y 𝕜] [HasPairingAddRight X Y 𝕜] (xStar : X) :
    (⟪xStar, (0 : Y)⟫ₚ : 𝕜) = 0 := by
  have h0 : (⟪xStar, (0 : Y)⟫ₚ : 𝕜) =
      (⟪xStar, (0 : Y)⟫ₚ : 𝕜) + (⟪xStar, (0 : Y)⟫ₚ : 𝕜) := by
    simpa using
      (HasPairingAddRight.pairing_add_right
        (X := X) (Y := Y) (𝕜 := 𝕜) xStar (0 : Y) (0 : Y))
  have h0' : (⟪xStar, (0 : Y)⟫ₚ : 𝕜) + 0 =
      (⟪xStar, (0 : Y)⟫ₚ : 𝕜) + (⟪xStar, (0 : Y)⟫ₚ : 𝕜) := by
    simpa using h0
  have hcancel : (0 : 𝕜) = (⟪xStar, (0 : Y)⟫ₚ : 𝕜) := add_left_cancel h0'
  simpa using hcancel.symm

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.4.1.1 states that the support function of the Minkowski sum
  `C₁ + ··· + C_m` is the sum of the individual support functions.
- `core/canonical`: the owner abstractions are the project support function `supportFunction` on
  subsets of a pairing space and the finite pointwise set sum over a finite family.
- `bridge/view`: Rockafellar's notation `δ^*(· | C)` is rendered by `supportFunction C`.

Domain-style sampling used here:
- `supportFunction` from `Defintion_4_8_2`;
- `supportFunction_eq_iSup`, confirming that the owner already lives on arbitrary pairing spaces
  rather than only on the concrete inner-product model;
- the binary owner theorem `supportFunction_set_add` from `Text_13_1_3`;
- the canonical finite-sum recursion `Finset.sum_insert`.

Primitive data vs derived API:
- primitive inputs: a finite family of sets `C : ι → Set Y`;
- derived API: the support-function identity for the finite pointwise sum, with the reusable
  finite-aggregation owner theorem on `Finset` and the source-facing `δᵛ` theorem surface as its
  pointwise companion.

Layer target: `source-facing`, stated directly in the canonical support-function language already
used across the project.

Semantic note: the displayed support-function identity is already meaningful in the project's
canonical API for an arbitrary finite family of subsets of a pairing-space codomain, so the
textbook's convexity and nonemptiness hypotheses are omitted from the Lean statement.
-/

/-- The support function of a finite Minkowski sum is the sum of the individual support
functions. This is the canonical finite-aggregation owner theorem behind Corollary 16.4.1.1. -/
theorem supportFunction_finset_sum
    (s : Finset ι) (C : ι → Set Y) :
    (supportFunction (∑ i ∈ s, C i) : X → WithTopBot 𝕜) =
      ∑ i ∈ s, (supportFunction (C i) : X → WithTopBot 𝕜) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext xStar
      change (δᵛ(xStar | ({0} : Set Y)) : WithTopBot 𝕜) = 0
      rw [supportFunction_singleton]
      change (((⟪xStar, (0 : Y)⟫ₚ : 𝕜) : WithTopBot 𝕜) = 0)
      simp
  | @insert i s hi hs =>
      have hadd :
          (supportFunction (C i + ∑ x ∈ s, C x) : X → WithTopBot 𝕜) =
            (supportFunction (C i) : X → WithTopBot 𝕜) +
              (supportFunction (∑ x ∈ s, C x) : X → WithTopBot 𝕜) := by
        simpa using
          (supportFunction_set_add
            (C1 := C i) (C2 := (∑ x ∈ s, C x)))
      rw [Finset.sum_insert hi, hadd, hs, Finset.sum_insert hi]

/-- Pointwise form of `supportFunction_finset_sum`, written in Rockafellar's support-function
notation `δᵛ`. -/
theorem supportFunction_finset_sum_apply
    (s : Finset ι) (C : ι → Set Y) (xStar : X) :
    (δᵛ(xStar | ∑ i ∈ s, C i) : WithTopBot 𝕜) = ∑ i ∈ s, δᵛ(xStar | C i) := by
  simpa using congrFun (supportFunction_finset_sum s C) xStar

-- Proof sketch: specialize the public `Finset` aggregation theorem
-- `supportFunction_finset_sum` to the full finite family `Finset.univ`.
/-- Corollary 16.4.1.1: for a finite family `C`, the support value of the Minkowski sum `∑ i, C i`
is the sum of the individual support values. -/
theorem supportFunction_sum_eq_sum_supportFunction
    [Fintype ι] (C : ι → Set Y) (xStar : X) :
    (δᵛ(xStar | ∑ i, C i) : WithTopBot 𝕜) = ∑ i, δᵛ(xStar | C i) := by
  classical
  simpa using supportFunction_finset_sum_apply Finset.univ C xStar

end
