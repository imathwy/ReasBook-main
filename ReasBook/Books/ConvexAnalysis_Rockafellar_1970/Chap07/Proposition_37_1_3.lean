import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_37_1_1

noncomputable section

universe u u' v w z

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {UStar : Type u'} {X : Type v} {XStar : Type w} {α : Type z}
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [Zero UStar] [Zero X]
variable [HasPairing U UStar (WithTopBot α)] [HasPairing X XStar (WithTopBot α)]
variable [HasPairingZeroRight U UStar (WithTopBot α)]
variable [HasPairingZeroLeft X XStar (WithTopBot α)]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 37.1.3 identifies the ambient minimax and maximin values of a
  saddle kernel `K` with the negatives of the lower and upper conjugates at the base point
  `(0, 0)`.
- `core/canonical`: the owner layer already present in the project is
  `Bifunction.minimaxValue`, `Bifunction.maximinValue`, `Bifunction.lowerConjugate`, and
  `Bifunction.upperConjugate`.
- `bridge/view`: evaluating the Chapter 37 conjugates at `(0, 0)` is exactly the source formula
  once the canonical zero-pairing owners are available, because the affine perturbation in
  Definition 37.1.1 then reduces to `-K` at that base point, and the chapter's canonical codomain
  owner `WithTopBot.negOrderIso` transports the resulting `iSup`/`iInf` values across negation.

Primary mathematical domain:
- conjugate saddle-functions and minimax values.

Domain-style sampling used here:
- `Bifunction.lowerConjugate` from `Definition_37_1_1`;
- `Bifunction.upperConjugate` from `Definition_37_1_1`;
- `Bifunction.maximinValue` from `Definition_36_0_1`;
- `Bifunction.minimaxValue` from `Definition_36_0_1`;
- `WithTopBot.negOrderIso` from `Chap01.EOrder.Operations`.

Primitive data vs derived API:
- primitive data: the saddle kernel `K` and the two zero-pairing owners
  `HasPairingZeroRight U UStar (WithTopBot α)` / `HasPairingZeroLeft X XStar (WithTopBot α)`;
- primitive owner objects reused here: the ambient maximin/minimax values and the lower/upper
  conjugates of `K`;
- derived API: the two zero-basepoint value identities recorded by Proposition 37.1.3.

Layer target: `source-facing`, stated directly on the existing Chapter 36 and Chapter 37 owners
on the chapter's canonical ordered-extended codomain layer `WithTopBot α`, rather than through a
new saddle-value wrapper.
-/

private theorem neg_iSup_eq_iInf_neg {ι : Sort*} (f : ι → WithTopBot α) :
    -(⨆ i, f i) = ⨅ i, -f i := by
  exact congrArg OrderDual.ofDual (WithTopBot.negOrderIso.map_iSup f)

private theorem neg_iInf_eq_iSup_neg {ι : Sort*} (f : ι → WithTopBot α) :
    -(⨅ i, f i) = ⨆ i, -f i := by
  exact congrArg OrderDual.ofDual (WithTopBot.negOrderIso.map_iInf f)

omit [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α] in
private theorem neg_zeroBase_perturbation
    (K : U → XStar → WithTopBot α) (u : U) (xStar : XStar) :
    -((⟪u, (0 : UStar)⟫ₚ + ⟪(0 : X), xStar⟫ₚ) - K u xStar) = K u xStar := by
  calc
    -((⟪u, (0 : UStar)⟫ₚ + ⟪(0 : X), xStar⟫ₚ) - K u xStar)
        = -((0 : WithTopBot α) - K u xStar) := by
            simp [pairing_zero_right, pairing_zero_left]
    _ = -(0 : WithTopBot α) + K u xStar := by
          exact
            WithBotTop.neg_sub
              (Or.inl WithBotTop.zero_ne_bot) (Or.inl WithBotTop.zero_ne_top)
    _ = K u xStar := by simp

local notation:max K " _*₀" => K _*((0 : UStar), (0 : X))
local notation:max K " ^*₀" => K ^*((0 : UStar), (0 : X))

/-- Proposition 37.1.3 (1): the whole-space minimax value of `K` is the negative of its lower
conjugate at the base point `(0, 0)`. -/
theorem minimaxValue_eq_neg_lowerConjugate_zero_zero
    (K : U → XStar → WithTopBot α) :
    minimaxValue K = -(K _*₀) := by
  calc
    minimaxValue K = ⨅ xStar : XStar, ⨆ u : U, K u xStar := by
      simp [minimaxValue, minimaxValueOn]
    _ = ⨅ xStar : XStar,
          -(⨅ u : U, ((⟪u, (0 : UStar)⟫ₚ + ⟪(0 : X), xStar⟫ₚ) - K u xStar)) := by
          refine iInf_congr fun xStar ↦ ?_
          rw [neg_iInf_eq_iSup_neg]
          refine iSup_congr fun u ↦ ?_
          exact (neg_zeroBase_perturbation K u xStar).symm
    _ = -(⨆ xStar : XStar, ⨅ u : U,
          ((⟪u, (0 : UStar)⟫ₚ + ⟪(0 : X), xStar⟫ₚ) - K u xStar)) := by
          symm
          exact neg_iSup_eq_iInf_neg _
    _ = -(K _*₀) := by
          simp [lowerConjugate_apply]

/-- Proposition 37.1.3 (2): the whole-space maximin value of `K` is the negative of its upper
conjugate at the base point `(0, 0)`. -/
theorem maximinValue_eq_neg_upperConjugate_zero_zero
    (K : U → XStar → WithTopBot α) :
    maximinValue K = -(K ^*₀) := by
  calc
    maximinValue K = ⨆ u : U, ⨅ xStar : XStar, K u xStar := by
      simp [maximinValue, maximinValueOn]
    _ = ⨆ u : U,
          -(⨆ xStar : XStar, ((⟪u, (0 : UStar)⟫ₚ + ⟪(0 : X), xStar⟫ₚ) - K u xStar)) := by
          refine iSup_congr fun u ↦ ?_
          rw [neg_iSup_eq_iInf_neg]
          refine iInf_congr fun xStar ↦ ?_
          exact (neg_zeroBase_perturbation K u xStar).symm
    _ = -(⨅ u : U, ⨆ xStar : XStar,
          ((⟪u, (0 : UStar)⟫ₚ + ⟪(0 : X), xStar⟫ₚ) - K u xStar)) := by
          symm
          exact neg_iInf_eq_iSup_neg _
    _ = -(K ^*₀) := by
          simp [upperConjugate_apply]

end

end Bifunction
