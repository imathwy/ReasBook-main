import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_6_29_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4

noncomputable section

open scoped Rockafellar

universe u v w z

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type z} {α : Type w}
variable [ConditionallyCompleteLattice α] [Add α] [Zero U]
variable [HasPairing U UStar α]

local notation "shiftedInf(" F ", " uStar ")" =>
  (⨅ u : U, perturbationFunction F u + ⟪u, uStar⟫ₚ)

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.19 introduces the notion of a Kuhn--Tucker vector `u⋆` for the
  generalized convex program attached to a bifunction `F`.
- `core/canonical`: the existing Chapter 6 owners are `Bifunction.perturbationFunction` from
  Definition 6.29.1 and `Bifunction.optimalValue` from Definition 6.29.15; under the stronger
  additive hypotheses needed for conjugation, the shifted infimum is the canonical concave
  conjugate owner `concaveConjugate (- perturbationFunction F)`.
- `bridge/view`: at the present weak codomain generality the source displayed infimum identity is
  kept as the primitive owner-side formulation, while the pointwise inequality
  `optimalValue F ≤ perturbationFunction F u + ⟪u, u⋆⟫ₚ` is the equivalent
  supporting-hyperplane reformulation and a later companion theorem bridges the infimum to the
  concave-conjugate owner once negation/subtraction are available.

Domain-style sampling used here:
- `Bifunction.perturbationFunction`;
- `Bifunction.perturbationFunction_apply`;
- `Bifunction.optimalValue`;
- `Bifunction.isConsistent_iff_optimalValue_lt_top`;
- `concaveConjugate` and `concaveConjugate_eq_iInf_pairing_sub`.

Primitive data vs derived API:
- primitive source data: the bifunction `F` and the dual vector `u⋆`;
- primitive owner in this file: `Bifunction.IsKuhnTuckerVector F uStar`, defined by the finiteness
  and equality statement for the infimum over perturbations;
- derived API: the pointwise lower-bound condition and consistency of the generalized convex
  program.

Layer target: `source-facing`. This item introduces a genuine new property of dual vectors for a
generalized convex program, so it is exposed directly on the existing bifunction owner rather than
through a witness package or a restated infimum wrapper.
-/

/-- Definition 6.29.19: a dual vector `u⋆` is a Kuhn--Tucker vector for the generalized convex
program attached to `F` when the infimum of the shifted perturbation values
`perturbationFunction F u + ⟪u, u⋆⟫ₚ` is finite and equals the unperturbed optimal value
`optimalValue F`. The source-facing primitive data are the two-sided finiteness of this shifted
infimum together with the equality, while primal consistency is derived API through
`optimalValue F < ⊤`. -/
class IsKuhnTuckerVector (F : U → X → WithBotTop α) (uStar : UStar) : Prop where
  infimum_mem_Ioo : shiftedInf(F, uStar) ∈ Set.Ioo (⊥ : WithBotTop α) ⊤
  infimum_eq_optimalValue : shiftedInf(F, uStar) = optimalValue F

/-- The Kuhn--Tucker vector set of the generalized convex program attached to `F`. -/
def kuhnTuckerVectorSet (F : U → X → WithBotTop α) : Set UStar :=
  {uStar | IsKuhnTuckerVector F uStar}

scoped[Rockafellar] notation "KT(" F ")" => (Bifunction.kuhnTuckerVectorSet F)

/-- Membership in `KT(F)` is exactly the Kuhn--Tucker-vector predicate. -/
@[simp] theorem mem_kuhnTuckerVectorSet
    {F : U → X → WithBotTop α} {uStar : UStar} :
    uStar ∈ KT(F) ↔ IsKuhnTuckerVector F uStar :=
  Iff.rfl

namespace IsKuhnTuckerVector

variable {F : U → X → WithBotTop α} {uStar : UStar}

/-- Lower finiteness bound from the defining interval-membership field. -/
theorem infimum_bot_lt (h : IsKuhnTuckerVector F uStar) :
    ⊥ < shiftedInf(F, uStar) :=
  h.infimum_mem_Ioo.1

/-- Upper finiteness bound from the defining interval-membership field. -/
theorem infimum_lt_top (h : IsKuhnTuckerVector F uStar) :
    shiftedInf(F, uStar) < ⊤ :=
  h.infimum_mem_Ioo.2

-- Proof sketch: unpack the defining interval-membership field `infimum_mem_Ioo`.
/-- A Kuhn--Tucker vector makes the defining shifted perturbation infimum finite. -/
theorem infimum_finite (h : IsKuhnTuckerVector F uStar) :
    ⊥ < shiftedInf(F, uStar) ∧ shiftedInf(F, uStar) < ⊤ :=
    ⟨h.infimum_bot_lt, h.infimum_lt_top⟩

-- Proof sketch: take the symmetric form of the defining equality
-- `h.infimum_eq_optimalValue`.
/-- A Kuhn--Tucker vector rewrites the optimal value as the defining shifted perturbation
infimum. -/
theorem optimalValue_eq_infimum (h : IsKuhnTuckerVector F uStar) :
    optimalValue F = shiftedInf(F, uStar) :=
    h.infimum_eq_optimalValue.symm

-- Proof sketch: rewrite `optimalValue F` using `h.optimalValue_eq_infimum`, then apply the upper
-- finiteness part of the defining data.
/-- A Kuhn--Tucker vector forces the primal optimal value to lie strictly below `⊤`. -/
theorem optimalValue_lt_top (h : IsKuhnTuckerVector F uStar) :
    optimalValue F < ⊤ :=
    by
      rw [← h.infimum_eq_optimalValue]
      exact h.infimum_lt_top

-- Proof sketch: combine `isConsistent_iff_optimalValue_lt_top` with
-- `IsKuhnTuckerVector.optimalValue_lt_top`.
/-- A Kuhn--Tucker vector forces consistency of the generalized convex program. -/
theorem consistent (h : IsKuhnTuckerVector F uStar) :
    IsConsistent F :=
    (isConsistent_iff_optimalValue_lt_top F).2 h.optimalValue_lt_top

-- Proof sketch: rewrite the defining infimum as `optimalValue F` using
-- `infimum_eq_optimalValue`; then transfer the lower bound from `infimum_bot_lt` and the upper
-- bound from `optimalValue_lt_top`.
/-- A Kuhn--Tucker vector forces the primal optimal value to be finite. -/
theorem optimalValue_finite (h : IsKuhnTuckerVector F uStar) :
    ⊥ < optimalValue F ∧ optimalValue F < ⊤ :=
    by
      refine ⟨?_, h.optimalValue_lt_top⟩
      rw [← h.infimum_eq_optimalValue]
      exact h.infimum_bot_lt

-- Proof sketch: rewrite `optimalValue F` using `h.infimum_eq_optimalValue`. The indexed infimum
-- is below each perturbed value `perturbationFunction F u + ⟪u, uStar⟫ₚ`, yielding the source's
-- equivalent lower-bound inequality.
/-- A Kuhn--Tucker vector satisfies the supporting-hyperplane inequality
`optimalValue F ≤ perturbationFunction F u + ⟪u, u⋆⟫ₚ` for every perturbation `u`. -/
theorem optimalValue_le_perturbationFunction_add_pairing
    (h : IsKuhnTuckerVector F uStar) (u : U) :
    optimalValue F ≤ perturbationFunction F u + ⟪u, uStar⟫ₚ :=
    by
      rw [h.optimalValue_eq_infimum]
      exact iInf_le _ u

end IsKuhnTuckerVector

end

section

variable {U : Type u} {X : Type v} {UStar : Type z} {α : Type w}
variable [ConditionallyCompleteLattice α] [AddCommSemigroup α] [InvolutiveNeg α]
variable [HasPairing U UStar α]

local notation "shiftedInf(" F ", " uStar ")" =>
  (⨅ u : U, perturbationFunction F u + ⟪u, uStar⟫ₚ)

/-- Under commutative addition and involutive negation on `α`, the shifted perturbation infimum
from Definition 6.29.19 is exactly the Chapter 6 concave-conjugate owner
`(- perturbationFunction F)∗`. -/
theorem shiftedInf_eq_concaveConjugate_neg_perturbationFunction
    (F : U → X → WithBotTop α) (uStar : UStar) :
    shiftedInf(F, uStar) = (- perturbationFunction F)∗ uStar := by
  rw [concaveConjugate_eq_iInf_pairing_sub]
  congr with u
  rw [WithBotTop.sub_eq_add_neg]
  calc
    perturbationFunction F u + ⟪u, uStar⟫ₚ
      = -(- perturbationFunction F u) + ⟪u, uStar⟫ₚ := by simp
    _ = ⟪u, uStar⟫ₚ + -(- perturbationFunction F u) := by rw [add_comm]

namespace IsKuhnTuckerVector

variable [Zero U]
variable {F : U → X → WithBotTop α} {uStar : UStar}

/-- Under commutative addition and involutive negation on `α`, a Kuhn--Tucker vector identifies
the canonical concave-conjugate owner `(- perturbationFunction F)∗` at `u⋆` with the primal
optimal value. -/
theorem concaveConjugate_neg_perturbationFunction_eq_optimalValue
    (h : IsKuhnTuckerVector F uStar) :
    (- perturbationFunction F)∗ uStar = optimalValue F := by
  rw [← shiftedInf_eq_concaveConjugate_neg_perturbationFunction, h.infimum_eq_optimalValue]

end IsKuhnTuckerVector

end

end Bifunction
