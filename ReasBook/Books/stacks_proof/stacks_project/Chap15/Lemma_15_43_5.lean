import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_119_7
import stacks_proof.stacks_project.Chap15.Lemma_15_43_1
import stacks_proof.stacks_project.Chap15.Lemma_15_43_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/- Domain-style sampling:
* primary domain: local commutative algebra of discrete valuation rings, regular local rings, and
  maximal-ideal adic completion;
* sampled owner declarations:
  `IsDiscreteValuationRing`,
  `discreteValuationRing_tfae`,
  `discreteValuationRing_iff_regularLocalRing_dim_one`,
  `isRegularLocalRing_iff_isRegularLocalRing_maximalIdeal_adicCompletion`,
  `ringKrullDim_eq_ringKrullDim_maximalIdeal_adicCompletion`;
* owner abstraction: the canonical owner `IsDiscreteValuationRing`, used on arbitrary commutative
  rings through the source-facing existential bridge
  `∃ (_ : IsDomain A), IsDiscreteValuationRing A`;
* primitive data: the Noetherian local ring `A`;
* derived API: the regular-local and dimension-one bridge
  `discreteValuationRing_iff_regularLocalRing_dim_one`, plus preservation of regularity
  and Krull dimension under maximal-ideal completion.

Source/core/bridge triage:
* source-facing: the textbook equivalence between `A` being a DVR and its maximal-ideal completion
  being a DVR;
* core/canonical: the owner predicate `IsDiscreteValuationRing`;
* bridge/view: the regular-local-dimension-one bridge
  `discreteValuationRing_iff_regularLocalRing_dim_one` together with the completion
  comparison theorems for regularity and Krull dimension.
-/
local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

-- Proof sketch: use Lemma `10.119.7` to characterize discrete valuation rings among Noetherian
-- local rings as the one-dimensional regular local rings. Then apply Lemma `15.43.4` for the
-- regular-local condition and Lemma `15.43.1` for preservation of Krull dimension under maximal-
-- ideal adic completion.
/-- Lemma 15.43.5: a Noetherian local ring `A` is a discrete valuation ring if and only if its
maximal-ideal adic completion is a discrete valuation ring. -/
@[stacks 0AP1]
theorem isDiscreteValuationRing_iff_isDiscreteValuationRing_maximalIdeal_adicCompletion :
    (∃ (_ : IsDomain A), IsDiscreteValuationRing A) ↔
      ∃ (_ : IsDomain ACompletion), IsDiscreteValuationRing ACompletion := by
  calc
    (∃ (_ : IsDomain A), IsDiscreteValuationRing A) ↔
        IsRegularLocalRing A ∧ ringKrullDim A = 1 :=
      discreteValuationRing_iff_regularLocalRing_dim_one
    _ ↔ IsRegularLocalRing ACompletion ∧ ringKrullDim A = 1 := by
      exact and_congr
        (isRegularLocalRing_iff_isRegularLocalRing_maximalIdeal_adicCompletion A) Iff.rfl
    _ ↔ IsRegularLocalRing ACompletion ∧ ringKrullDim ACompletion = 1 := by
      simp [ringKrullDim_eq_ringKrullDim_maximalIdeal_adicCompletion A]
    _ ↔ ∃ (_ : IsDomain ACompletion), IsDiscreteValuationRing ACompletion :=
      discreteValuationRing_iff_regularLocalRing_dim_one.symm

end
