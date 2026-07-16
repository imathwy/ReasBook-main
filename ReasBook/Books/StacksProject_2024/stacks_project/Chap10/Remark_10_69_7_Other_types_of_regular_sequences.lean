import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap15.Lemma_15_30_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_30_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/-
Domain triage:
* primary domain: Koszul-, `H_1`-, and quasi-regular refinements of regular sequences in
  commutative algebra;
* sampled owner API:
  `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.IsKoszulRegularSequence`,
  `RingTheory.Sequence.IsH1RegularSequence`,
  `RingTheory.Sequence.IsH1RegularOn.isQuasiRegular`;
* core/canonical owner: the finite-family predicates
  `IsKoszulRegularSequence` and `IsH1RegularSequence`;
* layer split: this remark is a `bridge/view` file, so the owner predicates stay recalled from
  Chapter 15 and only the source-facing implication theorems remain local.
-/

/- Remark 10.69.7: the canonical owner predicate for Koszul-regularity is
`RingTheory.Sequence.IsKoszulRegularSequence`. -/
recall IsKoszulRegularSequence

/- Companion specification recall for the canonical owner predicate
`RingTheory.Sequence.IsKoszulRegularSequence`. -/
recall isKoszulRegularSequence_iff

/- The canonical owner predicate for `H_1`-regularity is
`RingTheory.Sequence.IsH1RegularSequence`. -/
recall IsH1RegularSequence

/- Companion specification recall for the canonical owner predicate
`RingTheory.Sequence.IsH1RegularSequence`. -/
recall isH1RegularSequence_iff

-- Proof sketch: compare the Koszul complex of a regular sequence with the standard exterior
-- resolution of the quotient by the generated ideal; exactness away from degree zero gives the
-- vanishing of all positive Koszul homology groups.
/-- Every regular sequence is Koszul-regular. -/
theorem isKoszulRegular_of_isRegular {rs : List R} (hreg : IsRegular R rs) :
    IsKoszulRegularSequence rs.get := sorry

/- Companion recall: the owner bridge from Koszul-regularity to `H_1`-regularity is
`RingTheory.Sequence.isH1RegularSequence_of_isKoszulRegularSequence`. -/
recall isH1RegularSequence_of_isKoszulRegularSequence

-- Proof sketch: express `H₁` of the Koszul complex in degree one as the obstruction to the
-- graded coefficient criterion used in `IsQuasiRegular`; vanishing of that homology removes the
-- obstruction and yields quasi-regularity.
/-- Every `H_1`-regular sequence is quasi-regular. -/
theorem isQuasiRegular_of_isH1Regular {rs : List R}
    (hH1 : IsH1RegularSequence rs.get) :
    IsQuasiRegularSequence rs := by
  simpa [IsH1RegularSequence, List.ofFn_get] using
    hH1.isQuasiRegular

end RingTheory.Sequence
