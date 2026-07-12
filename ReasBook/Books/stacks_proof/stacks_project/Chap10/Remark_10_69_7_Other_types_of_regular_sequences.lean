import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Lemma_15_30_2
import StacksProject_2024.Chap15.Lemma_15_30_3
import StacksProject_2024.Chap15.Lemma_15_30_6
import StacksProject_2024.Chap10.Remark_10_69_7_Other_types_of_regular_sequences.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Set
open scoped Pointwise TensorProduct

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

/- Remark 10.69.7 (1): the canonical owner predicate for Koszul-regularity is
`RingTheory.Sequence.IsKoszulRegularSequence`, with the homology-vanishing formulation exposed by
the companion recall below. -/
recall IsKoszulRegularSequence

/- Companion specification recall for the canonical owner predicate
`RingTheory.Sequence.IsKoszulRegularSequence`. -/
recall isKoszulRegularSequence_iff

/- Remark 10.69.7 (2): the canonical owner predicate for `H_1`-regularity is
`RingTheory.Sequence.IsH1RegularSequence`, with the first-homology formulation exposed by the
companion recall below. -/
recall IsH1RegularSequence

/- Companion specification recall for the canonical owner predicate
`RingTheory.Sequence.IsH1RegularSequence`. -/
recall isH1RegularSequence_iff

/-- Helper for Chap10 Remark 10 69 7 Other types of regular sequences: a regular list is
Koszul-regular on the ambient module after passing to the canonical finite family `rs.get`. -/
theorem isKoszulRegularOn_get_of_isRegular {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M] {rs : List A} (hreg : IsRegular M rs) :
    IsKoszulRegularOn M rs.get := by
  -- Route correction: the duplicated local head/tail induction is replaced by the canonical
  -- Chapter 15 owner theorem, which has exactly this module-valued surface.
  exact IsRegular.isKoszulRegularOn hreg

/-- Helper for Chap10 Remark 10 69 7 Other types of regular sequences: a regular list is
Koszul-regular after passing to the canonical finite family `rs.get`. -/
theorem isKoszulRegularSequence_get_of_isRegular {rs : List R} (hreg : IsRegular R rs) :
    IsKoszulRegularSequence rs.get := by
  -- Specialize the repaired module-valued induction to the regular module.
  simpa [IsKoszulRegularSequence] using
    (isKoszulRegularOn_get_of_isRegular (A := R) (M := R) hreg)

/-- Chap10 Remark 10 69 7 Other types of regular sequences: every regular sequence is
Koszul-regular. -/
@[stacks 061T]
theorem isKoszulRegular_of_isRegular {rs : List R} (hreg : IsRegular R rs) :
    IsKoszulRegularSequence rs.get := by
  -- Route correction: keep the source proof at the owner level by first proving the stronger
  -- list-family statement and then specializing back to the theorem as stated.
  exact isKoszulRegularSequence_get_of_isRegular hreg

/- Remark 10.69.7 (4): the owner-level bridge from Koszul-regularity to `H_1`-regularity is
`RingTheory.Sequence.isH1RegularSequence_of_isKoszulRegularSequence`. -/
recall isH1RegularSequence_of_isKoszulRegularSequence

/-- Remark 10.69.7 (5): every `H_1`-regular sequence is quasi-regular. -/
@[stacks 061T]
theorem isQuasiRegular_of_isH1Regular {rs : List R}
    (hH1 : IsH1RegularSequence rs.get) :
    IsQuasiRegularSequence rs := by
  -- Specialize the Chapter 15 owner theorem to the regular module and convert the finite-family
  -- sequence `rs.get` back to the source-facing list `rs`.
  simpa [IsH1RegularSequence, IsQuasiRegularSequence, List.ofFn_get] using
    (IsH1RegularOn.isQuasiRegular (M := R) (f := rs.get) hH1)

end RingTheory.Sequence
