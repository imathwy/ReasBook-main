import Mathlib
import stacks_project.Chap10.Definition_10_69_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain triage:
* primary domain: regular and quasi-regular sequences in commutative algebra;
* sampled owner API:
  `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.isRegular_cons_iff`,
  `RingTheory.Sequence.IsWeaklyRegular`,
  `RingTheory.Sequence.IsQuasiRegular`;
* core/canonical owner: `RingTheory.Sequence.IsRegular M rs`;
* layer split: regularity on successive quotients is primitive owner data, while quasi-regularity
  is the source-facing graded comparison notion of `Definition 10.69.1`, and Lemma `10.69.2` is
  the derived bridge from the owner regularity theorem to that source-facing notion.
-/

/-- Lemma 10.69.2 (2): every `M`-regular sequence is `M`-quasi-regular. -/
theorem IsRegular.isQuasiRegular {rs : List R} (hreg : IsRegular M rs) :
    IsQuasiRegular M rs := sorry

/- Lemma 10.69.2 (1): the ring-valued statement is the specialization of
`IsRegular.isQuasiRegular` to the owner module `R`, so no parallel wrapper theorem is needed. -/
#check (IsRegular.isQuasiRegular : ∀ {rs : List R}, IsRegular R rs → IsQuasiRegularSequence rs)

end RingTheory.Sequence
