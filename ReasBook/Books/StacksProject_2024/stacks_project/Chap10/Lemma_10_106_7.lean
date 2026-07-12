import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open RingTheory Sequence IsLocalRing
open scoped nonZeroDivisors

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Domain triage:
* primary domain: regular sequences and regular local rings in commutative algebra;
* sampled owner declarations:
  `RingTheory.Sequence.IsRegular`,
  `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`,
  `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`,
  `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`;
* core/canonical owner: `IsRegularLocalRing R` together with the regular-sequence owner
  `Sequence.IsRegular R rs`;
* bridge/view: the quotient rings `R ⧸ Ideal.ofList rs` and `R ⧸ Ideal.span {x}`.

Primitive data here are only the ring `R`, the regular sequence `rs`, and the owner predicates
`IsRegular R rs` and `IsRegularLocalRing`. The singleton quotient dimension-drop statement is
already provided canonically by mathlib, so this file should reuse that owner theorem rather than
keep an unused parallel local wrapper.
-/

/- Companion recall: the singleton nonzerodivisor quotient step is already the canonical mathlib
theorem `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`. -/
recall ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors

-- Proof sketch: induct on the regular sequence `rs`. The empty sequence is tautological. For
-- `x :: rs`, the regularity hypothesis gives that `x` is a nonzerodivisor and that the tail is a
-- regular sequence on `R ⧸ Ideal.span ({x} : Set R)`. Apply the induction hypothesis to the tail,
-- then use the canonical singleton dimension-drop theorem
-- `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`; combine the
-- resulting dimension identities with `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`.
/-- Lemma 10.106.7: if `rs` is a regular sequence in a Noetherian local ring `R` and
`R ⧸ Ideal.ofList rs` is a regular local ring, then `R` is a regular local ring. -/
theorem isRegularLocalRing_of_quotient_of_isRegular {rs : List R} (hreg : IsRegular R rs)
    (hquot : IsRegularLocalRing (R ⧸ Ideal.ofList rs)) :
    IsRegularLocalRing R := sorry

end
