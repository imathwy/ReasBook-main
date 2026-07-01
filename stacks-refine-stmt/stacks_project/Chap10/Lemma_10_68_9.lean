import Mathlib.RingTheory.Regular.RegularSequence

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingTheory.Sequence

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain triage:
* primary domain: regular sequences in commutative algebra;
* sampled owner API:
  `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.isRegular_cons_iff`,
  `IsSMulRegular.pow_iff`,
  `CategoryTheory.ShortComplex.ShortExact.isRegular_X₂`;
* core/canonical owner: `RingTheory.Sequence.IsRegular M rs`;
* primitive vs derived split: the module `M`, the element list `rs`, and the owner predicate
  `IsRegular M rs` are primitive data; invariance under replacing entries by positive powers is
  derived source-facing API and should not be repackaged into a new owner wrapper;
* layer classification for this file: the theorem below is `source-facing`, while its proof should
  reuse the owner regular-sequence API and the quotient short-exact-sequence bridge from
  Lemma `10.68.8`.
-/

-- Proof sketch: argue by induction on the regular sequence. For a singleton, use that an element
-- is `M`-regular if and only if any positive power is `M`-regular. For a longer sequence, apply
-- the induction hypothesis to the quotient by the first element and then compare the first term
-- with its positive power using the short exact sequences relating `M / fM`, `M / f^e M`, and
-- `M / f^(e - 1) M` as in Lemmas 10.68.8 and 10.4.1.
/-- Lemma 10.68.9: a sequence `rs` is regular on `M` if and only if the sequence obtained by
taking pointwise positive powers of its terms is regular on `M`. -/
theorem isRegular_iff_isRegular_pow
    {rs : List R} {es : List ℕ}
    (hes : List.Forall₂ (fun (_ : R) e ↦ 0 < e) rs es) :
    IsRegular M rs ↔ IsRegular M (rs.zipWith (· ^ ·) es) := sorry

end

end RingTheory.Sequence
