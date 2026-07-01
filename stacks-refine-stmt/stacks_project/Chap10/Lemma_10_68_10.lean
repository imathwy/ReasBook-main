import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Regular.RegularSequence

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open RingTheory.Sequence MvPolynomial
open Ideal

section

variable {R : Type u} [CommRing R]

/-
Domain triage:
* primary domain: regular sequences in commutative algebra, together with their polynomial and
  quasi-regular comparison constructions;
* sampled owner API:
  `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.isRegular_cons_iff`,
  `IsLocalRing.isRegular_of_perm`,
  `RingTheory.Sequence.IsRegular.isQuasiRegular`;
* core/canonical owner: `RingTheory.Sequence.IsRegular M rs`;
* primitive vs derived split: the regular-sequence predicate and `Ideal.ofList fs` are primitive
  owner data, while permutation invariance, passage to subsequences, and the polynomial-ring test
  are derived source-facing/bridge statements;
* layer classification for this file: the theorem below is `source-facing`; it should stay a local
  `List.TFAE` rather than being repackaged into a second owner abstraction.
-/

-- Proof sketch: prove `(1) → (2)` by restricting a permutation-regular family to ordered
-- subsequences in
-- the given order; prove `(2) → (1)` by induction on the length and reduction to the case of length
-- two; prove `(2) ↔ (3)` by decomposing the polynomial quotient into the direct sum indexed by
-- monomials, so regularity of `C (fᵢ) * Xᵢ` is equivalent to regularity of `fᵢ` on the relevant
-- quotient modules.
/-- Lemma 10.68.10: if a list `fs` does not generate the unit ideal, then the following are
equivalent: every permutation of `fs` is a regular sequence, every ordered subsequence of `fs` is
a regular sequence, and the sequence `C (fᵢ) * Xᵢ` is regular in the polynomial ring with one
variable for each entry of `fs`. -/
theorem regular_permutations_subsequences_polynomial_tfae
    {fs : List R} (hfs : ofList fs ≠ ⊤) :
    List.TFAE
      [ (∀ gs : List R, List.Perm gs fs → IsRegular R gs),
        (∀ gs : List R, List.Sublist gs fs → IsRegular R gs),
        IsRegular (MvPolynomial (Fin fs.length) R)
          (List.ofFn fun i ↦ C (fs[i]) * X i) ] := sorry

end
