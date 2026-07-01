import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped TensorProduct
open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

local notation "f" => algebraMap R S

/- Layering for this item:
* source-facing: the TFAE characterizing surjectivity of `Spec S → Spec R` in terms of
  contraction formulas for extended ideals, plus its stability under arbitrary base change;
* core/canonical owner: `PrimeSpectrum.comap (algebraMap R S)` together with the ideal
  operations `Ideal.map`, `Ideal.comap`, and `Ideal.radical`;
* bridge/view: Lemma `10.18.6`, `PrimeSpectrum.mem_range_comap_iff`,
  `PrimeSpectrum.nontrivial_iff_mem_rangeComap`, `Ideal.comap_radical`, and
  `Ideal.radical_eq_sInf`, which translate between the owner map on spectra and the textbook
  contraction criteria.
-/

/-- Lemma 10.30.3: for a ring map `R → S`, the following are equivalent: `Spec S → Spec R` is
surjective, contraction of `√(IS)` is `√I` for every ideal `I`, contraction of `IS` is `I` for
every radical ideal `I`, and contraction of `pS` is `p` for every prime `p` of `R`. -/
-- Proof sketch: the owner object is the canonical spectral map `comap f : Spec S → Spec R`.
-- Use `Ideal.comap_radical` to identify the radical clause with the radical-ideal clause,
-- `Ideal.radical_eq_sInf` to recover a radical ideal as the intersection of primes containing it,
-- and `mem_range_comap_iff` together with Lemma 10.18.6 to identify surjectivity of `comap f`
-- with the prime-ideal contraction condition.
theorem specComap_surjective_tfae :
    List.TFAE
      [ Function.Surjective (comap f),
        ∀ I : Ideal R,
          ((I.map f).radical).comap f = I.radical,
        ∀ I : Ideal R, I.IsRadical → (I.map f).comap f = I,
        ∀ p : PrimeSpectrum R, (p.asIdeal.map f).comap f = p.asIdeal ] := sorry

section BaseChange

variable {R' : Type w} [CommRing R'] [Algebra R R']

/-- If `Spec S → Spec R` is surjective, then every base change `Spec (R' ⊗[R] S) → Spec R'` is
also surjective. The corresponding contraction formulas for the base-changed map then follow from
`specComap_surjective_tfae`. -/
-- Proof sketch: for `p' : Spec R'` lying over `p : Spec R`, apply Lemma 10.18.6 to reduce
-- surjectivity of `Spec (R' ⊗[R] S) → Spec R'` to nontriviality of the fiber ring over `p'`.
-- Identify that fiber with `(S ⊗[R] κ(p)) ⊗[κ(p)] κ(p')`, which is nontrivial because the first
-- factor is nontrivial by the surjectivity hypothesis and the second map is an extension of
-- fields.
theorem specComap_surjective_stable_under_baseChange
    (h : Function.Surjective (comap f)) :
    Function.Surjective (comap (algebraMap R' (R' ⊗[R] S))) := sorry

end BaseChange

end
