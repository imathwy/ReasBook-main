import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap10.Lemma_10_46_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

-- Proof sketch: represent an element of `κ(q)` by `y / z` in the localization `S_q`; choose
-- positive powers of `y` and `z` coming from `R`, and then `(y / z)^(nm)` lies in the image of
-- the induced map `κ(q ∩ R) → κ(q)`. Applying the field-level bridge from Lemma `10.46.2`
-- packages this source wording around the canonical owner predicate `IsPurelyInseparable`, with
-- the only exceptional branch being algebraicity over a prime field. The residue-field owner
-- object is the prime `p := comap f q`, not an auxiliary ideal-level wrapper around it. The
-- locally nilpotent-kernel hypothesis is only needed for the separate homeomorphism clause, which
-- is exactly the canonical theorem `PrimeSpectrum.isHomeomorph_comap`.
/-- Lemma 10.46.3 (1): if every element of `S` has a positive power in the image of a ring map
`f : R →+* S`, then for every prime `q` of `S` the induced residue-field map
`κ(comap f q) → κ(q)`
satisfies the canonical field-extension alternative from Lemma `10.46.2`: the extension is purely
inseparable, or the target residue field is algebraic over a prime field. This repackages the
textbook power-in-the-image conclusion around the owner notion `IsPurelyInseparable`. The
homeomorphism statement is the canonical theorem `PrimeSpectrum.isHomeomorph_comap`, recalled
below as clause `(2)`. -/
theorem residueFieldMap_purelyInseparable_or_primeFieldAlgebraic_of_exists_pow_mem_range
    (f : R →+* S)
    (hpow : ∀ x : S, ∃ n > 0, x ^ n ∈ f.range)
    (q : PrimeSpectrum S) :
    let p : PrimeSpectrum R := comap f q
    let fκ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
      Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl
    let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
    IsPurelyInseparable p.asIdeal.ResidueField q.asIdeal.ResidueField ∨
      PrimeFieldAlgebraic q.asIdeal.ResidueField := by
  sorry

/- Lemma 10.46.3 (2): if every element of `S` has a positive power in the image of a ring map
`f : R →+* S` and the kernel of `f` is locally nilpotent, then the induced map on prime spectra is
a homeomorphism. This is exactly the canonical theorem `PrimeSpectrum.isHomeomorph_comap`. -/
recall PrimeSpectrum.isHomeomorph_comap

end
