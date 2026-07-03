import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: quasi-finite localizations of finite-type commutative-algebra maps and Krull
  dimension comparisons at primes;
- sampled owner declarations:
  `Algebra.QuasiFiniteAt`,
  `Ideal.under`,
  `ringKrullDim_localizationAtPrime_le_ringKrullDim_localizationAtPrime_add_ringKrullDim_fiberLocalRingAt_of_liesOver`,
  `ringKrullDim_le_of_isIntegral`;
- best owner abstraction: the primewise owner `Algebra.QuasiFiniteAt R q`, with the base prime
  recovered canonically as `q.under R`;
- primitive data: the target prime `q` and the canonical quasi-finite owner structure;
- derived API: the base prime `p` together with `[q.LiesOver p]`, which are redundant once `q` is
  fixed.

This item is therefore kept at the `source-facing` layer as the local-dimension inequality, but
its public interface is refined to the canonical owner shape indexed only by `q`.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

-- Proof sketch: apply Zariski's main theorem at `q` to replace `S_q` by the localization at a
-- prime of the integral closure of `R_p` in `S_p`; then use the integral-extension dimension bound
-- from Lemma `10.112.3` for that integral closure over `R_p`.
/-- Lemma 10.125.4: for a finite type ring map `R → S`, if `q` is a prime ideal of `S` and the
map is quasi-finite at `q`, then the Krull dimension of the local ring `S_q` is at most the Krull
dimension of the local ring `R_(q ∩ R)`. -/
theorem ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt
    (q : Ideal S) [q.IsPrime] [Algebra.QuasiFiniteAt R q] :
    ringKrullDim (Localization.AtPrime q) ≤ ringKrullDim (Localization.AtPrime (q.under R)) := sorry

end
