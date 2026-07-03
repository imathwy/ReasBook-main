import Mathlib
import StacksProject_2024.Chap15.Lemma_15_90_1
import StacksProject_2024.Chap15.Lemma_15_91_1
import StacksProject_2024.Chap15.Proposition_15_90_19

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum

universe u v

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling:
* primary domain: commutative algebra of prime spectra under quotient and localization;
* sampled owner declarations:
  `principalIdealQuotientMap`,
  `PrimeSpectrum.comap`,
  `PrimeSpectrum.localization_away_comap_range`,
  `principalAdicCompletion_quotientMap_bijective`;
* best owner abstraction: the chapter owner `principalIdealQuotientMap` for reduction modulo
  `(f)`, together with the canonical prime-spectrum maps `PrimeSpectrum.comap`;
* primitive data: a ring map `R → R'` and an element `f : R`;
* derived API: the surjectivity of
  `Spec R' ⊔ Spec R_f → Spec R` under the quotient-map bijectivity hypothesis;
* triage: `source-facing` = the surjectivity statement below, `core/canonical` =
  `principalIdealQuotientMap` and `PrimeSpectrum.comap`, `bridge/view` =
  the completion specialization.
-/

-- Proof sketch: decompose `Spec(R)` as `V(f) ∪ D(f)`. The quotient-bijectivity hypothesis
-- identifies the image of `Spec(R')` with `V(f)` via the canonical quotient map
-- `principalIdealQuotientMap (algebraMap R R') f rfl : R ⧸ (f) →+* R' ⧸ (f R')`,
-- while `PrimeSpectrum.localization_away_comap_range` identifies the localization summand with
-- `D(f)`.
/-- Lemma 15.91.3: if `R → R'` induces an isomorphism `R / (f) → R' / (f)R'`, then the induced
map `Spec(R') ⊔ Spec(R_f) → Spec(R)` is surjective. -/
theorem primeSpectrum_sum_surjective_of_quotientByPrincipalIdeal_bijective
    {R' : Type v} [CommRing R'] [Algebra R R']
    (f : R)
    (hquot : Function.Bijective (principalIdealQuotientMap (algebraMap R R') f rfl)) :
    Function.Surjective
      (Sum.elim
        (comap (algebraMap R R'))
        (comap (algebraMap R (Localization.Away f)))) := sorry

-- Proof sketch: apply
-- `primeSpectrum_sum_surjective_of_quotientByPrincipalIdeal_bijective` with
-- `R' = principalAdicCompletion f`; Lemma `15.91.1` supplies the quotient
-- bijectivity assumption.
/-- The `(f)`-adic completion and the localization away from `f` cover `Spec(R)`. -/
theorem primeSpectrum_completion_sum_surjective (f : R) :
    Function.Surjective
      (Sum.elim
        (comap (algebraMap R (principalAdicCompletion f)))
        (comap (algebraMap R (Localization.Away f)))) := sorry

end
