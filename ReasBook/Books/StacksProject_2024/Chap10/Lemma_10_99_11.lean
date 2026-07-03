import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/- Domain-style sampling for Lemma 10.99.11:
- primary domain: flatness of a finite module over a Noetherian base, detected primewise after
  localizing the target ring and using flatness of the quotient modules by ideal powers;
- sampled owner declarations in the same domain:
  `Module.Flat`,
  `LocalizedModule.AtPrime`,
  `flat_iff_flat_localizedModule_atPrime_over_under`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`;
- best owner abstraction: the public conclusions belong on the canonical flatness owner
  `Module.Flat`, with `LocalizedModule.AtPrime` as the prime-local view and
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal` as the local owner theorem reused in the
  proof;
- primitive data: the ideal `I`, the prime `q` containing `IS`, and the hypothesis that every
  quotient `M / I^n M` is flat over `R / I^n`;
- derived API: flatness of `M_q` over `R`, and the local-ring specialization obtained by taking
  the unique closed point.

Source/core/bridge triage:
- `source-facing`: the Stacks prime-local flatness criterion and its local-ring specialization;
- `core/canonical`: `Module.Flat`, `LocalizedModule.AtPrime`,
  `flat_iff_flat_localizedModule_atPrime_over_under`, and
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`;
- `bridge/view`: Lemma `10.51.5` supplies the annihilation-after-localization step needed to turn
  the quotient-flatness hypotheses into the Tor-vanishing input of the local criterion, and the
  local-ring theorem is the closed-point specialization of the prime-local statement.
-/

private abbrev FlatQuotientsByIdealPowers (M : Type w) [AddCommGroup M] [Module R M]
    (I : Ideal R) : Prop :=
  ∀ n : ℕ, 1 ≤ n → Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M)))

-- Proof sketch: localize at `q` and apply the variant of the local criterion from Lemma
-- `10.99.10` over the local map `R_(q ∩ R) → S_q`. The hypothesis on all quotients `M / I^n M`
-- gives flatness modulo powers after localization, Remark `10.75.9` identifies the relevant
-- `Tor₁` group with the kernel of `I ⊗ M → M`, and Lemma `10.51.5` kills that kernel after
-- localizing at `q`.
/-- Lemma 10.99.11: let `R → S` be a ring map, let `I` be an ideal of `R`, and let `M` be a
finite `S`-module. Assume `R` and `S` are Noetherian and that `M / I^n M` is flat over `R / I^n`
for every `n ≥ 1`. Then for every prime `q` of `S` containing `IS`, the localization `M_q` is
flat over `R`. -/
theorem flat_localizedModule_atPrime_of_flat_quotients_by_ideal_powers
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal)
    (hflat : FlatQuotientsByIdealPowers M I) :
    Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := sorry

-- Proof sketch: specialize the prime-local statement to the closed point of `Spec S`; this is the
-- prime `⊤`, whose underlying ideal is `maximalIdeal S`.
/-- If the target ring `S` is local and `IS` is contained in its maximal ideal, then `M` is flat
over `R` under the same quotient-flatness hypotheses. -/
theorem flat_of_isLocalRing_and_flat_quotients_by_ideal_powers
    [IsLocalRing S] (I : Ideal R) (hI : I.map (algebraMap R S) ≤ maximalIdeal S)
    (hflat : FlatQuotientsByIdealPowers M I) :
    Module.Flat R M := sorry

end
