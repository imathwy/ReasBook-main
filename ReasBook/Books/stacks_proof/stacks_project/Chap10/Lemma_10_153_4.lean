import Mathlib
import StacksProject_2024.Chap10.Definition_10_122_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

/-
Domain-style sampling:
- primary domain: henselian local rings, finite and quasi-finite commutative algebra maps, and
  localization at primes over the maximal ideal;
- sampled owner declarations in this domain:
  `HenselianLocalRing`,
  `Algebra.QuasiFiniteAt`,
  `Algebra.QuasiFinite`,
  `Algebra.FiniteType.QuasiFiniteAt`,
  `Algebra.FiniteType.QuasiFinite`;
- best owner abstraction:
  the core/canonical owners are `HenselianLocalRing` and the quasi-finite owners
  `Algebra.QuasiFiniteAt` / `Algebra.QuasiFinite`, while this file is source-facing where the
  Stacks wording explicitly bundles finite type together with those local/global quasi-finite
  hypotheses;
- primitive data vs. derived API:
  the primitive input is the henselian local base together with finite, local, or
  finite-type-quasi-finite algebra hypotheses; the local-henselian and finite-localization
  conclusions are derived API around those owners.

Source/core/bridge triage:
- `source-facing`: the finite-product decomposition and the henselian/finiteness conclusions for
  localizations over the maximal ideal;
- `core/canonical`: `HenselianLocalRing`, `Algebra.QuasiFiniteAt`, `Algebra.QuasiFinite`;
- `bridge/view`: the chapter source-facing finite-type packages
  `Algebra.FiniteType.QuasiFiniteAt` and `Algebra.FiniteType.QuasiFinite`, which this file should
  reuse instead of restating their component hypotheses separately.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: apply Lemma `10.153.3` to decompose a finite `R`-algebra into a finite product of
-- local rings. Each factor is finite over `R`, local, and hence henselian by the local case below.
/-- Lemma 10.153.4 (1): if `(R, 𝔪, κ)` is a henselian local ring and `R → S` is finite, then `S`
is a finite product of henselian local rings, each finite over `R`. -/
@[stacks 04GH]
theorem exists_pi_algEquiv_henselianLocalRing_of_finite
    [HenselianLocalRing R] [Module.Finite R S] :
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
      (instAComm : ∀ i, CommRing (A i))
      (instAAlg : ∀ i, Algebra R (A i))
      (instAHenselian : ∀ i, HenselianLocalRing (A i))
      (instAFinite : ∀ i, Module.Finite R (A i)),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R (A i) := instAAlg
      letI : ∀ i, HenselianLocalRing (A i) := instAHenselian
      letI : ∀ i, Module.Finite R (A i) := instAFinite
      Nonempty (S ≃ₐ[R] ∀ i, A i) := sorry

-- Proof sketch: localize the finite product decomposition from clause (1) at the unique maximal
-- ideal of `S`; only one factor survives, so a finite local `R`-algebra is one of the henselian
-- local factors occurring there.
/-- Lemma 10.153.4 (2): if `(R, 𝔪, κ)` is henselian, `R → S` is finite, and `S` is local, then
`S` is a henselian local ring. -/
@[stacks 04GH]
theorem finite_local_henselianLocalRing
    [HenselianLocalRing R] [Module.Finite R S] [IsLocalRing S] :
    HenselianLocalRing S := sorry

-- Proof sketch: for a finite ring map between local rings, every element of `R` whose image in
-- `S` is a unit is already a unit in `R`; equivalently, the inverse image of the maximal ideal of
-- `S` is the maximal ideal of `R`.
/-- Lemma 10.153.4 (3): if `R → S` is a finite ring map and `S` is local, then `R → S` is a local
ring map. -/
@[stacks 04GH]
theorem algebraMap_isLocalHom_of_finite_local
    [Module.Finite R S] [IsLocalRing S] :
    IsLocalHom (algebraMap R S) := sorry

end

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: use Lemma `10.153.3` to split `S` near the maximal ideal of `R` into a finite
-- part and a complementary part with no quasi-finite primes above `𝔪`; the chosen prime `q`
-- lies on the finite part, and its localization is then a local finite `R`-algebra, hence
-- henselian by clause (2).
/-- Lemma 10.153.4 (4): if `(R, 𝔪, κ)` is henselian, `R → S` is finite type, `q` lies over `𝔪`,
and `R → S` is quasi-finite at `q`, then `S_q` is henselian. -/
@[stacks 04GH]
theorem localizationAtPrime_henselianLocalRing_of_quasiFiniteAt_over_maximalIdeal
    [HenselianLocalRing R]
    (q : PrimeSpectrum S)
    (hq : Ideal.comap (algebraMap R S) q.asIdeal = maximalIdeal R)
    (hqf : Algebra.FiniteType.QuasiFiniteAt R S q.asIdeal) :
    HenselianLocalRing (Localization.AtPrime q.asIdeal) := sorry

-- Proof sketch: in the decomposition from the previous clause, the localization `S_q` is a
-- localization of the finite factor `A` at a maximal ideal, so it remains finite over `R`.
/-- Lemma 10.153.4 (5): if `(R, 𝔪, κ)` is henselian, `R → S` is finite type, `q` lies over `𝔪`,
and `R → S` is quasi-finite at `q`, then `S_q` is finite over `R`. -/
@[stacks 04GH]
theorem moduleFinite_localizationAtPrime_of_quasiFiniteAt_over_maximalIdeal
    [HenselianLocalRing R]
    (q : PrimeSpectrum S)
    (hq : Ideal.comap (algebraMap R S) q.asIdeal = maximalIdeal R)
    (hqf : Algebra.FiniteType.QuasiFiniteAt R S q.asIdeal) :
    Module.Finite R (Localization.AtPrime q.asIdeal) := sorry

-- Proof sketch: a quasi-finite morphism is quasi-finite at every prime, so clause (4) applies to
-- each prime of `S` lying over the maximal ideal of `R`.
/-- Lemma 10.153.4 (6): if `(R, 𝔪, κ)` is henselian and `R → S` is quasi-finite, then `S_q` is
henselian for every prime `q` of `S` lying over `𝔪`. -/
@[stacks 04GH]
theorem localizationAtPrime_henselianLocalRing_of_quasiFinite_over_maximalIdeal
    [HenselianLocalRing R]
    (q : PrimeSpectrum S)
    (hq : Ideal.comap (algebraMap R S) q.asIdeal = maximalIdeal R)
    (hS : Algebra.FiniteType.QuasiFinite R S) :
    HenselianLocalRing (Localization.AtPrime q.asIdeal) := sorry

-- Proof sketch: combine the global quasi-finite hypothesis with clause (5) at the chosen prime
-- `q` lying over the maximal ideal of `R`.
/-- Lemma 10.153.4 (7): if `(R, 𝔪, κ)` is henselian and `R → S` is quasi-finite, then `S_q` is
finite over `R` for every prime `q` of `S` lying over `𝔪`. -/
@[stacks 04GH]
theorem moduleFinite_localizationAtPrime_of_quasiFinite_over_maximalIdeal
    [HenselianLocalRing R]
    (q : PrimeSpectrum S)
    (hq : Ideal.comap (algebraMap R S) q.asIdeal = maximalIdeal R)
    (hS : Algebra.FiniteType.QuasiFinite R S) :
    Module.Finite R (Localization.AtPrime q.asIdeal) := sorry

end
