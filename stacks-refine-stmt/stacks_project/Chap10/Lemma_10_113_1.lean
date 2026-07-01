import Mathlib
import stacks_project.Chap10.Definition_10_105_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open PrimeSpectrum

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S]

/-- Bridge/view: the natural-number transcendence degree of the induced fraction-field extension
attached to an injective algebra map of domains. The `FaithfulSMul` witness needed to lift the
algebra to fraction rings is derived internally from injectivity, so it stays out of theorem
surfaces. -/
noncomputable abbrev fractionRingTrdeg
    (hinj : Function.Injective (algebraMap R S)) : ℕ :=
  let _ : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  Cardinal.toNat (trdeg (FractionRing R) (FractionRing S))

end

end Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S]

/-
Domain-style sampling:
- primary domain: the dimension formula for finite type maps of domains, organized around prime
  spectra, localizations at primes, and universal catenarity;
- sampled owner API:
  `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown`,
  `FractionRing.liftAlgebra`,
  `FractionRing.isScalarTower_liftAlgebra`,
  `faithfulSMul_iff_algebraMap_injective`,
  `Algebra.fractionRingTrdeg`,
  `Ideal.over_under`,
  `UniversallyCatenaryRing`,
  `Ideal.Quotient.algebraOfLiesOver`;
- owner abstraction: a point `q : PrimeSpectrum S`, with the source prime recovered canonically as
  `q.asIdeal.under R`; the induced fraction-field algebra `Frac(R) → Frac(S)` is canonical
  derived scaffolding from injectivity is obtained directly from the canonical owner theorem
  `faithfulSMul_iff_algebraMap_injective`;
- primitive data: the finite type map `R → S`, injectivity of `algebraMap R S`, and the target
  point `q`;
- derived API: the fraction-field tower needed to state transcendence degrees, and the explicit
  ideal-level lies-over restatements below. The generic fraction-field transcendence-degree term is
  packaged as the thin bridge `Algebra.fractionRingTrdeg`, so the public statements do not expose
  instance plumbing.

Layer triage:
- `source-facing`: the height/transcendence-degree inequality and equality;
- `core/canonical`: the prime-spectrum/local-fiber owners from Lemma `10.112.7` together with the
  universally catenary owner from Definition `10.105.3`;
- `bridge/view`: the ideal-level formulations with an explicit `hq : q.LiesOver p`.

This file therefore uses the `PrimeSpectrum` statement as the public owner layer and derives the
ideal-level restatements from it, rather than keeping only the lower-level lies-over surface. The
fraction-field algebra/tower itself is the canonical `FractionRing` owner interface; only the
`FaithfulSMul` input needed to build it is derived from injectivity.
-/

section FiniteType

variable [IsNoetherianRing R] [Algebra.FiniteType R S]

-- Proof sketch: replace the heights of `p` and `q` by the dimensions of the local rings `R_p` and
-- `S_q`, then induct on a finite generating set of `S` over `R`. Reduce to the one-generator cases
-- `S = R[x]` and `S = R[x] / 𝔫`, using the flat dimension formula in the polynomial case, the drop
-- by at least one after quotienting by a nonzero principal ideal, and additivity of transcendence
-- degree in towers for the induction step.
/-- Prime-spectrum owner form of Lemma 10.113.1: for a point `q` of `Spec S`, the height of `q`
plus the transcendence degree of `κ(q)` over `κ(q ∩ R)` is bounded by the height of the
contraction together with the generic transcendence degree term. -/
theorem primeHeight_add_residueFieldTrdeg_le_primeHeight_under_add_trdeg_of_finiteType
    (hinj : Function.Injective (algebraMap R S)) (q : PrimeSpectrum S) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) ≤
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
        Algebra.fractionRingTrdeg hinj :=
  sorry

/-- Lemma 10.113.1: if `R → S` is an injective finite type map of domains with `R` Noetherian and
`q` lies over `p`, then the height of `q` plus the transcendence degree of the residue-field
extension `κ(q) / κ(p)` is bounded by the height of `p` plus the transcendence degree of `Frac(S)`
over `Frac(R)`. -/
theorem primeHeight_add_residueFieldTrdeg_le_primeHeight_add_trdeg_of_finiteType
    (hinj : Function.Injective (algebraMap R S)) (p : Ideal R) [p.IsPrime] (q : Ideal S)
    [q.IsPrime] (hq : q.LiesOver p) :
    ENat.toNat (Ideal.primeHeight q) +
        Cardinal.toNat (Algebra.trdeg p.ResidueField q.ResidueField) ≤
      ENat.toNat (Ideal.primeHeight p) +
        Algebra.fractionRingTrdeg hinj :=
  by
    have hp : p = q.under R := by
      simpa using hq.over
    subst p
    simpa using
      (primeHeight_add_residueFieldTrdeg_le_primeHeight_under_add_trdeg_of_finiteType
        hinj (⟨q, inferInstance⟩ : PrimeSpectrum S))

end FiniteType

section UniversallyCatenary

variable [Algebra.FiniteType R S] [UniversallyCatenaryRing.{u, v} R]

-- Proof sketch: in the universally catenary case, the one-generator polynomial step is already an
-- equality, and in the quotient step by a nonzero prime of `R[x]` catenarity shows the local
-- dimension drops by exactly one. Running the same induction as for the inequality keeps equality
-- at each stage.
/-- Prime-spectrum owner form of the universally catenary equality case. -/
theorem primeHeight_add_residueFieldTrdeg_eq_primeHeight_under_add_trdeg_of_universallyCatenary
    (hinj : Function.Injective (algebraMap R S)) (q : PrimeSpectrum S) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
        Algebra.fractionRingTrdeg hinj :=
  sorry

/-- Under the dimension-formula hypotheses, universal catenarity of `R` upgrades the inequality to
an equality. -/
theorem primeHeight_add_residueFieldTrdeg_eq_primeHeight_add_trdeg_of_universallyCatenary
    (hinj : Function.Injective (algebraMap R S)) (p : Ideal R) [p.IsPrime] (q : Ideal S)
    [q.IsPrime] (hq : q.LiesOver p) :
    ENat.toNat (Ideal.primeHeight q) +
        Cardinal.toNat (Algebra.trdeg p.ResidueField q.ResidueField) =
      ENat.toNat (Ideal.primeHeight p) +
        Algebra.fractionRingTrdeg hinj :=
  by
    have hp : p = q.under R := by
      simpa using hq.over
    subst p
    simpa using
      (primeHeight_add_residueFieldTrdeg_eq_primeHeight_under_add_trdeg_of_universallyCatenary
        hinj (⟨q, inferInstance⟩ : PrimeSpectrum S))

end UniversallyCatenary

end
