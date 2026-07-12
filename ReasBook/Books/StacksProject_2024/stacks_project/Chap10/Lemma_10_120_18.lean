import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open PrimeSpectrum

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [IsNoetherianRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]

local notation "B" => integralClosure A L

/- Domain-style sampling:
- primary domain: integral closures in finite extensions of fraction fields of one-dimensional
  Noetherian domains, together with the induced prime-spectrum and residue-field behavior;
- sampled canonical/project owners:
  `IsDedekindDomain`,
  `Algebra.IsIntegral.comap_surjective`,
  `Ideal.primesOver`,
  `Ideal.primesOver_finite`,
  `moduleFinite_residueField_of_primeOver_maximalIdeal_of_finite_fractionField_extension`;
- best owner abstraction: the integral-closure owner `B = integralClosure A L`, with
  `IsDedekindDomain B` as the canonical ambient owner once Lemma `10.120.18` proves it;
- primitive data: the ambient extension tower `A ⊆ FractionRing A ⊆ L` and the owner ring `B`;
- derived API: surjectivity of `Spec(B) → Spec(A)`, finiteness of the fibers `p.primesOver B`,
  and finiteness of the residue-field extensions.

Source/core/bridge triage:
- `source-facing`: the Dedekind-domain, finite-fiber, and residue-field-finiteness statements
  specialized to `B = integralClosure A L` under the source hypothesis `ringKrullDim A = 1`;
- `core/canonical`: `IsDedekindDomain`, `Algebra.IsIntegral.comap_surjective`,
  `Ideal.primesOver_finite`, and the local one-dimensional fiber theorem from
  `Lemma_10_119_10`;
- `bridge/view`: the present file should only keep the source-facing bridges that add the
  dimension-one input. The spectrum-surjectivity clause is an exact canonical recall and should
  not survive as a parallel local theorem.
-/

-- Proof sketch: apply Krull-Akizuki to get that `B` is Noetherian, use integrality of
-- `A → B` to identify `ringKrullDim B = 1`, and then invoke the Dedekind-domain
-- characterization from Lemma `10.120.17`, noting that `B` is integrally closed by construction.
/-- Lemma 10.120.18: if `A` is a one-dimensional Noetherian domain and `L` is a finite extension
of `FractionRing A`, then the integral closure of `A` in `L` is a Dedekind domain. -/
theorem integralClosure_isDedekindDomain_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) :
    IsDedekindDomain B := sorry

/- The map `Spec(integralClosure A L) → Spec(A)` induced by the inclusion
`A → integralClosure A L` is exactly the canonical integral-spectrum-surjectivity theorem
`Algebra.IsIntegral.comap_surjective`; the dimension-one hypothesis is redundant here and is
therefore removed from the public API. -/
recall Algebra.IsIntegral.comap_surjective

-- Proof sketch: if `p = 0`, then `B` is a domain and the only prime of `B` over `0` is `0`.
-- If `p ≠ 0`, then `p` is maximal because `A` has Krull dimension `1`; localize at `p` and apply
-- Lemma `10.119.10 (2)` to the resulting one-dimensional Noetherian local domain.
/-- For each `p : Spec(A)`, only finitely many prime ideals of `integralClosure A L` lie over
`p`. -/
theorem integralClosure_primesOver_finite_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) (p : PrimeSpectrum A) :
    (p.asIdeal.primesOver B).Finite := sorry

-- Proof sketch: localize at the contraction of `q`, identify the localized extension of fraction
-- fields with a finite extension, and apply Lemma `10.119.10 (3)` to obtain finiteness of the
-- induced residue-field extension.
/-- For each `q : Spec(integralClosure A L)`, the residue field extension
`κ(comap q) → κ(q)` is finite. -/
theorem integralClosure_residueField_finite_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) (q : PrimeSpectrum B) :
    Module.Finite (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField
      q.asIdeal.ResidueField := sorry

end
