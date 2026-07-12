import Mathlib
import StacksProject_2024.Chap15.Lemma_15_45_3
import StacksProject_2024.Chap15.Lemma_15_45_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open PrimeSpectrum
open scoped TensorProduct

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain triage:
- primary domain: local commutative algebra of henselizations, strict henselizations, and fibers
  over a prime;
- sampled owner declarations:
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `PrimeSpectrum.primesOver_finite_of_isFilteredColimitOfEtale_of_isNoetherianFiber`,
  `PrimeSpectrum.fiberToPiResidueField_bijective_of_isFilteredColimitOfEtale_of_isNoetherianFiber`,
  `residueField_isAlgebraic_and_separable_of_isWeaklyEtale`;
- best owner abstraction: this file is `source-facing`; its theorems should specialize the chapter
  owners above to henselizations and strict henselizations, with no new wrapper around primes over
  a fiber or the canonical fiber-to-product map;
- primitive data: the local Noetherian ring `R`, a prime `p : PrimeSpectrum R`, and chosen
  henselization / strict henselization owners;
- derived API: Noetherianity of `Rh` and `Rsh` from Lemma `15.45.3`, Noetherianity of
  `p.asIdeal.Fiber B` from the canonical tensor-product owner, and weakly étale residue-field
  control from the filtered-colimit owner.

Source/core/bridge triage:
- `source-facing`: the six specialized statements below;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`, `Ideal.primesOver`,
  `Ideal.fiberToPiResidueField`, and `Algebra.IsWeaklyEtale`;
- `bridge/view`: Lemma `15.45.3` upgrading `R`-Noetherianity to `Rh` and `Rsh`, and the tensor
  commutation equivalence identifying `p.asIdeal.Fiber B` with `B ⊗[R] p.asIdeal.ResidueField`.
-/
/-- Helper for Lemma 15.45.13: if `B` is Noetherian, then the fiber ring over a prime of `A` is
Noetherian. -/
private theorem fiber_isNoetherianRing
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [IsNoetherianRing B]
    (p : PrimeSpectrum A) : IsNoetherianRing (p.asIdeal.Fiber B) := by
  -- First give the tensor-model `B ⊗[A] κ(p)` its canonical Noetherian structure.
  let _ : Algebra.EssFiniteType B (B ⊗[A] p.asIdeal.ResidueField) := inferInstance
  let _ : IsNoetherianRing (B ⊗[A] p.asIdeal.ResidueField) :=
    Algebra.EssFiniteType.isNoetherianRing B (B ⊗[A] p.asIdeal.ResidueField)
  -- Then transport that structure across the standard tensor commutation equivalence.
  exact
    isNoetherianRing_of_ringEquiv (B ⊗[A] p.asIdeal.ResidueField)
      (Algebra.TensorProduct.comm A p.asIdeal.ResidueField B).toRingEquiv.symm

-- Proof sketch: Lemma `15.45.3` upgrades `R`-Noetherianity to `Rh`, the local tensor-product
-- instance above makes the fiber `p.asIdeal.Fiber Rh` Noetherian, and Lemma `15.45.12 (1)` then
-- applies directly to the filtered-colimit-of-étale owner `IsHenselizationOf.isFilteredColimitOfEtale`.
/-- For a Noetherian local ring `R`, a prime `p : Spec R`, and a chosen henselization `Rh` of
`R`, only finitely many primes of `Rh` lie over `p`. -/
theorem henselization_primesOver_finite
    (p : PrimeSpectrum R) :
    Finite (p.asIdeal.primesOver Rh) := by
  let _ : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  let _ : IsNoetherianRing (p.asIdeal.Fiber Rh) := fiber_isNoetherianRing R Rh p
  simpa using
    primesOver_finite_of_isFilteredColimitOfEtale_of_isNoetherianFiber
      IsHenselizationOf.isFilteredColimitOfEtale p

-- Proof sketch: the same owner data as above feed directly into Lemma `15.45.12 (2)`, whose
-- canonical map is already `p.asIdeal.fiberToPiResidueField Rh`.
/-- For a Noetherian local ring `R`, a prime `p : Spec R`, and a chosen henselization `Rh` of
`R`, the canonical map from the fiber ring `p.asIdeal.Fiber Rh` to the product of the residue
fields of the primes of `Rh` lying over `p` is bijective. -/
theorem fiberToPiResidueField_henselization_bijective
    (p : PrimeSpectrum R) :
    Function.Bijective (p.asIdeal.fiberToPiResidueField Rh) := by
  let _ : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  let _ : IsNoetherianRing (p.asIdeal.Fiber Rh) := fiber_isNoetherianRing R Rh p
  simpa using
    fiberToPiResidueField_bijective_of_isFilteredColimitOfEtale_of_isNoetherianFiber
      IsHenselizationOf.isFilteredColimitOfEtale p

-- Proof sketch: exactly as for henselizations, Lemma `15.45.3` first upgrades Noetherianity to
-- `Rsh`, then the local tensor-product owner gives Noetherianity of `p.asIdeal.Fiber Rsh`, and
-- Lemma `15.45.12 (1)` applies through `IsStrictHenselizationOf.isFilteredColimitOfEtale`.
/-- For a Noetherian local ring `R`, a prime `p : Spec R`, and a chosen strict henselization
`Rsh` of `R`, only finitely many primes of `Rsh` lie over `p`. -/
theorem strictHenselization_primesOver_finite
    (p : PrimeSpectrum R) :
    Finite (p.asIdeal.primesOver Rsh) := by
  let _ : IsNoetherianRing Rsh := isNoetherianRing_strictHenselization R Rsh
  let _ : IsNoetherianRing (p.asIdeal.Fiber Rsh) := fiber_isNoetherianRing R Rsh p
  simpa using
    primesOver_finite_of_isFilteredColimitOfEtale_of_isNoetherianFiber
      IsStrictHenselizationOf.isFilteredColimitOfEtale p

-- Proof sketch: apply the strict-henselization owner to the same generic fiber decomposition
-- theorem `15.45.12 (2)`.
/-- For a Noetherian local ring `R`, a prime `p : Spec R`, and a chosen strict henselization
`Rsh` of `R`, the canonical map from the fiber ring `p.asIdeal.Fiber Rsh` to the product of the
residue fields of the primes of `Rsh` lying over `p` is bijective. -/
theorem fiberToPiResidueField_strictHenselization_bijective
    (p : PrimeSpectrum R) :
    Function.Bijective (p.asIdeal.fiberToPiResidueField Rsh) := by
  let _ : IsNoetherianRing Rsh := isNoetherianRing_strictHenselization R Rsh
  let _ : IsNoetherianRing (p.asIdeal.Fiber Rsh) := fiber_isNoetherianRing R Rsh p
  simpa using
    fiberToPiResidueField_bijective_of_isFilteredColimitOfEtale_of_isNoetherianFiber
      IsStrictHenselizationOf.isFilteredColimitOfEtale p

end

section

open PrimeSpectrum

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-- Helper for Lemma 15.45.13: a henselization is weakly étale because it is a filtered colimit
of étale algebras over the base ring. -/
private theorem isWeaklyEtale_henselization : Algebra.IsWeaklyEtale R Rh := by
  -- Reuse the canonical filtered-colimit owner attached to a henselization.
  exact
    isWeaklyEtale_of_isFilteredColimitOfEtale IsHenselizationOf.isFilteredColimitOfEtale

/-- Helper for Lemma 15.45.13: a strict henselization is weakly étale because it is a filtered
colimit of étale algebras over the base ring. -/
private theorem isWeaklyEtale_strictHenselization : Algebra.IsWeaklyEtale R Rsh := by
  -- Reuse the canonical filtered-colimit owner attached to a strict henselization.
  exact
    isWeaklyEtale_of_isFilteredColimitOfEtale
      IsStrictHenselizationOf.isFilteredColimitOfEtale

-- Proof sketch: the residue-field statement is already a consequence of the canonical weakly
-- étale owner. A henselization is weakly étale because it is a filtered colimit of étale
-- `R`-algebras, so we reuse `residueField_isAlgebraic_and_separable_of_isWeaklyEtale` directly.
/-- For a prime of `Rh` lying over `p`, the induced residue field extension is algebraic and
separable over the residue field of `p`. -/
theorem henselization_residueField_isAlgebraic_and_separable
    (p : PrimeSpectrum R)
    (q : p.asIdeal.primesOver Rh) :
    Algebra.IsAlgebraic p.asIdeal.ResidueField q.1.ResidueField ∧
      Algebra.IsSeparable p.asIdeal.ResidueField q.1.ResidueField := by
  -- Install the weakly étale owner once, then invoke the general residue-field theorem.
  let _ : Algebra.IsWeaklyEtale R Rh := isWeaklyEtale_henselization (R := R) (Rh := Rh)
  simpa using
    residueField_isAlgebraic_and_separable_of_isWeaklyEtale p.asIdeal q

-- Proof sketch: the same weakly-étale owner argument applies to strict henselizations.
/-- For a prime of `Rsh` lying over `p`, the induced residue field extension is algebraic and
separable over the residue field of `p`. -/
theorem strictHenselization_residueField_isAlgebraic_and_separable
    (p : PrimeSpectrum R)
    (r : p.asIdeal.primesOver Rsh) :
    Algebra.IsAlgebraic p.asIdeal.ResidueField r.1.ResidueField ∧
      Algebra.IsSeparable p.asIdeal.ResidueField r.1.ResidueField := by
  -- Install the strict-henselization weakly étale owner once, then reuse the generic theorem.
  let _ : Algebra.IsWeaklyEtale R Rsh :=
    isWeaklyEtale_strictHenselization (R := R) (Rsh := Rsh)
  simpa using
    residueField_isAlgebraic_and_separable_of_isWeaklyEtale p.asIdeal r

end
