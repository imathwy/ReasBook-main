import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open RingHom
open Topology

universe u

/- Domain-style sampling:
- primary domain: quasi-finite finite-type morphisms in affine algebraic geometry;
- sampled owner declarations:
  `Algebra.QuasiFiniteAt`,
  `Scheme.Hom.QuasiFiniteAt`,
  `Scheme.arrowStalkMapSpecIso`,
  `Scheme.Hom.isOpen_quasiFiniteAt`;
- source-facing layer: the textbook affine statement that the quasi-finite locus in `Spec(S)` is
  open for a finite type algebra `R → S`;
- core/canonical owner: `Scheme.Hom.isOpen_quasiFiniteAt` for scheme morphisms, together with the
  affine-point owner `Scheme.Hom.QuasiFiniteAt`;
- bridge/view: the comparison below identifying `Scheme.Hom.QuasiFiniteAt` on
  `Spec.map (algebraMap R S)` with the ring-theoretic owner `Algebra.QuasiFiniteAt R q.asIdeal`.

Primitive data are only the finite-type algebra structure and the owner predicate
`Algebra.QuasiFiniteAt`. The openness statement itself belongs to the scheme-level owner
`Scheme.Hom.isOpen_quasiFiniteAt`, so this file should stay a thin affine bridge rather than
introducing any parallel local quasi-finite-locus wrapper.
-/

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

omit [Algebra.FiniteType R S] in
/-- Affine bridge: for `Spec(S) → Spec(R)`, the scheme-theoretic pointwise quasi-finite predicate
agrees with the ring-theoretic owner `Algebra.QuasiFiniteAt` at the corresponding prime of `S`. -/
lemma specMap_quasiFiniteAt_iff (q : PrimeSpectrum S) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).QuasiFiniteAt q ↔
      Algebra.QuasiFiniteAt R q.asIdeal := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  change (CommRingCat.Hom.hom ((Spec.map φ).stalkMap q)).QuasiFinite ↔ _
  rw [QuasiFinite.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ q)]
  have hloc :
      (algebraMap R (Localization.AtPrime (Ideal.comap (algebraMap R S) q.asIdeal))).QuasiFinite := by
    rw [RingHom.quasiFinite_algebraMap]
    exact .of_isLocalization (Ideal.comap (algebraMap R S) q.asIdeal).primeCompl
  trans ((Localization.localRingHom (Ideal.comap (algebraMap R S) q.asIdeal) q.asIdeal
      (algebraMap R S) rfl).comp
      (algebraMap R (Localization.AtPrime (Ideal.comap (algebraMap R S) q.asIdeal)))).QuasiFinite
  · exact (RingHom.QuasiFinite.comp_iff hloc).symm
  · have hcomp :
        (Localization.localRingHom (Ideal.comap (algebraMap R S) q.asIdeal) q.asIdeal
          (algebraMap R S) rfl).comp
          (algebraMap R (Localization.AtPrime (Ideal.comap (algebraMap R S) q.asIdeal))) =
          algebraMap R (Localization.AtPrime q.asIdeal) := by
        ext x
        simp [Localization.localRingHom_to_map]
        simpa using
          (IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.asIdeal) x).symm
    simp [hcomp, RingHom.quasiFinite_algebraMap]

/-- Lemma 10.123.13: for a finite type ring map `R → S`, the subset of `Spec(S)` consisting of the
points where `R → S` is quasi-finite is open. -/
-- Proof sketch: start with a prime `q` where `R → S` is quasi-finite. Apply Zariski's main
-- theorem to obtain an element of the integral closure away from `q` such that after localizing,
-- `S` agrees with an integral algebra over `R`. Replace that integral algebra by a finite
-- `R`-subalgebra after shrinking to a basic open neighborhood, use that finite algebras are
-- quasi-finite, and conclude that the whole basic open neighborhood lies in the quasi-finite locus.
@[stacks 00QA]
theorem isOpen_setOf_quasiFiniteAt :
    IsOpen { q : PrimeSpectrum S | Algebra.QuasiFiniteAt R q.asIdeal } := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  have hft : LocallyOfFiniteType (Spec.map φ) := by
    refine HasRingHomProperty.Spec_iff.mpr ?_
    change (algebraMap R S).FiniteType
    rw [RingHom.finiteType_algebraMap]
    infer_instance
  letI : LocallyOfFiniteType (Spec.map φ) := hft
  have hopen : IsOpen { q : PrimeSpectrum S | (Spec.map φ).QuasiFiniteAt q } :=
    (Spec.map φ).isOpen_quasiFiniteAt
  convert hopen using 1
  ext q
  change Algebra.QuasiFiniteAt R q.asIdeal ↔ (Spec.map φ).QuasiFiniteAt q
  simpa [φ] using (specMap_quasiFiniteAt_iff q).symm

end
