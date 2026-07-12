import StacksProject_2024.Chap10.Lemma_10_154_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open CommRingCat
open IsLocalRing
open RingHom

universe u v w

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/- Domain-style sampling:
* primary domain: local commutative algebra of filtered colimits of étale `R`-algebras and the
  induced residue-field extension on a local target;
* owner declarations inspected:
  - `CategoryTheory.MorphismProperty.ind`;
  - `CommRingCat.etale`;
  - `RingHom.IsFilteredColimitOfEtale`;
  - `RingHom.algebraMap_isFilteredColimitOfEtale_of_isColimit`;
  - `IsStrictHenselizationOf.isFilteredColimitOfEtale`;
  - `exists_flat_localAlgebra_with_residueField_equiv`.
* owner decision:
  - `source-facing`: the existence of a local `R`-algebra whose residue field realizes the given
    separable algebraic extension;
  - `core/canonical`: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
  - `bridge/view`: the hidden `ULift`-based same-universe presentation packaged by the source-facing
    owner `(algebraMap R R').IsFilteredColimitOfEtale`.

Primitive data are the local `R`-algebra itself, the locality of `R → R'`, and the owner-level
filtered-colimit-of-étale hypothesis. A chosen directed system of finite étale local stages is
derived bridge data, so it should not remain the main public output. Likewise the residue-field
comparison should be a direct existential `AlgEquiv` over `ResidueField R`, not a `Nonempty`
wrapper. The witness ring should range over the same ambient universe as in
`exists_flat_localAlgebra_with_residueField_equiv`, namely `Type (max u w)`. The universe-lift
needed to express the canonical owner should stay inside the owner wrapper rather than appearing in
the public theorem statement.
-/

variable (R)

-- Proof sketch: start from the flat local extension `R → R'` with residue field `K` from
-- Lemma `10.159.1`. Because `K / ResidueField R` is separable algebraic, the construction may be
-- arranged so that every finite subset of `R'` lies in a finite étale local `R`-subalgebra.
-- Those stages yield a filtered colimit presentation of `R'` by étale `R`-algebras. The chapter
-- owner `(algebraMap R R').IsFilteredColimitOfEtale` packages the same-universe `CommRingCat`
-- presentation internally, so the public statement can stay source-facing. The induced
-- residue-field comparison is then best expressed directly as a `ResidueField R`-algebra
-- equivalence.
/-- Lemma 10.159.2: for a separable algebraic extension `K / ResidueField R`, there exists a
local `R`-algebra `R'` such that `R → R'` is a local map, `R'` is a filtered colimit of étale
`R`-algebras, and the residue field of `R'` is isomorphic to `K` over `ResidueField R`. -/
theorem exists_filteredColimitOfEtale_localAlgebra_with_residueField_equiv
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K] :
    ∃ (R' : Type (max u w)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R'))
      (e : ResidueField R' ≃ₐ[ResidueField R] K),
      (algebraMap R R').IsFilteredColimitOfEtale := sorry

end
