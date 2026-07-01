import Mathlib
import stacks_project.Chap10.Lemma_10_155_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} {Rh : Type u} {Sh : Type v}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Sh] [Algebra S Sh] [Algebra R Sh] [IsScalarTower R S Sh]
variable [IsHenselizationOf S Sh]

/- Domain-style sampling:
- primary domain: local commutative algebra of henselizations and their functoriality under local
  ring maps;
- sampled owner declarations of the same kind:
  `IsHenselizationOf`,
  `IsHenselizationOf.residueFieldEquiv`,
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`,
  `IsLocalRing.local_hom_TFAE`;
- best owner abstraction: this file is a `bridge/view` specialization of the Chapter 10 owner
  theorem `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`,
  with the henselization owners providing the primitive ind-étale and residue-field data;
- primitive data: the local base map `R → S` and the owner hypotheses
  `IsHenselizationOf R Rh`, `IsHenselizationOf S Sh`;
- derived API: the canonical comparison map `Rh →ₐ[R] Sh` and its locality.

Source/core/bridge triage:
- `source-facing`: the uniqueness statement for the comparison map between henselizations;
- `core/canonical`: `IsHenselizationOf`, `IsHenselizationOf.residueFieldEquiv`, and
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`;
- `bridge/view`: the induced comparison `henselizationMap`.
-/
-- Proof sketch: apply the universal property of the henselization `Rh` from Lemma `10.154.6` with
-- target `Sh`, using that `Sh` is henselian local by `IsHenselizationOf S Sh`. The required
-- residue-field map is the composite `ResidueField Rh ≃ ResidueField R → ResidueField S ≃
-- ResidueField Sh`, where the two equivalences come from the henselization structures and the
-- middle map comes from the given local homomorphism `R → S`. The uniqueness part of
-- `Lemma 10.154.6` then gives uniqueness of the local `R`-algebra map.
/-- Lemma 10.155.6: let `R → S` be a local map of local rings, and let `Rh` and `Sh` be
henselizations of `R` and `S`. Then there exists a unique `R`-algebra map `Rh → Sh`; equivalently,
there is a unique local ring map `Rh → Sh` fitting into the commutative square over `R → S`. -/
lemma existsUnique_algHom_between_henselizations_of_localHom
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra S Sh] [IsScalarTower R S Sh] [IsHenselizationOf S Sh] :
    ∃! f : Rh →ₐ[R] Sh, IsLocalHom (f : Rh →+* Sh) := sorry

/-- The canonical comparison map between henselizations induced by the local map `R → S`. -/
noncomputable abbrev henselizationMap
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra S Sh] [IsScalarTower R S Sh] [IsHenselizationOf S Sh] :
    Rh →ₐ[R] Sh :=
  Classical.choose <|
    ExistsUnique.exists <|
      existsUnique_algHom_between_henselizations_of_localHom
        (R := R) (S := S) (Rh := Rh) (Sh := Sh)

/-- The ring-hom view of the canonical comparison map between henselizations, with the ambient
`R`-algebra structure on `Sh` derived canonically from `R → S → Sh`. -/
noncomputable abbrev henselizationMapRingHom
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra S Sh] [IsHenselizationOf S Sh] :
    Rh →+* Sh :=
  let _ : Algebra R Sh :=
    RingHom.toAlgebra ((algebraMap S Sh).comp (algebraMap R S))
  let _ : IsScalarTower R S Sh :=
    IsScalarTower.of_algebraMap_eq' rfl
  (henselizationMap (R := R) (S := S) (Rh := Rh) (Sh := Sh)).toRingHom

/-- The canonical comparison map between henselizations is local. -/
theorem henselizationMap_isLocalHom
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra S Sh] [IsScalarTower R S Sh] [IsHenselizationOf S Sh] :
    IsLocalHom ((henselizationMap (R := R) (S := S) (Rh := Rh) (Sh := Sh) : Rh →ₐ[R] Sh).toRingHom) :=
  Classical.choose_spec <|
    ExistsUnique.exists <|
      existsUnique_algHom_between_henselizations_of_localHom
        (R := R) (S := S) (Rh := Rh) (Sh := Sh)

/-- The `Rh`-algebra structure on `Sh` induced by the canonical comparison map between
henselizations. -/
noncomputable abbrev henselizationMapAlgebra
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra S Sh] [IsScalarTower R S Sh] [IsHenselizationOf S Sh] :
    Algebra Rh Sh :=
  RingHom.toAlgebra
    (henselizationMap (R := R) (S := S) (Rh := Rh) (Sh := Sh)).toRingHom

end
