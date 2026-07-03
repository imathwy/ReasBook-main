import Mathlib
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Henselian

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_155_1 (from Chap10) -/
open IsLocalRing

universe u

section

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable (S : Type u) [CommRing S] [Algebra R S]

/-
Domain-style sampling:
- primary domain: henselian local rings and henselization maps of local rings;
- sampled owner declarations of the same kind:
  `HenselianLocalRing`,
  `IsLocalHom`,
  `RingHom.IsFilteredColimitOfEtale`,
  `RingHom.algebraMap_isFilteredColimitOfEtale_of_isColimit`;
- best owner abstraction: there is no upstream bundled henselization owner in mathlib, so the
  source-facing owner here should be the class `IsHenselizationOf R S`, assembled from the
  canonical owners for henselianity, locality, and filtered-colimit-of-étale presentation;
- primitive data: the henselian local target, the local structural map, the filtered-colimit-of-
  étale presentation, the maximal-ideal image equality, and bijectivity on residue fields;
- derived API: the canonical residue-field equivalence induced by the structural map.

Source/core/bridge triage:
- `source-facing`: `IsHenselizationOf` and `exists_henselization`;
- `core/canonical`: `HenselianLocalRing`, `IsLocalHom`, and `RingHom.IsFilteredColimitOfEtale`;
- `bridge/view`: `IsHenselizationOf.residueFieldEquiv`.
-/
/-- An `R`-algebra `S` is a henselization of the local ring `R` if `R → S` is a local map, `S` is
henselian, `S` is a filtered colimit of étale `R`-algebras, the maximal ideal of `S` is the image
of the maximal ideal of `R`, and the induced residue-field map is bijective. -/
class IsHenselizationOf : Prop extends HenselianLocalRing S, IsLocalHom (algebraMap R S) where
  isFilteredColimitOfEtale :
    (algebraMap R S).IsFilteredColimitOfEtale
  map_maximalIdeal :
    Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S
  residueField_bijective :
    Function.Bijective (ResidueField.map (algebraMap R S))

namespace IsHenselizationOf

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {S : Type u} [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- The canonical residue-field isomorphism induced by a henselization. -/
noncomputable def residueFieldEquiv : ResidueField R ≃+* ResidueField S :=
  RingEquiv.ofBijective (ResidueField.map (algebraMap R S))
    IsHenselizationOf.residueField_bijective

end IsHenselizationOf

-- Proof sketch: define `Rʰ` as the filtered colimit of étale local `R`-algebras whose residue
-- field over `ResidueField R` is unchanged. The filtered-colimit-of-étale property is built into
-- the construction, the local and maximal-ideal statements come from the unique prime over the
-- closed point, the residue-field map is the canonical colimit identification, and henselianity
-- follows by descending a monic polynomial with a simple residue-field root to some étale stage
-- and lifting that root there.
/-- Lemma 10.155.1: every local ring admits a henselization `R → Rʰ`, namely a local map to a
henselian local ring that is a filtered colimit of étale `R`-algebras, whose maximal ideal is the
image of `maximalIdeal R`, and whose residue field agrees with `ResidueField R`. -/
theorem exists_henselization :
    ∃ (Rh : Type u) (_ : CommRing Rh) (_ : Algebra R Rh), IsHenselizationOf R Rh := sorry

end

/-! ### Lemma_10_155_2 (from Chap10) -/
open CategoryTheory MorphismProperty
open CommRingCat
open IsLocalRing
open RingHom

universe u

section

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable (S : Type u) [CommRing S] [Algebra R S]

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations and strict henselizations;
- sampled owner declarations of the same kind:
  `StrictHenselianLocalRing`,
  `IsLocalHom`,
  `RingHom.IsFilteredColimitOfEtale`,
  `IsHenselizationOf`;
- best owner abstraction: there is no upstream bundled strict-henselization owner in mathlib, so
  the source-facing owner here is `IsStrictHenselizationOf R S`, built from the canonical owners
  above;
- primitive data: strict henselianity of the target, locality of `R → S`, the filtered-colimit-
  of-étale presentation, and the maximal-ideal image equality;
- derived API: any choice of henselization-to-strict-henselization comparison map and any chosen
  residue-field identification with a separable closure.

Source/core/bridge triage:
- `source-facing`: `IsStrictHenselizationOf` and
  `exists_henselization_to_strictHenselization`;
- `core/canonical`: `StrictHenselianLocalRing`, `IsLocalHom`, and
  `RingHom.IsFilteredColimitOfEtale`;
- `bridge/view`: `exists_strictHenselization`, which forgets the auxiliary chosen separable-closure
  identification and keeps only the strict-henselization owner.
-/
/-- A strict henselization of the local ring `R` is an `R`-algebra `S` for which `R → S` is a
local map, `S` is strictly henselian, `S` is a filtered colimit of étale `R`-algebras, and the
maximal ideal of `S` is the image of the maximal ideal of `R`. -/
class IsStrictHenselizationOf : Prop extends StrictHenselianLocalRing S,
    IsLocalHom (algebraMap R S) where
  isFilteredColimitOfEtale :
    (algebraMap R S).IsFilteredColimitOfEtale
  map_maximalIdeal :
    Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S

variable (Ksep : Type u) [Field Ksep] [Algebra (ResidueField R) Ksep]
variable [IsSepClosure (ResidueField R) Ksep]

-- Proof sketch: repeat the filtered-colimit construction of the henselization, but index stages
-- by triples `(S, 𝔮, α)` where `R → S` is étale, `𝔮` lies over `maximalIdeal R`, and `α`
-- embeds the stage residue field into `Ksep`. The colimit then carries compatible maps from both
-- a henselization `Rʰ` and the chosen separable closure of the residue field, while
-- `Lemma 10.154.8` and `Definition 10.153.1` give strict henselianity from the separably closed
-- residue field.
/-- Lemma 10.155.2: given a separable closure `Ksep` of the residue field of a local ring `R`,
there exist a henselization `Rʰ` of `R`, a strict henselization `Rˢʰ` of `R`, a local map
`Rʰ → Rˢʰ`, and a residue-field isomorphism from `ResidueField Rˢʰ` to `Ksep` compatible with the
canonical map from `ResidueField R`. -/
theorem exists_henselization_to_strictHenselization :
    ∃ (Rh : Type u) (_ : CommRing Rh) (_ : Algebra R Rh) (_ : IsHenselizationOf R Rh)
      (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra R Rsh)
      (_ : IsStrictHenselizationOf R Rsh) (_ : Algebra Rh Rsh) (_ : IsScalarTower R Rh Rsh)
      (_ : IsLocalHom (algebraMap Rh Rsh)) (φ : ResidueField Rsh ≃+* Ksep),
      φ.toRingHom.comp (ResidueField.map (algebraMap R Rsh)) =
        algebraMap (ResidueField R) Ksep := sorry

-- Proof sketch: apply Lemma `10.155.2` with the canonical separable closure
-- `SeparableClosure (ResidueField R)` and discard the auxiliary henselization and residue-field
-- comparison data. The strict-henselization owner is the primitive public output.
/-- Every local ring admits a strict henselization. This is the owner-level existence theorem
obtained from Lemma `10.155.2` by choosing the canonical separable closure of the residue field
and forgetting the auxiliary comparison data. -/
theorem exists_strictHenselization :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra R Rsh), IsStrictHenselizationOf R Rsh := by
  let Ksep := SeparableClosure (ResidueField R)
  let _ : Field Ksep := inferInstance
  let _ : Algebra (ResidueField R) Ksep := inferInstance
  let _ : IsSepClosure (ResidueField R) Ksep := inferInstance
  obtain ⟨_, _, _, _, Rsh, _, _, hRsh, _, _, _, _, _⟩ :=
    exists_henselization_to_strictHenselization R Ksep
  exact ⟨Rsh, inferInstance, inferInstance, hRsh⟩

end

/-! ### Definition_10_155_3 (from Chap10) -/
/-
Domain-style sampling pass for Definition 10.155.3.

Primary domain: local commutative algebra of henselizations and strict henselizations.

Sampled owner declarations:
* `HenselianLocalRing`;
* `StrictHenselianLocalRing`;
* `IsHenselizationOf`;
* `IsStrictHenselizationOf`.

Owner abstraction: the source-facing owners for this item already exist upstream in the chapter as
`IsHenselizationOf` and `IsStrictHenselizationOf`, built from the canonical local-ring owners
above. This file should therefore be recall-only, not a second wrapper layer.

Primitive data vs derived API:
* primitive owner data live in `IsHenselizationOf` and `IsStrictHenselizationOf`;
* existence theorems and residue-field comparison maps are derived API in
  `Lemma_10_155_1` and `Lemma_10_155_2`.

Source/core/bridge triage:
* source-facing: `IsHenselizationOf`, `IsStrictHenselizationOf`;
* core/canonical: `HenselianLocalRing`, `StrictHenselianLocalRing`, `IsLocalHom`,
  `RingHom.IsFilteredColimitOfEtale`;
* bridge/view: the existence theorems and residue-field comparison data attached to those owners.
-/

/- Definition 10.155.3: the henselization of a local ring is the canonical project notion
`IsHenselizationOf R S`, expressing that the local map `R → S` constructed in Lemma 10.155.1 is a
henselian local étale-neighborhood colimit with unchanged residue field. -/
#check IsHenselizationOf

/- Companion recall: the strict henselization of a local ring is the canonical project notion
`IsStrictHenselizationOf R S`, expressing the local maps produced in Lemma 10.155.2 after choosing
a separable closure of the residue field. -/
#check IsStrictHenselizationOf

/-! ### Remark_10_155_4 (from Chap10) -/
open IsLocalRing

universe u

section

variable {R : Type u} {Rh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

/-
Domain-style sampling pass for Remark 10.155.4.

Primary domain: local commutative algebra of henselizations, strict henselizations, and residue-
field comparison maps.

Sampled owner declarations:
* `IsHenselizationOf`;
* `IsHenselizationOf.residueFieldEquiv`;
* `IsStrictHenselizationOf`;
* `exists_henselization_to_strictHenselization`.

Best owner abstraction:
* source-facing owner data already live in `IsStrictHenselizationOf`;
* the chosen residue-field identification belongs to the bridge theorem
  `exists_henselization_to_strictHenselization`;
* the fact that a strict henselization over a henselization is again a strict henselization of the
  base is derived API and should not stay bundled as primitive existential data.

Primitive data vs. derived API:
* primitive data: a strict henselization of `Rh` together with the chosen residue-field
  identification with `Ksep`;
* derived API: the resulting `R`-algebra is also a strict henselization of `R`.

Source/core/bridge triage:
* `source-facing`: `exists_strictHenselization_of_henselization`;
* `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`,
  `IsHenselizationOf.residueFieldEquiv`, `exists_henselization_to_strictHenselization`;
* `bridge/view`: `strictHenselization_over_henselization_isStrictHenselizationOf`.
-/

-- Proof sketch: transport the filtered-colimit-of-étale and maximal-ideal conditions from
-- `Rh → Rsh` back along the henselization map `R → Rh`, and obtain strict henselianity of `Rsh`
-- over `R` from the same underlying local ring together with the unchanged separably closed
-- residue field.
/-- A strict henselization over a henselization is again a strict henselization of the base local
ring. This is the owner-level bridge behind Remark 10.155.4. -/
theorem strictHenselization_over_henselization_isStrictHenselizationOf
    {Rsh : Type u} [CommRing Rsh] [Algebra Rh Rsh] [Algebra R Rsh] [IsScalarTower R Rh Rsh]
    [IsStrictHenselizationOf Rh Rsh] :
    IsStrictHenselizationOf R Rsh := sorry

variable {Ksep : Type u}
variable [Field Ksep] [Algebra (ResidueField R) Ksep] [IsSepClosure (ResidueField R) Ksep]

-- Proof sketch: transport the chosen separable closure `Ksep` of `ResidueField R` across the
-- canonical residue-field isomorphism of the henselization `Rh`, then apply the strict
-- henselization existence theorem to `Rh`. The resulting `Rh`-algebra is strictly henselian with
-- residue field `Ksep`; viewed as an `R`-algebra through `R → Rh`, it is still a filtered colimit
-- of étale `R`-algebras, so Lemma `10.154.7` identifies it with the strict henselization of `R`.
/-- Remark 10.155.4: starting from a henselization `R → Rh` and a chosen separable closure `Ksep`
of `ResidueField R`, one can construct a strict henselization over `Rh`; the resulting `Rh`-algebra
has residue field identified with `Ksep` over `ResidueField R`. The companion theorem
`strictHenselization_over_henselization_isStrictHenselizationOf` records that the same `Rh`-algebra
is also a strict henselization of `R`. -/
theorem exists_strictHenselization_of_henselization :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra Rh Rsh)
      (_ : IsStrictHenselizationOf Rh Rsh) (ι : ResidueField Rsh ≃+* Ksep),
      ι.toRingHom.comp
          (ResidueField.map ((algebraMap Rh Rsh).comp (algebraMap R Rh))) =
        algebraMap (ResidueField R) Ksep := sorry

end

/-! ### Lemma_10_155_5 (from Chap10) -/
universe u v w

open IsLocalRing

section

variable {R : Type u} (S : Type v) {Sh : Type v} {A : Type w}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
variable [CommRing Sh] [Algebra S Sh] [Algebra R Sh] [IsScalarTower R S Sh]
variable [IsHenselizationOf S Sh]
variable [CommRing A] [Algebra R A] [Algebra.Etale R A]

/- Domain-style sampling:
- primary domain: henselian local targets, henselization owners, and étale lifting of local
  points controlled by residue fields;
- sampled owner declarations of the same kind:
  `IsHenselizationOf`,
  `Ideal.ResidueField.map`,
  `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap`,
  `IsHenselizationOf.residueFieldEquiv`;
- best owner abstraction: `Lemma_10_153_11` is the core lifting owner, while the present lemma is
  a `source-facing` specialization in which the target henselian local ring is a henselization of
  `S`, and the source-side residue-field input should be the primitive canonical map
  `κ(maximalIdeal R) → κ(q)` together with its bijectivity, not a separately chosen ring
  equivalence;
- primitive data: the étale `R`-algebra `A`, the prime `q`, the contraction condition
  `q.under R = maximalIdeal R`, and bijectivity of the canonical residue-field map
  `κ(maximalIdeal R) → κ(q)`;
- derived API: the unique `R`-algebra map `A → Sh`, with the inverse-image condition on
  `maximalIdeal Sh`, and the companion `κ`-based reformulation obtained by upgrading the bijective
  canonical map to a ring equivalence.

Source/core/bridge triage:
- `source-facing`: the present source-specialized henselization lifting statement;
- `core/canonical`: `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap`;
- `bridge/view`: the chosen ring equivalence version of the residue-field hypothesis, which is
  derived from bijectivity of the canonical map and retained only as a thin companion surface.
-/
-- Proof sketch: apply `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap` with
-- target `Sh`. Since `Sh` is henselian local, it suffices to supply the residue-field map
-- required by Lemma `10.153.11`. The source hypothesis gives that the canonical map
-- `κ(maximalIdeal R) → κ(q)` is bijective, so it can be inverted to identify `κ(q)` with the
-- common source residue field and compared with the canonical residue-field map into `Sh`.
/-- Lemma 10.155.5: if `R → S` is a local map of local rings, `Sh` is a henselization of `S`,
`R → A` is étale, and `q` is a prime of `A` over `maximalIdeal R` such that the canonical map
`κ(maximalIdeal R) → κ(q)` is bijective, then there is a unique `R`-algebra map `A → Sh` whose
inverse image of `maximalIdeal Sh` is `q`. -/
lemma existsUnique_algHom_to_henselization_of_etale_of_residueFieldMap_bijective
    (q : Ideal A) [q.IsPrime] (hq : q.under R = maximalIdeal R)
    (hκ : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hq.symm)) :
    ∃! f : A →ₐ[R] Sh,
      q = Ideal.comap (f : A →+* Sh) (maximalIdeal Sh) := by
  sorry

/-- Thin bridge/view companion: a chosen ring equivalence identifying `κ(maximalIdeal R)` with
`κ(q)` through the canonical map also suffices. -/
lemma existsUnique_algHom_to_henselization_of_etale_of_residueFieldEquiv
    (q : Ideal A) [q.IsPrime] (hq : q.under R = maximalIdeal R)
    (κ : (maximalIdeal R).ResidueField ≃+* q.ResidueField)
    (hκ : κ.toRingHom = Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hq.symm) :
    ∃! f : A →ₐ[R] Sh,
      q = Ideal.comap (f : A →+* Sh) (maximalIdeal Sh) := by
  let hbij :
      Function.Bijective (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hq.symm) := by
    rw [← hκ]
    exact κ.bijective
  simpa using
    existsUnique_algHom_to_henselization_of_etale_of_residueFieldMap_bijective S q hq hbij

end

/-! ### Lemma_10_155_6 (from Chap10) -/
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

/-! ### Lemma_10_155_7 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing

universe u

section

variable {R : Type u} [CommRing R]
variable (p : Ideal R) [p.IsPrime]

open RingHom

/- Domain-style sampling:
* primary domain: local commutative algebra of henselizations of `Localization.AtPrime p`,
  expressed through filtered colimits of étale neighborhoods with fixed residue field `κ(p)`;
* sampled owner declarations of the same kind:
  - `RingHom.IsFilteredColimitOfEtale`;
  - `IsHenselizationOf`;
  - `selectedAlgebrasOverTargetDiagram`;
  - `CommAlgCat.of`.
* best owner abstraction:
  - `source-facing`: the category of étale neighborhoods `(S, q)` of `p` with residue field
    identified with `κ(p)`, together with its canonical source diagram in `CommAlgCat R` and its
    localized diagram in `CommAlgCat (Localization.AtPrime p)`;
  - `core/canonical`: the owner property
    `(algebraMap (Localization.AtPrime p) Rh).IsFilteredColimitOfEtale`;
  - `bridge/view`: colimit comparisons from those source-facing diagrams to a chosen
    henselization `Rh`.
* primitive data:
  - the pointed over-category `Over (CommAlgCat.of R p.ResidueField)`;
  - the étale object property on that over-category;
  - the canonical source diagram and the localized `Localization.AtPrime p`-algebra diagram.
* derived API:
  - the filteredness of the neighborhood category;
  - the colimit realizations of those two diagrams by a chosen henselization.

This file should therefore keep the neighborhood diagrams as source-facing input data, but the main
henselization outputs should prove those diagrams realize the henselization colimit in the ambient
algebra categories, leaving the owner property itself to `IsHenselizationOf`.
-/

/-- The over-category of `R`-algebras equipped with a chosen `R`-algebra map to `κ(p)`. Such a
map packages a prime over `p` with residue field `κ(p)`. -/
abbrev ResidueFieldPointedAlgebraCategory (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :=
  Over (CommAlgCat.of R p.ResidueField)

/-- The object property selecting those `R`-algebras over `κ(p)` whose structure map from `R` is
étale. -/
abbrev etaleResidueFieldPointedAlgebraProperty (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] :
    ObjectProperty (ResidueFieldPointedAlgebraCategory R p) :=
  fun A ↦ RingHom.Etale (algebraMap R A.left)

/-- The category of étale neighborhoods of `p` with residue field identified with `κ(p)`. -/
abbrev EtaleResidueFieldNeighborhoodCategory (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] :=
  (etaleResidueFieldPointedAlgebraProperty R p).FullSubcategory

/-- The diagram sending an étale neighborhood `(S, q)` of `p` to its underlying `R`-algebra `S`. -/
abbrev etaleResidueFieldNeighborhoodSourceDiagram (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] :
    EtaleResidueFieldNeighborhoodCategory R p ⥤ CommAlgCat R :=
  selectedAlgebrasOverTargetDiagram (etaleResidueFieldPointedAlgebraProperty R p)

/-- The structure map from an object over `κ(p)` to the fixed target object of the over-category. -/
private noncomputable abbrev residueFieldPointedAlgebraToResidueField
    (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] (A : ResidueFieldPointedAlgebraCategory R p) :
    A.left →+* p.ResidueField :=
  let φ := (forget₂ (CommAlgCat R) CommRingCat).map A.hom
  φ.hom

/-- The underlying ring homomorphism of a morphism over `κ(p)`. -/
private abbrev residueFieldPointedAlgebraHom (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    {A B : ResidueFieldPointedAlgebraCategory R p} (f : A ⟶ B) :
    A.left →+* B.left :=
  let φ := f.left
  φ.hom

/-- The underlying ring homomorphism of a morphism in the full subcategory of étale
neighborhoods. -/
private abbrev etaleResidueFieldNeighborhoodHom (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] {A B : EtaleResidueFieldNeighborhoodCategory R p} (f : A ⟶ B) :
    A.obj.left →+* B.obj.left :=
  residueFieldPointedAlgebraHom R p f.hom

/-- The prime ideal of an object over `κ(p)` is the kernel of its structure map to the fixed
target object. -/
private noncomputable abbrev residueFieldPointedAlgebraKernel
    (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] (A : ResidueFieldPointedAlgebraCategory R p) :
    Ideal A.left :=
  RingHom.ker (residueFieldPointedAlgebraToResidueField R p A)

-- Proof sketch: for a morphism of objects over `κ(p)`, the defining commutative triangle says that
-- the two maps to `κ(p)` agree after precomposition with the underlying algebra map. Taking kernels
-- gives the required equality of primes.
/-- The chosen prime of the source object is the comap of the chosen prime of the target. -/
private theorem residueFieldPointedAlgebraKernel_comap (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime]
    {A B : ResidueFieldPointedAlgebraCategory R p} (f : A ⟶ B) :
    residueFieldPointedAlgebraKernel R p A =
      Ideal.comap (residueFieldPointedAlgebraHom R p f) (residueFieldPointedAlgebraKernel R p B) :=
  sorry

/-- The kernel of a morphism to the residue field `κ(p)` is a prime ideal. -/
private instance residueFieldPointedAlgebraKernel_isPrime (A : ResidueFieldPointedAlgebraCategory R p) :
    (residueFieldPointedAlgebraKernel R p A).IsPrime :=
  RingHom.ker_isPrime _

-- Proof sketch: the structural map `A.left → κ(p)` is an `R`-algebra map, so its composite with
-- `R → A.left` is the canonical residue map `R → κ(p)`. Taking kernels identifies the chosen
-- prime of `A` with the extension of `p`.
/-- The chosen prime of an object over `κ(p)` lies over `p`. -/
private theorem residueFieldPointedAlgebraKernel_comap_algebraMap
    (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] (A : ResidueFieldPointedAlgebraCategory R p) :
    p = Ideal.comap (algebraMap R A.left) (residueFieldPointedAlgebraKernel R p A) :=
  sorry

/-- The canonical `R_p`-algebra map to the localization of an étale neighborhood at its chosen
prime. -/
private noncomputable abbrev etaleResidueFieldNeighborhoodLocalizationAlgebraMap
    (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] (A : EtaleResidueFieldNeighborhoodCategory R p) :
    Localization.AtPrime p →+* Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) :=
  Localization.localRingHom
    p
    (residueFieldPointedAlgebraKernel R p A.obj)
    (algebraMap R A.obj.left)
    (residueFieldPointedAlgebraKernel_comap_algebraMap R p A.obj)

-- Proof sketch: the identity morphism in the over-category induces the identity map on local
-- rings because both maps agree on the image of the source ring, and `Localization.localRingHom`
-- is uniquely determined by that property.
/-- The localization map induced by an identity morphism is the identity. -/
private theorem residueFieldPointedAlgebraLocalization_map_id (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime]
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    Localization.localRingHom
        (residueFieldPointedAlgebraKernel R p A.obj)
        (residueFieldPointedAlgebraKernel R p A.obj)
        (RingHom.id A.obj.left)
        (residueFieldPointedAlgebraKernel_comap R p (𝟙 A.obj)) =
      RingHom.id _ := sorry

-- Proof sketch: both sides are local ring maps from the localization of the source to the
-- localization of the target induced by the same composite algebra map. They agree on the image of
-- the source ring, so uniqueness of `Localization.localRingHom` identifies them.
/-- Localization along a composite morphism agrees with the composite of the localization maps. -/
private theorem residueFieldPointedAlgebraLocalization_map_comp (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime]
    {A B C : EtaleResidueFieldNeighborhoodCategory R p} (f : A ⟶ B) (g : B ⟶ C) :
    Localization.localRingHom
        (residueFieldPointedAlgebraKernel R p A.obj)
        (residueFieldPointedAlgebraKernel R p C.obj)
        ((etaleResidueFieldNeighborhoodHom R p g).comp (etaleResidueFieldNeighborhoodHom R p f))
        (residueFieldPointedAlgebraKernel_comap R p (f.hom ≫ g.hom)) =
      (Localization.localRingHom
          (residueFieldPointedAlgebraKernel R p B.obj)
          (residueFieldPointedAlgebraKernel R p C.obj)
          (etaleResidueFieldNeighborhoodHom R p g)
          (residueFieldPointedAlgebraKernel_comap R p g.hom)).comp
        (Localization.localRingHom
          (residueFieldPointedAlgebraKernel R p A.obj)
          (residueFieldPointedAlgebraKernel R p B.obj)
          (etaleResidueFieldNeighborhoodHom R p f)
          (residueFieldPointedAlgebraKernel_comap R p f.hom)) := sorry

-- Proof sketch: both sides are local ring maps from `R_p` to `T_r`, induced by the same composite
-- `R → S → T`, and they agree on the image of `R`, so uniqueness of `Localization.localRingHom`
-- identifies them.
/-- The transition maps in the localized neighborhood diagram are `R_p`-algebra maps. -/
private theorem etaleResidueFieldNeighborhoodLocalization_map_commutes
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    {A B : EtaleResidueFieldNeighborhoodCategory R p} (f : A ⟶ B) :
    (Localization.localRingHom
        (residueFieldPointedAlgebraKernel R p A.obj)
        (residueFieldPointedAlgebraKernel R p B.obj)
        (etaleResidueFieldNeighborhoodHom R p f)
        (residueFieldPointedAlgebraKernel_comap R p f.hom)).comp
      (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A) =
        etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p B :=
  sorry

/-- The localized neighborhood diagram sending `(S, q)` to the `R_p`-algebra `S_q`. -/
private noncomputable abbrev etaleResidueFieldNeighborhoodLocalizationObject
    (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] (A : EtaleResidueFieldNeighborhoodCategory R p) :
    CommAlgCat (Localization.AtPrime p) :=
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
    RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
  CommAlgCat.of (Localization.AtPrime p)
    (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))

/-- The induced `R_p`-algebra map on localized neighborhoods. -/
private noncomputable abbrev etaleResidueFieldNeighborhoodLocalizationMorphism
    (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] {A B : EtaleResidueFieldNeighborhoodCategory R p} (f : A ⟶ B) :
    etaleResidueFieldNeighborhoodLocalizationObject R p A ⟶
      etaleResidueFieldNeighborhoodLocalizationObject R p B :=
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
    RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p B.obj)) :=
    RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p B)
  CommAlgCat.ofHom <|
    { toRingHom :=
        Localization.localRingHom
          (residueFieldPointedAlgebraKernel R p A.obj)
          (residueFieldPointedAlgebraKernel R p B.obj)
          (etaleResidueFieldNeighborhoodHom R p f)
          (residueFieldPointedAlgebraKernel_comap R p f.hom)
      commutes' := by
        intro x
        exact congrArg (fun g : Localization.AtPrime p →+*
            Localization.AtPrime (residueFieldPointedAlgebraKernel R p B.obj) ↦ g x)
          (etaleResidueFieldNeighborhoodLocalization_map_commutes R p f) }

/-- The diagram sending an étale neighborhood `(S, q)` of `p` to the localized `R_p`-algebra
`S_q`. -/
noncomputable def etaleResidueFieldNeighborhoodLocalizationDiagram (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] :
    EtaleResidueFieldNeighborhoodCategory R p ⥤ CommAlgCat (Localization.AtPrime p) where
  obj A := etaleResidueFieldNeighborhoodLocalizationObject R p A
  map f := etaleResidueFieldNeighborhoodLocalizationMorphism R p f
  map_id A := by
    apply CommAlgCat.hom_ext
    exact DFunLike.ext _ _ fun x ↦
      congrArg
        (fun g : Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) →+*
            Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) ↦ g x)
        (residueFieldPointedAlgebraLocalization_map_id R p A)
  map_comp {A B C} f g := by
    apply CommAlgCat.hom_ext
    exact DFunLike.ext _ _ fun x ↦
      congrArg
        (fun h : Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) →+*
            Localization.AtPrime (residueFieldPointedAlgebraKernel R p C.obj) ↦ h x)
        (residueFieldPointedAlgebraLocalization_map_comp R p f g)

private noncomputable abbrev etaleResidueFieldNeighborhoodSourceHenselizationPoint
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh] :
    CommAlgCat R :=
  let _ : Algebra R Rh :=
    RingHom.toAlgebra <|
      (algebraMap (Localization.AtPrime p) Rh).comp (algebraMap R (Localization.AtPrime p))
  CommAlgCat.of R Rh

/-- The localization `S_q` of an étale residue-field neighborhood is étale over `R_p`. -/
private theorem etaleResidueFieldNeighborhoodLocalization_etale
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
      RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
    Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) := by
  sorry

/-- The maximal ideal of `S_q` lies over the maximal ideal of `R_p`. -/
private theorem etaleResidueFieldNeighborhoodLocalization_maximalIdeal_under
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
      RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
    (maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))).under
      (Localization.AtPrime p) =
      maximalIdeal (Localization.AtPrime p) := by
  sorry

/-- The localization `S_q` has the same residue field as `R_p`, through the canonical
residue-field map. -/
private noncomputable def etaleResidueFieldNeighborhoodLocalization_residueFieldEquiv
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    (maximalIdeal (Localization.AtPrime p)).ResidueField ≃+*
      (maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))).ResidueField :=
  RingEquiv.ofBijective
    (Ideal.ResidueField.map
      (maximalIdeal (Localization.AtPrime p))
      (maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)))
      (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
      (etaleResidueFieldNeighborhoodLocalization_maximalIdeal_under p A).symm)
    (by
      sorry)

/-- The localized residue-field equivalence is the equivalence attached to the canonical
residue-field map. -/
private theorem etaleResidueFieldNeighborhoodLocalization_residueFieldEquiv_spec
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    (etaleResidueFieldNeighborhoodLocalization_residueFieldEquiv p A).toRingHom =
      Ideal.ResidueField.map
        (maximalIdeal (Localization.AtPrime p))
        (maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)))
        (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
        (etaleResidueFieldNeighborhoodLocalization_maximalIdeal_under p A).symm :=
  rfl

/-- The localized neighborhood `S_q` admits a unique `R_p`-algebra map to any chosen
henselization `R_p^h`. -/
private theorem etaleResidueFieldNeighborhoodLocalization_existsUnique_toHenselization
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh]
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
      RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
    ∃! f :
        Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) →ₐ[Localization.AtPrime p] Rh,
      maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) =
        Ideal.comap (f : Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) →+* Rh)
          (maximalIdeal Rh) := by
  sorry

/-- The canonical morphism from the localized neighborhood `S_q` to a chosen henselization
`R_p^h`. -/
private noncomputable abbrev etaleResidueFieldNeighborhoodLocalizationToHenselizationHom
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh]
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    (etaleResidueFieldNeighborhoodLocalizationDiagram R p).obj A ⟶
      CommAlgCat.of (Localization.AtPrime p) Rh :=
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
    RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
  CommAlgCat.ofHom <|
    Classical.choose <|
      etaleResidueFieldNeighborhoodLocalization_existsUnique_toHenselization p Rh A

/-- The canonical morphism from the source neighborhood `S` to a chosen henselization `R_p^h`,
obtained by composing `S → S_q` with the canonical localized map `S_q → R_p^h`. -/
private noncomputable def etaleResidueFieldNeighborhoodSourceToHenselizationHom
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh]
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    (etaleResidueFieldNeighborhoodSourceDiagram R p).obj A ⟶
      etaleResidueFieldNeighborhoodSourceHenselizationPoint R p Rh :=
  let _ : Algebra R Rh :=
    RingHom.toAlgebra <|
      (algebraMap (Localization.AtPrime p) Rh).comp (algebraMap R (Localization.AtPrime p))
  CommAlgCat.ofHom <|
    { toRingHom :=
        (etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh A).hom.toRingHom.comp
          (algebraMap A.obj.left
            (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)))
      commutes' := by
        intro x
        sorry }

/-- The canonical cocone from the localized neighborhood diagram to a chosen henselization
`R_p^h`. -/
noncomputable def etaleResidueFieldNeighborhoodLocalizationCoconeToHenselization
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    Cocone (etaleResidueFieldNeighborhoodLocalizationDiagram R p) where
  pt := CommAlgCat.of (Localization.AtPrime p) Rh
  ι :=
    { app := etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh
      naturality := by
        intro A B f
        apply CommAlgCat.hom_ext
        sorry }

/-- The canonical cocone from the source neighborhood diagram to a chosen henselization `R_p^h`,
viewed as an `R`-algebra by restriction of scalars. -/
noncomputable def etaleResidueFieldNeighborhoodSourceCoconeToHenselization
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    Cocone (etaleResidueFieldNeighborhoodSourceDiagram R p) where
  pt := etaleResidueFieldNeighborhoodSourceHenselizationPoint R p Rh
  ι :=
    { app := etaleResidueFieldNeighborhoodSourceToHenselizationHom p Rh
      naturality := by
        intro A B f
        apply CommAlgCat.hom_ext
        sorry }

-- Proof sketch: the pair `(R, p)` yields an object of the category, tensor products of étale
-- neighborhoods remain étale and admit a prime over `p` with residue field `κ(p)`, and the usual
-- iterated fiber-product construction over `κ(p)` equalizes parallel morphisms.
/-- Lemma 10.155.7 (1): the category of étale neighborhoods `(S, q)` of `p` with residue field
`κ(q) = κ(p)` is filtered. -/
theorem etaleResidueFieldNeighborhoodCategory_isFiltered :
    IsFiltered (EtaleResidueFieldNeighborhoodCategory R p) := sorry

-- Proof sketch: compare this diagram with the filtered diagram used in the construction of the
-- henselization of `R_p` in Lemma `10.155.1`. Localizing an object `(S, q)` at `q` does not
-- change the corresponding henselian colimit, and every étale neighborhood of `R_p` with residue
-- field `κ(p)` descends from one over `R`.
/-- Lemma 10.155.7 (2): the canonical cocone from the source diagram `(S, q) ↦ S` to a chosen
henselization `R_p^h`, viewed in `CommAlgCat R`, is colimiting. -/
noncomputable def etaleResidueFieldNeighborhoodSourceCoconeToHenselizationIsColimit
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    IsColimit (etaleResidueFieldNeighborhoodSourceCoconeToHenselization p Rh) := by
  sorry

-- Proof sketch: after replacing each object `(S, q)` by its localization `S_q`, the resulting
-- filtered diagram is the standard étale-neighborhood presentation of the henselization of `R_p`.
-- Apply the construction from Lemma `10.155.1` to identify its colimit with any fixed
-- henselization of `R_p`.
/-- Lemma 10.155.7 (3): the canonical cocone from the localized neighborhood diagram
`(S, q) ↦ S_q` to a chosen henselization `R_p^h` is colimiting. -/
noncomputable def etaleResidueFieldNeighborhoodLocalizationCoconeToHenselizationIsColimit
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    IsColimit (etaleResidueFieldNeighborhoodLocalizationCoconeToHenselization p Rh) := by
  sorry

end

/-! ### Lemma_10_155_8 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct
open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

section LocalRingLocalization

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- A local ring is already a localization at the complement of its maximal ideal. -/
private instance self_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal A).primeCompl A := sorry

end LocalRingLocalization

section

variable {R S Rh Sh : Type u}
variable [CommRing R] [CommRing S] [CommRing Rh] [CommRing Sh]
variable [Algebra R S]
variable (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [q.LiesOver p]
variable [Algebra R Rh] [Algebra R Sh]
variable [Algebra (Localization.AtPrime p) Rh] [IsHenselizationOf (Localization.AtPrime p) Rh]
variable [Algebra (Localization.AtPrime q) Sh] [IsHenselizationOf (Localization.AtPrime q) Sh]
variable [Algebra (Localization.AtPrime p) Sh]
variable [IsScalarTower R (Localization.AtPrime p) Rh]
variable [IsScalarTower R (Localization.AtPrime p) Sh]
variable [IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Sh]

local notation "Rₚ" => Localization.AtPrime p
local notation "S_q" => Localization.AtPrime q
local notation "TensorRing" => Rh ⊗[R] S

private noncomputable abbrev henselizationToSh : Rh →ₐ[Rₚ] Sh :=
  @henselizationMap Rₚ Rh Sh _ _ _ _ _ _ _ S_q _ _ _ _ _ _ _

/-- The canonical map `S → S_q^h` obtained by composing `S → S_q` with the henselization
structure map `S_q → Sh`. -/
noncomputable def sourceToLocalizedHenselization : S →ₐ[R] Sh where
  toRingHom := (algebraMap S_q Sh).comp (algebraMap S S_q)
  commutes' r := by
    change (algebraMap S_q Sh) ((algebraMap S S_q) ((algebraMap R S) r)) = (algebraMap R Sh) r
    rw [← IsScalarTower.algebraMap_apply R S S_q]
    rw [IsScalarTower.algebraMap_apply R Rₚ S_q]
    rw [← IsScalarTower.algebraMap_apply Rₚ S_q Sh]
    exact (IsScalarTower.algebraMap_apply R Rₚ Sh r).symm

/-- The canonical tensor-product comparison map `Rʰ ⊗[R] S → S_q^h`. -/
noncomputable abbrev henselizationTensorMap : TensorRing →ₐ[R] Sh :=
  Algebra.TensorProduct.lift
    ((henselizationToSh p q : Rh →ₐ[Rₚ] Sh).restrictScalars R)
    (sourceToLocalizedHenselization p q)
    (fun _ _ ↦ Commute.all _ _)

/-- The canonical prime of `Rʰ ⊗[R] S` cut out by the maximal ideal of `S_q^h`. -/
noncomputable abbrev henselizationTensorPrime : Ideal TensorRing :=
  Ideal.comap ((henselizationTensorMap p q).toRingHom) (maximalIdeal Sh)

local instance localizationAtPrime_isLocalHom :
    IsLocalHom (algebraMap Rₚ S_q) := by
  simpa [RingHom.algebraMap_toAlgebra] using
    (Localization.isLocalHom_localRingHom p q (algebraMap R S) (q.over_def p))

local notation "sourceToSh" => (sourceToLocalizedHenselization p q : S →ₐ[R] Sh)
local notation "tensorToSh" =>
  ((@henselizationTensorMap R S Rh Sh _ _ _ _ _ p _ q _ _ _ _ _ _ _ _ _ _ _ _ :
      TensorRing →ₐ[R] Sh))
local notation "tensorPrime" =>
  ((@henselizationTensorPrime R S Rh Sh _ _ _ _ _ p _ q _ _ _ _ _ _ _ _ _ _ _ _ :
      Ideal TensorRing))

/- Domain-style sampling:
- primary domain: henselization base change along `R → S`, expressed through the tensor product
  of a henselization of `R_p` with the target algebra `S`;
- sampled owner declarations of the same kind:
  `IsHenselizationOf`,
  `henselizationMap`,
  `Localization.localAlgHom`,
  `Localization.localRingHom`,
  `RingHom.isFilteredColimitOfEtale_of_isFilteredColimitOfEtale_over_common_base`;
- best owner abstraction:
  `source-facing`: the canonical prime of `Rʰ ⊗[R] S` cut out by `maximalIdeal Sh` and the
    induced henselization statement;
  `core/canonical`: `IsHenselizationOf`, `Localization.localRingHom`, and
    the comparison `henselizationMap` from Lemma `10.155.6`;
  `bridge/view`: the canonical source map `S → Sh`, the public tensor comparison map to `Sh`, and
    the contracted prime they define;
- primitive data: the henselization owners on `Rₚ` and `S_q`;
- derived API: the local comparison `Rh → Sh`, the canonical source map `S → S_q → Sh`, the
  tensor-product map, its contracted prime, and the induced localization algebra structure.

This file should therefore expose the canonical `S → Sh` bridge, the tensor comparison map, and
the induced prime as public bridge declarations, while keeping the localization algebra structure
itself derived.
-/

local instance tensorPrime_isPrime :
    Ideal.IsPrime tensorPrime :=
  Ideal.comap_isPrime _ (maximalIdeal Sh)

noncomputable abbrev henselizationTensorLocalizationToSh :
    Localization.AtPrime tensorPrime →+* Sh :=
  (IsLocalization.algEquiv
      (maximalIdeal Sh).primeCompl
      (Localization.AtPrime (maximalIdeal Sh))
      Sh : Localization.AtPrime (maximalIdeal Sh) →+* Sh).comp <|
    Localization.localRingHom
      tensorPrime
      (maximalIdeal Sh)
      ((henselizationTensorMap p q).toRingHom)
      rfl

/-- The canonical algebra structure on `Sh` over the localization of `Rʰ ⊗[R] S` at the tensor
prime cut out by `maximalIdeal Sh`. -/
noncomputable instance henselizationTensorPrime_algebra :
    Algebra (Localization.AtPrime tensorPrime) Sh :=
  RingHom.toAlgebra (henselizationTensorLocalizationToSh p q)

/-- The localized tensor-product map to `Sh` agrees with the unlocalized tensor map on pure
source elements. -/
theorem henselizationTensorLocalizationToSh_algebraMap (x : TensorRing) :
    henselizationTensorLocalizationToSh p q
        (algebraMap TensorRing (Localization.AtPrime tensorPrime) x) =
      tensorToSh x := by
  rw [henselizationTensorLocalizationToSh, RingHom.comp_apply,
    Localization.localRingHom_to_map]
  simpa using
    (IsLocalization.algEquiv_apply
      (maximalIdeal Sh).primeCompl
      (Localization.AtPrime (maximalIdeal Sh))
      Sh
      (algebraMap Sh (Localization.AtPrime (maximalIdeal Sh)) (tensorToSh x)))

-- Proof sketch: the tensor-product map to `Sh` restricts on the left to the local map `Rh → Sh`.
-- Since that map is local, the inverse image of `maximalIdeal Sh` is `maximalIdeal Rh`. Unfold the
-- definition of the tensor prime and rewrite the comap along the composite with the left
-- inclusion.
/-- The tensor-product prime lies over the maximal ideal of `Rh`. -/
theorem henselizationTensorPrime_comap_includeLeft :
    Ideal.comap
        (includeLeftRingHom : Rh →+* (Rh ⊗[R] S))
        tensorPrime =
      maximalIdeal Rh := sorry

-- Proof sketch: the tensor-product map to `Sh` restricts on the right to the composite
-- `S → S_q → Sh`. The maximal ideal of `Sh` therefore pulls back to the prime `q` of `S`. Unfold
-- the tensor prime and rewrite the resulting comap along the right inclusion.
/-- The tensor-product prime lies over the chosen prime `q` of `S`. -/
theorem henselizationTensorPrime_comap_includeRight :
    Ideal.comap
        (includeRight : S →ₐ[R] (Rh ⊗[R] S)).toRingHom
        tensorPrime =
      q := sorry

-- Proof sketch: by Lemma `10.155.7`, both henselizations are filtered colimits of étale
-- neighborhoods over their respective local rings; then Lemma `10.143.3` and Lemma `10.154.5`
-- show that the local ring `Sh_(m_Sh)`, hence canonically `Sh` itself, is a filtered colimit of
-- étale algebras over the localized tensor product. The tensor-product prime is the unique prime
-- over `maximalIdeal Rh` and `q` cut out by the map to `Sh`, so Lemma `10.154.7` identifies this
-- local ring with the henselization of that localization.
/-- Lemma 10.155.8: if `Rh` and `Sh` are henselizations of `R_p` and `S_q`, and `Rh → Sh` is the
local ring map induced by Lemma `10.155.6`, then `Sh`, canonically viewed as the localization of
`Sh` at its maximal ideal, is a henselization of the localization of `Rʰ ⊗[R] S` at the
canonical prime cut out by `maximalIdeal Sh`, i.e. the prime lying over `maximalIdeal Rh` and
`q`. -/
theorem isHenselizationOf_localizationAt_henselizationTensorPrime :
    IsHenselizationOf
      (Localization.AtPrime tensorPrime)
      Sh :=
  sorry

end

/-! ### Lemma_10_155_9 (from Chap10) -/
universe u v w y

open IsLocalRing

section

variable {R : Type u} {A : Type v} {S : Type w} {Ssh : Type w} {Ksep : Type y}
variable [CommRing R] [CommRing A] [CommRing S] [CommRing Ssh] [Field Ksep]
variable [IsLocalRing R] [IsLocalRing S]
variable [Algebra R A] [Algebra R S] [Algebra S Ssh] [Algebra R Ssh]
variable [IsLocalHom (algebraMap R S)] [IsScalarTower R S Ssh]
variable [Algebra.Etale R A]
variable [IsStrictHenselizationOf S Ssh]
variable [Algebra (maximalIdeal S).ResidueField Ksep]

/- Domain-style sampling:
- primary domain: strict henselizations of local rings and residue-field-controlled lifting of
  étale points;
- sampled owner declarations of the same kind:
  `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap`,
  `IsStrictHenselizationOf`,
  `ResidueField.map`;
- best owner abstraction:
  the present theorem is a `source-facing` strict-henselization specialization of the core
  henselian lifting owner `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap`,
  with `IsStrictHenselizationOf S Ssh` as the owner and the chosen residue-field equivalence
  `κ(Ssh) ≃+* Ksep` only as a bridge to the auxiliary coefficient field `Ksep`;
- primitive data vs. derived API:
  primitive inputs are the strict-henselization owner on `Ssh`, the prime `q`, the contraction
  equality, the chosen residue-field identification `κ(Ssh) ≃+* Ksep`, and the two
  compatibility equations;
  the derived output is the unique `R`-algebra map `A → Ssh` inducing the chosen residue-field
  map on `q`.

Source/core/bridge triage:
- `source-facing`: the present strict-henselization lifting statement;
- `core/canonical`: `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap` together
  with the canonical local-ring residue-field map `ResidueField.map`;
- `bridge/view`: the auxiliary field `Ksep` together with the residue-field identification
  `κ(Ssh) ≃+* Ksep`.
-/

-- Proof sketch: transport the given map `κ(q) → Ksep` across the chosen residue-field
-- identification `κ(Ssh) ≃+* Ksep` to obtain a compatible map `κ(q) → κ(Ssh)`.
-- Since a strict henselization is henselian local, apply Lemma `10.153.11` with target `Ssh`.
-- The residue-field compatibility with `Ksep` then rewrites the resulting condition exactly into
-- the desired one.
/-- Lemma 10.155.9: let `Ssh` be a strict henselization of the local ring `S`, and let `Ksep` be
a field equipped with an algebra map from `κ(S)` and identified with `κ(Ssh)` over `κ(S)`; in the
source application, `Ksep` is a chosen separable closure of `κ(S)`. If `R → A` is étale, `q` lies
over `maximalIdeal R`, and `τ : κ(q) → Ksep` is compatible with the induced map
`κ(maximalIdeal R) → κ(S) → Ksep`, then there exists a unique `R`-algebra map `f : A → Ssh`
whose inverse image of `maximalIdeal Ssh` is `q` and whose induced map on residue fields agrees
with `τ` after the chosen identification `κ(Ssh) ≃ Ksep`. -/
lemma existsUnique_algHom_to_strictHenselization_of_etale_of_residueFieldMap
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = maximalIdeal R)
    (ι : (maximalIdeal Ssh).ResidueField ≃+* Ksep)
    (hι :
      ι.toRingHom.comp
          (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
            (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm) =
        algebraMap (maximalIdeal S).ResidueField Ksep)
    (τ : q.ResidueField →+* Ksep)
    (hτ :
      τ.comp (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hq.symm) =
        (algebraMap (maximalIdeal S).ResidueField Ksep).comp
          (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S)
            (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm)) :
    ∃! f : A →ₐ[R] Ssh,
      ∃ hfq : q = Ideal.comap (f : A →+* Ssh) (maximalIdeal Ssh),
        ι.toRingHom.comp (Ideal.ResidueField.map q (maximalIdeal Ssh) (f : A →+* Ssh) hfq) = τ := by
  let _ : IsLocalHom (algebraMap R Ssh) := by
    simpa [IsScalarTower.algebraMap_eq R S Ssh] using
      (show IsLocalHom ((algebraMap S Ssh).comp (algebraMap R S)) from inferInstance)
  let τSsh : q.ResidueField →+* (maximalIdeal Ssh).ResidueField :=
    ι.symm.toRingHom.comp τ
  have hqS : q.under R = (maximalIdeal S).under R := by
    rw [hq]
    simpa [Ideal.under_def] using
      (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm
  have hqSsh : q.under R = (maximalIdeal Ssh).under R := by
    rw [hq]
    simpa [Ideal.under_def] using
      (IsLocalRing.maximalIdeal_comap (algebraMap R Ssh)).symm
  have hι' :
      ι.symm.toRingHom.comp (algebraMap (maximalIdeal S).ResidueField Ksep) =
        Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
          (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm := by
    refine RingHom.ext fun x ↦ ?_
    apply ι.injective
    simpa using (congrArg (fun φ ↦ φ x) hι).symm
  have hmap :
      Ideal.ResidueField.map (q.under R) (maximalIdeal Ssh) (algebraMap R Ssh) hqSsh =
        (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
          (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm).comp
          (Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hqS) := by
    apply Ideal.ResidueField.ringHom_ext
    ext r
    simp [IsScalarTower.algebraMap_eq R S Ssh]
  have hτS :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        (algebraMap (maximalIdeal S).ResidueField Ksep).comp
          (Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hqS) := by
    apply Ideal.ResidueField.ringHom_ext
    ext r
    have hr :=
      congrArg (fun φ ↦ φ (algebraMap R (maximalIdeal R).ResidueField r)) hτ
    simpa [hq, hqS] using hr
  have hτSsh :
      τSsh.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal Ssh) (algebraMap R Ssh) hqSsh := by
    calc
      τSsh.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl)
          = ι.symm.toRingHom.comp
              (τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl)) := by
              rfl
      _ = ι.symm.toRingHom.comp
            ((algebraMap (maximalIdeal S).ResidueField Ksep).comp
              (Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hqS)) := by
            simpa using congrArg (fun φ ↦ ι.symm.toRingHom.comp φ) hτS
      _ = (ι.symm.toRingHom.comp (algebraMap (maximalIdeal S).ResidueField Ksep)).comp
            (Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hqS) := by
            rw [RingHom.comp_assoc]
      _ = (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
            (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm).comp
            (Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hqS) := by
            rw [hι']
      _ = Ideal.ResidueField.map (q.under R) (maximalIdeal Ssh) (algebraMap R Ssh) hqSsh := by
            rw [hmap]
  obtain ⟨f, hf, huniq⟩ :=
    existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap
      q hqSsh τSsh hτSsh
  refine ⟨f, ?_, ?_⟩
  · rcases hf with ⟨hfq, hτf⟩
    refine ⟨hfq, ?_⟩
    calc
      ι.toRingHom.comp (Ideal.ResidueField.map q (maximalIdeal Ssh) (f : A →+* Ssh) hfq)
          = ι.toRingHom.comp τSsh := by rw [hτf]
      _ = τ := by
        refine RingHom.ext fun x ↦ ?_
        simp [τSsh]
  · intro g hg
    apply huniq g
    rcases hg with ⟨hgq, hgτ⟩
    refine ⟨hgq, ?_⟩
    refine RingHom.ext fun x ↦ ?_
    apply ι.injective
    simpa [τSsh] using congrArg (fun φ ↦ φ x) hgτ

end
