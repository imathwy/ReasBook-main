import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

/-- The canonical `core/canonical` bridge for Lemma 10.107.14: for a commutative `R`-algebra `S`,
the algebra map is epic exactly when restriction of scalars on module categories is fully
faithful. This refines the source-text equality
`Hom_S(N₁, N₂) = Hom_R(N₁, N₂)` to the owner abstraction `Algebra.IsEpi R S`. -/
-- Proof sketch: if `R → S` is epic, `TensorProduct.lid'` upgrades every `R`-linear map of
-- `S`-modules canonically to an `S`-linear map, so restriction of scalars is fully faithful.
-- Conversely, full faithfulness forces the `R`-linear map `s ↦ 1 ⊗ s : S → S ⊗[R] S` to come
-- from an `S`-linear map for the left `S`-module structure, hence `1 ⊗ s = s ⊗ 1` for all `s`,
-- which is exactly `Algebra.IsEpi R S`.
theorem algebra_isEpi_iff_restrictScalars_fullyFaithful
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.IsEpi R S ↔
      Nonempty ((ModuleCat.restrictScalars (algebraMap R S)).FullyFaithful) := sorry

/-- Lemma 10.107.14: a ring homomorphism `f : R →+* S` is an epimorphism of commutative rings if
and only if the restriction-of-scalars functor `ModuleCat.restrictScalars f : ModuleCat S ⥤
ModuleCat R` is fully faithful. This is the canonical category-theoretic form of the equivalence
between ring epimorphisms, equality of `S`-linear and `R`-linear maps between `S`-modules, and
full faithfulness of restriction of scalars. -/
-- Proof sketch: equip `S` with the `R`-algebra structure induced by `f`. The core bridge above
-- gives `Algebra.IsEpi R S ↔` full faithfulness of `ModuleCat.restrictScalars f`, and
-- `CommRingCat.epi_iff_epi` identifies `Algebra.IsEpi R S` with `Epi (CommRingCat.ofHom f)`.
theorem ringHom_epi_iff_restrictScalars_fullyFaithful
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Epi (CommRingCat.ofHom f) ↔ Nonempty ((ModuleCat.restrictScalars f).FullyFaithful) := by
  letI : Algebra R S := f.toAlgebra
  have hf : Epi (CommRingCat.ofHom f) ↔ Algebra.IsEpi R S := by
    simpa [RingHom.algebraMap_toAlgebra] using CommRingCat.epi_iff_epi
  exact hf.trans <| by
    simpa [RingHom.algebraMap_toAlgebra] using
      algebra_isEpi_iff_restrictScalars_fullyFaithful

/-- Restriction of scalars along an epimorphism of commutative rings is fully faithful. This is
the canonical instance-level companion to `ringHom_epi_iff_restrictScalars_fullyFaithful`. -/
noncomputable instance restrictScalars_fullyFaithful_of_epi
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) [Epi (CommRingCat.ofHom f)] :
    (ModuleCat.restrictScalars f).FullyFaithful :=
  ((ringHom_epi_iff_restrictScalars_fullyFaithful f).mp inferInstance).some
