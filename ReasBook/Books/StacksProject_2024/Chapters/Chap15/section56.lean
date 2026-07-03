import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_56_1 (from Chap15) -/
open CategoryTheory
open ComplexShape
open ModuleCat

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S]

/- Domain-style sampling:
- primary domain: change of rings for module-valued cochain complexes and preservation of
  `CochainComplex.IsKInjective`.
- inspected owner declarations:
  `CochainComplex.IsKInjective`,
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`,
  `ModuleCat.extendRestrictScalarsAdj`,
  `extendScalars_exact_of_flat`.
- source/core/bridge triage:
  `source-facing`: the flat restriction-of-scalars specialization for K-injective cochain
    complexes;
  `core/canonical`: `right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
  `bridge/view`: `extendRestrictScalarsAdj f` and `extendScalars_exact_of_flat f hf`.
- primitive data: the ring map `f` and its flatness.
- derived API: K-injectivity of the restricted complex.
- owner decision: this file should keep the flat specialization as a source-facing bridge, not
  introduce a second owner parallel to the Chapter 13 theorem.
-/

-- Proof sketch: `extendScalars f ⊣ restrictScalars f` is the canonical change-of-rings adjunction,
-- and flatness makes the left adjoint exact by `extendScalars_exact_of_flat`. The theorem is then
-- exactly the Chapter 13 owner theorem specialized to this adjunction.
/-- Lemma 15.56.1: for a flat ring map `f : R →+* S`, a K-injective cochain complex of
`S`-modules remains K-injective when regarded as a cochain complex of `R`-modules via restriction
of scalars. -/
theorem restrictScalars_isKInjective_of_flat
    (f : R →+* S) (hf : f.Flat) (I : CochainComplex (ModuleCat.{u} S) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj I) := by
  simpa using
    right_adjoint_preserves_isKInjective_of_exact_left_adjoint
      (restrictScalars.{u} f) (extendScalars.{u, u, u} f) (extendRestrictScalarsAdj f)
      (extendScalars_exact_of_flat f hf) I

end

/-! ### Lemma_15_56_2 (from Chap15) -/
open CategoryTheory
open ComplexShape
open ModuleCat

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S]

/- Domain-style sampling:
- primary domain: change of rings for module-valued cochain complexes and reflection of
  `CochainComplex.IsKInjective` along restriction of scalars.
- inspected owner declarations:
  `restrictScalars_fullyFaithful_of_epi`,
  `coextendScalars_isKInjective`,
  `ModuleCat.restrictCoextendScalarsAdj`,
  `CategoryTheory.Adjunction.mapHomologicalComplex`,
  `CochainComplex.isKInjective_of_iso`.
- layer: `source-facing`; the source statement is the reflection step for K-injectivity under a
  ring epimorphism.
- core/canonical owner abstraction: the adjunction `restrictScalars f ⊣ coextendScalars f`,
  together with the unit isomorphism induced by full faithfulness of `restrictScalars f`.
- primitive data: the ring epimorphism hypothesis and K-injectivity of the restricted complex.
- derived API: the earlier Chapter 15 bridge `coextendScalars_isKInjective` supplies
  K-injectivity of the coextended restricted complex, and then `I` is recovered via the canonical
  unit isomorphism on cochain complexes.
- source/core/bridge triage:
  `source-facing`: reflection of K-injectivity from the restricted complex back to the original
    `S`-complex;
  `core/canonical`: the lifted adjunction `restrictScalars f ⊣ coextendScalars f` on cochain
    complexes;
  `bridge/view`: the Chapter 15 specialization `coextendScalars_isKInjective` and the
    full-faithful unit isomorphism.
-/
-- Proof sketch: by Lemma `10.107.14`, restriction of scalars along an epimorphism of rings is
-- fully faithful. The canonical lifted adjunction
-- `restrictScalars f ⊣ coextendScalars f` on cochain complexes therefore has invertible unit by
-- `Adjunction.unit_isIso_of_L_fully_faithful`. The earlier Chapter 15 bridge theorem makes the
-- coextended restricted complex K-injective, and transporting across that unit isomorphism gives the
-- required K-injectivity of `I`.
/-- Lemma 15.56.2: if `f : R →+* S` is an epimorphism of commutative rings and a cochain complex
`I` of `S`-modules is K-injective after restriction of scalars to `R`, then `I` is already
K-injective as a cochain complex of `S`-modules. -/
theorem isKInjective_of_restrictScalars_of_epi
    (f : R →+* S) [Epi (CommRingCat.ofHom f)] (I : CochainComplex (ModuleCat.{u} S) ℤ)
    [CochainComplex.IsKInjective (((restrictScalars f).mapHomologicalComplex (up ℤ)).obj I)] :
    I.IsKInjective := by
  let res := (restrictScalars f).mapHomologicalComplex (up ℤ)
  let coext := (coextendScalars f).mapHomologicalComplex (up ℤ)
  letI : CochainComplex.IsKInjective ((res ⋙ coext).obj I) := by
    change CochainComplex.IsKInjective (coext.obj (res.obj I))
    exact coextendScalars_isKInjective f (res.obj I)
  let moduleAdj := restrictCoextendScalarsAdj f
  let hff : (restrictScalars f).FullyFaithful := restrictScalars_fullyFaithful_of_epi f
  letI : (restrictScalars f).Full := hff.full
  letI : (restrictScalars f).Faithful := hff.faithful
  letI : IsIso moduleAdj.unit := moduleAdj.unit_isIso_of_L_fully_faithful
  let unitIso : 𝟭 (CochainComplex (ModuleCat.{u} S) ℤ) ≅ res ⋙ coext :=
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} S) (up ℤ)).symm ≪≫
      NatIso.mapHomologicalComplex (asIso moduleAdj.unit) (up ℤ)
  exact CochainComplex.isKInjective_of_iso (unitIso.app I).symm

end

/-! ### Lemma_15_56_3 (from Chap15) -/
open CategoryTheory
open ComplexShape
open ModuleCat

universe u

section

variable {R S : Type u} [Ring R] [Ring S]

/- Domain-style sampling for Lemma 15.56.3:
- primary domain: change of rings for module-valued cochain complexes and preservation of
  `CochainComplex.IsKInjective` under adjunctions;
- inspected owner declarations:
  `ModuleCat.restrictCoextendScalarsAdj`,
  `restrictScalars_exact`,
  `right_adjoint_preserves_isKInjective_of_exact_left_adjoint`,
  `CochainComplex.IsKInjective`;
- best owner abstraction:
  `right_adjoint_preserves_isKInjective_of_exact_left_adjoint`.

Source/core/bridge triage:
- `source-facing`: coextension of scalars along a ring map sends K-injective cochain complexes to
  K-injective cochain complexes;
- `core/canonical`: `right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- `bridge/view`: the canonical adjunction `restrictScalars f ⊣ coextendScalars f` together with
  the exactness theorem `restrictScalars_exact f`.

The source statement is a source-facing bridge specialization of that owner theorem to the
canonical adjunction `restrictScalars f ⊣ coextendScalars f`; it should stay as a thin bridge
rather than a duplicate local owner.
-/

-- Proof sketch: `restrictScalars f ⊣ coextendScalars f` is the canonical change-of-rings
-- adjunction, and `restrictScalars f` is exact by Remark `12.29.2`. The result is the Chapter 13
-- owner theorem specialized to this adjunction.
/-- Lemma 15.56.3: for a ring homomorphism `f : R →+* S`, coextension of scalars sends
K-injective cochain complexes of `R`-modules to K-injective cochain complexes of `S`-modules. -/
theorem coextendScalars_isKInjective
    (f : R →+* S) (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (((coextendScalars f).mapHomologicalComplex (up ℤ)).obj I) := by
  exact
    (right_adjoint_preserves_isKInjective_of_exact_left_adjoint
      (coextendScalars f) (restrictScalars f) (restrictCoextendScalarsAdj f)
      (restrictScalars_exact f) I :
        CochainComplex.IsKInjective (((coextendScalars f).mapHomologicalComplex (up ℤ)).obj I))

end
