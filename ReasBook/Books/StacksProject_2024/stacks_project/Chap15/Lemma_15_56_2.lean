import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_107_14
import StacksProject_2024.stacks_project.Chap15.Lemma_15_56_3

-- Declarations for this item will be appended below by the statement pipeline.

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
