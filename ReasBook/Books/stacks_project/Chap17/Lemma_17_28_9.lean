import Mathlib
import stacks_project.Chap18.Lemma_18_33_8

open CategoryTheory TopCat TopologicalSpace
open TopCat.Presheaf
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite TensorProduct

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ O₂' : X.Sheaf CommRingCat.{u}}

/- Domain-style sampling for Lemma 17.28.9:
- primary domain: the conormal exact sequence for a composable pair
  `O₁ ⟶ O₂ ⟶ O₂'` of sheaves of commutative rings on a fixed topological space;
- sampled owner declarations:
  `SheafOfModules.RingedSite.conormalMap`,
  `SheafOfModules.RingedSite.conormalToDifferentials`,
  `SheafOfModules.RingedSite.conormalSequence_exact`,
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`,
  `KaehlerDifferential.kerCotangentToTensor_toCotangent`;
- best owner abstraction: the generic-site owner in namespace
  `SheafOfModules.RingedSite`, specialized here to the opens site of `X`;
- primitive data: the composable morphisms `φ : O₁ ⟶ O₂` and `α : O₂ ⟶ O₂'`;
- derived API: the opens-site exactness theorem and the stalkwise Kähler recalls obtained by
  specializing to `stalkFunctor CommRingCat x`.

Source/core/bridge triage:
- `source-facing`: Lemma 17.28.9 on a topological space and its stalkwise reformulations;
- `core/canonical`: the generic-site conormal sequence owner in
  `SheafOfModules.RingedSite`;
- `bridge/view`: this file is only the opens-site specialization of the site-level owner; the
  stalk statements are companion recalls of the existing ring-level Kähler owners, not new theorem
  wrappers. -/

/-- Lemma 17.28.9: if `α : O₂ ⟶ O₂'` is surjective on stalks, then the canonical opens-site
conormal sequence of sheaves of `O₂'`-modules
`conormalSource α ⟶ O₂' ⊗[O₂] Ω_{O₂/O₁} ⟶ Ω_{O₂'/O₁} ⟶ 0`
is exact. -/
theorem conormalSequence_exact_of_stalkwise_surjective
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂')
    (hsurj : ∀ x : X, Function.Surjective ((stalkFunctor CommRingCat x).map α.hom).hom) :
    (ShortComplex.mk
      (conormalMap φ α)
      (conormalToDifferentials φ α)
      (conormal_comp_zero φ α)).Exact ∧
      Epi (conormalToDifferentials φ α) := by
  have hloc : Sheaf.IsLocallySurjective α := by
    exact (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks α.hom).2 hsurj
  simpa using SheafOfModules.RingedSite.conormalSequence_exact φ α hloc

private abbrev stalkRing (O : X.Sheaf CommRingCat.{u}) (x : X) : CommRingCat :=
  (stalkFunctor CommRingCat x).obj O.obj

private abbrev stalkRingHom {O O' : X.Sheaf CommRingCat.{u}} (β : O ⟶ O') (x : X) :
    stalkRing O x ⟶ stalkRing O' x :=
  (stalkFunctor CommRingCat x).map β.hom

section StalkRecalls

variable (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂')
variable (x : X)

/- Companion recall: at each stalk `x`, the ring-level exact conormal sequence is exactly the
Kähler owner pair
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` and
`KaehlerDifferential.mapBaseChange_surjective` for the stalk map
`(stalkRingHom α x).hom`. -/
#check
  (fun hsurj : ∀ x : X, Function.Surjective ((stalkFunctor CommRingCat x).map α.hom).hom ↦
    let _ : Algebra (stalkRing O₁ x) (stalkRing O₂ x) := (stalkRingHom φ x).hom.toAlgebra
    let _ : Algebra (stalkRing O₂ x) (stalkRing O₂' x) := (stalkRingHom α x).hom.toAlgebra
    let _ : Algebra (stalkRing O₁ x) (stalkRing O₂' x) :=
      ((stalkRingHom α x).hom.comp (stalkRingHom φ x).hom).toAlgebra
    let _ : IsScalarTower (stalkRing O₁ x) (stalkRing O₂ x) (stalkRing O₂' x) :=
      IsScalarTower.of_algebraMap_eq' rfl
    show
        Function.Exact
            (KaehlerDifferential.kerCotangentToTensor
              (stalkRing O₁ x) (stalkRing O₂ x) (stalkRing O₂' x))
            (KaehlerDifferential.mapBaseChange
              (stalkRing O₁ x) (stalkRing O₂ x) (stalkRing O₂' x)) ∧
          Function.Surjective
            (KaehlerDifferential.mapBaseChange
              (stalkRing O₁ x) (stalkRing O₂ x) (stalkRing O₂' x))
      from
        ⟨KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
            (stalkRing O₁ x) (stalkRing O₂ x) (stalkRing O₂' x) (hsurj x),
          KaehlerDifferential.mapBaseChange_surjective
            (stalkRing O₁ x) (stalkRing O₂ x) (stalkRing O₂' x) (hsurj x)⟩)

/- Companion recall: on the class of an element in the kernel ideal of the stalk map
`(stalkRingHom α x).hom`, the
left conormal map is the canonical formula
`KaehlerDifferential.kerCotangentToTensor_toCotangent`. -/
#check
  (fun f : RingHom.ker (stalkRingHom α x).hom ↦
    let _ : Algebra (stalkRing O₁ x) (stalkRing O₂ x) := (stalkRingHom φ x).hom.toAlgebra
    let _ : Algebra (stalkRing O₂ x) (stalkRing O₂' x) := (stalkRingHom α x).hom.toAlgebra
    show
        KaehlerDifferential.kerCotangentToTensor
            (stalkRing O₁ x) (stalkRing O₂ x) (stalkRing O₂' x)
            (Ideal.toCotangent (RingHom.ker (stalkRingHom α x).hom) f) =
          (1 : stalkRing O₂' x) ⊗ₜ[stalkRing O₂ x]
            KaehlerDifferential.D
              (stalkRing O₁ x) (stalkRing O₂ x) (f : stalkRing O₂ x)
      from
        rfl)

end StalkRecalls

end TopCat.Sheaf
