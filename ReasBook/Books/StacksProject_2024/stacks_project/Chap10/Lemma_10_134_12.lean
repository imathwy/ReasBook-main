import Mathlib
import StacksProject_2024.Chap10.Definition_10_134_1

open Algebra
open Algebra.Extension
open Algebra.Generators
open CategoryTheory
open CategoryTheory.Limits
open scoped NaiveCotangent TensorProduct

universe u v

noncomputable section

section

variable (A : Type u) (B : Type v) (Bg : Type v)
variable [CommRing A] [CommRing B] [CommRing Bg]
variable [Algebra A B] [Algebra A Bg] [Algebra B Bg]
variable [IsScalarTower A B Bg]
variable (g : B) [IsLocalization.Away g Bg]

attribute [local instance] SMulCommClass.of_commMonoid
attribute [local instance] TensorProduct.rightAlgebra

private noncomputable abbrev scalarExtendedNaiveCotangent :
    ChainComplex (ModuleCat Bg) ℕ :=
  ((ModuleCat.extendScalars (algebraMap B Bg)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (NL_{B⁄A})

/- Domain triage:
* primary domain: naive cotangent complexes under localization of the target algebra.
* sampled owner declarations:
  - `Algebra.naiveCotangent`, the Chapter 10 owner `NL_{-⁄-}`;
  - `Algebra.Generators.localizationAway`, the canonical presentation of an arbitrary
    away-localization target;
  - `Algebra.Generators.cotangentCompLocalizationAwayEquiv`, the presentation-level splitting of
    the localized conormal module;
  - `Algebra.Extension.CotangentSpace.compEquiv`, the matching presentation-level splitting of the
    localized cotangent-space term.
* best owner abstraction: the public source-facing statement should still be about the canonical
  comparison map from the literal scalar extension of `NL_{B⁄A}` from `B` to `Bg`, written
  `NL_{B⁄A} ⊗[B] B_g`, to the owner `NL_{Bg⁄A}` for an arbitrary localization target `Bg` with
  `[IsLocalization.Away g Bg]`. The localization presentation obtained by adjoining an inverse of
  `g` is bridge data used only to define that comparison map.
* primitive vs. derived:
  - primitive data: the algebra map `A → B`, the away-localization target `Bg`, and the owner
    complexes `NL_{B⁄A}` and `NL_{Bg⁄A}`;
  - derived API: the private tensor-model bridge and the canonical chain map through the localized
    self-presentation.
* layer triage:
  - `source-facing`: the canonical map `NL_{B⁄A} ⊗[B] Bg → NL_{Bg⁄A}`;
  - `core/canonical`: `NL_{B⁄A}` and `NL_{Bg⁄A}`;
  - `bridge/view`: the localized self-presentation
    `(Generators.localizationAway Bg g).comp (Generators.self A B)`.
-/

private noncomputable abbrev selfExtension :
    Extension A B :=
  (Generators.self A B).toExtension

private abbrev selfLiftCotangent : Type (max u v) :=
  ULift.{v, max u v} (selfExtension A B).Cotangent

private noncomputable abbrev selfLiftCotangentEquiv :
    selfLiftCotangent A B ≃ₗ[B] (selfExtension A B).Cotangent :=
  ULift.moduleEquiv

private noncomputable abbrev localizedSelfGenerators :
    Generators A Bg (Unit ⊕ B) :=
  (Generators.localizationAway Bg g).comp (Generators.self A B)

/-- Private bridge/view model for `NL_{B⁄A} ⊗[B] Bg` with the degree-`1` term normalized from
`Bg ⊗[B] ULift P.Cotangent` to `Bg ⊗[B] P.Cotangent`. -/
private noncomputable def tensorNaiveCotangentAwayModel :
    ChainComplex (ModuleCat Bg) ℕ :=
  let P := selfExtension A B
  ChainComplex.mk'
    (ModuleCat.of Bg (Bg ⊗[B] P.CotangentSpace))
    (ModuleCat.of Bg (Bg ⊗[B] P.Cotangent))
    (ModuleCat.ofHom (LinearMap.baseChange Bg P.cotangentComplex))
    (fun {_ _} _ ↦ ⟨ModuleCat.of Bg PUnit, 0, zero_comp⟩)

private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap B Bg)).obj (ModuleCat.of Bg Bg)) ≃ₗ[Bg] Bg :=
  { __ := AddEquiv.refl Bg
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower B Bg ↑((ModuleCat.restrictScalars (algebraMap B Bg)).obj (ModuleCat.of Bg Bg)) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    rfl

private noncomputable def scalarExtendedPUnitIso :
    (ModuleCat.extendScalars (algebraMap B Bg)).obj (ModuleCat.of B PUnit) ≅
      ModuleCat.of Bg PUnit := by
  let e₁ :
      (ModuleCat.extendScalars (algebraMap B Bg)).obj (ModuleCat.of B PUnit) ≅
        ModuleCat.of Bg (Bg ⊗[B] PUnit) := by
    simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        (restrictScalarsSelfEquiv B Bg)
        (LinearEquiv.refl B PUnit)).toModuleIso
  letI : Subsingleton (Bg ⊗[B] PUnit) := inferInstance
  let e₂ : ModuleCat.of Bg (Bg ⊗[B] PUnit) ≅ ModuleCat.of Bg PUnit :=
    (LinearEquiv.ofSubsingleton _ _).toModuleIso
  exact e₁ ≪≫ e₂

omit [Algebra A Bg] [IsScalarTower A B Bg] in
private theorem tensorNaiveCotangentAwayModel_d_succ_succ
    (n : ℕ) :
    (tensorNaiveCotangentAwayModel A B Bg).d (n + 2) (n + 1) = 0 := by
  rw [tensorNaiveCotangentAwayModel, ChainComplex.mk'_d]
  ext x
  rfl

omit [Algebra A Bg] [IsScalarTower A B Bg] in
private theorem naiveCotangentTensor_d_succ_succ
    (n : ℕ) :
    (scalarExtendedNaiveCotangent A B Bg).d (n + 2) (n + 1) = 0 := by
  rw [scalarExtendedNaiveCotangent, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
    Extension.naiveCotangentChainComplex_d_succ_succ (selfExtension A B) n]
  simpa using CategoryTheory.Functor.map_zero (ModuleCat.extendScalars (algebraMap B Bg))
    ((NL_{B⁄A}).X (n + 2)) ((NL_{B⁄A}).X (n + 1))

private noncomputable def naiveCotangentTensorToTensorModelXIso :
    ∀ n : ℕ,
      (scalarExtendedNaiveCotangent A B Bg).X n ≅
        (tensorNaiveCotangentAwayModel A B Bg).X n
  | 0 => by
      let P := selfExtension A B
      simpa [scalarExtendedNaiveCotangent, tensorNaiveCotangentAwayModel, Algebra.naiveCotangent, P,
        Extension.naiveCotangentChainComplex, ModuleCat.extendScalars,
        ModuleCat.ExtendScalars.obj'] using
        (TensorProduct.AlgebraTensorModule.congr
          (restrictScalarsSelfEquiv B Bg)
          (LinearEquiv.refl B P.CotangentSpace)).toModuleIso
  | 1 => by
      let P := selfExtension A B
      simpa [scalarExtendedNaiveCotangent, tensorNaiveCotangentAwayModel,
        Algebra.naiveCotangent, P, Extension.naiveCotangentChainComplex, ModuleCat.extendScalars,
        ModuleCat.ExtendScalars.obj'] using
        (TensorProduct.AlgebraTensorModule.congr
          (restrictScalarsSelfEquiv B Bg)
          (selfLiftCotangentEquiv A B)).toModuleIso
  | n + 2 => by
      let P := selfExtension A B
      let succZero :
          ∀ {X₀ X₁ : ModuleCat Bg} (f : X₁ ⟶ X₀),
            Σ' (X₂ : ModuleCat Bg) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
        fun {_ _} _ ↦ ⟨ModuleCat.of Bg PUnit, 0, zero_comp⟩
      let succZeroB :
          ∀ {X₀ X₁ : ModuleCat B} (f : X₁ ⟶ X₀),
            Σ' (X₂ : ModuleCat B) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
        fun {_ _} _ ↦ ⟨ModuleCat.of B PUnit, 0, zero_comp⟩
      have hsrc :
          (scalarExtendedNaiveCotangent A B Bg).X (n + 2) ≅
            ModuleCat.of Bg PUnit := by
        let hX :
            (scalarExtendedNaiveCotangent A B Bg).X (n + 2) =
              (ModuleCat.extendScalars (algebraMap B Bg)).obj ((NL_{B⁄A}).X (n + 2)) :=
          CategoryTheory.Functor.mapHomologicalComplex_obj_X
            (ModuleCat.extendScalars (algebraMap B Bg)) (ComplexShape.down ℕ) (NL_{B⁄A}) (n + 2)
        have hmk : (NL_{B⁄A}).X (n + 2) ≅ ModuleCat.of B PUnit := by
          simpa [Algebra.naiveCotangent, P, Extension.naiveCotangentChainComplex] using
            (ChainComplex.mk'XIso
              (ModuleCat.of B P.CotangentSpace)
              (ModuleCat.of B (selfLiftCotangent A B))
              (ModuleCat.ofHom
                (P.cotangentComplex.comp (selfLiftCotangentEquiv A B).toLinearMap))
              succZeroB n)
        simpa [scalarExtendedNaiveCotangent] using
          eqToIso hX ≪≫ (ModuleCat.extendScalars (algebraMap B Bg)).mapIso hmk ≪≫
            scalarExtendedPUnitIso B Bg
      have htrg :
          (tensorNaiveCotangentAwayModel A B Bg).X (n + 2) ≅
            ModuleCat.of Bg PUnit := by
        simpa [tensorNaiveCotangentAwayModel, P] using
          (ChainComplex.mk'XIso
            (ModuleCat.of Bg (Bg ⊗[B] P.CotangentSpace))
            (ModuleCat.of Bg (Bg ⊗[B] P.Cotangent))
            (ModuleCat.ofHom (LinearMap.baseChange Bg P.cotangentComplex))
            succZero n)
      exact hsrc ≪≫ htrg.symm

omit [Algebra A Bg] [IsScalarTower A B Bg] in
private theorem naiveCotangentTensorToTensorModelXIso_comm :
    ∀ i j (_ : (ComplexShape.down ℕ).Rel i j),
      (naiveCotangentTensorToTensorModelXIso A B Bg i).hom ≫
          (tensorNaiveCotangentAwayModel A B Bg).d i j =
        (scalarExtendedNaiveCotangent A B Bg).d i j ≫
          (naiveCotangentTensorToTensorModelXIso A B Bg j).hom := by
  intro i j hij
  subst i
  cases j with
  | zero =>
      let P := selfExtension A B
      ext x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · have hL :
            (ModuleCat.Hom.hom
                ((naiveCotangentTensorToTensorModelXIso A B Bg (0 + 1)).hom ≫
                  (tensorNaiveCotangentAwayModel A B Bg).d (0 + 1) 0))
              0 = 0 := by
            rw [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.map_zero, LinearMap.map_zero]
        have hR :
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangent A B Bg).d (0 + 1) 0 ≫
                  (naiveCotangentTensorToTensorModelXIso A B Bg 0).hom))
              0 = 0 := by
            rw [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.map_zero, LinearMap.map_zero]
        exact hL.trans hR.symm
      · intro t x
        rcases x with ⟨x⟩
        change
          (LinearMap.baseChange Bg P.cotangentComplex)
              ((TensorProduct.AlgebraTensorModule.congr
                  (restrictScalarsSelfEquiv B Bg)
                  (selfLiftCotangentEquiv A B))
                (t ⊗ₜ[B] ULift.up x)) =
            (LinearMap.baseChange Bg
              (P.cotangentComplex.comp
                (selfLiftCotangentEquiv A B).toLinearMap))
              (t ⊗ₜ[B] ULift.up x)
        rfl
      · intro x y hx hy
        calc
          (ModuleCat.Hom.hom
                ((naiveCotangentTensorToTensorModelXIso A B Bg (0 + 1)).hom ≫
                  (tensorNaiveCotangentAwayModel A B Bg).d (0 + 1) 0))
              (x + y) =
          (ModuleCat.Hom.hom
                ((naiveCotangentTensorToTensorModelXIso A B Bg (0 + 1)).hom ≫
                  (tensorNaiveCotangentAwayModel A B Bg).d (0 + 1) 0))
                x +
              (ModuleCat.Hom.hom
                ((naiveCotangentTensorToTensorModelXIso A B Bg (0 + 1)).hom ≫
                  (tensorNaiveCotangentAwayModel A B Bg).d (0 + 1) 0))
                y := by
                  simpa using
                    (LinearMap.map_add
                      (ModuleCat.Hom.hom
                        ((naiveCotangentTensorToTensorModelXIso A B Bg (0 + 1)).hom ≫
                          (tensorNaiveCotangentAwayModel A B Bg).d (0 + 1) 0))
                      x y)
          _ =
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangent A B Bg).d (0 + 1) 0 ≫
                  (naiveCotangentTensorToTensorModelXIso A B Bg 0).hom))
                x +
              (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangent A B Bg).d (0 + 1) 0 ≫
                  (naiveCotangentTensorToTensorModelXIso A B Bg 0).hom))
                y := by rw [hx, hy]
          _ =
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangent A B Bg).d (0 + 1) 0 ≫
                  (naiveCotangentTensorToTensorModelXIso A B Bg 0).hom))
              (x + y) := by
                simpa using
                  (LinearMap.map_add
                    (ModuleCat.Hom.hom
                      ((scalarExtendedNaiveCotangent A B Bg).d (0 + 1) 0 ≫
                        (naiveCotangentTensorToTensorModelXIso A B Bg 0).hom))
                    x y).symm
  | succ j =>
      rw [show (tensorNaiveCotangentAwayModel A B Bg).d (j + 1 + 1) (j + 1) = 0 by
            simpa [Nat.add_assoc] using tensorNaiveCotangentAwayModel_d_succ_succ
              A B Bg j,
        show (scalarExtendedNaiveCotangent A B Bg).d (j + 1 + 1) (j + 1) = 0 by
            simpa [Nat.add_assoc] using naiveCotangentTensor_d_succ_succ
              A B Bg j]
      ext x
      have hL :
          (ModuleCat.Hom.hom
              ((naiveCotangentTensorToTensorModelXIso A B Bg (j + 2)).hom ≫
                (0 : (tensorNaiveCotangentAwayModel A B Bg).X (j + 2) ⟶
                  (tensorNaiveCotangentAwayModel A B Bg).X (j + 1))))
            x = 0 := by
        rfl
      have hR :
          (ModuleCat.Hom.hom
              ((0 : (scalarExtendedNaiveCotangent A B Bg).X (j + 2) ⟶
                (scalarExtendedNaiveCotangent A B Bg).X (j + 1)) ≫
                (naiveCotangentTensorToTensorModelXIso A B Bg (j + 1)).hom))
            x = 0 := by
        rw [ModuleCat.hom_comp, LinearMap.comp_apply]
        change (ModuleCat.Hom.hom (naiveCotangentTensorToTensorModelXIso A B Bg (j + 1)).hom) 0 = 0
        simpa using
          (LinearMap.map_zero
            (ModuleCat.Hom.hom (naiveCotangentTensorToTensorModelXIso A B Bg (j + 1)).hom))
      simpa [Nat.add_assoc] using hL.trans hR.symm

private noncomputable def naiveCotangentTensorToTensorModelIso :
    scalarExtendedNaiveCotangent A B Bg ≅
      tensorNaiveCotangentAwayModel A B Bg :=
  HomologicalComplex.Hom.isoOfComponents
    (naiveCotangentTensorToTensorModelXIso A B Bg)
    (naiveCotangentTensorToTensorModelXIso_comm A B Bg)

private theorem tensorToLocalizedSelfPresentation_cotangentComplex_apply
    (x : Bg ⊗[B] (selfExtension A B).Cotangent) :
    ((localizedSelfGenerators A B Bg g).toExtension.cotangentComplex)
        (LinearMap.liftBaseChange Bg
          (Extension.Cotangent.map
            ((Generators.localizationAway Bg g).toComp
              (Generators.self A B)).toExtensionHom) x) =
      ((Extension.CotangentSpace.map
          ((Generators.localizationAway Bg g).toComp
            (Generators.self A B)).toExtensionHom).liftBaseChange Bg)
        (LinearMap.baseChange Bg
          ((selfExtension A B).cotangentComplex) x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro t y
    rw [LinearMap.liftBaseChange_tmul, map_smul, LinearMap.baseChange_tmul,
      LinearMap.liftBaseChange_tmul]
    exact congrArg (fun z ↦ t • z)
      (Extension.CotangentSpace.map_cotangentComplex
        ((Generators.localizationAway Bg g).toComp
          (Generators.self A B)).toExtensionHom y).symm
  · intro x y hx hy
    simp [map_add, hx, hy]

private noncomputable def tensorToLocalizedSelfPresentation :
    tensorNaiveCotangentAwayModel A B Bg ⟶
      (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex :=
  let P := selfExtension A B
  let Q := Generators.localizationAway Bg g
  let C := (localizedSelfGenerators A B Bg g).toExtension
  ChainComplex.mkHom _ _
    (ModuleCat.ofHom
      (LinearMap.liftBaseChange Bg
        (Extension.CotangentSpace.map (Q.toComp (Generators.self A B)).toExtensionHom)))
    (ModuleCat.ofHom
      (((ULift.moduleEquiv :
            ULift C.Cotangent ≃ₗ[Bg] C.Cotangent).symm.toLinearMap) ∘ₗ
        LinearMap.liftBaseChange Bg
          (Extension.Cotangent.map (Q.toComp (Generators.self A B)).toExtensionHom)))
    (by
      ext x
      change
        ((localizedSelfGenerators A B Bg g).toExtension.cotangentComplex)
            (LinearMap.liftBaseChange Bg
              (Extension.Cotangent.map
                ((Generators.localizationAway Bg g).toComp
                  (Generators.self A B)).toExtensionHom) x) =
          ((Extension.CotangentSpace.map
              ((Generators.localizationAway Bg g).toComp
                (Generators.self A B)).toExtensionHom).liftBaseChange Bg)
            (LinearMap.baseChange Bg
              ((selfExtension A B).cotangentComplex) x)
      simpa [tensorNaiveCotangentAwayModel, selfExtension, localizedSelfGenerators,
        LinearMap.comp_assoc] using
        tensorToLocalizedSelfPresentation_cotangentComplex_apply A B Bg g x)
    (by
      intro n h
      refine ⟨0, ?_⟩
      rw [tensorNaiveCotangentAwayModel_d_succ_succ A B Bg n,
        Extension.naiveCotangentChainComplex_d_succ_succ
          ((localizedSelfGenerators A B Bg g).toExtension) n]
      simp)

/-- The canonical chain map
`NL_{B⁄A} ⊗[B] Bg ⟶ NL_{Bg⁄A}` obtained by localizing the
canonical self-presentation of `B` away from `g` and then comparing that localized presentation
with the owner self-presentation of the chosen away-localization target `Bg`. -/
noncomputable def naiveCotangent_tensor_comparison_of_isLocalizationAway :
    (((ModuleCat.extendScalars (algebraMap B Bg)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (NL_{B⁄A})) ⟶
      NL_{Bg⁄A} :=
  let f :
      (localizedSelfGenerators A B Bg g).toExtension.Hom
        (Generators.self A Bg).toExtension :=
    (Generators.defaultHom
      (localizedSelfGenerators A B Bg g)
      (Generators.self A Bg)).toExtensionHom
  (naiveCotangentTensorToTensorModelIso A B Bg).hom ≫
    tensorToLocalizedSelfPresentation A B Bg g ≫
    Extension.naiveCotangentChainMap f

-- Proof sketch: let `P := Generators.self A B`, and let `β` be the localized presentation
-- `(Generators.localizationAway Bg g).comp P` of `Bg` obtained by adjoining an inverse of `g`.
-- Mathlib's `cotangentCompLocalizationAwayEquiv` and `CotangentSpace.compEquiv` identify the
-- conormal and cotangent-space terms of `β` with the tensorized terms of `NL_{B⁄A}` plus the
-- contractible localization-away summand. The resulting comparison
-- `NL_{B⁄A} ⊗[B] Bg → β.naiveCotangentChainComplex` is therefore a homotopy equivalence, and the
-- canonical presentation-independence map from `β.naiveCotangentChainComplex` to the owner
-- `NL_{Bg⁄A}` is a homotopy equivalence as well. Passing to the homotopy category packages the
-- source statement as the claim that the canonical comparison morphism becomes an isomorphism.
private theorem naiveCotangent_tensor_comparison_of_isLocalizationAway_isIso_aux :
    IsIso
      ((HomotopyCategory.quotient (ModuleCat Bg) (ComplexShape.down ℕ)).map
        (naiveCotangent_tensor_comparison_of_isLocalizationAway A B Bg g)) := by
  sorry

/-- Lemma 10.134.12: for any away-localization target `Bg` of `B` at `g`, the canonical
comparison map
`NL_{B⁄A} ⊗[B] Bg ⟶ NL_{Bg⁄A}`
is a homotopy equivalence. -/
noncomputable def naiveCotangent_tensor_comparison_of_isLocalizationAway_homotopyEquiv :
    HomotopyEquiv
      (((ModuleCat.extendScalars (algebraMap B Bg)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (NL_{B⁄A}))
      NL_{Bg⁄A} := by
  let f := naiveCotangent_tensor_comparison_of_isLocalizationAway A B Bg g
  letI :
      IsIso
        ((HomotopyCategory.quotient (ModuleCat Bg) (ComplexShape.down ℕ)).map f) :=
    naiveCotangent_tensor_comparison_of_isLocalizationAway_isIso_aux A B Bg g
  let e :
      HomotopyEquiv
        (((ModuleCat.extendScalars (algebraMap B Bg)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (NL_{B⁄A}))
        NL_{Bg⁄A} :=
    HomotopyCategory.homotopyEquivOfIso <|
      asIso ((HomotopyCategory.quotient (ModuleCat Bg) (ComplexShape.down ℕ)).map f)
  have h : Homotopy e.hom f := by
    simpa [e, f, HomotopyCategory.homotopyEquivOfIso] using
      (HomotopyCategory.homotopyOutMap f)
  exact
    { hom := f
      inv := e.inv
      homotopyHomInvId := (h.symm.compRight e.inv).trans e.homotopyHomInvId
      homotopyInvHomId := (h.compLeft e.inv).symm.trans e.homotopyInvHomId }

/-- Companion: the homotopy-category image of the canonical comparison map from
`Lemma 10.134.12` is an isomorphism. -/
theorem naiveCotangent_tensor_comparison_of_isLocalizationAway_isIso :
    IsIso
      ((HomotopyCategory.quotient (ModuleCat Bg) (ComplexShape.down ℕ)).map
        (naiveCotangent_tensor_comparison_of_isLocalizationAway A B Bg g)) := by
  let e := naiveCotangent_tensor_comparison_of_isLocalizationAway_homotopyEquiv A B Bg g
  change IsIso (HomotopyCategory.isoOfHomotopyEquiv e).hom
  infer_instance

end
