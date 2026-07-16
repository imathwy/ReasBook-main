import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap10.Lemma_10_134_3

open scoped NaiveCotangent TensorProduct
open Algebra
open Algebra.Extension
open Algebra.Generators
open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

section

variable {R : Type u} {S : Type u} {R' : Type u}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

attribute [local instance] SMulCommClass.of_commMonoid
attribute [local instance] TensorProduct.leftAlgebra
attribute [local instance] TensorProduct.rightAlgebra

local notation:max "NL_{" S "⁄" R "}↾[" T "]" =>
  Algebra.Extension.naiveCotangentChainComplexRestrictScalars
    (Generators.toExtension (Generators.self R S)) T

/- Domain triage:
* primary domain: flat base change for naive cotangent complexes of commutative algebras;
* sampled owner declarations:
  - `Algebra.naiveCotangent`, the source-facing owner `NL_{S⁄R}`;
  - `Algebra.Extension.naiveCotangentChainComplex`, the presentation-level owner for the
    underived two-term complex;
  - `Algebra.Extension.naiveCotangentChainComplexRestrictScalars`, the canonical bridge/view for
    viewing that owner over a smaller base ring;
  - `Algebra.Extension.tensorCotangentSpace` and `Algebra.Extension.tensorCotangentOfFlat`, the
    degree-`0` and degree-`1` flat base-change isomorphisms.
* best owner abstraction: the main source-facing statement should expose the canonical comparison
  from the scalar extension of `NL_{S⁄R}` as an `R`-linear complex to the restricted target owner
  `NL_{R' ⊗[R] S⁄R'}` as an `R'`-linear complex.
* primitive data vs. derived API:
  - primitive data: the owner complexes `NL_{S⁄R}` and
    `Algebra.Extension.naiveCotangentChainComplex` for the base-changed extension;
  - derived API: the tensor-model normalization of degree `1`, the comparison chain map, and the
    induced chain-complex isomorphism / homotopy equivalence.
* layer triage:
  - `source-facing`: flat base change for `NL_{S⁄R}`;
  - `core/canonical`: `NL_{S⁄R}` and `(P.baseChange : Extension R' (R' ⊗[R] S))
      .naiveCotangentChainComplexRestrictScalars R'`;
  - `bridge/view`: the private tensor model with degree `1` written as `R' ⊗[R] P.Cotangent`.
-/

private abbrev LiftCotangent (P : Extension R S) :=
  ULift.{u, u} P.Cotangent

private noncomputable abbrev liftCotangentEquiv (P : Extension R S) :
    LiftCotangent P ≃ₗ[S] P.Cotangent :=
  ULift.moduleEquiv

private noncomputable def restrictCotangentSpaceEquiv (P : Extension R S) :
    ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S P.CotangentSpace)) ≃ₗ[R]
      P.CotangentSpace :=
  { __ := AddEquiv.refl _
    map_smul' := fun _ _ ↦ by simp }

private noncomputable abbrev scalarExtendedNaiveCotangentChainComplex
    (T : Type u) [CommRing T] [Algebra R T] (P : Extension R S) :
    ChainComplex (ModuleCat T) ℕ :=
  ((ModuleCat.extendScalars (algebraMap R T)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (P.naiveCotangentChainComplexRestrictScalars R)

private noncomputable def tensorNaiveCotangentChainComplex
    (T : Type u) [CommRing T] [Algebra R T] (P : Extension R S) :
    ChainComplex (ModuleCat T) ℕ :=
  ChainComplex.mk'
    (ModuleCat.of T (T ⊗[R] P.CotangentSpace))
    (ModuleCat.of T (T ⊗[R] P.Cotangent))
    (ModuleCat.ofHom (LinearMap.baseChange T (P.cotangentComplex.restrictScalars R)))
    (fun {_ _} _ ↦ ⟨ModuleCat.of T PUnit, 0, zero_comp⟩)

private noncomputable abbrev baseChangedExtension
    (T : Type u) [CommRing T] [Algebra R T] (P : Extension R S) :
    Extension T (T ⊗[R] S) := by
  let Q : Extension T (T ⊗[R] S) := P.baseChange
  exact Q

private noncomputable abbrev baseChangedNaiveCotangentChainComplex
    (T : Type u) [CommRing T] [Algebra R T] (P : Extension R S) :
    ChainComplex (ModuleCat T) ℕ := by
  let Q : Extension T (T ⊗[R] S) := baseChangedExtension T P
  exact Q.naiveCotangentChainComplexRestrictScalars T

private noncomputable abbrev selfBaseChangedExtension :
    Extension R' (R' ⊗[R] S) := by
  let Q : Extension R' (R' ⊗[R] S) := (Generators.self R S).toExtension.baseChange
  exact Q

private noncomputable abbrev selfBaseChangedGenerators :
    Generators R' (R' ⊗[R] S) S := by
  let Q : Generators R' (R' ⊗[R] S) S := (Generators.self R S).baseChange R'
  exact Q

private theorem baseChangedExtension_algebraMap_smul_cotangent
    (P : Extension R S) :
    ∀ t : R', ∀ x : (baseChangedExtension R' P).Cotangent,
      (algebraMap R' (R' ⊗[R] S) t) • x = t • x := by
  intro t x
  rfl

private theorem baseChangedExtension_algebraMap_smul_cotangentSpace
    (P : Extension R S) :
    ∀ t : R', ∀ x : (baseChangedExtension R' P).CotangentSpace,
      (algebraMap R' (R' ⊗[R] S) t) • x = t • x := by
  intro t x
  dsimp [Extension.CotangentSpace] at x ⊢
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul s y =>
      simp [TensorProduct.smul_tmul', Algebra.smul_def]

private instance baseChangedExtensionCotangentIsScalarTower
    (P : Extension R S) :
    IsScalarTower R' (R' ⊗[R] S) (baseChangedExtension R' P).Cotangent :=
  IsScalarTower.of_algebraMap_smul
    (baseChangedExtension_algebraMap_smul_cotangent P)

private instance baseChangedExtensionCotangentSpaceIsScalarTower
    (P : Extension R S) :
    IsScalarTower R' (R' ⊗[R] S) (baseChangedExtension R' P).CotangentSpace :=
  IsScalarTower.of_algebraMap_smul
    (baseChangedExtension_algebraMap_smul_cotangentSpace P)

private instance baseChangedExtensionLiftCotangentIsScalarTower
    (P : Extension R S) :
    IsScalarTower R' (R' ⊗[R] S) (LiftCotangent (baseChangedExtension R' P)) :=
  IsScalarTower.of_algebraMap_smul fun t x ↦ by
    change ULift.up ((algebraMap R' (R' ⊗[R] S) t) • x.down) = ULift.up (t • x.down)
    simpa using baseChangedExtension_algebraMap_smul_cotangent P t x.down

private noncomputable def restrictScalarsSelfEquiv
    (T : Type u) [CommRing T] [Algebra R T] :
    ↑((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T T)) ≃ₗ[T] T :=
  { __ := AddEquiv.refl T
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower
    (T : Type u) [CommRing T] [Algebra R T] :
    IsScalarTower R T
      ↑((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T T)) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    rfl

private noncomputable def scalarExtendedPUnitIso
    (T : Type u) [CommRing T] [Algebra R T] :
    (ModuleCat.extendScalars (algebraMap R T)).obj (ModuleCat.of R PUnit) ≅
      ModuleCat.of T PUnit := by
  let e₁ :
      (ModuleCat.extendScalars (algebraMap R T)).obj (ModuleCat.of R PUnit) ≅
        ModuleCat.of T (T ⊗[R] PUnit) := by
    simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        (restrictScalarsSelfEquiv T)
        (LinearEquiv.refl R PUnit)).toModuleIso
  letI : Subsingleton (T ⊗[R] PUnit) := inferInstance
  let e₂ : ModuleCat.of T (T ⊗[R] PUnit) ≅ ModuleCat.of T PUnit :=
    (LinearEquiv.ofSubsingleton _ _).toModuleIso
  exact e₁ ≪≫ e₂

private noncomputable def restrictOfIso
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Type*) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] :
    (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M) ≅ ModuleCat.of A M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M)) ≃ₗ[A] M from
      { __ := AddEquiv.refl _
        map_smul' := fun _ _ ↦ by simp }).toModuleIso

private theorem tensorNaiveCotangentChainComplex_d_eq_zero
    (P : Extension R S) (n : ℕ) :
    ((tensorNaiveCotangentChainComplex R' P : ChainComplex (ModuleCat R') ℕ)).d (n + 2) (n + 1) = 0 := by
  rw [tensorNaiveCotangentChainComplex, ChainComplex.mk'_d]
  simp

private theorem scalarExtendedNaiveCotangentChainComplex_d_eq_zero
    (P : Extension R S) (n : ℕ) :
    (scalarExtendedNaiveCotangentChainComplex R' P).d (n + 2) (n + 1) = 0 := by
  sorry

private theorem baseChangedNaiveCotangentChainComplex_d_eq_zero
    (P : Extension R S) (n : ℕ) :
    (baseChangedNaiveCotangentChainComplex R' P).d (n + 2) (n + 1) = 0 := by
  sorry

private noncomputable def scalarExtendedNaiveCotangentChainComplexXIso
    (P : Extension R S) :
    ∀ n : ℕ,
      (scalarExtendedNaiveCotangentChainComplex R' P).X n ≅
        (tensorNaiveCotangentChainComplex R' P).X n
  | 0 => by
      let e :
          ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) ⊗[R]
              ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S P.CotangentSpace))
            ≃ₗ[R'] R' ⊗[R] P.CotangentSpace :=
        TensorProduct.AlgebraTensorModule.congr
          (restrictScalarsSelfEquiv R')
          (restrictCotangentSpaceEquiv P)
      simpa [scalarExtendedNaiveCotangentChainComplex, tensorNaiveCotangentChainComplex,
        Extension.naiveCotangentChainComplexRestrictScalars, Extension.naiveCotangentChainComplex,
        ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using e.toModuleIso
  | 1 => by
      let e :
          ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) ⊗[R]
              LiftCotangent P ≃ₗ[R'] R' ⊗[R] P.Cotangent :=
        TensorProduct.AlgebraTensorModule.congr
          (restrictScalarsSelfEquiv R')
          ((liftCotangentEquiv P).restrictScalars R)
      simpa [scalarExtendedNaiveCotangentChainComplex, tensorNaiveCotangentChainComplex,
        Extension.naiveCotangentChainComplexRestrictScalars, Extension.naiveCotangentChainComplex,
        ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using e.toModuleIso
  | n + 2 => by
      let succZeroR :
          ∀ {X₀ X₁ : ModuleCat.{u} R} (f : X₁ ⟶ X₀),
            Σ' (X₂ : ModuleCat.{u} R) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
        fun {_ _} _ ↦ ⟨ModuleCat.of.{u} R PUnit, 0, zero_comp⟩
      let succZeroR' :
          ∀ {X₀ X₁ : ModuleCat R'} (f : X₁ ⟶ X₀),
            Σ' (X₂ : ModuleCat R') (d : X₂ ⟶ X₁), d ≫ f = 0 :=
        fun {_ _} _ ↦ ⟨ModuleCat.of R' PUnit, 0, zero_comp⟩
      have hsrc :
          (scalarExtendedNaiveCotangentChainComplex R' P).X (n + 2) ≅
            ModuleCat.of R' PUnit := by
        let hX :
            (scalarExtendedNaiveCotangentChainComplex R' P).X (n + 2) =
              (ModuleCat.extendScalars (algebraMap R R')).obj
                ((P.naiveCotangentChainComplexRestrictScalars R).X (n + 2)) :=
          CategoryTheory.Functor.mapHomologicalComplex_obj_X
            (ModuleCat.extendScalars (algebraMap R R')) (ComplexShape.down ℕ)
            (P.naiveCotangentChainComplexRestrictScalars R) (n + 2)
        have hmkS : P.naiveCotangentChainComplex.X (n + 2) ≅ ModuleCat.of S PUnit := by
          simpa [Extension.naiveCotangentChainComplex] using
            (ChainComplex.mk'XIso
              (ModuleCat.of S P.CotangentSpace)
              (ModuleCat.of S (LiftCotangent P))
              (ModuleCat.ofHom (P.cotangentComplex.comp (liftCotangentEquiv P).toLinearMap))
              (fun {_ _} _ ↦ ⟨ModuleCat.of S PUnit, 0, zero_comp⟩) n)
        have hmk : (P.naiveCotangentChainComplexRestrictScalars R).X (n + 2) ≅
            ModuleCat.of R PUnit := by
          simpa [Extension.naiveCotangentChainComplexRestrictScalars] using
            (ModuleCat.restrictScalars (algebraMap R S)).mapIso hmkS ≪≫
              restrictOfIso PUnit
        simpa [scalarExtendedNaiveCotangentChainComplex] using
          eqToIso hX ≪≫ (ModuleCat.extendScalars (algebraMap R R')).mapIso hmk ≪≫
            scalarExtendedPUnitIso R'
      have htrg :
          (tensorNaiveCotangentChainComplex R' P).X (n + 2) ≅
            ModuleCat.of R' PUnit := by
        simpa [tensorNaiveCotangentChainComplex] using
          (ChainComplex.mk'XIso
            (ModuleCat.of R' (R' ⊗[R] P.CotangentSpace))
            (ModuleCat.of R' (R' ⊗[R] P.Cotangent))
            (ModuleCat.ofHom (LinearMap.baseChange R' (P.cotangentComplex.restrictScalars R)))
            succZeroR' n)
      exact hsrc ≪≫ htrg.symm

private theorem scalarExtendedNaiveCotangentChainComplexXIso_comm
    (P : Extension R S) :
    ∀ i j (_ : (ComplexShape.down ℕ).Rel i j),
      (scalarExtendedNaiveCotangentChainComplexXIso P i).hom ≫
          (tensorNaiveCotangentChainComplex R' P).d i j =
        (scalarExtendedNaiveCotangentChainComplex R' P).d i j ≫
          (scalarExtendedNaiveCotangentChainComplexXIso P j).hom := by
  sorry

private noncomputable def scalarExtendedNaiveCotangentChainComplexIso
    (P : Extension R S) :
    scalarExtendedNaiveCotangentChainComplex R' P ≅
      tensorNaiveCotangentChainComplex R' P :=
  HomologicalComplex.Hom.isoOfComponents
    (scalarExtendedNaiveCotangentChainComplexXIso P)
    (scalarExtendedNaiveCotangentChainComplexXIso_comm P)

private theorem tensorCotangent_baseChangeCotangentComplex_apply
    (P : Extension R S) [Module.Flat R R'] (x : R' ⊗[R] P.Cotangent) :
    (baseChangedExtension R' P).cotangentComplex (P.tensorCotangentOfFlat R' x) =
      (P.tensorCotangentSpace R')
        (LinearMap.baseChange R' (P.cotangentComplex.restrictScalars R) x) := by
  sorry

private noncomputable def tensorNaiveCotangentChainComplexXIso
    (P : Extension R S) [Module.Flat R R'] :
    ∀ n : ℕ,
      (tensorNaiveCotangentChainComplex R' P).X n ≅
        (baseChangedNaiveCotangentChainComplex R' P).X n
  | 0 => by
      let Q := baseChangedExtension R' P
      simpa [tensorNaiveCotangentChainComplex, baseChangedNaiveCotangentChainComplex,
        baseChangedExtension, Extension.naiveCotangentChainComplexRestrictScalars,
        Extension.naiveCotangentChainComplex] using
        (P.tensorCotangentSpace R').toModuleIso ≪≫
          (restrictOfIso Q.CotangentSpace).symm
  | 1 => by
      let Q := baseChangedExtension R' P
      simpa [tensorNaiveCotangentChainComplex, baseChangedNaiveCotangentChainComplex,
        baseChangedExtension, Extension.naiveCotangentChainComplexRestrictScalars,
        Extension.naiveCotangentChainComplex] using
        ((P.tensorCotangentOfFlat R').toModuleIso ≪≫
          (restrictOfIso Q.Cotangent).symm ≪≫
          (ModuleCat.restrictScalars (algebraMap R' (R' ⊗[R] S))).mapIso
            ((liftCotangentEquiv Q).symm.toModuleIso))
  | n + 2 => by
      let succZero :
          ∀ {X₀ X₁ : ModuleCat R'} (f : X₁ ⟶ X₀),
            Σ' (X₂ : ModuleCat R') (d : X₂ ⟶ X₁), d ≫ f = 0 :=
        fun {_ _} _ ↦ ⟨ModuleCat.of R' PUnit, 0, zero_comp⟩
      have htensor :
          (tensorNaiveCotangentChainComplex R' P).X (n + 2) ≅
            ModuleCat.of R' PUnit := by
        simpa [tensorNaiveCotangentChainComplex] using
          (ChainComplex.mk'XIso
            (ModuleCat.of R' (R' ⊗[R] P.CotangentSpace))
            (ModuleCat.of R' (R' ⊗[R] P.Cotangent))
            (ModuleCat.ofHom (LinearMap.baseChange R' (P.cotangentComplex.restrictScalars R)))
            succZero n)
      have hbase :
          (baseChangedNaiveCotangentChainComplex R' P).X (n + 2) ≅
            ModuleCat.of R' PUnit := by
        let Q := baseChangedExtension R' P
        let succZeroQ :
            ∀ {X₀ X₁ : ModuleCat (R' ⊗[R] S)} (f : X₁ ⟶ X₀),
              Σ' (X₂ : ModuleCat (R' ⊗[R] S)) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
          fun {_ _} _ ↦ ⟨ModuleCat.of (R' ⊗[R] S) PUnit, 0, zero_comp⟩
        let hX :
            (baseChangedNaiveCotangentChainComplex R' P).X (n + 2) =
              (ModuleCat.restrictScalars (algebraMap R' (R' ⊗[R] S))).obj
                (Q.naiveCotangentChainComplex.X (n + 2)) :=
          CategoryTheory.Functor.mapHomologicalComplex_obj_X
            (ModuleCat.restrictScalars (algebraMap R' (R' ⊗[R] S))) (ComplexShape.down ℕ)
            Q.naiveCotangentChainComplex (n + 2)
        have hmk : Q.naiveCotangentChainComplex.X (n + 2) ≅
            ModuleCat.of (R' ⊗[R] S) PUnit := by
          simpa [Extension.naiveCotangentChainComplex] using
            (ChainComplex.mk'XIso
              (ModuleCat.of (R' ⊗[R] S) Q.CotangentSpace)
              (ModuleCat.of (R' ⊗[R] S) (LiftCotangent Q))
              (ModuleCat.ofHom (Q.cotangentComplex.comp (liftCotangentEquiv Q).toLinearMap))
              succZeroQ n)
        simpa [baseChangedNaiveCotangentChainComplex] using
          eqToIso hX ≪≫ (ModuleCat.restrictScalars (algebraMap R' (R' ⊗[R] S))).mapIso hmk ≪≫
            restrictOfIso PUnit
      exact htensor ≪≫ hbase.symm

private theorem tensorNaiveCotangentChainComplexXIso_comm
    (P : Extension R S) [Module.Flat R R'] :
    ∀ i j (_ : (ComplexShape.down ℕ).Rel i j),
      (tensorNaiveCotangentChainComplexXIso P i).hom ≫
          (baseChangedNaiveCotangentChainComplex R' P).d i j =
        (tensorNaiveCotangentChainComplex R' P).d i j ≫
          (tensorNaiveCotangentChainComplexXIso P j).hom := by
  sorry

private noncomputable def tensorNaiveCotangentChainComplexIso
    (P : Extension R S) [Module.Flat R R'] :
    tensorNaiveCotangentChainComplex R' P ≅
      baseChangedNaiveCotangentChainComplex R' P :=
  HomologicalComplex.Hom.isoOfComponents
    (tensorNaiveCotangentChainComplexXIso P)
    (tensorNaiveCotangentChainComplexXIso_comm P)

private noncomputable def naiveCotangent_tensor_comparison_to_baseChangePresentation_iso
    [Module.Flat R R'] :
    (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (NL_{S⁄R}↾[R])) ≅
      (let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
       E.naiveCotangentChainComplexRestrictScalars R') := by
  let P : Extension R S := (Generators.self R S).toExtension
  let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
  simpa [scalarExtendedNaiveCotangentChainComplex, baseChangedNaiveCotangentChainComplex,
    baseChangedExtension, Algebra.naiveCotangent, E] using
    scalarExtendedNaiveCotangentChainComplexIso P ≪≫
      tensorNaiveCotangentChainComplexIso P

private noncomputable def baseChangeExtensionToPresentationHomotopyEquiv [Module.Flat R R'] :
    HomotopyEquiv
      (let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
       E.naiveCotangentChainComplexRestrictScalars R')
      (let P' : Generators R' (R' ⊗[R] S) S := selfBaseChangedGenerators
       P'.toExtension.naiveCotangentChainComplexRestrictScalars R') := by
  let F :=
    (ModuleCat.restrictScalars (algebraMap R' (R' ⊗[R] S))).mapHomologicalComplex (ComplexShape.down ℕ)
  let P := Generators.self R S
  let P' : Generators R' (R' ⊗[R] S) S := selfBaseChangedGenerators
  refine
    { hom := F.map (Extension.naiveCotangentChainMap (P.baseChangeFromBaseChange R'))
      inv := F.map (Extension.naiveCotangentChainMap (P.baseChangeToBaseChange R'))
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · sorry
  · sorry

private noncomputable def baseChangePresentationToOwnerHomotopyEquiv [Module.Flat R R'] :
    HomotopyEquiv
      (let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
       E.naiveCotangentChainComplexRestrictScalars R')
      NL_{R' ⊗[R] S⁄R'}↾[R'] := by
  let G := ModuleCat.restrictScalars (algebraMap R' (R' ⊗[R] S))
  let P' : Generators R' (R' ⊗[R] S) S := selfBaseChangedGenerators
  let e :=
    Generators.naiveCotangentChainHomotopyEquiv
      P'
      (Generators.self R' (R' ⊗[R] S))
  have eRaw :
      HomotopyEquiv
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P'.toExtension.naiveCotangentChainComplex)
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (Generators.self R' (R' ⊗[R] S)).toExtension.naiveCotangentChainComplex) :=
    G.mapHomotopyEquiv e
  let e' :
      HomotopyEquiv
        (P'.toExtension.naiveCotangentChainComplexRestrictScalars R')
        ((Generators.self R' (R' ⊗[R] S)).toExtension.naiveCotangentChainComplexRestrictScalars
          R') := by
    simpa [Extension.naiveCotangentChainComplexRestrictScalars] using eRaw
  exact (baseChangeExtensionToPresentationHomotopyEquiv).trans e'

-- Proof sketch: rewrite the scalar extension of `NL_{S⁄R}` as the private tensor model with
-- degree `1` normalized from `R' ⊗[R] ULift(I / I²)` to `R' ⊗[R] (I / I²)`. The flat base-change
-- isomorphisms `tensorCotangentSpace` and `tensorCotangentOfFlat` identify that tensor model with
-- the restricted owner complex `NL_{R' ⊗[R] S⁄R'}`.
/-- Lemma 10.134.8 (Flat base change): if `R → R'` is flat, then the canonical base-change map
from the scalar extension of `NL_{S⁄R}` to `NL_{R' ⊗[R] S⁄R'}`, both viewed as chain complexes of
`R'`-modules, is the owner-level comparison morphism induced by the flat base-change
identifications on the degree `0` and degree `1` terms. -/
noncomputable def naiveCotangent_tensor_comparison_of_flat [Module.Flat R R'] :
    (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (NL_{S⁄R}↾[R])) ⟶
      NL_{R' ⊗[R] S⁄R'}↾[R'] := by
  let e₁ :
      (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (NL_{S⁄R}↾[R])) ≅
        (let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
         E.naiveCotangentChainComplexRestrictScalars R') :=
    naiveCotangent_tensor_comparison_to_baseChangePresentation_iso
  let e₂ :
      HomotopyEquiv
        (let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
         E.naiveCotangentChainComplexRestrictScalars R')
        NL_{R' ⊗[R] S⁄R'}↾[R'] :=
    baseChangePresentationToOwnerHomotopyEquiv
  exact e₁.hom ≫ e₂.hom

/-- Lemma 10.134.8 (Flat base change): if `R → R'` is flat, then the canonical base-change map
from the scalar extension of `NL_{S⁄R}` to `NL_{R' ⊗[R] S⁄R'}`, both viewed as chain complexes of
`R'`-modules, is a homotopy equivalence. -/
noncomputable def naiveCotangent_tensor_homotopyEquiv_of_flat [Module.Flat R R'] :
    HomotopyEquiv
      (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (NL_{S⁄R}↾[R]))
      NL_{R' ⊗[R] S⁄R'}↾[R'] := by
  let e₁ :
      (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (NL_{S⁄R}↾[R])) ≅
        (let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
         E.naiveCotangentChainComplexRestrictScalars R') :=
    naiveCotangent_tensor_comparison_to_baseChangePresentation_iso
  let e₂ :
      HomotopyEquiv
        (let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
         E.naiveCotangentChainComplexRestrictScalars R')
        NL_{R' ⊗[R] S⁄R'}↾[R'] :=
    baseChangePresentationToOwnerHomotopyEquiv
  exact (HomotopyEquiv.ofIso e₁).trans e₂

/- The induced identification on first homology is the canonical owner theorem
`Algebra.tensorH1CotangentOfFlat`. -/
recall Algebra.tensorH1CotangentOfFlat

end
