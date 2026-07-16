import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Lemma_10_134_3

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
  -- The scalar-extended complex is the image of the restricted two-term complex, so its higher
  -- differentials are the image of zero.
  rw [scalarExtendedNaiveCotangentChainComplex,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d,
    Extension.naiveCotangentChainComplexRestrictScalars_d_succ_succ P R n]
  simpa using
    CategoryTheory.Functor.map_zero (ModuleCat.extendScalars (algebraMap R R'))
      ((P.naiveCotangentChainComplexRestrictScalars R).X (n + 2))
      ((P.naiveCotangentChainComplexRestrictScalars R).X (n + 1))

private theorem baseChangedNaiveCotangentChainComplex_d_eq_zero
    (P : Extension R S) (n : ℕ) :
    (baseChangedNaiveCotangentChainComplex R' P).d (n + 2) (n + 1) = 0 := by
  -- The base-changed presentation is also a two-term naive cotangent complex after restriction.
  let Q : Extension R' (R' ⊗[R] S) := baseChangedExtension R' P
  simpa [baseChangedNaiveCotangentChainComplex, baseChangedExtension, Q] using
    Extension.naiveCotangentChainComplexRestrictScalars_d_succ_succ Q R' n

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
  -- Only the degree `1 → 0` differential is nontrivial; every higher differential vanishes.
  intro i j hij
  subst i
  cases j with
  | zero =>
      ext x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · have hL :
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplexXIso P (0 + 1)).hom ≫
                  (tensorNaiveCotangentChainComplex R' P).d (0 + 1) 0))
              0 = 0 := by
            rw [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.map_zero, LinearMap.map_zero]
        have hR :
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplex R' P).d (0 + 1) 0 ≫
                  (scalarExtendedNaiveCotangentChainComplexXIso P 0).hom))
              0 = 0 := by
            rw [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.map_zero, LinearMap.map_zero]
        exact hL.trans hR.symm
      · intro t x
        rcases x with ⟨x⟩
        change
          (LinearMap.baseChange R' (P.cotangentComplex.restrictScalars R))
              ((TensorProduct.AlgebraTensorModule.congr
                  (restrictScalarsSelfEquiv R')
                  ((liftCotangentEquiv P).restrictScalars R))
                (t ⊗ₜ[R] ULift.up x)) =
            (LinearMap.baseChange R'
              ((P.cotangentComplex.comp (liftCotangentEquiv P).toLinearMap).restrictScalars R))
              (t ⊗ₜ[R] ULift.up x)
        rfl
      · intro x y hx hy
        calc
          (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplexXIso P (0 + 1)).hom ≫
                  (tensorNaiveCotangentChainComplex R' P).d (0 + 1) 0))
              (x + y) =
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplexXIso P (0 + 1)).hom ≫
                  (tensorNaiveCotangentChainComplex R' P).d (0 + 1) 0))
                x +
              (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplexXIso P (0 + 1)).hom ≫
                  (tensorNaiveCotangentChainComplex R' P).d (0 + 1) 0))
                y := by
                  simpa using
                    (LinearMap.map_add
                      (ModuleCat.Hom.hom
                        ((scalarExtendedNaiveCotangentChainComplexXIso P (0 + 1)).hom ≫
                          (tensorNaiveCotangentChainComplex R' P).d (0 + 1) 0))
                      x y)
          _ =
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplex R' P).d (0 + 1) 0 ≫
                  (scalarExtendedNaiveCotangentChainComplexXIso P 0).hom))
                x +
              (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplex R' P).d (0 + 1) 0 ≫
                  (scalarExtendedNaiveCotangentChainComplexXIso P 0).hom))
                y := by rw [hx, hy]
          _ =
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplex R' P).d (0 + 1) 0 ≫
                  (scalarExtendedNaiveCotangentChainComplexXIso P 0).hom))
              (x + y) := by
                simpa using
                  (LinearMap.map_add
                    (ModuleCat.Hom.hom
                      ((scalarExtendedNaiveCotangentChainComplex R' P).d (0 + 1) 0 ≫
                        (scalarExtendedNaiveCotangentChainComplexXIso P 0).hom))
                    x y).symm
  | succ j =>
      rw [show (tensorNaiveCotangentChainComplex R' P).d (j + 1 + 1) (j + 1) = 0 by
            simpa [Nat.add_assoc] using tensorNaiveCotangentChainComplex_d_eq_zero (P := P) j,
        show (scalarExtendedNaiveCotangentChainComplex R' P).d (j + 1 + 1) (j + 1) = 0 by
            simpa [Nat.add_assoc] using scalarExtendedNaiveCotangentChainComplex_d_eq_zero
              (P := P) j]
      ext x
      have hL :
          (ModuleCat.Hom.hom
              ((scalarExtendedNaiveCotangentChainComplexXIso P (j + 2)).hom ≫
                (0 : (tensorNaiveCotangentChainComplex R' P).X (j + 2) ⟶
                  (tensorNaiveCotangentChainComplex R' P).X (j + 1))))
            x = 0 := by
        rfl
      have hR :
          (ModuleCat.Hom.hom
              ((0 : (scalarExtendedNaiveCotangentChainComplex R' P).X (j + 2) ⟶
                (scalarExtendedNaiveCotangentChainComplex R' P).X (j + 1)) ≫
                (scalarExtendedNaiveCotangentChainComplexXIso P (j + 1)).hom))
            x = 0 := by
        rw [ModuleCat.hom_comp, LinearMap.comp_apply]
        change (ModuleCat.Hom.hom (scalarExtendedNaiveCotangentChainComplexXIso P (j + 1)).hom) 0 = 0
        simpa using
          (LinearMap.map_zero
            (ModuleCat.Hom.hom (scalarExtendedNaiveCotangentChainComplexXIso P (j + 1)).hom))
      simpa [Nat.add_assoc] using hL.trans hR.symm

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
  -- The base-change isomorphisms identify the conormal differential on pure tensors and hence
  -- on the whole tensor product by linearity.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- Both comparison maps are linear, so they agree on the zero tensor.
    exact (LinearMap.map_zero _).trans (LinearEquiv.map_zero _).symm
  · intro t y
    rw [Extension.tensorCotangentOfFlat_tmul, LinearMap.baseChange_tmul,
      Extension.tensorCotangentSpace_tmul,
      ← baseChangedExtension_algebraMap_smul_cotangent P t
          (Cotangent.map (P.toBaseChange R') y)]
    have hs :
        (algebraMap R' (R' ⊗[R] S) t) •
            CotangentSpace.map (P.toBaseChange R') (P.cotangentComplex y) =
          t • CotangentSpace.map (P.toBaseChange R') (P.cotangentComplex y) :=
      baseChangedExtension_algebraMap_smul_cotangentSpace P t
        (CotangentSpace.map (P.toBaseChange R') (P.cotangentComplex y))
    rw [map_smul, ← Extension.CotangentSpace.map_cotangentComplex (P.toBaseChange R') y]
    simpa using hs
  · intro x y hx hy
    simp [map_add, hx, hy]

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
  -- Route correction: the only nontrivial square is again `1 → 0`; higher squares collapse
  -- immediately because both complexes are two-term.
  intro i j hij
  subst i
  cases j with
  | zero =>
      ext x
      simpa [tensorNaiveCotangentChainComplex, baseChangedNaiveCotangentChainComplex,
        baseChangedExtension, Extension.naiveCotangentChainComplexRestrictScalars,
        Extension.naiveCotangentChainComplex, LinearMap.comp_assoc] using
        tensorCotangent_baseChangeCotangentComplex_apply (P := P) (R' := R') x
  | succ j =>
      rw [show (baseChangedNaiveCotangentChainComplex R' P).d (j + 1 + 1) (j + 1) = 0 by
            simpa [Nat.add_assoc] using baseChangedNaiveCotangentChainComplex_d_eq_zero
              (P := P) j,
        show (tensorNaiveCotangentChainComplex R' P).d (j + 1 + 1) (j + 1) = 0 by
            simpa [Nat.add_assoc] using tensorNaiveCotangentChainComplex_d_eq_zero (P := P) j]
      ext x
      have hL :
          (ModuleCat.Hom.hom
              ((tensorNaiveCotangentChainComplexXIso P (j + 2)).hom ≫
                (0 : (baseChangedNaiveCotangentChainComplex R' P).X (j + 2) ⟶
                  (baseChangedNaiveCotangentChainComplex R' P).X (j + 1))))
            x = 0 := by
        rfl
      have hR :
          (ModuleCat.Hom.hom
              ((0 : (tensorNaiveCotangentChainComplex R' P).X (j + 2) ⟶
                (tensorNaiveCotangentChainComplex R' P).X (j + 1)) ≫
                (tensorNaiveCotangentChainComplexXIso P (j + 1)).hom))
            x = 0 := by
        rw [ModuleCat.hom_comp, LinearMap.comp_apply]
        change (ModuleCat.Hom.hom (tensorNaiveCotangentChainComplexXIso P (j + 1)).hom) 0 = 0
        simpa using
          (LinearMap.map_zero
            (ModuleCat.Hom.hom (tensorNaiveCotangentChainComplexXIso P (j + 1)).hom))
      simpa [Nat.add_assoc] using hL.trans hR.symm

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
  · -- The two presentation maps are inverse on the source base-changed polynomial ring.
    have hfg :
        (P.baseChangeToBaseChange R').comp (P.baseChangeFromBaseChange R') =
          .id (P.toExtension.baseChange (T := R')) := by
      ext x
      change
        (MvPolynomial.algebraTensorAlgEquiv (σ := S) R R').symm
            ((MvPolynomial.algebraTensorAlgEquiv (σ := S) R R') x) = x
      exact (MvPolynomial.algebraTensorAlgEquiv (σ := S) R R').symm_apply_apply x
    exact Homotopy.ofEq <| by
      rw [← F.map_comp,
        ← Extension.naiveCotangentChainMap_comp (P.baseChangeFromBaseChange R')
          (P.baseChangeToBaseChange R'),
        hfg, Extension.naiveCotangentChainMap_id, F.map_id]
  · -- The reverse composition is the identity on the target base-changed presentation.
    have hgf :
        (P.baseChangeFromBaseChange R').comp (P.baseChangeToBaseChange R') =
          .id P'.toExtension := by
      ext x
      change
        (MvPolynomial.algebraTensorAlgEquiv (σ := S) R R')
            ((MvPolynomial.algebraTensorAlgEquiv (σ := S) R R').symm x) = x
      exact (MvPolynomial.algebraTensorAlgEquiv (σ := S) R R').apply_symm_apply x
    exact Homotopy.ofEq <| by
      rw [← F.map_comp,
        ← Extension.naiveCotangentChainMap_comp (P.baseChangeToBaseChange R')
          (P.baseChangeFromBaseChange R'),
        hgf, Extension.naiveCotangentChainMap_id, F.map_id]

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
@[stacks 00S4]
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
@[stacks 00S4]
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
