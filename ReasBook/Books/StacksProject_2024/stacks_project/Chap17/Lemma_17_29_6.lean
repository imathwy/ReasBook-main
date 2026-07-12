import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Monoidal
import StacksProject_2024.Chap10.Lemma_10_133_6
import StacksProject_2024.Chap17.Lemma_17_28_4
import StacksProject_2024.Chap17.Definition_17_29_1

open CategoryTheory MonoidalCategory TopologicalSpace
open Functor.OplaxMonoidal
open PresheafOfModules.DifferentialsConstruction
open TopCat.Sheaf

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
variable (varphi : 𝒪₁ ⟶ 𝒪₂)
variable (ℱ : SheafOfModules (ringSheaf 𝒪₂))

-- Route correction: the prior version imported Chapter 18 only to obtain sheafification/tensor
-- adapter API. This file now carries the minimal adapter layer locally so the proof stays
-- dependency-closed inside Chapter 17.

/-- Helper for Lemma 17.29.6: the local sheafification functor on presheaves of
`\mathcal O`-modules over the opens site of `X`. -/
private noncomputable abbrev moduleSheafification
    (𝒪 : TopCat.Sheaf CommRingCat.{u} X) :
    PresheafOfModules (ringSheaf 𝒪).obj ⥤ SheafOfModules (ringSheaf 𝒪) :=
  PresheafOfModules.sheafification (𝟙 (ringSheaf 𝒪).obj)

/-- Helper for Lemma 17.29.6: the source-facing tensor product of sheaves of modules over
`\mathcal O`, presented by sheafifying the objectwise presheaf tensor product. -/
private noncomputable abbrev moduleTensor
    {𝒪 : TopCat.Sheaf CommRingCat.{u} X}
    (ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪)) :
    SheafOfModules (ringSheaf 𝒪) :=
  (moduleSheafification 𝒪).obj (PresheafOfModules.Monoidal.tensorObj ℱ.val 𝒢.val)

local infixr:70 " ⊗ " => moduleTensor

/-- Helper for Lemma 17.29.6: tensoring morphisms of sheaves of modules in each factor. -/
private noncomputable abbrev moduleTensorMap
    {𝒪 : TopCat.Sheaf CommRingCat.{u} X}
    {ℱ₁ ℱ₂ 𝒢₁ 𝒢₂ : SheafOfModules (ringSheaf 𝒪)}
    (α : ℱ₁ ⟶ ℱ₂) (β : 𝒢₁ ⟶ 𝒢₂) :
    moduleTensor ℱ₁ 𝒢₁ ⟶ moduleTensor ℱ₂ 𝒢₂ :=
  (moduleSheafification 𝒪).map (PresheafOfModules.Monoidal.tensorHom α.val β.val)

/-- Helper for Lemma 17.29.6: restricting scalars along the identity ring-sheaf map does not
change a presheaf of modules. -/
private noncomputable def restrictScalarsIdIso
    (𝒪 : TopCat.Sheaf CommRingCat.{u} X)
    (ℱ : PresheafOfModules (ringSheaf 𝒪).obj) :
    (PresheafOfModules.restrictScalars (𝟙 (ringSheaf 𝒪).obj)).obj ℱ ≅ ℱ :=
  PresheafOfModules.isoMk
    (fun U ↦ by
      simpa using
        (ModuleCat.restrictScalarsId'App
          (((𝟙 (ringSheaf 𝒪).obj : (ringSheaf 𝒪).obj ⟶ (ringSheaf 𝒪).obj).app U).hom)
          rfl
          (ℱ.obj U)))
    (fun {U V} i ↦ by
      -- Proof comment: the identity restriction adapter is componentwise the standard module
      -- identity, so naturality reduces to extensionality on sections.
      ext x
      rfl)

/-- Helper for Lemma 17.29.6: the sheafification unit, transported away from the identity
restriction-of-scalars presentation. -/
private noncomputable abbrev sheafificationUnitToVal
    (𝒪 : TopCat.Sheaf CommRingCat.{u} X)
    (ℱ : PresheafOfModules (ringSheaf 𝒪).obj) :
    ℱ ⟶ ((moduleSheafification 𝒪).obj ℱ).val :=
  -- Proof comment: compose the sheafification unit with the identity restriction-of-scalars
  -- adapter so the codomain is the literal underlying presheaf of the sheafification.
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒪).obj)).unit.app ℱ ≫
    (restrictScalarsIdIso 𝒪 ((moduleSheafification 𝒪).obj ℱ).val).hom

/-- Helper for Lemma 17.29.6: the tensor product of two sheafifications is canonically
identified with the sheafification of their presheaf tensor product. -/
private noncomputable abbrev moduleSheafificationTensorIso
    (𝒪 : TopCat.Sheaf CommRingCat.{u} X)
    (ℱ 𝒢 : PresheafOfModules (ringSheaf 𝒪).obj) :
    (((moduleSheafification 𝒪).obj ℱ) ⊗ ((moduleSheafification 𝒪).obj 𝒢)) ≅
      (moduleSheafification 𝒪).obj (PresheafOfModules.Monoidal.tensorObj ℱ 𝒢) :=
  (Functor.Monoidal.μIso
    (_root_.moduleSheafification
      (J := Opens.grothendieckTopology X)
      (TopCat.Sheaf.toRingedSpace (X := X) 𝒪).sheaf)
    ℱ 𝒢).symm

/-- The morphism `𝒪₁(U) → 𝒪₂(U)` on an open set, viewed as an algebra structure. -/
private abbrev sectionAlgebra (U : (Opens X)ᵒᵖ) :
    Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) :=
  RingHom.toAlgebra (varphi.hom.app U).hom

/-- The `𝒪₁(U)`-module structure on `ℱ(U)` induced by restriction of scalars along
`𝒪₁(U) → 𝒪₂(U)`. -/
private abbrev sectionModule (U : (Opens X)ᵒᵖ) :
    Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
  Module.compHom (ℱ.val.obj U) (((TopCat.Sheaf.ringSheafMap varphi).hom.app U).hom)

/-- Helper for Lemma 17.29.6: the sectionwise scalar tower induced by `varphi`. -/
private abbrev sectionIsScalarTower (U : (Opens X)ᵒᵖ) :
    letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
    letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
    IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) := by
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  exact IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)

/-- Helper for Lemma 17.29.6: the objectwise `k`-th principal-parts module on an open set. -/
private abbrev objectwisePrincipalPartsModule
    (k : ℕ) (U : (Opens X)ᵒᵖ) :
    ModuleCat (𝒪₂.obj.obj U) :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  ModuleCat.of (𝒪₂.obj.obj U)
    (principal_parts_module (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) k)

/-- Helper for Lemma 17.29.6: the universal class map `ℱ(U) → P^k_{𝒪₂(U)/𝒪₁(U)}(ℱ(U))`. -/
private abbrev objectwiseUniversalDifferential
    (k : ℕ) (U : (Opens X)ᵒᵖ) :
    letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
    letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
    letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
      sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
    ℱ.val.obj U →ₗ[𝒪₁.obj.obj U] ↑(objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) k U) :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  principal_parts_universal_differential
    (R := 𝒪₁.obj.obj U) (S := 𝒪₂.obj.obj U) (M := ℱ.val.obj U) k

/-- Helper for Lemma 17.29.6: the opens-site restriction map on objectwise principal parts. -/
private abbrev objectwisePrincipalPartsMap
    (k : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) k U ⟶
      (ModuleCat.restrictScalars (((ringSheaf 𝒪₂).obj.map i).hom)).obj
        (objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) k V) :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  letI : Algebra (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) := sectionAlgebra varphi V
  letI : Module (𝒪₁.obj.obj V) (ℱ.val.obj V) := sectionModule varphi ℱ V
  letI : IsScalarTower (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V)
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) := (𝒪₁.obj.map i).hom.toAlgebra
  letI : Algebra (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) := (𝒪₂.obj.map i).hom.toAlgebra
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj V) :=
    (((varphi.hom.app V).hom).comp ((𝒪₁.obj.map i).hom)).toAlgebra
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj V) :=
    Module.compHom (ℱ.val.obj V)
      (((varphi.hom.app V).hom).comp ((𝒪₁.obj.map i).hom))
  letI : Module (𝒪₂.obj.obj U) (ℱ.val.obj V) :=
    Module.compHom (ℱ.val.obj V) ((𝒪₂.obj.map i).hom)
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (varphi.hom.naturality i))
  letI : IsScalarTower (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
    IsScalarTower.of_compHom (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) (ℱ.val.obj V)
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (ℱ.val.obj V) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (ℱ.val.obj V)
  let iU : ℱ.val.obj U →ₗ[𝒪₂.obj.obj U] ℱ.val.obj V := (ℱ.val.map i).hom
  ModuleCat.ofHom (principalPartsBaseChangeMap k iU)

/-- Helper for Lemma 17.29.6: the opens-site restriction map is literally the Chapter 10
base-change map after installing the sectionwise scalar towers. -/
private theorem objectwisePrincipalPartsMap_typed
    (k : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    objectwisePrincipalPartsMap (varphi := varphi) (ℱ := ℱ) k i =
      letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
      letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
      letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
        IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
      letI : Algebra (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) := sectionAlgebra varphi V
      letI : Module (𝒪₁.obj.obj V) (ℱ.val.obj V) := sectionModule varphi ℱ V
      letI : IsScalarTower (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
        IsScalarTower.of_compHom (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V)
      letI : Algebra (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) := (𝒪₁.obj.map i).hom.toAlgebra
      letI : Algebra (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) := (𝒪₂.obj.map i).hom.toAlgebra
      letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj V) :=
        (((varphi.hom.app V).hom).comp ((𝒪₁.obj.map i).hom)).toAlgebra
      letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj V) :=
        Module.compHom (ℱ.val.obj V)
          (((varphi.hom.app V).hom).comp ((𝒪₁.obj.map i).hom))
      letI : Module (𝒪₂.obj.obj U) (ℱ.val.obj V) :=
        Module.compHom (ℱ.val.obj V) ((𝒪₂.obj.map i).hom)
      letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) :=
        IsScalarTower.of_algebraMap_eq' rfl
      letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) :=
        IsScalarTower.of_algebraMap_eq'
          (congrArg CommRingCat.Hom.hom (varphi.hom.naturality i))
      letI : IsScalarTower (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
        IsScalarTower.of_compHom (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) (ℱ.val.obj V)
      letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (ℱ.val.obj V) :=
        IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (ℱ.val.obj V)
      let iU : ℱ.val.obj U →ₗ[𝒪₂.obj.obj U] ℱ.val.obj V := (ℱ.val.map i).hom
      ModuleCat.ofHom (principalPartsBaseChangeMap
        (A := 𝒪₁.obj.obj U) (B := 𝒪₂.obj.obj U)
        (A' := 𝒪₁.obj.obj V) (B' := 𝒪₂.obj.obj V)
        (k := k) iU) := by
  -- Proof comment: this freezes the intended normal form so later proofs can rewrite directly to
  -- the Chapter 10 base-change map instead of re-unfolding the opens-site wrapper.
  rfl

/-- Helper for Lemma 17.29.6: linear maps out of principal parts are determined by the universal
generators `[m]`. -/
private theorem principalPartsLinearMapExtOnUniversalDifferential
    {A B M N : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [AddCommGroup N] [Module B N]
    (k : ℕ)
    {f g : principal_parts_module A B M k →ₗ[B] N}
    (h : ∀ m,
      f (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) =
        g (principal_parts_universal_differential (R := A) (S := B) (M := M) k m)) :
    f = g := by
  classical
  -- Proof comment: every quotient class is a linear combination of the universal generators `[m]`.
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (principal_parts_relation_submodule A B M k) x
  induction y using Finsupp.induction_linear with
  | zero =>
      simp
  | add y z hy hz =>
      rw [LinearMap.map_add, LinearMap.map_add, hy, hz]
      symm
      exact LinearMap.map_add g _ _
  | single m b =>
      have hsingle :
          (principal_parts_relation_submodule A B M k).mkQ (Finsupp.single m b) =
            b • principal_parts_universal_differential (R := A) (S := B) (M := M) k m := by
        -- Proof comment: a basis vector with coefficient `b` is `b` times the universal class.
        change
          (principal_parts_relation_submodule A B M k).mkQ (Finsupp.single m b) =
            b • (principal_parts_relation_submodule A B M k).mkQ (Finsupp.single m (1 : B))
        rw [← LinearMap.map_smul]
        congr
        ext m'
        by_cases hm' : m' = m
        · subst hm'
          simp
        · simp [hm']
      calc
        f ((principal_parts_relation_submodule A B M k).mkQ (Finsupp.single m b)) =
            f (b • principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
              rw [hsingle]
        _ = b • f (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
              rw [LinearMap.map_smul]
        _ = b • g (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
              rw [h m]
        _ = g (b • principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
              rw [LinearMap.map_smul]
        _ = g ((principal_parts_relation_submodule A B M k).mkQ (Finsupp.single m b)) := by
              rw [hsingle]

/-- Helper for Lemma 17.29.6: restriction on objectwise principal parts sends the universal
generator `[m]` to the universal generator of the restricted section. -/
private theorem objectwisePrincipalPartsMap_on_universal_differential
    (k : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom (objectwisePrincipalPartsMap (varphi := varphi) (ℱ := ℱ) k i))
        (objectwiseUniversalDifferential (varphi := varphi) (ℱ := ℱ) k U m) =
      objectwiseUniversalDifferential (varphi := varphi) (ℱ := ℱ) k V ((ℱ.val.map i).hom m) := by
  -- Proof comment: after freezing the opens-site restriction map as the Chapter 10 base-change
  -- map, the computation on `[m]` is the defining `Submodule.mapQ` formula.
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  letI : Algebra (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) := sectionAlgebra varphi V
  letI : Module (𝒪₁.obj.obj V) (ℱ.val.obj V) := sectionModule varphi ℱ V
  letI : IsScalarTower (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) V
  rw [objectwisePrincipalPartsMap_typed]
  rfl

/-- Helper for Lemma 17.29.6: identity restriction acts trivially on objectwise principal parts. -/
private theorem objectwisePrincipalPartsMap_id
    (k : ℕ) (U : (Opens X)ᵒᵖ) :
    objectwisePrincipalPartsMap (varphi := varphi) (ℱ := ℱ) k (𝟙 U) =
      (ModuleCat.restrictScalarsId' (((ringSheaf 𝒪₂).obj.map (𝟙 U)).hom)
        (congrArg RingCat.Hom.hom (((ringSheaf 𝒪₂).obj.map_id U)))).inv.app
        (objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) k U) := by
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  apply ModuleCat.hom_ext
  -- Proof comment: morphisms out of principal parts are determined by the universal generators
  -- `[m]`, so it suffices to compare the two maps on those generators.
  apply principalPartsLinearMapExtOnUniversalDifferential
    (A := 𝒪₁.obj.obj U) (B := 𝒪₂.obj.obj U) (M := ℱ.val.obj U) k
  intro m
  have hmap :
      (ModuleCat.Hom.hom (ℱ.val.map (𝟙 U))) m = m := by
    have hmap' :
        (ModuleCat.Hom.hom (ℱ.val.map (𝟙 U))) m =
          (ModuleCat.Hom.hom
            ((ModuleCat.restrictScalarsId' (((ringSheaf 𝒪₂).obj.map (𝟙 U)).hom)
              (congrArg RingCat.Hom.hom (((ringSheaf 𝒪₂).obj.map_id U)))).inv.app
              (ℱ.val.obj U))) m := by
      exact congrArg (fun h ↦ (ModuleCat.Hom.hom h) m) (ℱ.val.map_id U)
    -- Proof comment: the presheaf identity axiom factors through the standard restriction-of-scalars
    -- identity coherence, which is pointwise the identity map.
    calc
      (ModuleCat.Hom.hom (ℱ.val.map (𝟙 U))) m =
          (ModuleCat.Hom.hom
            ((ModuleCat.restrictScalarsId' (((ringSheaf 𝒪₂).obj.map (𝟙 U)).hom)
              (congrArg RingCat.Hom.hom (((ringSheaf 𝒪₂).obj.map_id U)))).inv.app
              (ℱ.val.obj U))) m := hmap'
      _ = m := by
        exact ModuleCat.restrictScalarsId'App_inv_apply
          (((ringSheaf 𝒪₂).obj.map (𝟙 U)).hom)
          (congrArg RingCat.Hom.hom (((ringSheaf 𝒪₂).obj.map_id U)))
          (ℱ.val.obj U)
          m
  rw [objectwisePrincipalPartsMap_on_universal_differential]
  rw [hmap]
  -- Proof comment: the restriction-of-scalars identity coherence acts trivially on the target.
  symm
  exact ModuleCat.restrictScalarsId'App_inv_apply
    (((ringSheaf 𝒪₂).obj.map (𝟙 U)).hom)
    (congrArg RingCat.Hom.hom (((ringSheaf 𝒪₂).obj.map_id U)))
    (objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) k U)
    (objectwiseUniversalDifferential (varphi := varphi) (ℱ := ℱ) k U m)

/-- Helper for Lemma 17.29.6: restriction on objectwise principal parts is functorial. -/
private theorem objectwisePrincipalPartsMap_comp
    (k : ℕ) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    objectwisePrincipalPartsMap (varphi := varphi) (ℱ := ℱ) k (i ≫ j) =
      objectwisePrincipalPartsMap (varphi := varphi) (ℱ := ℱ) k i ≫
        (ModuleCat.restrictScalars (((ringSheaf 𝒪₂).obj.map i).hom)).map
          (objectwisePrincipalPartsMap (varphi := varphi) (ℱ := ℱ) k j) ≫
        (ModuleCat.restrictScalarsComp' (((ringSheaf 𝒪₂).obj.map i).hom)
          (((ringSheaf 𝒪₂).obj.map j).hom)
          (((ringSheaf 𝒪₂).obj.map (i ≫ j)).hom)
          (congrArg RingCat.Hom.hom (((ringSheaf 𝒪₂).obj.map_comp i j)))).inv.app
          (objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) k W) := by
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  apply ModuleCat.hom_ext
  -- Proof comment: as in the identity case, it is enough to compare the two composites on the
  -- universal generators `[m]`.
  apply principalPartsLinearMapExtOnUniversalDifferential
    (A := 𝒪₁.obj.obj U) (B := 𝒪₂.obj.obj U) (M := ℱ.val.obj U) k
  intro m
  have hmap :
      (ModuleCat.Hom.hom (ℱ.val.map (i ≫ j))) m =
        (ModuleCat.Hom.hom (ℱ.val.map j)) ((ModuleCat.Hom.hom (ℱ.val.map i)) m) := by
    -- Proof comment: the presheaf composition axiom for `ℱ` supplies the sectionwise equality.
    simpa using congrArg (fun h ↦ (ModuleCat.Hom.hom h) m) (ℱ.val.map_comp i j)
  rw [objectwisePrincipalPartsMap_on_universal_differential]
  simp only [Category.assoc, objectwisePrincipalPartsMap_on_universal_differential,
    ModuleCat.restrictScalarsComp'App_inv_apply]
  rw [hmap]

/-- Helper for Lemma 17.29.6: the presheaf `U ↦ P^k_{𝒪₂(U)/𝒪₁(U)}(ℱ(U))` of objectwise
principal-parts modules. -/
private def principalPartsPresheaf
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) :
    PresheafOfModules (ringSheaf 𝒪₂).obj where
  obj U := objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) k U
  map i := objectwisePrincipalPartsMap (varphi := varphi) (ℱ := ℱ) k i
  map_id U := objectwisePrincipalPartsMap_id (varphi := varphi) (ℱ := ℱ) k U
  map_comp i j := objectwisePrincipalPartsMap_comp (varphi := varphi) (ℱ := ℱ) k i j

/-- Helper for Lemma 17.29.6: the sheaf `P^k_{𝒪₂/𝒪₁}(ℱ)`, obtained by sheafifying the canonical
principal-parts presheaf on the opens site of `X`. -/
private noncomputable abbrev principalPartsSheaf
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) :
    SheafOfModules (ringSheaf 𝒪₂) :=
  -- Proof comment: for this file we only need the sheafified presentation of principal parts.
  (moduleSheafification 𝒪₂).obj (principalPartsPresheaf varphi ℱ k)

local notation:max "P^{" k "}_[" φ "](" ℱ ")" =>
  principalPartsSheaf φ ℱ k

/- Domain-style sampling for Lemma 17.29.6:
- primary domain: the first principal-parts exact sequence for sheaves of modules over a morphism
  of sheaves of commutative rings;
- sampled owner declarations:
  `TopCat.Sheaf.principalParts`,
  `TopCat.Sheaf.principalParts_is_principal_parts_module_of_order`,
  `TopCat.Sheaf.relativeDifferentials`,
  `SheafOfModules.RingedSite.moduleTensor`,
  `Module.principalPartsSequence`;
- best owner abstraction: the source-facing owner is the sheaf of first principal parts
  `P^{1}_[varphi](ℱ)`, with the principal-parts sequence and its naturality maps attached as
  derived API on that owner;
- primitive data versus derived API: the only genuinely new primitive map is the left comparison
  `Ω(varphi) ⊗ ℱ ⟶ P^{1}_[varphi](ℱ)`, while the projection to `ℱ`, the short complex, and the
  induced maps on principal parts and on the resulting short complex are all derived from the
  existing owner `TopCat.Sheaf.principalParts`.

Source/core/bridge triage:
- `source-facing`: the principal-parts short exact sequence attached to `P^{1}_[varphi](ℱ)`;
- `core/canonical`: `TopCat.Sheaf.principalParts`, `Ω(varphi)`,
  `SheafOfModules.RingedSite.moduleTensor`,
  `Functor.CorepresentableBy`, and `ShortComplex`;
- `bridge/view`: the sheafified cotangent comparison map and the naturality morphisms it induces.
-/

namespace TopCat.Sheaf.principalParts

/-- Helper for Lemma 17.29.6: the objectwise principal-parts projection on an open set. -/
private noncomputable abbrev projectionPresheafApp
    (U : (Opens X)ᵒᵖ) :
    (principalPartsPresheaf varphi ℱ 1).obj U ⟶ ℱ.val.obj U :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  ModuleCat.ofHom
    (Module.principalPartsProjection
      (R := 𝒪₁.obj.obj U) (S := 𝒪₂.obj.obj U) (M := ℱ.val.obj U))

/-- Helper for Lemma 17.29.6: the sectionwise principal-parts projections commute with
restriction maps. -/
private theorem projectionPresheaf_naturality
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (principalPartsPresheaf varphi ℱ 1).map i ≫
        (ModuleCat.restrictScalars (((ringSheaf 𝒪₂).obj.map i).hom)).map
          (projectionPresheafApp (varphi := varphi) (ℱ := ℱ) V) =
      projectionPresheafApp (varphi := varphi) (ℱ := ℱ) U ≫ ℱ.val.map i := by
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  letI : Algebra (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) := sectionAlgebra varphi V
  letI : Module (𝒪₁.obj.obj V) (ℱ.val.obj V) := sectionModule varphi ℱ V
  letI : IsScalarTower (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) V
  -- Proof comment: this is the right commutative square of the sectionwise principal-parts
  -- sequence map induced by the restriction map on sections.
  simpa [projectionPresheafApp, objectwisePrincipalPartsMap_typed] using
    (Module.principalPartsSequenceMap
      (R := 𝒪₁.obj.obj U) (S := 𝒪₂.obj.obj U)
      (M := ℱ.val.obj U) (N := ℱ.val.obj V) ((ℱ.val.map i).hom)).comm₂₃

/-- Helper for Lemma 17.29.6: the sectionwise principal-parts projection assembled into a
presheaf morphism. -/
private noncomputable def projectionPresheaf :
    principalPartsPresheaf varphi ℱ 1 ⟶ ℱ.val :=
  { app := projectionPresheafApp (varphi := varphi) (ℱ := ℱ)
    naturality := projectionPresheaf_naturality (varphi := varphi) (ℱ := ℱ) }

/-- The canonical projection `P^1_{𝒪₂/𝒪₁}(ℱ) \to ℱ`, obtained by sheafifying the sectionwise
principal-parts projection. -/
noncomputable def projection :
    P^{1}_[varphi](ℱ) ⟶ ℱ :=
  -- Proof comment: this is the sheafified objectwise projection followed by the counit that
  -- identifies the sheafification of `ℱ.val` with `ℱ`.
  (moduleSheafification 𝒪₂).map (projectionPresheaf (varphi := varphi) (ℱ := ℱ)) ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒪₂).obj)).counit.app ℱ

/-- The objectwise tensor-source presheaf
`U ↦ Ω[𝒪₂(U)⁄𝒪₁(U)] ⊗_{𝒪₂(U)} ℱ(U)` underlying the sheaf map to principal parts. -/
private abbrev tensorSourcePresheaf :
    PresheafOfModules (ringSheaf 𝒪₂).obj :=
  PresheafOfModules.Monoidal.tensorObj (relativeDifferentials' varphi.hom) ℱ.val

/-- The sectionwise canonical map
`Ω[𝒪₂(U)⁄𝒪₁(U)] ⊗_{𝒪₂(U)} ℱ(U) → P^1_{𝒪₂(U)/𝒪₁(U)}(ℱ(U))`,
assembled into a morphism of presheaves. -/
private noncomputable abbrev cotangentToPresheafApp
    (U : (Opens X)ᵒᵖ) :
    (tensorSourcePresheaf varphi ℱ).obj U ⟶ (principalPartsPresheaf varphi ℱ 1).obj U :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  show (tensorSourcePresheaf varphi ℱ).obj U ⟶
      objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) 1 U from
    ModuleCat.ofHom
      (Module.principalPartsCotangentToPrincipalParts
        (R := 𝒪₁.obj.obj U) (S := 𝒪₂.obj.obj U) (M := ℱ.val.obj U))

/-- Helper for Lemma 17.29.6: the sectionwise cotangent maps commute with restriction maps. -/
private theorem cotangentToPresheaf_naturality_app
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (tensorSourcePresheaf varphi ℱ).map i ≫
        (ModuleCat.restrictScalars (((ringSheaf 𝒪₂).obj.map i).hom)).map
          (cotangentToPresheafApp (varphi := varphi) (ℱ := ℱ) V) =
      cotangentToPresheafApp (varphi := varphi) (ℱ := ℱ) U ≫
        (principalPartsPresheaf varphi ℱ 1).map i := by
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  letI : Algebra (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) := sectionAlgebra varphi V
  letI : Module (𝒪₁.obj.obj V) (ℱ.val.obj V) := sectionModule varphi ℱ V
  letI : IsScalarTower (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) V
  -- Proof comment: this is the left commutative square of the sectionwise principal-parts
  -- sequence map induced by restriction of sections.
  simpa [cotangentToPresheafApp, objectwisePrincipalPartsMap_typed] using
    (Module.principalPartsSequenceMap
      (R := 𝒪₁.obj.obj U) (S := 𝒪₂.obj.obj U)
      (M := ℱ.val.obj U) (N := ℱ.val.obj V) ((ℱ.val.map i).hom)).comm₁₂

private noncomputable def cotangentToPresheaf :
    tensorSourcePresheaf varphi ℱ ⟶ principalPartsPresheaf varphi ℱ 1 :=
  { app := cotangentToPresheafApp (varphi := varphi) (ℱ := ℱ)
    naturality := cotangentToPresheaf_naturality_app (varphi := varphi) (ℱ := ℱ) }

/-- Helper for Lemma 17.29.6: the presheaf-level left map lands in the kernel of the presheaf-level
projection. -/
private theorem cotangentToPresheaf_comp_projectionPresheaf :
    cotangentToPresheaf varphi ℱ ≫ projectionPresheaf (varphi := varphi) (ℱ := ℱ) = 0 := by
  ext U x
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  -- Proof comment: on each open set the row is exactly the algebraic principal-parts sequence.
  have hzero :=
    (Module.principalPartsSequence
      (R := 𝒪₁.obj.obj U) (S := 𝒪₂.obj.obj U) (M := ℱ.val.obj U)).zero
  simpa [cotangentToPresheaf, projectionPresheaf, cotangentToPresheafApp, projectionPresheafApp,
    Module.principalPartsSequence] using
    congrArg (fun f ↦ (ModuleCat.Hom.hom f) x) hzero

/-- The inverse of the sheafification counit for the underlying presheaf of `ℱ`. -/
private noncomputable abbrev sheafificationCounitInv :
    ℱ ⟶ (moduleSheafification 𝒪₂).obj ℱ.val :=
  let e :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒪₂).obj)).counit
  (e.app ℱ).inv

/-- Helper for Lemma 17.29.6: the inverse to the sheafification counit is a left inverse. -/
private theorem sheafificationCounitInv_comp_counit :
    sheafificationCounitInv (𝒪₂ := 𝒪₂) (ℱ := ℱ) ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒪₂).obj)).counit.app ℱ =
      𝟙 ℱ := by
  -- Proof comment: `sheafificationCounitInv` is the inverse morphism extracted from the counit
  -- isomorphism, so this is exactly `hom_inv_id`.
  let e :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒪₂).obj)).counit
  simpa [sheafificationCounitInv] using (e.app ℱ).inv_hom_id

/-- Helper for Lemma 17.29.6: the sheafification counit is also a left inverse to its chosen
inverse. -/
private theorem counit_comp_sheafificationCounitInv :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒪₂).obj)).counit.app ℱ ≫
        sheafificationCounitInv (𝒪₂ := 𝒪₂) (ℱ := ℱ) =
      𝟙 ((moduleSheafification 𝒪₂).obj ℱ.val) := by
  -- Proof comment: this is the companion identity `inv_hom_id` for the same counit isomorphism.
  let e :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒪₂).obj)).counit
  simpa [sheafificationCounitInv] using (e.app ℱ).hom_inv_id

/-- Helper for Lemma 17.29.6: the chosen inverse to the sheafification counit is natural in the
sheaf argument. -/
private theorem sheafificationCounitInv_naturality
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    α ≫ sheafificationCounitInv (𝒪₂ := 𝒪₂) (ℱ := 𝒢) =
      sheafificationCounitInv (𝒪₂ := 𝒪₂) (ℱ := ℱ) ≫
        (moduleSheafification 𝒪₂).map α.val := by
  -- Proof comment: this is exactly naturality of the inverse natural isomorphism to the counit.
  let e :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒪₂).obj)).counit
  simpa [sheafificationCounitInv] using e.inv.naturality α

/-- The canonical left map
`\Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F
  \to \mathcal P^1_{\mathcal O_2/\mathcal O_1}(\mathcal F)`,
obtained by sheafifying the sectionwise algebraic map from Lemma `10.133.6`. -/
noncomputable def cotangentTo :
    Ω(varphi) ⊗ ℱ ⟶ P^{1}_[varphi](ℱ) :=
  moduleTensorMap (𝟙 Ω(varphi)) (sheafificationCounitInv ℱ) ≫
    (moduleSheafificationTensorIso 𝒪₂ (relativeDifferentials' varphi.hom) ℱ.val).hom ≫
    (moduleSheafification 𝒪₂).map (cotangentToPresheaf varphi ℱ)

-- Proof sketch: objectwise this is exactly the algebraic identity
-- `principalPartsCotangentToPrincipalParts ≫ principalPartsProjection = 0` from
-- Lemma `10.133.6`, transported through the sheafification/tensor comparisons above.
@[reassoc]
theorem cotangentTo_comp_projection :
    cotangentTo varphi ℱ ≫ projection varphi ℱ = 0 := by
  -- Proof comment: after reassociating, the middle composite is the sheafification of the
  -- presheaf-level zero composite already proved above.
  rw [cotangentTo, projection, Category.assoc, Category.assoc, ← Functor.map_comp]
  rw [cotangentToPresheaf_comp_projectionPresheaf, Functor.map_zero, zero_comp, zero_comp]

/-- The canonical short complex
`\Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F
  \to \mathcal P^1_{\mathcal O_2/\mathcal O_1}(\mathcal F) \to \mathcal F`
attached to first principal parts. -/
noncomputable def sequence :
    ShortComplex (SheafOfModules (ringSheaf 𝒪₂)) :=
  ShortComplex.mk
    (cotangentTo varphi ℱ)
    (projection varphi ℱ)
    (cotangentTo_comp_projection varphi ℱ)

/-- Helper for Lemma 17.29.6: evaluation functors jointly reflect isomorphisms in an ordinary
functor category. -/
private theorem evaluationJointlyReflectsIsomorphisms
    {J A : Type*} [Category J] [Category A] :
    JointlyReflectIsomorphisms
      ((CategoryTheory.evaluation J A).obj : J → (J ⥤ A) ⥤ A) := by
  -- Proof comment: a natural transformation is an isomorphism as soon as each component is.
  refine ⟨fun {F G} α _ ↦ ?_⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro j
  simpa using (inferInstance : IsIso (((CategoryTheory.evaluation J A).obj j).map α))

/-- Helper for Lemma 17.29.6: a short complex in a functor category is short exact exactly when
all of its evaluations are short exact. -/
private theorem shortExact_iff_pointwiseShortExactFunctorCategory
    {J A : Type*} [Category J] [Category A] [Abelian A]
    {S : ShortComplex (J ⥤ A)} :
    S.ShortExact ↔ ∀ j, (S.map ((CategoryTheory.evaluation J A).obj j)).ShortExact := by
  let hEval := evaluationJointlyReflectsIsomorphisms (J := J) (A := A)
  constructor
  · intro hS j
    -- Proof comment: exactness, monomorphy, and epimorphy in a functor category are componentwise.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact (hEval.exact_iff S).1 hS.exact j
    · exact (NatTrans.mono_iff_mono_app S.f).1 hS.mono_f j
    · exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g j
  · intro hS
    -- Proof comment: reassemble the global short exact row from the pointwise ones.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact (hEval.exact_iff S).2 fun j ↦ (hS j).exact
    · exact (NatTrans.mono_iff_mono_app S.f).2 fun j ↦ (hS j).mono_f
    · exact (NatTrans.epi_iff_epi_app S.g).2 fun j ↦ (hS j).epi_g

/-- Helper for Lemma 17.29.6: a short complex of presheaves of modules is short exact once all
open-set evaluations are short exact. -/
private theorem presheafOfModules_shortExact_of_pointwise
    {𝒪 : TopCat.Sheaf CommRingCat.{u} X}
    {S : ShortComplex (PresheafOfModules (ringSheaf 𝒪).obj)}
    (hS : ∀ U : (Opens X)ᵒᵖ,
      (S.map (PresheafOfModules.evaluation (ringSheaf 𝒪).obj U)).ShortExact) :
    S.ShortExact := by
  let F := PresheafOfModules.toPresheaf (ringSheaf 𝒪).obj
  have hUnderlying :
      (S.map F).ShortExact := by
    refine (shortExact_iff_pointwiseShortExactFunctorCategory
      (J := (Opens X)ᵒᵖ) (A := Ab.{u}) (S := S.map F)).2 ?_
    intro U
    let evalU := PresheafOfModules.evaluation (ringSheaf 𝒪).obj U
    let G : ModuleCat ((ringSheaf 𝒪).obj.obj U) ⥤ Ab.{u} := forget₂ _ _
    have hForgetU :
        (((S.map evalU).map G)).ShortExact := by
      let hExactG :
          exactFunctor
            (ModuleCat ((ringSheaf 𝒪).obj.obj U))
            Ab.{u}
            G := (ExactFunctor.of G).property
      exact
        (((Functor.exact_tfae G).out 3 0).1
          (by simpa [exactFunctor_iff] using hExactG))
          (S.map evalU) (hS U)
    -- Proof comment: after forgetting module structure at `U`, evaluation is the ordinary
    -- functor-category evaluation on the underlying additive presheaf.
    change
      ((S.map F).map ((CategoryTheory.evaluation (Opens X)ᵒᵖ Ab.{u}).obj U)).ShortExact
    simpa [F, evalU, PresheafOfModules.evaluation] using hForgetU
  -- Proof comment: the faithful forgetful functor from module-valued presheaves reflects short
  -- exactness once the underlying additive presheaf row is short exact.
  exact ShortComplex.reflects_shortExact_of_faithful F hUnderlying

/-- Helper for Lemma 17.29.6: the presheaf-level principal-parts row before sheafification. -/
private noncomputable def presheafSequence :
    ShortComplex (PresheafOfModules (ringSheaf 𝒪₂).obj) :=
  ShortComplex.mk
    (cotangentToPresheaf varphi ℱ)
    (projectionPresheaf (varphi := varphi) (ℱ := ℱ))
    (cotangentToPresheaf_comp_projectionPresheaf (varphi := varphi) (ℱ := ℱ))

/-- Helper for Lemma 17.29.6: the presheaf principal-parts row is already short exact sectionwise,
and hence short exact as a row of presheaves of modules. -/
private theorem presheafSequenceShortExact :
    (presheafSequence (varphi := varphi) (ℱ := ℱ)).ShortExact := by
  -- TODO: invoke the sectionwise algebraic short exact sequence once the Chapter 10 theorem name
  -- and normalization are stabilized.
  refine presheafOfModules_shortExact_of_pointwise (𝒪 := 𝒪₂) ?_
  intro U
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  -- Proof comment: evaluation on an open set recovers the algebraic principal-parts sequence.
  simpa [presheafSequence, cotangentToPresheaf, projectionPresheaf, cotangentToPresheafApp,
    projectionPresheafApp, Module.principalPartsSequence] using
    (principal_parts_sequence_shortExact
      (R := 𝒪₁.obj.obj U) (S := 𝒪₂.obj.obj U) (M := ℱ.val.obj U))

-- Proof sketch: apply the sectionwise short exact principal-parts sequence from
-- Lemma `10.133.6`, transport the source and middle terms through Lemmas `17.28.4` and `17.29.5`,
-- and identify the resulting right map with `projection`.
/-- Lemma 17.29.6: there is a canonical short exact sequence
`0 ⟶ \Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F
  ⟶ \mathcal P^1_{\mathcal O_2/\mathcal O_1}(\mathcal F) ⟶ \mathcal F ⟶ 0`,
called the sequence of principal parts. -/
theorem sequence_shortExact :
    (sequence varphi ℱ).ShortExact := by
  let S := moduleSheafification 𝒪₂
  have hExactS :
      exactFunctor
        (PresheafOfModules (ringSheaf 𝒪₂).obj)
        (SheafOfModules (ringSheaf 𝒪₂))
        S := (ExactFunctor.of S).property
  have hMapped :
      ((presheafSequence (varphi := varphi) (ℱ := ℱ)).map S).ShortExact := by
    exact
      (((Functor.exact_tfae S).out 3 0).1
        (by simpa [exactFunctor_iff] using hExactS))
        (presheafSequence (varphi := varphi) (ℱ := ℱ))
        (presheafSequenceShortExact (varphi := varphi) (ℱ := ℱ))
  let counitIso :
      S.obj ℱ.val ≅ ℱ :=
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒪₂).obj)).counit).app ℱ
  let targetIso : ℱ ≅ S.obj ℱ.val := counitIso.symm
  let sourceIso :
      Ω(varphi) ⊗ ℱ ≅ S.obj (tensorSourcePresheaf varphi ℱ) :=
    (MonoidalCategory.tensorIso (Iso.refl _) targetIso) ≪≫
      moduleSheafificationTensorIso 𝒪₂ (relativeDifferentials' varphi.hom) ℱ.val
  let e :
      sequence varphi ℱ ≅ ((presheafSequence (varphi := varphi) (ℱ := ℱ)).map S) :=
    ShortComplex.isoMk sourceIso (Iso.refl _) targetIso
      (by
        -- Proof comment: this is the definition of `cotangentTo`, with the source comparison
        -- isolated as `sourceIso`.
        simp [sourceIso, targetIso, counitIso, cotangentTo, sheafificationCounitInv])
      (by
        -- Proof comment: the right comparison is the inverse of the sheafification counit used
        -- to identify the sheafified target presheaf with `ℱ`.
        simp [projection, targetIso, counitIso, sheafificationCounitInv])
  exact ShortComplex.shortExact_of_iso e.symm hMapped

-- The next block packages the canonical map on first principal-parts sheaves induced by a
-- morphism of `\mathcal O_2`-module sheaves.
/-- Helper for Lemma 17.29.6: the objectwise principal-parts base-change map on an open set. -/
private noncomputable abbrev mapPresheafApp
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢)
    (U : (Opens X)ᵒᵖ) :
    (principalPartsPresheaf varphi ℱ 1).obj U ⟶ (principalPartsPresheaf varphi 𝒢 1).obj U :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := 𝒢) U
  show objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) 1 U ⟶
      objectwisePrincipalPartsModule (varphi := varphi) (ℱ := 𝒢) 1 U from
    ModuleCat.ofHom
      (principalPartsBaseChangeMap 1 ((α.val.app U).hom))

/-- Helper for Lemma 17.29.6: the objectwise principal-parts base-change map sends the universal
generator `[m]` to the universal generator of the image section. -/
private theorem mapPresheafApp_on_universal_differential
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢)
    (U : (Opens X)ᵒᵖ) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom (mapPresheafApp (varphi := varphi) α U))
        (objectwiseUniversalDifferential (varphi := varphi) (ℱ := ℱ) 1 U m) =
      objectwiseUniversalDifferential (varphi := varphi) (ℱ := 𝒢) 1 U
        ((α.val.app U).hom m) := by
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := 𝒢) U
  -- Proof comment: once the wrapper is frozen as the Chapter 10 base-change map, the image of
  -- `[m]` is the defining `Submodule.mapQ` computation.
  rfl

/-- Helper for Lemma 17.29.6: the objectwise principal-parts base-change maps commute with
restriction maps. -/
private theorem mapPresheaf_naturality_app
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (principalPartsPresheaf varphi ℱ 1).map i ≫
        (ModuleCat.restrictScalars (((ringSheaf 𝒪₂).obj.map i).hom)).map
          (mapPresheafApp (varphi := varphi) α V) =
      mapPresheafApp (varphi := varphi) α U ≫
        (principalPartsPresheaf varphi 𝒢 1).map i := by
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := 𝒢) U
  apply ModuleCat.hom_ext
  -- Proof comment: both composites out of principal parts are determined by their values on the
  -- universal generators `[m]`.
  apply principalPartsLinearMapExtOnUniversalDifferential
    (A := 𝒪₁.obj.obj U) (B := 𝒪₂.obj.obj U) (M := ℱ.val.obj U) 1
  intro m
  have hα :
      (ModuleCat.Hom.hom (α.val.app V)) ((ℱ.val.map i).hom m) =
        (ModuleCat.Hom.hom (𝒢.val.map i)) ((ModuleCat.Hom.hom (α.val.app U)) m) := by
    -- Proof comment: this is the sectionwise naturality of the module morphism `α`.
    simpa [ModuleCat.restrictScalarsComp'App_inv_apply] using
      congrArg (fun h ↦ (ModuleCat.Hom.hom h) m) (α.val.naturality i)
  rw [objectwisePrincipalPartsMap_on_universal_differential]
  simp only [Category.assoc, mapPresheafApp_on_universal_differential,
    objectwisePrincipalPartsMap_on_universal_differential,
    ModuleCat.restrictScalarsComp'App_inv_apply]
  rw [hα]

/-- Helper for Lemma 17.29.6: package the objectwise principal-parts base-change maps into a
presheaf morphism. -/
private noncomputable def mapPresheaf
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    principalPartsPresheaf varphi ℱ 1 ⟶ principalPartsPresheaf varphi 𝒢 1 :=
  { app := mapPresheafApp (varphi := varphi) α
    naturality := mapPresheaf_naturality_app (varphi := varphi) α }

/-- Helper for Lemma 17.29.6: the presheaf-level principal-parts projection is natural in the
module argument. -/
private theorem projectionPresheaf_naturality_module
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    mapPresheaf (varphi := varphi) α ≫ projectionPresheaf (varphi := varphi) (ℱ := 𝒢) =
      projectionPresheaf (varphi := varphi) (ℱ := ℱ) ≫ α.val := by
  ext U
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := 𝒢) U
  -- Proof comment: at each open set this is the right square of the algebraic principal-parts
  -- sequence map induced by `α(U)`.
  simpa [mapPresheaf, projectionPresheaf, mapPresheafApp, projectionPresheafApp] using
    (Module.principalPartsSequenceMap
      (R := 𝒪₁.obj.obj U) (S := 𝒪₂.obj.obj U)
      (M := ℱ.val.obj U) (N := 𝒢.val.obj U) ((α.val.app U).hom)).comm₂₃

/-- Helper for Lemma 17.29.6: the left map in the presheaf-level principal-parts sequence is
natural in the module argument. -/
private theorem cotangentToPresheaf_naturality
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    PresheafOfModules.Monoidal.tensorHom (𝟙 (relativeDifferentials' varphi.hom)) α.val ≫
        cotangentToPresheaf varphi 𝒢 =
      cotangentToPresheaf varphi ℱ ≫ mapPresheaf (varphi := varphi) α := by
  ext U
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := 𝒢) U
  -- Proof comment: at each open set this is the left square of the algebraic principal-parts
  -- sequence map induced by `α(U)`.
  simpa [cotangentToPresheaf, mapPresheaf, cotangentToPresheafApp, mapPresheafApp] using
    (Module.principalPartsSequenceMap
      (R := 𝒪₁.obj.obj U) (S := 𝒪₂.obj.obj U)
      (M := ℱ.val.obj U) (N := 𝒢.val.obj U) ((α.val.app U).hom)).comm₁₂

@[inherit_doc mapPresheaf]
noncomputable def map
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    P^{1}_[varphi](ℱ) ⟶ P^{1}_[varphi](𝒢) :=
  -- Proof comment: sheafify the packaged objectwise principal-parts base-change map.
  (moduleSheafification 𝒪₂).map (mapPresheaf (varphi := varphi) α)

/-- Helper for Lemma 17.29.6: tensoring by a fixed left factor preserves composition in the right
factor. -/
private theorem moduleTensorMap_comp_right
    {𝒪 : TopCat.Sheaf CommRingCat.{u} X}
    {𝒜 ℬ 𝒞 𝒟 : SheafOfModules (ringSheaf 𝒪)}
    (β : ℬ ⟶ 𝒞) (γ : 𝒞 ⟶ 𝒟) :
    moduleTensorMap (𝒪 := 𝒪) (𝟙 𝒜) β ≫
        moduleTensorMap (𝒪 := 𝒪) (𝟙 𝒜) γ =
      moduleTensorMap (𝒪 := 𝒪) (𝟙 𝒜) (β ≫ γ) := by
  -- Proof comment: `tensorHom` is bifunctorial, so sheafifying preserves the same composition.
  simpa [moduleTensorMap, Functor.map_comp] using
    congrArg
      (fun f ↦ (moduleSheafification 𝒪).map f)
      (MonoidalCategory.tensorHom_comp_tensorHom (𝟙 𝒜.val) β.val (𝟙 𝒜.val) γ.val)

/-- Helper for Lemma 17.29.6: the tensor/sheafification comparison is natural in the right
presheaf argument. -/
private theorem moduleSheafificationTensorIso_naturality_right
    (𝒪 : TopCat.Sheaf CommRingCat.{u} X)
    (𝒜 : PresheafOfModules (ringSheaf 𝒪).obj)
    {ℬ 𝒞 : PresheafOfModules (ringSheaf 𝒪).obj} (β : ℬ ⟶ 𝒞) :
    moduleTensorMap (𝒪 := 𝒪)
        (𝟙 ((moduleSheafification 𝒪).obj 𝒜))
        ((moduleSheafification 𝒪).map β) ≫
      (moduleSheafificationTensorIso 𝒪 𝒜 𝒞).hom =
    (moduleSheafificationTensorIso 𝒪 𝒜 ℬ).hom ≫
      (moduleSheafification 𝒪).map (PresheafOfModules.Monoidal.tensorHom (𝟙 𝒜) β) := by
  let _ :
      Functor.Monoidal
        (_root_.moduleSheafification
          (J := Opens.grothendieckTopology X)
          (TopCat.Sheaf.toRingedSpace (X := X) 𝒪).sheaf) := inferInstance
  rw [moduleSheafificationTensorIso]
  rw [μ_natural_right_assoc]
  simp [moduleTensorMap]

-- Proof sketch: this is the sheafified version of the sectionwise naturality of
-- `Module.principalPartsProjection`.
theorem projection_naturality
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    CommSq
      (map varphi α)
      (projection varphi ℱ)
      (projection varphi 𝒢)
      α := by
  -- Proof comment: after sheafifying the presheaf-level right square, the remaining step is the
  -- counit naturality square for sheafification.
  refine ⟨?_⟩
  rw [map, projection, projection]
  rw [Category.assoc, ← Functor.map_comp, projectionPresheaf_naturality_module]
  rw [Functor.map_comp]
  simpa using
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒪₂).obj)).counit.naturality α

-- Proof sketch: this is the sheafified version of the sectionwise naturality of
-- `Module.principalPartsCotangentToPrincipalParts`.
theorem cotangentTo_naturality
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    CommSq
      (moduleTensorMap (𝟙 Ω(varphi)) α)
      (cotangentTo varphi ℱ)
      (cotangentTo varphi 𝒢)
      (map varphi α) := by
  -- Proof comment: move `α` past the chosen inverse counit, transport across the tensor/
  -- sheafification comparison, and finish with the presheaf-level left square.
  refine ⟨?_⟩
  rw [cotangentTo, cotangentTo, map]
  rw [Category.assoc, Category.assoc]
  rw [moduleTensorMap_comp_right]
  rw [sheafificationCounitInv_naturality]
  rw [← moduleTensorMap_comp_right]
  rw [Category.assoc, moduleSheafificationTensorIso_naturality_right]
  rw [Category.assoc, ← Functor.map_comp, cotangentToPresheaf_naturality]
  simp [Functor.map_comp, Category.assoc]

/-- The canonical morphism of principal-parts sequences induced by a morphism of
`\mathcal O_2`-module sheaves. -/
noncomputable def sequenceMap
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    sequence varphi ℱ ⟶ sequence varphi 𝒢 :=
  ShortComplex.homMk
    (show Ω(varphi) ⊗ ℱ ⟶ Ω(varphi) ⊗ 𝒢 from moduleTensorMap (𝟙 Ω(varphi)) α)
    (map varphi α)
    α
    (cotangentTo_naturality varphi α).w
    (projection_naturality varphi α).w

end TopCat.Sheaf.principalParts

end
