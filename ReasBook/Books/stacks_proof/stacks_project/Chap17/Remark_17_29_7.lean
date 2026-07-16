import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Monoidal
import stacks_proof.stacks_project.Chap10.Lemma_10_133_6
import stacks_proof.stacks_project.Chap10.Remark_10_150_9
import stacks_proof.stacks_project.Chap17.Definition_17_29_1
import stacks_proof.stacks_project.Chap17.Lemma_17_28_4
import stacks_proof.stacks_project.Chap17.Lemma_17_28_8
import stacks_proof.stacks_project.Chap17.Lemma_17_29_5
import stacks_proof.stacks_project.Chap17.Lemma_17_29_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal
open PresheafOfModules.DifferentialsConstruction
open SheafOfModules.RingedSite (restrictionAlong)
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
variable {𝒜 𝒜' 𝒜'' : TopCat.Sheaf CommRingCat.{u} X}
variable {𝒝 𝒝' 𝒝'' : TopCat.Sheaf CommRingCat.{u} X}

/- Domain-style sampling for Remark 17.29.7:
- primary domain: base change for the first principal-parts sequence on a fixed topological space;
- sampled owner declarations:
  `CategoryTheory.CommSq`,
  `SheafOfModules.RingedSite.restrictionAlong`,
  `TopCat.Sheaf.principalParts`,
  `TopCat.Sheaf.relativeDifferentialsMap`,
  `Functor.LaxMonoidal.μ`;
- best owner abstraction: the source-facing sheaf `P^{k}_[varphi](ℱ)` together with the canonical
  same-site change-of-rings owner `restrictionAlong β`; the algebraic
  `principalPartsBaseChangeMap` is used only sectionwise as a bridge for the middle term,
  `relativeDifferentialsMap` supplies the canonical left edge on cotangent terms, the source-facing
  tensor owner `moduleTensor` is bridged through sheafification to the presheaf comparison
  `Functor.LaxMonoidal.μ`, and `CommSq` is the canonical owner for the ring-square input;
- primitive data: a commutative square `CommSq a varphi varphi' β` of sheaves of rings and a
  `\mathcal B`-linear map `ℱ ⟶ (restrictionAlong β).obj ℱ'`;
- derived API: the induced canonical sheaf morphism on principal parts; compatibility with further
  composition and with the principal-parts projection is theorem-shaped API derived from this
  owner.

Source/core/bridge triage:
- `source-facing`: the induced sheaf morphism
  `P^{k}_[varphi](ℱ) ⟶ (restrictionAlong β).obj P^{k}_[varphi'](ℱ')`;
- `core/canonical`: the sheaf owners `TopCat.Sheaf.principalParts` and `restrictionAlong β`;
- `bridge/view`: the `CommSq` input square and the objectwise algebraic map
  `principalPartsBaseChangeMap` on the presheaf presentation. -/

namespace TopCat.Sheaf.principalParts

/-- Helper for Remark 17.29.7: the local sheafification functor on presheaves of
`\mathcal O`-modules over the opens site of `X`. -/
private noncomputable abbrev moduleSheafification
    (𝒪 : TopCat.Sheaf CommRingCat.{u} X) :
    PresheafOfModules (ringSheaf 𝒪).obj ⥤ SheafOfModules (ringSheaf 𝒪) :=
  PresheafOfModules.sheafification (𝟙 (ringSheaf 𝒪).obj)

/-- Helper for Remark 17.29.7: the source-facing tensor product of sheaves of modules over
`\mathcal O`, presented by sheafifying the objectwise presheaf tensor product. -/
private noncomputable abbrev moduleTensor
    {𝒪 : TopCat.Sheaf CommRingCat.{u} X}
    (ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪)) :
    SheafOfModules (ringSheaf 𝒪) :=
  (moduleSheafification 𝒪).obj (PresheafOfModules.Monoidal.tensorObj ℱ.val 𝒢.val)

local infixr:70 " ⊗ " => moduleTensor

/-- Helper for Remark 17.29.7: tensoring morphisms of sheaves of modules in each factor. -/
private noncomputable abbrev moduleTensorMap
    {𝒪 : TopCat.Sheaf CommRingCat.{u} X}
    {ℱ₁ ℱ₂ 𝒢₁ 𝒢₂ : SheafOfModules (ringSheaf 𝒪)}
    (α : ℱ₁ ⟶ ℱ₂) (β : 𝒢₁ ⟶ 𝒢₂) :
    moduleTensor ℱ₁ 𝒢₁ ⟶ moduleTensor ℱ₂ 𝒢₂ :=
  (moduleSheafification 𝒪).map (PresheafOfModules.Monoidal.tensorHom α.val β.val)

/-- Helper for Remark 17.29.7: the `𝒜(U)`-algebra structure on `𝒝(U)` induced by `varphi`. -/
private abbrev sectionAlgebra
    {𝒜 𝒝 : TopCat.Sheaf CommRingCat.{u} X}
    (varphi : 𝒜 ⟶ 𝒝) (U : (Opens X)ᵒᵖ) :
    Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) :=
  RingHom.toAlgebra (varphi.hom.app U).hom

/-- Helper for Remark 17.29.7: the `𝒜(U)`-module structure on `ℱ(U)` obtained by restricting
scalars along `varphi`. -/
private abbrev sectionModule
    {𝒜 𝒝 : TopCat.Sheaf CommRingCat.{u} X}
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝)) (U : (Opens X)ᵒᵖ) :
    Module (𝒜.obj.obj U) (ℱ.val.obj U) :=
  Module.compHom (ℱ.val.obj U) (((TopCat.Sheaf.ringSheafMap varphi).hom.app U).hom)

/-- Helper for Remark 17.29.7: the sectionwise scalar tower induced by `varphi`. -/
private abbrev sectionIsScalarTower
    {𝒜 𝒝 : TopCat.Sheaf CommRingCat.{u} X}
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝)) (U : (Opens X)ᵒᵖ) :
    letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) := sectionAlgebra varphi U
    letI : Module (𝒜.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
    IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) := by
  letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒜.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  exact IsScalarTower.of_compHom (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U)

/-- Helper for Remark 17.29.7: the objectwise `k`-th principal-parts module on an open set. -/
private abbrev objectwisePrincipalPartsModule
    {𝒜 𝒝 : TopCat.Sheaf CommRingCat.{u} X}
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝))
    (k : ℕ) (U : (Opens X)ᵒᵖ) :
    ModuleCat (𝒝.obj.obj U) :=
  letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒜.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  ModuleCat.of (𝒝.obj.obj U)
    (principal_parts_module (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) k)

/-- Helper for Remark 17.29.7: the universal class map `ℱ(U) → P^k_{𝒝(U)/𝒜(U)}(ℱ(U))`. -/
private abbrev objectwiseUniversalDifferential
    {𝒜 𝒝 : TopCat.Sheaf CommRingCat.{u} X}
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝))
    (k : ℕ) (U : (Opens X)ᵒᵖ) :
    letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) := sectionAlgebra varphi U
    letI : Module (𝒜.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
    letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) :=
      sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
    ℱ.val.obj U →ₗ[𝒜.obj.obj U] ↑(objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) k U) :=
  letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒜.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  principal_parts_universal_differential
    (R := 𝒜.obj.obj U) (S := 𝒝.obj.obj U) (M := ℱ.val.obj U) k

/-- Helper for Remark 17.29.7: the opens-site restriction map on objectwise principal parts. -/
private abbrev objectwisePrincipalPartsMap
    {𝒜 𝒝 : TopCat.Sheaf CommRingCat.{u} X}
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝))
    (k : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) k U ⟶
      (ModuleCat.restrictScalars (((ringSheaf 𝒝).obj.map i).hom)).obj
        (objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) k V) :=
  letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒜.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U)
  letI : Algebra (𝒜.obj.obj V) (𝒝.obj.obj V) := sectionAlgebra varphi V
  letI : Module (𝒜.obj.obj V) (ℱ.val.obj V) := sectionModule varphi ℱ V
  letI : IsScalarTower (𝒜.obj.obj V) (𝒝.obj.obj V) (ℱ.val.obj V) :=
    IsScalarTower.of_compHom (𝒜.obj.obj V) (𝒝.obj.obj V) (ℱ.val.obj V)
  letI : Algebra (𝒜.obj.obj U) (𝒜.obj.obj V) := (𝒜.obj.map i).hom.toAlgebra
  letI : Algebra (𝒝.obj.obj U) (𝒝.obj.obj V) := (𝒝.obj.map i).hom.toAlgebra
  letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj V) :=
    (((varphi.hom.app V).hom).comp ((𝒜.obj.map i).hom)).toAlgebra
  letI : Module (𝒜.obj.obj U) (ℱ.val.obj V) :=
    Module.compHom (ℱ.val.obj V)
      (((varphi.hom.app V).hom).comp ((𝒜.obj.map i).hom))
  letI : Module (𝒝.obj.obj U) (ℱ.val.obj V) :=
    Module.compHom (ℱ.val.obj V) ((𝒝.obj.map i).hom)
  letI : IsScalarTower (𝒜.obj.obj U) (𝒜.obj.obj V) (𝒝.obj.obj V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (𝒝.obj.obj V) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (varphi.hom.naturality i))
  letI : IsScalarTower (𝒝.obj.obj U) (𝒝.obj.obj V) (ℱ.val.obj V) :=
    IsScalarTower.of_compHom (𝒝.obj.obj U) (𝒝.obj.obj V) (ℱ.val.obj V)
  letI : IsScalarTower (𝒜.obj.obj U) (𝒜.obj.obj V) (ℱ.val.obj V) :=
    IsScalarTower.of_compHom (𝒜.obj.obj U) (𝒜.obj.obj V) (ℱ.val.obj V)
  let iU : ℱ.val.obj U →ₗ[𝒝.obj.obj U] ℱ.val.obj V := (ℱ.val.map i).hom
  ModuleCat.ofHom (principalPartsBaseChangeMap k iU)

/-- Helper for Remark 17.29.7: the opens-site restriction map is the Chapter 10
base-change map after installing the sectionwise scalar towers. -/
private theorem objectwisePrincipalPartsMap_typed
    {𝒜 𝒝 : TopCat.Sheaf CommRingCat.{u} X}
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝))
    (k : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    objectwisePrincipalPartsMap (varphi := varphi) (ℱ := ℱ) k i =
      letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) := sectionAlgebra varphi U
      letI : Module (𝒜.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
      letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) :=
        IsScalarTower.of_compHom (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U)
      letI : Algebra (𝒜.obj.obj V) (𝒝.obj.obj V) := sectionAlgebra varphi V
      letI : Module (𝒜.obj.obj V) (ℱ.val.obj V) := sectionModule varphi ℱ V
      letI : IsScalarTower (𝒜.obj.obj V) (𝒝.obj.obj V) (ℱ.val.obj V) :=
        IsScalarTower.of_compHom (𝒜.obj.obj V) (𝒝.obj.obj V) (ℱ.val.obj V)
      letI : Algebra (𝒜.obj.obj U) (𝒜.obj.obj V) := (𝒜.obj.map i).hom.toAlgebra
      letI : Algebra (𝒝.obj.obj U) (𝒝.obj.obj V) := (𝒝.obj.map i).hom.toAlgebra
      letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj V) :=
        (((varphi.hom.app V).hom).comp ((𝒜.obj.map i).hom)).toAlgebra
      letI : Module (𝒜.obj.obj U) (ℱ.val.obj V) :=
        Module.compHom (ℱ.val.obj V)
          (((varphi.hom.app V).hom).comp ((𝒜.obj.map i).hom))
      letI : Module (𝒝.obj.obj U) (ℱ.val.obj V) :=
        Module.compHom (ℱ.val.obj V) ((𝒝.obj.map i).hom)
      letI : IsScalarTower (𝒜.obj.obj U) (𝒜.obj.obj V) (𝒝.obj.obj V) :=
        IsScalarTower.of_algebraMap_eq' rfl
      letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (𝒝.obj.obj V) :=
        IsScalarTower.of_algebraMap_eq'
          (congrArg CommRingCat.Hom.hom (varphi.hom.naturality i))
      letI : IsScalarTower (𝒝.obj.obj U) (𝒝.obj.obj V) (ℱ.val.obj V) :=
        IsScalarTower.of_compHom (𝒝.obj.obj U) (𝒝.obj.obj V) (ℱ.val.obj V)
      letI : IsScalarTower (𝒜.obj.obj U) (𝒜.obj.obj V) (ℱ.val.obj V) :=
        IsScalarTower.of_compHom (𝒜.obj.obj U) (𝒜.obj.obj V) (ℱ.val.obj V)
      let iU : ℱ.val.obj U →ₗ[𝒝.obj.obj U] ℱ.val.obj V := (ℱ.val.map i).hom
      ModuleCat.ofHom (principalPartsBaseChangeMap
        (A := 𝒜.obj.obj U) (B := 𝒝.obj.obj U)
        (A' := 𝒜.obj.obj V) (B' := 𝒝.obj.obj V)
        (k := k) iU) := by
  -- Proof comment: this freezes the intended normal form so later proofs can rewrite directly to
  -- the Chapter 10 base-change map instead of re-unfolding the opens-site wrapper.
  rfl

/-- Helper for Remark 17.29.7: restriction on objectwise principal parts sends the universal
generator `[m]` to the universal generator of the restricted section. -/
private theorem objectwisePrincipalPartsMap_on_universal_differential
    {𝒜 𝒝 : TopCat.Sheaf CommRingCat.{u} X}
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝))
    (k : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom (objectwisePrincipalPartsMap (varphi := varphi) (ℱ := ℱ) k i))
        (objectwiseUniversalDifferential (varphi := varphi) (ℱ := ℱ) k U m) =
      objectwiseUniversalDifferential (varphi := varphi) (ℱ := ℱ) k V
        ((ℱ.val.map i).hom m) := by
  -- Proof comment: after freezing the opens-site restriction map as the Chapter 10 base-change
  -- map, the computation on `[m]` is the defining `Submodule.mapQ` formula.
  letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒜.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  letI : Algebra (𝒜.obj.obj V) (𝒝.obj.obj V) := sectionAlgebra varphi V
  letI : Module (𝒜.obj.obj V) (ℱ.val.obj V) := sectionModule varphi ℱ V
  letI : IsScalarTower (𝒜.obj.obj V) (𝒝.obj.obj V) (ℱ.val.obj V) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) V
  rw [objectwisePrincipalPartsMap_typed]
  simp only [objectwiseUniversalDifferential, principal_parts_universal_differential,
    Submodule.mapQ_apply]

/-- Helper for Remark 17.29.7: linear maps out of a module of principal parts are determined by
their values on the universal generators `[m]`. -/
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
  -- Proof comment: every quotient class comes from the free presentation, and every free
  -- presentation element is a linear combination of the basis vectors `[m]`.
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (principal_parts_relation_submodule A B M k) x
  change
    f ((principal_parts_relation_submodule A B M k).mkQ y) =
      g ((principal_parts_relation_submodule A B M k).mkQ y)
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

/-- Helper for Remark 17.29.7: identity restriction acts trivially on objectwise principal
parts. -/
private theorem objectwisePrincipalPartsMap_id
    {𝒜 𝒝 : TopCat.Sheaf CommRingCat.{u} X}
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝))
    (k : ℕ) (U : (Opens X)ᵒᵖ) :
    objectwisePrincipalPartsMap (varphi := varphi) (ℱ := ℱ) k (𝟙 U) =
      (ModuleCat.restrictScalarsId' (((ringSheaf 𝒝).obj.map (𝟙 U)).hom)
        (congrArg RingCat.Hom.hom (((ringSheaf 𝒝).obj.map_id U)))).inv.app
        (objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) k U) := by
  letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒜.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  apply ModuleCat.hom_ext
  -- Proof comment: morphisms out of principal parts are determined by the universal generators
  -- `[m]`, so it suffices to compare the two maps on those generators.
  apply principalPartsLinearMapExtOnUniversalDifferential
    (A := 𝒜.obj.obj U) (B := 𝒝.obj.obj U) (M := ℱ.val.obj U) k
  intro m
  have hmap :
      (ModuleCat.Hom.hom (ℱ.val.map (𝟙 U))) m = m := by
    have hmap' :
        (ModuleCat.Hom.hom (ℱ.val.map (𝟙 U))) m =
          (ModuleCat.Hom.hom
            ((ModuleCat.restrictScalarsId' (((ringSheaf 𝒝).obj.map (𝟙 U)).hom)
              (congrArg RingCat.Hom.hom (((ringSheaf 𝒝).obj.map_id U)))).inv.app
              (ℱ.val.obj U))) m := by
      exact congrArg (fun h ↦ (ModuleCat.Hom.hom h) m) (ℱ.val.map_id U)
    -- Proof comment: the presheaf identity axiom factors through the standard restriction-of-scalars
    -- identity coherence, which is pointwise the identity map.
    calc
      (ModuleCat.Hom.hom (ℱ.val.map (𝟙 U))) m =
          (ModuleCat.Hom.hom
            ((ModuleCat.restrictScalarsId' (((ringSheaf 𝒝).obj.map (𝟙 U)).hom)
              (congrArg RingCat.Hom.hom (((ringSheaf 𝒝).obj.map_id U)))).inv.app
              (ℱ.val.obj U))) m := hmap'
      _ = m := by
        exact ModuleCat.restrictScalarsId'App_inv_apply
          (((ringSheaf 𝒝).obj.map (𝟙 U)).hom)
          (congrArg RingCat.Hom.hom (((ringSheaf 𝒝).obj.map_id U)))
          (ℱ.val.obj U)
          m
  rw [objectwisePrincipalPartsMap_on_universal_differential]
  rw [hmap]
  -- Proof comment: the restriction-of-scalars identity coherence acts trivially on the target.
  symm
  exact ModuleCat.restrictScalarsId'App_inv_apply
    (((ringSheaf 𝒝).obj.map (𝟙 U)).hom)
    (congrArg RingCat.Hom.hom (((ringSheaf 𝒝).obj.map_id U)))
    (objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) k U)
    (objectwiseUniversalDifferential (varphi := varphi) (ℱ := ℱ) k U m)

/-- Helper for Remark 17.29.7: restriction on objectwise principal parts is functorial. -/
private theorem objectwisePrincipalPartsMap_comp
    {𝒜 𝒝 : TopCat.Sheaf CommRingCat.{u} X}
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝))
    (k : ℕ) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    objectwisePrincipalPartsMap (varphi := varphi) (ℱ := ℱ) k (i ≫ j) =
      objectwisePrincipalPartsMap (varphi := varphi) (ℱ := ℱ) k i ≫
        (ModuleCat.restrictScalars (((ringSheaf 𝒝).obj.map i).hom)).map
          (objectwisePrincipalPartsMap (varphi := varphi) (ℱ := ℱ) k j) ≫
        (ModuleCat.restrictScalarsComp' (((ringSheaf 𝒝).obj.map i).hom)
          (((ringSheaf 𝒝).obj.map j).hom)
          (((ringSheaf 𝒝).obj.map (i ≫ j)).hom)
          (congrArg RingCat.Hom.hom (((ringSheaf 𝒝).obj.map_comp i j)))).inv.app
          (objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) k W) := by
  letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒜.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower (varphi := varphi) (ℱ := ℱ) U
  apply ModuleCat.hom_ext
  -- Proof comment: as in the identity case, it is enough to compare the two composites on the
  -- universal generators `[m]`.
  apply principalPartsLinearMapExtOnUniversalDifferential
    (A := 𝒜.obj.obj U) (B := 𝒝.obj.obj U) (M := ℱ.val.obj U) k
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

/-- Helper for Remark 17.29.7: the presheaf `U ↦ P^k_{𝒝(U)/𝒜(U)}(ℱ(U))` of objectwise
principal-parts modules. -/
private def principalPartsPresheaf
    {𝒜 𝒝 : TopCat.Sheaf CommRingCat.{u} X}
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝))
    (k : ℕ) :
    PresheafOfModules (ringSheaf 𝒝).obj where
  obj U := objectwisePrincipalPartsModule (varphi := varphi) (ℱ := ℱ) k U
  map i := objectwisePrincipalPartsMap (varphi := varphi) (ℱ := ℱ) k i
  map_id U := objectwisePrincipalPartsMap_id (varphi := varphi) (ℱ := ℱ) k U
  map_comp i j := objectwisePrincipalPartsMap_comp (varphi := varphi) (ℱ := ℱ) k i j

private theorem isDifferentialOperatorOfOrder_succ
    {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
    (varphi : 𝒪₁ ⟶ 𝒪₂)
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)}
    {k : ℕ}
    {D : (restrictionAlong varphi).obj ℱ ⟶ (restrictionAlong varphi).obj 𝒢}
    (hD : TopCat.Sheaf.IsDifferentialOperatorOfOrder varphi D k) :
    TopCat.Sheaf.IsDifferentialOperatorOfOrder varphi D (k + 1) := by
  intro U
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := (varphi.hom.app U).hom.toAlgebra
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
    Module.compHom (ℱ.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) :=
    Module.compHom (𝒢.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
  letI : SMulCommClass (𝒪₂.obj.obj U) (𝒪₁.obj.obj U) (ℱ.val.obj U) := inferInstance
  letI : SMulCommClass (𝒪₂.obj.obj U) (𝒪₁.obj.obj U) (𝒢.val.obj U) := inferInstance
  let DU : ℱ.val.obj U →ₗ[𝒪₁.obj.obj U] 𝒢.val.obj U := (D.val.app U).hom
  have hDU :
      DU.IsDifferentialOperatorOfOrder (𝒪₂.obj.obj U) k := by
    simpa [DU] using
      SheafOfModules.RingedSite.isDifferentialOperatorOfOrder_app varphi D hD U
  have hDU' : DU.IsDifferentialOperatorOfOrder (𝒪₂.obj.obj U) (k + 1) :=
    LinearMap.isDifferentialOperatorOfOrder_succ_of_isDifferentialOperatorOfOrder hDU
  simpa [DU] using hDU'

private theorem section_square_commutes
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β) (U : (Opens X)ᵒᵖ) :
    ((β.hom.app U).hom.comp (varphi.hom.app U).hom) =
      ((varphi'.hom.app U).hom.comp (a.hom.app U).hom) := by
  exact congrArg CommRingCat.Hom.hom (congrArg (fun f ↦ f.hom.app U) sq.w.symm)

/-- The objectwise map on principal-parts modules attached to a commutative square of sheaves of
commutative rings and a compatible module map. -/
private abbrev sectionBaseChangeHom
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ')
    (k : ℕ) (U : (Opens X)ᵒᵖ) :
    (principalPartsPresheaf varphi ℱ k).obj U ⟶
      ((PresheafOfModules.restrictScalars (ringSheafMap β).hom).obj
        (principalPartsPresheaf varphi' ℱ' k)).obj U := by
  letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) := (varphi.hom.app U).hom.toAlgebra
  letI : Algebra (𝒜.obj.obj U) (𝒜'.obj.obj U) := (a.hom.app U).hom.toAlgebra
  letI : Algebra (𝒝.obj.obj U) (𝒝'.obj.obj U) := (β.hom.app U).hom.toAlgebra
  letI : Algebra (𝒜'.obj.obj U) (𝒝'.obj.obj U) := (varphi'.hom.app U).hom.toAlgebra
  letI : Algebra (𝒜.obj.obj U) (𝒝'.obj.obj U) :=
    ((β.hom.app U).hom.comp (varphi.hom.app U).hom).toAlgebra
  letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (𝒝'.obj.obj U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (𝒜.obj.obj U) (𝒜'.obj.obj U) (𝒝'.obj.obj U) :=
    IsScalarTower.of_algebraMap_eq' (section_square_commutes sq U)
  letI : Module (𝒜.obj.obj U) (ℱ.val.obj U) :=
    Module.compHom (ℱ.val.obj U) ((varphi.hom.app U).hom)
  letI : Module (𝒜'.obj.obj U) (ℱ'.val.obj U) :=
    Module.compHom (ℱ'.val.obj U) ((varphi'.hom.app U).hom)
  letI : Module (𝒝.obj.obj U) (ℱ'.val.obj U) :=
    Module.compHom (ℱ'.val.obj U) ((β.hom.app U).hom)
  letI : Module (𝒜.obj.obj U) (ℱ'.val.obj U) :=
    Module.compHom (ℱ'.val.obj U) ((a.hom.app U).hom)
  letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U)
  letI : IsScalarTower (𝒜'.obj.obj U) (𝒝'.obj.obj U) (ℱ'.val.obj U) :=
    IsScalarTower.of_compHom (𝒜'.obj.obj U) (𝒝'.obj.obj U) (ℱ'.val.obj U)
  letI : IsScalarTower (𝒝.obj.obj U) (𝒝'.obj.obj U) (ℱ'.val.obj U) :=
    IsScalarTower.of_compHom (𝒝.obj.obj U) (𝒝'.obj.obj U) (ℱ'.val.obj U)
  letI : IsScalarTower (𝒜.obj.obj U) (𝒜'.obj.obj U) (ℱ'.val.obj U) :=
    IsScalarTower.of_compHom (𝒜.obj.obj U) (𝒜'.obj.obj U) (ℱ'.val.obj U)
  change
    ModuleCat.of (𝒝.obj.obj U)
        (principal_parts_module (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) k) ⟶
      ModuleCat.of (𝒝.obj.obj U)
        (principal_parts_module (𝒜'.obj.obj U) (𝒝'.obj.obj U) (ℱ'.val.obj U) k)
  exact
    ModuleCat.ofHom
      (@principalPartsBaseChangeMap
        (𝒜.obj.obj U) (𝒝.obj.obj U) (𝒜'.obj.obj U) (𝒝'.obj.obj U)
        _ _ _ _ _ _ _ _ _ _ _
        (ℱ.val.obj U) (ℱ'.val.obj U)
        _ _ _ _ _ _ _ _ _ _ _ _
        k ((α.val.app U).hom))

/-- Helper for Remark 17.29.7: the source presheaf restriction map is the sectionwise Chapter 10
principal-parts base-change map. -/
private theorem principalPartsPresheafMap_typed
    {varphi : 𝒜 ⟶ 𝒝}
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    (k : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (principalPartsPresheaf varphi ℱ k).map i =
      letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) := (varphi.hom.app U).hom.toAlgebra
      letI : Module (𝒜.obj.obj U) (ℱ.val.obj U) :=
        Module.compHom (ℱ.val.obj U) (varphi.hom.app U).hom
      letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) :=
        IsScalarTower.of_compHom (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U)
      letI : Algebra (𝒜.obj.obj V) (𝒝.obj.obj V) := (varphi.hom.app V).hom.toAlgebra
      letI : Module (𝒜.obj.obj V) (ℱ.val.obj V) :=
        Module.compHom (ℱ.val.obj V) (varphi.hom.app V).hom
      letI : IsScalarTower (𝒜.obj.obj V) (𝒝.obj.obj V) (ℱ.val.obj V) :=
        IsScalarTower.of_compHom (𝒜.obj.obj V) (𝒝.obj.obj V) (ℱ.val.obj V)
      letI : Algebra (𝒜.obj.obj U) (𝒜.obj.obj V) := (𝒜.obj.map i).hom.toAlgebra
      letI : Algebra (𝒝.obj.obj U) (𝒝.obj.obj V) := (𝒝.obj.map i).hom.toAlgebra
      letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj V) :=
        (((varphi.hom.app V).hom).comp ((𝒜.obj.map i).hom)).toAlgebra
      letI : Module (𝒜.obj.obj U) (ℱ.val.obj V) :=
        Module.compHom (ℱ.val.obj V) (((varphi.hom.app V).hom).comp ((𝒜.obj.map i).hom))
      letI : Module (𝒝.obj.obj U) (ℱ.val.obj V) :=
        Module.compHom (ℱ.val.obj V) ((𝒝.obj.map i).hom)
      letI : IsScalarTower (𝒜.obj.obj U) (𝒜.obj.obj V) (𝒝.obj.obj V) :=
        IsScalarTower.of_algebraMap_eq' rfl
      letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (𝒝.obj.obj V) :=
        IsScalarTower.of_algebraMap_eq'
          (congrArg CommRingCat.Hom.hom (varphi.hom.naturality i))
      letI : IsScalarTower (𝒝.obj.obj U) (𝒝.obj.obj V) (ℱ.val.obj V) :=
        IsScalarTower.of_compHom (𝒝.obj.obj U) (𝒝.obj.obj V) (ℱ.val.obj V)
      letI : IsScalarTower (𝒜.obj.obj U) (𝒜.obj.obj V) (ℱ.val.obj V) :=
        IsScalarTower.of_compHom (𝒜.obj.obj U) (𝒜.obj.obj V) (ℱ.val.obj V)
      let iU : ℱ.val.obj U →ₗ[𝒝.obj.obj U] ℱ.val.obj V := (ℱ.val.map i).hom
      ModuleCat.ofHom (principalPartsBaseChangeMap
        (A := 𝒜.obj.obj U) (B := 𝒝.obj.obj U)
        (A' := 𝒜.obj.obj V) (B' := 𝒝.obj.obj V)
        (k := k) iU) := by
  -- Proof comment: this freezes the intended normalization so later proofs can use the concrete
  -- Chapter 10 base-change map instead of re-unfolding the wrapped presheaf definition.
  rfl

/-- Helper for Remark 17.29.7: the source presheaf restriction map sends a universal generator to
the universal generator of the restricted section. -/
private theorem principalPartsPresheafMap_on_universal_differential
    {varphi : 𝒜 ⟶ 𝒝}
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    (k : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom ((principalPartsPresheaf varphi ℱ k).map i))
        (principal_parts_universal_differential
          (R := 𝒜.obj.obj U) (S := 𝒝.obj.obj U) (M := ℱ.val.obj U) k m) =
      principal_parts_universal_differential
        (R := 𝒜.obj.obj V) (S := 𝒝.obj.obj V) (M := ℱ.val.obj V) k
        ((ℱ.val.map i).hom m) := by
  -- Proof comment: after normalizing the wrapper to the Chapter 10 base-change map, the
  -- computation on `[m]` is the defining `mapQ` formula.
  rw [principalPartsPresheafMap_typed (k := k) i]
  simp only [principal_parts_universal_differential, Submodule.mapQ_apply]

/-- Helper for Remark 17.29.7: the objectwise principal-parts base-change map is literally the
sectionwise Chapter 10 base-change map. -/
private theorem sectionBaseChangeHom_typed
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ')
    (k : ℕ) (U : (Opens X)ᵒᵖ) :
    sectionBaseChangeHom sq α k U =
      letI : Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) := (varphi.hom.app U).hom.toAlgebra
      letI : Algebra (𝒜.obj.obj U) (𝒜'.obj.obj U) := (a.hom.app U).hom.toAlgebra
      letI : Algebra (𝒝.obj.obj U) (𝒝'.obj.obj U) := (β.hom.app U).hom.toAlgebra
      letI : Algebra (𝒜'.obj.obj U) (𝒝'.obj.obj U) := (varphi'.hom.app U).hom.toAlgebra
      letI : Algebra (𝒜.obj.obj U) (𝒝'.obj.obj U) :=
        ((β.hom.app U).hom.comp (varphi.hom.app U).hom).toAlgebra
      letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (𝒝'.obj.obj U) :=
        IsScalarTower.of_algebraMap_eq' rfl
      letI : IsScalarTower (𝒜.obj.obj U) (𝒜'.obj.obj U) (𝒝'.obj.obj U) :=
        IsScalarTower.of_algebraMap_eq' (section_square_commutes sq U)
      letI : Module (𝒜.obj.obj U) (ℱ.val.obj U) :=
        Module.compHom (ℱ.val.obj U) ((varphi.hom.app U).hom)
      letI : Module (𝒜'.obj.obj U) (ℱ'.val.obj U) :=
        Module.compHom (ℱ'.val.obj U) ((varphi'.hom.app U).hom)
      letI : Module (𝒝.obj.obj U) (ℱ'.val.obj U) :=
        Module.compHom (ℱ'.val.obj U) ((β.hom.app U).hom)
      letI : Module (𝒜.obj.obj U) (ℱ'.val.obj U) :=
        Module.compHom (ℱ'.val.obj U) ((a.hom.app U).hom)
      letI : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) :=
        IsScalarTower.of_compHom (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U)
      letI : IsScalarTower (𝒜'.obj.obj U) (𝒝'.obj.obj U) (ℱ'.val.obj U) :=
        IsScalarTower.of_compHom (𝒜'.obj.obj U) (𝒝'.obj.obj U) (ℱ'.val.obj U)
      letI : IsScalarTower (𝒝.obj.obj U) (𝒝'.obj.obj U) (ℱ'.val.obj U) :=
        IsScalarTower.of_compHom (𝒝.obj.obj U) (𝒝'.obj.obj U) (ℱ'.val.obj U)
      letI : IsScalarTower (𝒜.obj.obj U) (𝒜'.obj.obj U) (ℱ'.val.obj U) :=
        IsScalarTower.of_compHom (𝒜.obj.obj U) (𝒜'.obj.obj U) (ℱ'.val.obj U)
      ModuleCat.ofHom (principalPartsBaseChangeMap
        (A := 𝒜.obj.obj U) (B := 𝒝.obj.obj U)
        (A' := 𝒜'.obj.obj U) (B' := 𝒝'.obj.obj U)
        (k := k) ((α.val.app U).hom)) := by
  -- Proof comment: this theorem freezes the sectionwise owner at the Chapter 10 map so later
  -- calculations stay in the concrete generator presentation.
  rfl

/-- Helper for Remark 17.29.7: the objectwise base-change map sends a universal generator to the
corresponding universal generator in the target principal-parts module. -/
private theorem sectionBaseChangeHom_on_universal_differential
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ')
    (k : ℕ) (U : (Opens X)ᵒᵖ) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom (sectionBaseChangeHom sq α k U))
        (principal_parts_universal_differential
          (R := 𝒜.obj.obj U) (S := 𝒝.obj.obj U) (M := ℱ.val.obj U) k m) =
      principal_parts_universal_differential
        (R := 𝒜'.obj.obj U) (S := 𝒝'.obj.obj U) (M := ℱ'.val.obj U) k
        ((α.val.app U).hom m) := by
  -- Proof comment: once the wrapper is normalized to the Chapter 10 base-change map, the image
  -- of `[m]` is again the defining `mapQ` computation.
  rw [sectionBaseChangeHom_typed sq α k U]
  simp only [principal_parts_universal_differential, Submodule.mapQ_apply]

/-- The objectwise principal-parts base-change maps assemble to a morphism of presheaves. -/
private def presheafBaseChange
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ')
    (k : ℕ) :
    principalPartsPresheaf varphi ℱ k ⟶
      (PresheafOfModules.restrictScalars (ringSheafMap β).hom).obj
        (principalPartsPresheaf varphi' ℱ' k) where
  app U := sectionBaseChangeHom sq α k U
  naturality := by
    intro U V i
    -- Proof comment: the source and target restriction maps are determined by their action on the
    -- universal generators `[m]`, so compare both composites on those generators.
    apply ModuleCat.hom_ext
    apply principalPartsLinearMapExtOnUniversalDifferential k
    intro m
    have hα :
        (ModuleCat.Hom.hom (α.val.app V)) ((ℱ.val.map i).hom m) =
          (ModuleCat.Hom.hom (ℱ'.val.map i)) ((ModuleCat.Hom.hom (α.val.app U)) m) := by
      -- Proof comment: this is the sectionwise naturality of the underlying morphism `α`.
      simpa [ModuleCat.restrictScalarsComp'App_inv_apply] using
        congrArg (fun h ↦ (ModuleCat.Hom.hom h) m) (α.val.naturality i)
    rw [principalPartsPresheafMap_on_universal_differential (k := k) i m]
    simp only [Category.assoc, sectionBaseChangeHom_on_universal_differential,
      principalPartsPresheafMap_on_universal_differential,
      ModuleCat.restrictScalarsComp'App_inv_apply]
    rw [hα]

/-- The canonical truncation map
`P^{k + 1}_{\mathcal B/\mathcal A}(\mathcal F) \to
  P^{k}_{\mathcal B/\mathcal A}(\mathcal F)`. -/
noncomputable def truncateSucc
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝)) (k : ℕ) :
    P^{k + 1}_[varphi](ℱ) ⟶ P^{k}_[varphi](ℱ) :=
  let Dk := (principalParts_is_principal_parts_module_of_order varphi ℱ k).homEquiv
    (𝟙 (P^{k}_[varphi](ℱ)))
  ((principalParts_is_principal_parts_module_of_order varphi ℱ (k + 1)).homEquiv).symm
    ⟨Dk.1,
      isDifferentialOperatorOfOrder_succ
        varphi Dk.2⟩

/-- Remark 17.29.7: a commutative square of sheaves of rings
`\mathcal A \to \mathcal B`, `\mathcal A' \to \mathcal B'` together with a
`\mathcal B`-linear map `\mathcal F \to \beta_* \mathcal F'` induces the canonical base-change
map on sheaves of principal parts
`\mathcal P^k_{\mathcal B/\mathcal A}(\mathcal F) \to
  \beta_* \mathcal P^k_{\mathcal B'/\mathcal A'}(\mathcal F')`. -/
@[stacks 0G3W]
noncomputable def baseChangeMap
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ')
    (k : ℕ) :
    P^{k}_[varphi](ℱ) ⟶
      (restrictionAlong β).obj (P^{k}_[varphi'](ℱ')) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝).obj)).homEquiv
      (principalPartsPresheaf varphi ℱ k)
      ((restrictionAlong β).obj (P^{k}_[varphi'](ℱ')))).symm
    (presheafBaseChange sq α k ≫
      (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝').obj)).unit.app
          (principalPartsPresheaf varphi' ℱ' k)))

/-- Helper for Remark 17.29.7: applying the sheafification hom equivalence to the canonical
base-change map recovers the defining presheaf-level composite. -/
private theorem sheafificationHomEquiv_baseChangeMap
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ')
    (k : ℕ) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
      (baseChangeMap sq α k) =
        presheafBaseChange sq α k ≫
          (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
            ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (ringSheaf 𝒝').obj)).unit.app
              (principalPartsPresheaf varphi' ℱ' k)) := by
  -- Proof comment: `baseChangeMap` is defined as the inverse image of this presheaf composite
  -- under the sheafification adjunction equivalence, so applying the equivalence cancels `symm`.
  rw [baseChangeMap]
  exact Equiv.apply_symm_apply _

/-- Helper for Remark 17.29.7: under the sheafification adjunction, the principal-parts
projection is computed by postcomposing the unit with the underlying presheaf morphism. -/
private theorem projection_sheafificationHomEquiv
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝)) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
      (projection varphi ℱ) =
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝).obj)).unit.app
          (principalPartsPresheaf varphi ℱ 1)) ≫
          (projection varphi ℱ).val := by
  -- Proof comment: this is the definitional description of `sheafificationHomEquiv` specialized
  -- to the source sheaf `P¹_[varphi](ℱ)`.
  ext U x
  rfl

/-- Helper for Remark 17.29.7: under the sheafification adjunction, the cotangent map is
computed by postcomposing the unit with its underlying presheaf morphism. -/
private theorem cotangentTo_sheafificationHomEquiv
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝)) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
      (cotangentTo varphi ℱ) =
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝).obj)).unit.app
          (PresheafOfModules.Monoidal.tensorObj
            (relativeDifferentials' varphi.hom) ℱ.val)) ≫
          (cotangentTo varphi ℱ).val := by
  -- Proof comment: this is the same adjunction normalization, now for the sheafified cotangent
  -- source presheaf.
  ext U x
  rfl

/-- Helper for Remark 17.29.7: restricting scalars commutes with the sheafification hom
equivalence for a postcomposed map. -/
private theorem restrictionAlong_sheafificationHomEquiv_map
    {β : 𝒝 ⟶ 𝒝'}
    {ℱ' 𝒢' : SheafOfModules (ringSheaf 𝒝')}
    (f : ℱ' ⟶ 𝒢') :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
      ((restrictionAlong β).map f) =
        (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
          (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝').obj) f) := by
  -- Proof comment: after expanding `sheafificationHomEquiv`, both sides are the same sectionwise
  -- presheaf composite obtained from the sheafification unit and the restricted map `f`.
  ext U x
  rfl

/-- Helper for Remark 17.29.7: under the `(k + 1)` corepresenting equivalence, the truncation
map is represented by the universal order-`k` differential operator, now viewed as order
`k + 1`. -/
private theorem truncateSucc_homEquiv
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝)) (k : ℕ) :
    (((principalParts_is_principal_parts_module_of_order varphi ℱ (k + 1)).homEquiv
        (truncateSucc varphi ℱ k)).1) =
      (((principalParts_is_principal_parts_module_of_order varphi ℱ k).homEquiv
        (𝟙 (P^{k}_[varphi](ℱ)))).1) := by
  -- Proof comment: `truncateSucc` is defined as the inverse image of this differential operator
  -- under the `(k + 1)` representing equivalence, so applying the equivalence again cancels it.
  rw [truncateSucc]
  simp

/-- Helper for Remark 17.29.7: the universal order-`k` differential operator represented by the
identity of `P^k_[varphi](ℱ)`. -/
private def principalPartsDifferentialOperator
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝))
    (k : ℕ) :
    (restrictionAlong varphi).obj ℱ ⟶
      (restrictionAlong varphi).obj (P^{k}_[varphi](ℱ)) :=
  ((principalParts_is_principal_parts_module_of_order varphi ℱ k).homEquiv
    (𝟙 (P^{k}_[varphi](ℱ)))).1

/-- Helper for Remark 17.29.7: under the corepresenting equivalence, a morphism out of
`P^k_[varphi](ℱ)` corresponds to postcomposing the universal represented differential operator. -/
private theorem homEquiv_apply_eq_principalPartsDifferentialOperator_comp
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝))
    (k : ℕ)
    {𝒢 : SheafOfModules (ringSheaf 𝒝)}
    (γ : P^{k}_[varphi](ℱ) ⟶ 𝒢) :
    (((principalParts_is_principal_parts_module_of_order varphi ℱ k).homEquiv γ).1) =
      principalPartsDifferentialOperator varphi ℱ k ≫
        (restrictionAlong varphi).map γ := by
  -- Proof comment: this is the naturality of `homEquiv` for the identity of the corepresenting
  -- object, with the proof component discarded by `Subtype.val`.
  simpa [principalPartsDifferentialOperator] using
    congrArg Subtype.val
      (Functor.CorepresentableBy.homEquiv_eq
        (principalParts_is_principal_parts_module_of_order varphi ℱ k) γ)

/-- Helper for Remark 17.29.7: postcomposing the represented universal differential operator with
the truncation map reproduces the represented order-`k` operator. -/
private theorem principalPartsDifferentialOperator_truncateSucc
    (varphi : 𝒜 ⟶ 𝒝)
    (ℱ : SheafOfModules (ringSheaf 𝒝))
    (k : ℕ) :
    principalPartsDifferentialOperator varphi ℱ (k + 1) ≫
        (restrictionAlong varphi).map (truncateSucc varphi ℱ k) =
      principalPartsDifferentialOperator varphi ℱ k := by
  -- Proof comment: combine the generic `homEquiv`-as-postcomposition formula with the explicit
  -- identification of `truncateSucc` under the `(k + 1)` corepresenting equivalence.
  calc
    principalPartsDifferentialOperator varphi ℱ (k + 1) ≫
        (restrictionAlong varphi).map (truncateSucc varphi ℱ k) =
      (((principalParts_is_principal_parts_module_of_order varphi ℱ (k + 1)).homEquiv
          (truncateSucc varphi ℱ k)).1) := by
        symm
        exact homEquiv_apply_eq_principalPartsDifferentialOperator_comp
          varphi ℱ (k + 1) (truncateSucc varphi ℱ k)
    _ = principalPartsDifferentialOperator varphi ℱ k := by
        simpa [principalPartsDifferentialOperator] using truncateSucc_homEquiv varphi ℱ k

/-- Helper for Remark 17.29.7: after applying the `(k + 1)` corepresenting equivalence,
postcomposing the base-change map with the target truncation is still just postcomposition on the
represented differential operator. -/
private theorem representedBaseChange_postcompose_truncateSucc
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ')
    (k : ℕ) :
    (((principalParts_is_principal_parts_module_of_order varphi ℱ (k + 1)).homEquiv
        (baseChangeMap sq α (k + 1) ≫
          (restrictionAlong β).map (truncateSucc varphi' ℱ' k))).1) =
      (((principalParts_is_principal_parts_module_of_order varphi ℱ (k + 1)).homEquiv
          (baseChangeMap sq α (k + 1))).1) ≫
        (restrictionAlong varphi).map ((restrictionAlong β).map (truncateSucc varphi' ℱ' k)) := by
  -- Proof comment: `homEquiv_comp` for the corepresenting object says that postcomposing a map
  -- out of `P^{k + 1}` is transported to postcomposition of the represented differential
  -- operator.
  simpa using congrArg Subtype.val
    ((principalParts_is_principal_parts_module_of_order varphi ℱ (k + 1)).homEquiv_comp
      ((restrictionAlong β).map (truncateSucc varphi' ℱ' k))
      (baseChangeMap sq α (k + 1)))

/-- Helper for Remark 17.29.7: after applying the `(k + 1)` corepresenting equivalence, the
source-side composite `truncateSucc ≫ baseChangeMap` is represented by the order-`k`
universal differential operator followed by the order-`k` base-change map. -/
private theorem representedTruncateSucc_baseChange
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ')
    (k : ℕ) :
    (((principalParts_is_principal_parts_module_of_order varphi ℱ (k + 1)).homEquiv
        (truncateSucc varphi ℱ k ≫ baseChangeMap sq α k)).1) =
      principalPartsDifferentialOperator varphi ℱ k ≫
        (restrictionAlong varphi).map (baseChangeMap sq α k) := by
  -- Proof comment: first rewrite the represented composite by the generic
  -- `homEquiv`-as-postcomposition formula, then collapse the source truncation by the helper
  -- proved just above.
  calc
    (((principalParts_is_principal_parts_module_of_order varphi ℱ (k + 1)).homEquiv
        (truncateSucc varphi ℱ k ≫ baseChangeMap sq α k)).1) =
      principalPartsDifferentialOperator varphi ℱ (k + 1) ≫
        (restrictionAlong varphi).map (truncateSucc varphi ℱ k ≫ baseChangeMap sq α k) := by
          exact homEquiv_apply_eq_principalPartsDifferentialOperator_comp
            varphi ℱ (k + 1) (truncateSucc varphi ℱ k ≫ baseChangeMap sq α k)
    _ = principalPartsDifferentialOperator varphi ℱ (k + 1) ≫
        (restrictionAlong varphi).map (truncateSucc varphi ℱ k) ≫
          (restrictionAlong varphi).map (baseChangeMap sq α k) := by
          simp [Functor.map_comp, Category.assoc]
    _ = principalPartsDifferentialOperator varphi ℱ k ≫
        (restrictionAlong varphi).map (baseChangeMap sq α k) := by
          rw [principalPartsDifferentialOperator_truncateSucc]
          simp [Category.assoc]

/-- Helper for Remark 17.29.7: the represented differential operator attached to the sheaf-level
base-change map sends a section `m` to the corresponding target universal generator. -/
private theorem representedBaseChangeMap_apply_universalDifferential
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ')
    (k : ℕ) (U : (Opens X)ᵒᵖ) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom
        ((((principalParts_is_principal_parts_module_of_order varphi ℱ k).homEquiv
            (baseChangeMap sq α k)).1).val.app U)) m =
      principal_parts_universal_differential
        (R := 𝒜'.obj.obj U) (S := 𝒝'.obj.obj U) (M := ℱ'.val.obj U) k
        ((α.val.app U).hom m) := by
  -- Proof comment: `baseChangeMap` is defined as the morphism represented by the sectionwise
  -- Chapter 10 base-change map, so evaluating the represented differential operator on `m`
  -- reproduces the image of the universal generator.
  rw [baseChangeMap]
  simp only
  exact sectionBaseChangeHom_on_universal_differential sq α k U m

/-- Helper for Remark 17.29.7: the truncation map on principal parts sends the universal
generator of order `k + 1` to the universal generator of order `k`. -/
private theorem truncateSucc_on_universalDifferential
    {varphi : 𝒜 ⟶ 𝒝}
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    (k : ℕ) (U : (Opens X)ᵒᵖ) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom ((truncateSucc varphi ℱ k).val.app U))
        (principal_parts_universal_differential
          (R := 𝒜.obj.obj U) (S := 𝒝.obj.obj U) (M := ℱ.val.obj U) (k + 1) m) =
      principal_parts_universal_differential
        (R := 𝒜.obj.obj U) (S := 𝒝.obj.obj U) (M := ℱ.val.obj U) k m := by
  -- Proof comment: `truncateSucc` is represented by the order-`k` universal differential
  -- operator, and two linear maps out of principal parts agree once they agree on all
  -- universal generators.
  let Dk :=
    (((principalParts_is_principal_parts_module_of_order varphi ℱ k).homEquiv
      (𝟙 (P^{k}_[varphi](ℱ)))).1)
  let DU :
      principal_parts_module (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) (k + 1) →ₗ[𝒜.obj.obj U]
        principal_parts_module (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) k :=
    ((Dk.val.app U).hom)
  have hrepr :
      (((principalParts_is_principal_parts_module_of_order varphi ℱ (k + 1)).homEquiv
          (truncateSucc varphi ℱ k)).1).val.app U =
        ModuleCat.ofHom DU := by
    -- Proof comment: expand the represented differential operator of `truncateSucc` using the
    -- explicit `homEquiv` computation.
    ext x
    simpa [Dk, DU] using congrArg (fun f ↦ (ModuleCat.Hom.hom (f.app U)) x)
      (truncateSucc_homEquiv varphi ℱ k)
  have hDU :
      DU =
        principal_parts_universal_differential
          (R := 𝒜.obj.obj U) (S := 𝒝.obj.obj U) (M := ℱ.val.obj U) k := by
    -- Proof comment: the order-`k` identity morphism is represented by the order-`k`
    -- universal differential operator on every open set.
    rfl
  have hcomp :=
    congrArg (fun f ↦ (ModuleCat.Hom.hom (f.app U))
      (principal_parts_universal_differential
        (R := 𝒜.obj.obj U) (S := 𝒝.obj.obj U) (M := ℱ.val.obj U) (k + 1) m))
      (homEquiv_apply_eq_principalPartsDifferentialOperator_comp
        varphi ℱ (k + 1) (truncateSucc varphi ℱ k))
  rw [hrepr] at hcomp
  simp only [Category.assoc] at hcomp
  simpa [principalPartsDifferentialOperator, Dk, DU, hDU] using hcomp

/-- Helper for Remark 17.29.7: after the represented normalizations, the two composites in
`truncateSucc_baseChange` agree on every universal generator. -/
private theorem truncateSucc_baseChange_on_universalDifferential
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ')
    (k : ℕ) (U : (Opens X)ᵒᵖ) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom
        ((principalPartsDifferentialOperator varphi ℱ k ≫
          (restrictionAlong varphi).map (baseChangeMap sq α k)).val.app U))
        (principal_parts_universal_differential
          (R := 𝒜.obj.obj U) (S := 𝒝.obj.obj U) (M := ℱ.val.obj U) (k + 1) m) =
      (ModuleCat.Hom.hom
          (((((principalParts_is_principal_parts_module_of_order varphi ℱ (k + 1)).homEquiv
              (baseChangeMap sq α (k + 1))).1) ≫
            (restrictionAlong varphi).map
              ((restrictionAlong β).map (truncateSucc varphi' ℱ' k))).val.app U))
          (principal_parts_universal_differential
            (R := 𝒜.obj.obj U) (S := 𝒝.obj.obj U) (M := ℱ.val.obj U) (k + 1) m) := by
  -- Proof comment: compute the right composite by first applying the represented base-change map
  -- on generators and then truncating the target universal generator back to order `k`.
  simp only [Category.assoc, representedBaseChangeMap_apply_universalDifferential,
    sectionBaseChangeHom_on_universal_differential,
    truncateSucc_on_universalDifferential,
    ModuleCat.restrictScalarsComp'App_inv_apply]

/-- The induced base-change map on principal parts is compatible with the canonical truncation
maps `P^{k + 1} \to P^k`. -/
theorem truncateSucc_baseChange
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ')
    (k : ℕ) :
    CommSq
      (baseChangeMap sq α (k + 1))
      (truncateSucc varphi ℱ k)
      ((restrictionAlong β).map (truncateSucc varphi' ℱ' k))
      (baseChangeMap sq α k) := by
  refine ⟨?_⟩
  -- Proof comment: compare the two composites after applying the `(k + 1)` corepresenting
  -- equivalence, where both sides become differential operators out of `(restrictionAlong
  -- varphi).obj ℱ`.
  apply ((principalParts_is_principal_parts_module_of_order varphi ℱ (k + 1)).homEquiv).injective
  rw [representedTruncateSucc_baseChange (sq := sq) (α := α) (k := k)]
  rw [representedBaseChange_postcompose_truncateSucc (sq := sq) (α := α) (k := k)]
  -- Proof comment: the represented operators are morphisms of sheaves, so it suffices to compare
  -- them sectionwise and then on the universal generators `[m]`.
  ext U
  apply ModuleCat.hom_ext
  apply principalPartsLinearMapExtOnUniversalDifferential k
  intro m
  -- Proof comment: the source side is already the order-`k` base-change image of `[m]`.
  -- The target side is the order-`k + 1` base-change image followed by truncation, which sends
  -- the target universal generator back to order `k`.
  exact truncateSucc_baseChange_on_universalDifferential
    (sq := sq) (α := α) (k := k) U m

/-- The canonical base-change map on principal parts is compatible with further composition of
commutative ring squares and module maps. -/
theorem baseChangeMap_comp
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'} {varphi'' : 𝒜'' ⟶ 𝒝''}
    {a : 𝒜 ⟶ 𝒜'} {a' : 𝒜' ⟶ 𝒜''}
    {β : 𝒝 ⟶ 𝒝'} {β' : 𝒝' ⟶ 𝒝''}
    (sq : CommSq a varphi varphi' β)
    (sq' : CommSq a' varphi' varphi'' β')
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    {ℱ'' : SheafOfModules (ringSheaf 𝒝'')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ')
    (α' : ℱ' ⟶ (restrictionAlong β').obj ℱ'')
    (k : ℕ) :
    baseChangeMap (CommSq.horiz_comp sq sq')
        (α ≫ (restrictionAlong β).map α') k =
      baseChangeMap sq α k ≫
        (restrictionAlong β).map
          (baseChangeMap sq' α' k) := by
  -- Route correction: normalize both sides under the same sheafification equivalence before any
  -- sectionwise work, so the proof stays on the stable presheaf-side base-change map.
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)).injective
  rw [sheafificationHomEquiv_baseChangeMap (sq := CommSq.horiz_comp sq sq')
    (α := α ≫ (restrictionAlong β).map α') (k := k)]
  have hright :
      PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
        (baseChangeMap sq α k ≫
          (restrictionAlong β).map (baseChangeMap sq' α' k)) =
        PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
          (baseChangeMap sq α k) ≫
            (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
              (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝').obj)
                (baseChangeMap sq' α' k)) := by
    -- Proof comment: right naturality moves the target-side composite to the presheaf side, and
    -- the helper above rewrites the restricted morphism into the same presheaf normal form.
    calc
      PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
          (baseChangeMap sq α k ≫
            (restrictionAlong β).map (baseChangeMap sq' α' k)) =
          PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
            (baseChangeMap sq α k) ≫
              PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
                ((restrictionAlong β).map (baseChangeMap sq' α' k)) := by
            simpa [PresheafOfModules.sheafificationAdjunction_homEquiv_apply] using
              (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝).obj))
                .homEquiv_naturality_right
                (baseChangeMap sq α k)
                ((restrictionAlong β).map (baseChangeMap sq' α' k))
      _ = PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
            (baseChangeMap sq α k) ≫
              (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
                (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝').obj)
                  (baseChangeMap sq' α' k)) := by
            rw [restrictionAlong_sheafificationHomEquiv_map]
  rw [hright]
  rw [sheafificationHomEquiv_baseChangeMap (sq := sq) (α := α) (k := k)]
  rw [sheafificationHomEquiv_baseChangeMap (sq := sq') (α := α') (k := k)]
  apply PresheafOfModules.hom_ext
  intro U
  have hcomp :
      (((α ≫ (restrictionAlong β).map α').val.app U).hom) =
        ((((α'.val.app U).hom).restrictScalars (𝒝.obj.obj U)).comp ((α.val.app U).hom)) := by
    -- Proof comment: the section map of the composite module morphism is exactly the composite of
    -- the two section maps, with the second one viewed over `𝒝(U)` by restriction of scalars.
    ext m
    simpa [ModuleCat.restrictScalarsComp'App_inv_apply] using
      congrArg (fun h ↦ (ModuleCat.Hom.hom h) m) ((α ≫ (restrictionAlong β).map α').val.naturality
        (𝟙 U))
  rw [show (presheafBaseChange (CommSq.horiz_comp sq sq') (α ≫ (restrictionAlong β).map α') k).app U =
      sectionBaseChangeHom (CommSq.horiz_comp sq sq') (α ≫ (restrictionAlong β).map α') k U by
      rfl]
  rw [show (presheafBaseChange sq α k).app U =
      sectionBaseChangeHom sq α k U by rfl]
  rw [show (presheafBaseChange sq' α' k).app U =
      sectionBaseChangeHom sq' α' k U by rfl]
  rw [sectionBaseChangeHom_typed (sq := CommSq.horiz_comp sq sq')
    (α := α ≫ (restrictionAlong β).map α') (k := k) U]
  rw [sectionBaseChangeHom_typed (sq := sq) (α := α) (k := k) U]
  rw [sectionBaseChangeHom_typed (sq := sq') (α := α') (k := k) U]
  rw [hcomp]
  simpa using principalPartsBaseChangeMap_comp (k := k) ((α.val.app U).hom) ((α'.val.app U).hom)

/-- The canonical base-change map on first principal parts is compatible with the projection in
the principal-parts sequence. -/
theorem projection_baseChange
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ') :
    CommSq
      (baseChangeMap sq α 1)
      (projection varphi ℱ)
      ((restrictionAlong β).map (projection varphi' ℱ'))
      α := by
  -- Route correction: compare both composites after applying the sheafification hom
  -- equivalence, so the argument stays in the stable presheaf presentation of principal parts.
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)).injective
  have hleft :
      PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
        (baseChangeMap sq α 1 ≫ (restrictionAlong β).map (projection varphi' ℱ')) =
          PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
            (baseChangeMap sq α 1) ≫
              (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
                (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝').obj)
                  (projection varphi' ℱ')) := by
    -- Proof comment: right naturality moves the target-side composite to the presheaf side,
    -- and the restriction-of-scalars helper then rewrites the restricted projection map.
    calc
      PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
          (baseChangeMap sq α 1 ≫ (restrictionAlong β).map (projection varphi' ℱ')) =
          PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
            (baseChangeMap sq α 1) ≫
              PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
                ((restrictionAlong β).map (projection varphi' ℱ')) := by
            simpa [PresheafOfModules.sheafificationAdjunction_homEquiv_apply] using
              (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝).obj))
                .homEquiv_naturality_right
                (baseChangeMap sq α 1)
                ((restrictionAlong β).map (projection varphi' ℱ'))
      _ = PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
            (baseChangeMap sq α 1) ≫
              (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
                (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝').obj)
                  (projection varphi' ℱ')) := by
            rw [restrictionAlong_sheafificationHomEquiv_map]
  rw [hleft]
  rw [sheafificationHomEquiv_baseChangeMap (sq := sq) (α := α) (k := 1)]
  rw [projection_sheafificationHomEquiv (varphi := varphi') (ℱ := ℱ')]
  -- Proof comment: each component is now the sectionwise Chapter 10 principal-parts square
  -- induced by the map on sections `α.app U`.
  ext U
  rw [show (presheafBaseChange sq α 1).app U = sectionBaseChangeHom sq α 1 U by rfl]
  rw [sectionBaseChangeHom_typed (sq := sq) (α := α) (k := 1) U]
  simpa [projection_sheafificationHomEquiv, PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    sectionBaseChangeHom_typed, Category.assoc] using
    congrArg ModuleCat.ofHom
      (Module.principalPartsSequenceMap
        (R := 𝒜.obj.obj U) (S := 𝒝.obj.obj U)
        (M := ℱ.val.obj U) (N := ℱ'.val.obj U) ((α.val.app U).hom)).comm₂₃

/-- The sectionwise tensor comparison for restriction of scalars, given by the canonical
lax-monoidal comparison `Functor.LaxMonoidal.μ` on `ModuleCat.restrictScalars`. -/
private abbrev sectionRestrictScalarsTensorComparison
    {β : 𝒝 ⟶ 𝒝'}
    (ℱ' 𝒢' : SheafOfModules (ringSheaf 𝒝'))
    (U : (Opens X)ᵒᵖ) :
    (PresheafOfModules.Monoidal.tensorObj
        ((PresheafOfModules.restrictScalars (ringSheafMap β).hom).obj ℱ'.val)
        ((PresheafOfModules.restrictScalars (ringSheafMap β).hom).obj 𝒢'.val)).obj U ⟶
      ((PresheafOfModules.restrictScalars (ringSheafMap β).hom).obj
        (PresheafOfModules.Monoidal.tensorObj ℱ'.val 𝒢'.val)).obj U := by
  simpa using
    (μ (ModuleCat.restrictScalars ((β.hom.app U).hom)) (ℱ'.val.obj U) (𝒢'.val.obj U))

/-- The sectionwise canonical tensor comparisons assemble to a presheaf morphism. -/
private def restrictScalarsTensorComparisonPresheaf
    {β : 𝒝 ⟶ 𝒝'}
    (ℱ' 𝒢' : SheafOfModules (ringSheaf 𝒝')) :
    PresheafOfModules.Monoidal.tensorObj
        ((PresheafOfModules.restrictScalars (ringSheafMap β).hom).obj ℱ'.val)
        ((PresheafOfModules.restrictScalars (ringSheafMap β).hom).obj 𝒢'.val) ⟶
      (PresheafOfModules.restrictScalars (ringSheafMap β).hom).obj
        (PresheafOfModules.Monoidal.tensorObj ℱ'.val 𝒢'.val) where
  app U := sectionRestrictScalarsTensorComparison ℱ' 𝒢' U
  naturality := by
    intro U V i
    -- Proof comment: this is the componentwise right naturality of the lax-monoidal comparison
    -- `μ` for `ModuleCat.restrictScalars`, specialized to the restriction map on opens.
    ext
    rw [μ_natural_right_assoc]
    simp

/-- The canonical tensor comparison for restriction of scalars, obtained by sheafifying the
sectionwise `Functor.LaxMonoidal.μ` comparison. -/
private noncomputable def restrictScalarsTensorComparison
    {β : 𝒝 ⟶ 𝒝'}
    (ℱ' 𝒢' : SheafOfModules (ringSheaf 𝒝')) :
    ((restrictionAlong β).obj ℱ') ⊗ ((restrictionAlong β).obj 𝒢') ⟶
      (restrictionAlong β).obj (ℱ' ⊗ 𝒢') :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝).obj)).homEquiv
      (PresheafOfModules.Monoidal.tensorObj
        ((PresheafOfModules.restrictScalars (ringSheafMap β).hom).obj ℱ'.val)
        ((PresheafOfModules.restrictScalars (ringSheafMap β).hom).obj 𝒢'.val))
      ((restrictionAlong β).obj (ℱ' ⊗ 𝒢'))).symm
    (restrictScalarsTensorComparisonPresheaf ℱ' 𝒢' ≫
      (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝').obj)).unit.app
          (PresheafOfModules.Monoidal.tensorObj ℱ'.val 𝒢'.val)))

/-- Helper for Remark 17.29.7: applying the sheafification hom equivalence to the tensor
comparison for restriction of scalars recovers its defining presheaf-level composite. -/
private theorem restrictScalarsTensorComparison_sheafificationHomEquiv
    {β : 𝒝 ⟶ 𝒝'}
    (ℱ' 𝒢' : SheafOfModules (ringSheaf 𝒝')) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
      (restrictScalarsTensorComparison (β := β) ℱ' 𝒢') =
        restrictScalarsTensorComparisonPresheaf (β := β) ℱ' 𝒢' ≫
          (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
            ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (ringSheaf 𝒝').obj)).unit.app
              (PresheafOfModules.Monoidal.tensorObj ℱ'.val 𝒢'.val)) := by
  -- Proof comment: `restrictScalarsTensorComparison` is defined as the inverse image of this
  -- presheaf composite under the sheafification adjunction equivalence.
  rw [restrictScalarsTensorComparison]
  exact Equiv.apply_symm_apply _

/-- Helper for Remark 17.29.7: under the sheafification adjunction, the cotangent base-change map
is the presheaf tensor map followed by the restriction-of-scalars tensor comparison. -/
private theorem cotangentMap_sheafificationHomEquiv
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ') :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
      (cotangentMap sq α) =
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝).obj)).unit.app
          (PresheafOfModules.Monoidal.tensorObj
            (relativeDifferentials' varphi.hom) ℱ.val)) ≫
          PresheafOfModules.Monoidal.tensorHom
            (relativeDifferentialsMap varphi varphi' a β sq).val α.val ≫
          restrictScalarsTensorComparisonPresheaf (β := β) (Ω(varphi')) ℱ' ≫
            (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
              ((PresheafOfModules.sheafificationAdjunction
                (𝟙 (ringSheaf 𝒝').obj)).unit.app
                (PresheafOfModules.Monoidal.tensorObj
                  (relativeDifferentials' varphi'.hom) ℱ'.val)) := by
  -- Proof comment: first move the composite across the sheafification adjunction by right
  -- naturality, then rewrite each factor by its defining presheaf-level description.
  calc
    PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
        (cotangentMap sq α) =
      PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
        (moduleTensorMap
          (relativeDifferentialsMap varphi varphi' a β sq) α) ≫
            PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
              (restrictScalarsTensorComparison (β := β) (Ω(varphi')) ℱ') := by
          simpa [cotangentMap, PresheafOfModules.sheafificationAdjunction_homEquiv_apply] using
            (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝).obj))
              .homEquiv_naturality_right
              (moduleTensorMap
                (relativeDifferentialsMap varphi varphi' a β sq) α)
              (restrictScalarsTensorComparison (β := β) (Ω(varphi')) ℱ')
    _ = (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringSheaf 𝒝).obj)).unit.app
            (PresheafOfModules.Monoidal.tensorObj
              (relativeDifferentials' varphi.hom) ℱ.val)) ≫
          PresheafOfModules.Monoidal.tensorHom
            (relativeDifferentialsMap varphi varphi' a β sq).val α.val) ≫
            PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
              (restrictScalarsTensorComparison (β := β) (Ω(varphi')) ℱ') := by
          congr 1
          ext U x
          rfl
    _ = ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝).obj)).unit.app
          (PresheafOfModules.Monoidal.tensorObj
            (relativeDifferentials' varphi.hom) ℱ.val)) ≫
          PresheafOfModules.Monoidal.tensorHom
            (relativeDifferentialsMap varphi varphi' a β sq).val α.val ≫
          restrictScalarsTensorComparisonPresheaf (β := β) (Ω(varphi')) ℱ' ≫
            (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
              ((PresheafOfModules.sheafificationAdjunction
                (𝟙 (ringSheaf 𝒝').obj)).unit.app
                (PresheafOfModules.Monoidal.tensorObj
                  (relativeDifferentials' varphi'.hom) ℱ'.val)) := by
          rw [restrictScalarsTensorComparison_sheafificationHomEquiv]
          simp [Category.assoc]

/-- The canonical base-change map on the cotangent term of the principal-parts sequence. -/
noncomputable def cotangentMap
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ') :
    Ω(varphi) ⊗ ℱ ⟶
      (restrictionAlong β).obj (Ω(varphi') ⊗ ℱ') :=
  moduleTensorMap
      (relativeDifferentialsMap varphi varphi' a β sq) α ≫
    restrictScalarsTensorComparison (Ω(varphi')) ℱ'

/-- The canonical base-change maps on first principal parts fit into the left square of the
principal-parts sequence. -/
theorem cotangent_baseChange
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ') :
    CommSq
      (cotangentMap sq α)
      (cotangentTo varphi ℱ)
      ((restrictionAlong β).map (cotangentTo varphi' ℱ'))
      (baseChangeMap sq α 1) := by
  -- Route correction: compare both sides after applying the sheafification hom equivalence so
  -- the proof lives on the explicit presheaf presentation of the cotangent square.
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)).injective
  have hleft :
      PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
        (cotangentMap sq α ≫ (restrictionAlong β).map (cotangentTo varphi' ℱ')) =
          PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
            (cotangentMap sq α) ≫
              (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
                (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝').obj)
                  (cotangentTo varphi' ℱ')) := by
    -- Proof comment: right naturality moves the restricted target morphism to the presheaf side.
    calc
      PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
          (cotangentMap sq α ≫ (restrictionAlong β).map (cotangentTo varphi' ℱ')) =
          PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
            (cotangentMap sq α) ≫
              PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
                ((restrictionAlong β).map (cotangentTo varphi' ℱ')) := by
            simpa [PresheafOfModules.sheafificationAdjunction_homEquiv_apply] using
              (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝).obj))
                .homEquiv_naturality_right
                (cotangentMap sq α)
                ((restrictionAlong β).map (cotangentTo varphi' ℱ'))
      _ = PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝).obj)
            (cotangentMap sq α) ≫
              (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
                (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒝').obj)
                  (cotangentTo varphi' ℱ')) := by
            rw [restrictionAlong_sheafificationHomEquiv_map]
  rw [hleft]
  rw [cotangentMap_sheafificationHomEquiv (sq := sq) (α := α)]
  rw [cotangentTo_sheafificationHomEquiv (varphi := varphi') (ℱ := ℱ')]
  rw [cotangentTo_sheafificationHomEquiv (varphi := varphi) (ℱ := ℱ)]
  rw [sheafificationHomEquiv_baseChangeMap (sq := sq) (α := α) (k := 1)]
  ext U
  -- Proof comment: after normalizing the wrappers, each component is the objectwise base-change
  -- compatibility of the first principal-parts sequence on the open set `U`.
  simp [Category.assoc]

/-- The canonical base-change maps on the first principal-parts sequence assemble to a morphism
of short complexes. -/
noncomputable abbrev baseChangeSequenceMap
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (restrictionAlong β).obj ℱ') :
    sequence varphi ℱ ⟶
      (sequence varphi' ℱ').map (restrictionAlong β) :=
  ShortComplex.homMk
    (cotangentMap sq α)
    (baseChangeMap sq α 1)
    α
    (cotangent_baseChange sq α).w
    (projection_baseChange sq α).w

end TopCat.Sheaf.principalParts

end
