import Mathlib
import stacks_proof.stacks_project.Chap10.Remark_10_133_7
import stacks_proof.stacks_project.Chap18.Remark_18_34_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open PresheafOfModules

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace PresheafOfModules

/-- Helper for Lemma 18.34.5: the `RingCat`-valued presheaf underlying a presheaf of
commutative rings. -/
abbrev ringPresheaf (O : Cᵒᵖ ⥤ CommRingCat.{u}) : Cᵒᵖ ⥤ RingCat.{u} :=
  O ⋙ forget₂ CommRingCat RingCat

/-- Helper for Lemma 18.34.5: the same-site `RingCat` morphism underlying a morphism of
presheaves of commutative rings. -/
abbrev presheafStructureMap
    {O O' : Cᵒᵖ ⥤ CommRingCat.{u}} (α : O ⟶ O') :
    ringPresheaf O ⟶ ringPresheaf O' :=
  Functor.whiskerRight α (forget₂ CommRingCat RingCat)

/-- Helper for Lemma 18.34.5: the sheafification of a presheaf of commutative rings. -/
abbrev commRingSheafification (O : Cᵒᵖ ⥤ CommRingCat.{u}) :
    Sheaf J CommRingCat.{u} :=
  (presheafToSheaf J CommRingCat.{u}).obj O

/-- Helper for Lemma 18.34.5: the comparison from the ring-valued sheafification of the
underlying `RingCat` presheaf to the ring sheaf of the commutative-ring sheafification. -/
private noncomputable abbrev sheafificationRingBridge
    (O : Cᵒᵖ ⥤ CommRingCat.{u}) :
    (presheafToSheaf J RingCat.{u}).obj (ringPresheaf O) ⟶
      ringSheaf J (commRingSheafification J O) :=
  (CategoryTheory.sheafComposeNatTrans J (forget₂ CommRingCat RingCat)
    (CategoryTheory.sheafificationAdjunction J CommRingCat.{u})
    (CategoryTheory.sheafificationAdjunction J RingCat.{u})).app O

/-- Helper for Lemma 18.34.5: the canonical ring map `O → O^#` on the underlying `RingCat`
presheaves. -/
abbrev sheafificationRingMap (O : Cᵒᵖ ⥤ CommRingCat.{u}) :
    ringPresheaf O ⟶ (ringSheaf J (commRingSheafification J O)).obj :=
  CategoryTheory.toSheafify J (ringPresheaf O) ≫
    (sheafToPresheaf J RingCat.{u}).map (sheafificationRingBridge (J := J) O)

/-- Helper for Lemma 18.34.5: the underlying `RingCat` sheafification unit agrees with the
forgotten commutative-ring sheafification unit. -/
private theorem sheafificationRingMap_eq_whiskerRight
    (O : Cᵒᵖ ⥤ CommRingCat.{u}) :
    sheafificationRingMap (J := J) O =
      Functor.whiskerRight
        (show O ⟶ (commRingSheafification J O).obj from CategoryTheory.toSheafify J O)
        (forget₂ CommRingCat RingCat) := by
  simpa [sheafificationRingMap, sheafificationRingBridge, commRingSheafification, ringPresheaf,
    ringSheaf] using
    (CategoryTheory.sheafComposeNatTrans_fac J (forget₂ CommRingCat RingCat)
      (CategoryTheory.sheafificationAdjunction J CommRingCat.{u})
      (CategoryTheory.sheafificationAdjunction J RingCat.{u}) O)

instance sheafificationRingMap_isLocallyInjective
    (O : Cᵒᵖ ⥤ CommRingCat.{u}) :
    Presheaf.IsLocallyInjective J (sheafificationRingMap (J := J) O) := by
  let η : O ⟶ (commRingSheafification J O).obj := CategoryTheory.toSheafify J O
  have hη : Presheaf.IsLocallyInjective J η :=
    (J.W_toSheafify (A := CommRingCat.{u}) O).isLocallyInjective
  have hηForget :
      Presheaf.IsLocallyInjective J
        (Functor.whiskerRight (Functor.whiskerRight η (forget₂ CommRingCat RingCat))
          (CategoryTheory.forget RingCat)) := by
    simpa using ((Presheaf.isLocallyInjective_forget_iff (J := J) (φ := η)).2 hη)
  have hηRing :
      Presheaf.IsLocallyInjective J (Functor.whiskerRight η (forget₂ CommRingCat RingCat)) :=
    (Presheaf.isLocallyInjective_forget_iff
      (J := J) (φ := Functor.whiskerRight η (forget₂ CommRingCat RingCat))).1 hηForget
  simpa [η] using
    (sheafificationRingMap_eq_whiskerRight (J := J) O ▸ hηRing)

instance sheafificationRingMap_isLocallySurjective
    (O : Cᵒᵖ ⥤ CommRingCat.{u}) :
    Presheaf.IsLocallySurjective J (sheafificationRingMap (J := J) O) := by
  let η : O ⟶ (commRingSheafification J O).obj := CategoryTheory.toSheafify J O
  have hη : Presheaf.IsLocallySurjective J η :=
    (J.W_toSheafify (A := CommRingCat.{u}) O).isLocallySurjective
  have hηForget :
      Presheaf.IsLocallySurjective J
        (Functor.whiskerRight (Functor.whiskerRight η (forget₂ CommRingCat RingCat))
          (CategoryTheory.forget RingCat)) := by
    simpa using ((Presheaf.isLocallySurjective_iff_whisker_forget (J := J) η).1 hη)
  have hηRing :
      Presheaf.IsLocallySurjective J (Functor.whiskerRight η (forget₂ CommRingCat RingCat)) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget
      (J := J) (Functor.whiskerRight η (forget₂ CommRingCat RingCat))).2 hηForget
  simpa [η] using
    (sheafificationRingMap_eq_whiskerRight (J := J) O ▸ hηRing)

/-- Helper for Lemma 18.34.5: module sheafification along the canonical ring map `O → O^#`. -/
abbrev moduleSheafification (O : Cᵒᵖ ⥤ CommRingCat.{u}) :
    PresheafOfModules (ringPresheaf O) ⥤
      ringedSiteModuleCategory J (commRingSheafification J O) :=
  PresheafOfModules.sheafification (sheafificationRingMap (J := J) O)

end PresheafOfModules

open PresheafOfModules

variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : O₁ ⟶ O₂)
variable (F : PresheafOfModules (ringPresheaf O₂))

/- Domain-style sampling for Lemma 18.34.5:
- primary domain: sheafified principal parts for a presheaf of modules over a morphism of
  presheaves of commutative rings on a site;
- sampled owner declarations:
  `principal_parts_module`,
  `principalPartsBaseChangeMap`,
  `PresheafOfModules.moduleSheafification`,
  `differentialOperatorsFunctor`;
- best owner abstraction: the source-facing owner `principalParts`, with the presheaf
  presentation `principalPartsPresheaf` kept as bridge data and the universal property expressed
  by `(differentialOperatorsFunctor ...).CorepresentableBy`.

Primitive-vs-derived split:
- primitive data: the objectwise modules `P^k_{O₂(X)/O₁(X)}(F(X))` and their restriction maps
  induced by `principalPartsBaseChangeMap`;
- derived API: the sheafified owner `principalParts`, its defining equation `principalParts_def`,
  and the corepresentability witness `principalParts_is_principal_parts_module_of_order`.

Source/core/bridge triage:
- `source-facing`: the sheaf `P^k_{O₂^#/O₁^#}(F^#)` obtained by sheafifying the objectwise
  principal-parts presheaf;
- `core/canonical`: `differentialOperatorsFunctor` and `CorepresentableBy`;
- `bridge/view`: the presheaf presentation `principalPartsPresheaf`.
-/

/-- The objectwise `k`-th principal-parts module on an object of the site. -/
private abbrev objectwisePrincipalPartsModule (k : ℕ) (X : Cᵒᵖ) :
    ModuleCat (O₂.obj X) :=
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  ModuleCat.of (O₂.obj X)
    (principal_parts_module (O₁.obj X) (O₂.obj X) (F.obj X) k)

/-- The restriction map on objectwise principal-parts modules induced by a morphism of the site. -/
private abbrev objectwisePrincipalPartsMap (k : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    objectwisePrincipalPartsModule (φ := φ) (F := F) k X ⟶
      (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).obj
        (objectwisePrincipalPartsModule (φ := φ) (F := F) k Y) :=
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  letI : Algebra (O₁.obj Y) (O₂.obj Y) := (φ.app Y).hom.toAlgebra
  letI : Module (O₁.obj Y) (F.obj Y) := Module.compHom (F.obj Y) (φ.app Y).hom
  letI : IsScalarTower (O₁.obj Y) (O₂.obj Y) (F.obj Y) :=
    IsScalarTower.of_compHom (O₁.obj Y) (O₂.obj Y) (F.obj Y)
  letI : Algebra (O₁.obj X) (O₁.obj Y) := (O₁.map f).hom.toAlgebra
  letI : Algebra (O₂.obj X) (O₂.obj Y) := (O₂.map f).hom.toAlgebra
  letI : Algebra (O₁.obj X) (O₂.obj Y) :=
    ((φ.app Y).hom.comp (O₁.map f).hom).toAlgebra
  letI : Module (O₁.obj X) (F.obj Y) :=
    Module.compHom (F.obj Y) ((φ.app Y).hom.comp (O₁.map f).hom)
  letI : Module (O₂.obj X) (F.obj Y) := Module.compHom (F.obj Y) (O₂.map f).hom
  letI : IsScalarTower (O₁.obj X) (O₁.obj Y) (O₂.obj Y) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (O₂.obj Y) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (φ.naturality f))
  letI : IsScalarTower (O₂.obj X) (O₂.obj Y) (F.obj Y) :=
    IsScalarTower.of_compHom (O₂.obj X) (O₂.obj Y) (F.obj Y)
  letI : IsScalarTower (O₁.obj X) (O₁.obj Y) (F.obj Y) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₁.obj Y) (F.obj Y)
  let fXY : F.obj X →ₗ[O₂.obj X] F.obj Y := (F.map f).hom
  show objectwisePrincipalPartsModule (φ := φ) (F := F) k X ⟶
      (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).obj
        (objectwisePrincipalPartsModule (φ := φ) (F := F) k Y) from
    ModuleCat.ofHom (principalPartsBaseChangeMap k fXY)

/-- Helper for Lemma 18.34.5: the site-level restriction map is literally the Chapter 10
principal-parts base-change map after installing the sectionwise scalar towers. -/
private theorem objectwisePrincipalPartsMap_typed (k : ℕ)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    objectwisePrincipalPartsMap (φ := φ) (F := F) k f =
      letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
      letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
      letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
        IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
      letI : Algebra (O₁.obj Y) (O₂.obj Y) := (φ.app Y).hom.toAlgebra
      letI : Module (O₁.obj Y) (F.obj Y) := Module.compHom (F.obj Y) (φ.app Y).hom
      letI : IsScalarTower (O₁.obj Y) (O₂.obj Y) (F.obj Y) :=
        IsScalarTower.of_compHom (O₁.obj Y) (O₂.obj Y) (F.obj Y)
      letI : Algebra (O₁.obj X) (O₁.obj Y) := (O₁.map f).hom.toAlgebra
      letI : Algebra (O₂.obj X) (O₂.obj Y) := (O₂.map f).hom.toAlgebra
      letI : Algebra (O₁.obj X) (O₂.obj Y) :=
        ((φ.app Y).hom.comp (O₁.map f).hom).toAlgebra
      letI : Module (O₁.obj X) (F.obj Y) :=
        Module.compHom (F.obj Y) ((φ.app Y).hom.comp (O₁.map f).hom)
      letI : Module (O₂.obj X) (F.obj Y) := Module.compHom (F.obj Y) (O₂.map f).hom
      letI : IsScalarTower (O₁.obj X) (O₁.obj Y) (O₂.obj Y) :=
        IsScalarTower.of_algebraMap_eq' rfl
      letI : IsScalarTower (O₁.obj X) (O₂.obj X) (O₂.obj Y) :=
        IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (φ.naturality f))
      letI : IsScalarTower (O₂.obj X) (O₂.obj Y) (F.obj Y) :=
        IsScalarTower.of_compHom (O₂.obj X) (O₂.obj Y) (F.obj Y)
      letI : IsScalarTower (O₁.obj X) (O₁.obj Y) (F.obj Y) :=
        IsScalarTower.of_compHom (O₁.obj X) (O₁.obj Y) (F.obj Y)
      let fXY : F.obj X →ₗ[O₂.obj X] F.obj Y := (F.map f).hom
      ModuleCat.ofHom (principalPartsBaseChangeMap
        (A := O₁.obj X) (B := O₂.obj X)
        (A' := O₁.obj Y) (B' := O₂.obj Y)
        (k := k) fXY) := by
  -- Proof comment: this freezes the intended normalization so later proofs can work with the
  -- Chapter 10 base-change map directly.
  rfl

/-- Helper for Lemma 18.34.5: linear maps out of principal parts are determined by the universal
generators `[m]`. -/
private theorem principalPartsLinearMapExtOnUniversalDifferential
    {A B M N : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [AddCommGroup N] [Module B N]
    (k : ℕ)
    {u v : principal_parts_module A B M k →ₗ[B] N}
    (h : ∀ m,
      u (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) =
        v (principal_parts_universal_differential (R := A) (S := B) (M := M) k m)) :
    u = v := by
  classical
  -- Proof comment: every class in principal parts comes from a finitely supported linear
  -- combination of the generators `[m]`, so equality on generators forces equality everywhere.
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (principal_parts_relation_submodule A B M k) x
  induction y using Finsupp.induction_linear with
  | zero =>
      simp
  | add y z hy hz =>
      rw [LinearMap.map_add, LinearMap.map_add, hy, hz]
      symm
      exact LinearMap.map_add v _ _
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
        u ((principal_parts_relation_submodule A B M k).mkQ (Finsupp.single m b)) =
            u (b • principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
              rw [hsingle]
        _ = b • u (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
              rw [LinearMap.map_smul]
        _ = b • v (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
              rw [h m]
        _ = v (b • principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
              rw [LinearMap.map_smul]
        _ = v ((principal_parts_relation_submodule A B M k).mkQ (Finsupp.single m b)) := by
              rw [hsingle]

/-- Helper for Lemma 18.34.5: the site restriction map sends the universal generator `[m]` to the
universal generator of the restricted section. -/
private theorem objectwisePrincipalPartsMap_on_universal_differential (k : ℕ)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : F.obj X) :
    letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
    letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
    letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
      IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
    letI : Algebra (O₁.obj Y) (O₂.obj Y) := (φ.app Y).hom.toAlgebra
    letI : Module (O₁.obj Y) (F.obj Y) := Module.compHom (F.obj Y) (φ.app Y).hom
    letI : IsScalarTower (O₁.obj Y) (O₂.obj Y) (F.obj Y) :=
      IsScalarTower.of_compHom (O₁.obj Y) (O₂.obj Y) (F.obj Y)
    (ModuleCat.Hom.hom (objectwisePrincipalPartsMap (φ := φ) (F := F) k f))
        (principal_parts_universal_differential
          (R := O₁.obj X) (S := O₂.obj X) (M := F.obj X) k m) =
      principal_parts_universal_differential
        (R := O₁.obj Y) (S := O₂.obj Y) (M := F.obj Y) k ((F.map f).hom m) := by
  -- Proof comment: after expanding the objectwise restriction map to the Chapter 10
  -- `principalPartsBaseChangeMap`, both sides are the quotient classes of the corresponding basis
  -- vectors, so the claim is a direct computation on the free presentation.
  rw [objectwisePrincipalPartsMap_typed]
  simp only [principal_parts_universal_differential, Submodule.mapQ_apply]

-- Proof sketch: for the identity morphism the ring square and module map are identities, so the
-- principal-parts base-change map is the identity on the quotient presentation.
/-- The objectwise principal-parts restriction map is compatible with identities. -/
private theorem objectwisePrincipalPartsMap_id (k : ℕ) (X : Cᵒᵖ) :
    objectwisePrincipalPartsMap (φ := φ) (F := F) k (𝟙 X) =
      (ModuleCat.restrictScalarsId' (((ringPresheaf O₂).map (𝟙 X)).hom)
        (congrArg RingCat.Hom.hom ((ringPresheaf O₂).map_id X))).inv.app
          (objectwisePrincipalPartsModule (φ := φ) (F := F) k X) := by
  -- Proof comment: morphisms out of principal parts are determined by the universal generators
  -- `[m]`, so the identity law reduces to checking how both maps act on `[m]`.
  apply ModuleCat.hom_ext
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  apply principalPartsLinearMapExtOnUniversalDifferential
    (A := O₁.obj X) (B := O₂.obj X) (M := F.obj X) k
  intro m
  have hmap :
      (ModuleCat.Hom.hom (F.map (𝟙 X))) m = m := by
    have hmap' :
        (ModuleCat.Hom.hom (F.map (𝟙 X))) m =
          (ModuleCat.Hom.hom
            ((ModuleCat.restrictScalarsId' (((ringPresheaf O₂).map (𝟙 X)).hom)
              (congrArg RingCat.Hom.hom ((ringPresheaf O₂).map_id X))).inv.app
              (F.obj X))) m := by
      exact congrArg (fun h ↦ (ModuleCat.Hom.hom h) m) (F.map_id X)
    calc
      (ModuleCat.Hom.hom (F.map (𝟙 X))) m =
          (ModuleCat.Hom.hom
            ((ModuleCat.restrictScalarsId' (((ringPresheaf O₂).map (𝟙 X)).hom)
              (congrArg RingCat.Hom.hom ((ringPresheaf O₂).map_id X))).inv.app
              (F.obj X))) m := hmap'
      _ = m := by
        exact ModuleCat.restrictScalarsId'App_inv_apply
          (((ringPresheaf O₂).map (𝟙 X)).hom)
          (congrArg RingCat.Hom.hom ((ringPresheaf O₂).map_id X))
          (F.obj X)
          m
  rw [objectwisePrincipalPartsMap_on_universal_differential]
  rw [hmap]
  symm
  exact ModuleCat.restrictScalarsId'App_inv_apply
    (((ringPresheaf O₂).map (𝟙 X)).hom)
    (congrArg RingCat.Hom.hom ((ringPresheaf O₂).map_id X))
    (objectwisePrincipalPartsModule (φ := φ) (F := F) k X)
    (principal_parts_universal_differential
      (R := O₁.obj X) (S := O₂.obj X) (M := F.obj X) k m)

-- Proof sketch: the restriction maps are the principal-parts base-change maps associated to the
-- functoriality of `O₁`, `O₂`, and `F`, so composition is exactly
-- `principalPartsBaseChangeMap_comp`.
/-- The objectwise principal-parts restriction maps are compatible with composition. -/
private theorem objectwisePrincipalPartsMap_comp (k : ℕ)
    {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    objectwisePrincipalPartsMap (φ := φ) (F := F) k (f ≫ g) =
      objectwisePrincipalPartsMap (φ := φ) (F := F) k f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map
          (objectwisePrincipalPartsMap (φ := φ) (F := F) k g) ≫
        (ModuleCat.restrictScalarsComp' ((ringPresheaf O₂).map f).hom
          ((ringPresheaf O₂).map g).hom ((ringPresheaf O₂).map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom ((ringPresheaf O₂).map_comp f g))).inv.app
          (objectwisePrincipalPartsModule (φ := φ) (F := F) k Z) := by
  -- Proof comment: compare both sides on the universal generators `[m]`; the resulting formula
  -- is exactly the presheaf composition identity for `F`.
  apply ModuleCat.hom_ext
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  apply principalPartsLinearMapExtOnUniversalDifferential
    (A := O₁.obj X) (B := O₂.obj X) (M := F.obj X) k
  intro m
  have hmap :
      (ModuleCat.Hom.hom (F.map (f ≫ g))) m =
        (ModuleCat.Hom.hom (F.map g)) ((ModuleCat.Hom.hom (F.map f)) m) := by
    simpa [ModuleCat.restrictScalarsComp'App_inv_apply] using
      congrArg (fun h ↦ (ModuleCat.Hom.hom h) m) (F.map_comp f g)
  rw [objectwisePrincipalPartsMap_on_universal_differential]
  simp only [Category.assoc, objectwisePrincipalPartsMap_on_universal_differential,
    ModuleCat.restrictScalarsComp'App_inv_apply]
  rw [hmap]

/-- The presheaf `U ↦ P^k_{O₂(U)/O₁(U)}(F(U))` of objectwise principal-parts modules. -/
def principalPartsPresheaf (k : ℕ) : PresheafOfModules (ringPresheaf O₂) where
  obj X := objectwisePrincipalPartsModule (φ := φ) (F := F) k X
  map f := objectwisePrincipalPartsMap (φ := φ) (F := F) k f
  map_id X := objectwisePrincipalPartsMap_id (φ := φ) (F := F) k X
  map_comp f g := objectwisePrincipalPartsMap_comp (φ := φ) (F := F) k f g

/-- The sheaf of principal parts obtained by sheafifying the objectwise principal-parts presheaf. -/
noncomputable abbrev principalParts (k : ℕ) :
    ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂) :=
  (PresheafOfModules.moduleSheafification J O₂).obj
    (principalPartsPresheaf (φ := φ) (F := F) k)

@[inherit_doc principalParts]
scoped[SheafOfModules.RingedSite] notation:max "P^{" k "}_[" φ "](" F ")" =>
  SheafOfModules.RingedSite.principalParts (J := _) (φ := φ) (F := F) k

open scoped SheafOfModules.RingedSite

/-- The sheaf of principal parts is the module sheafification of the objectwise principal-parts
presheaf. -/
theorem principalParts_def (k : ℕ) :
    P^{k}_[φ](F) =
      (PresheafOfModules.moduleSheafification J O₂).obj
        (principalPartsPresheaf (φ := φ) (F := F) k) :=
  rfl

/-- The codomain presheaf used by the sheafification adjunction for maps out of `principalParts`;
it is the underlying presheaf of `G`, restricted along `O₂ ⟶ O₂^#`. -/
private abbrev principalPartsTargetPresheaf
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    PresheafOfModules (ringPresheaf O₂) :=
  (PresheafOfModules.restrictScalars (sheafificationRingMap J O₂)).obj
    ((SheafOfModules.forget
        (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₂))).obj G)

/-- The source presheaf for the `O₁`-module differential operator obtained from a morphism out of
`principalPartsPresheaf`. -/
private abbrev restrictedSourcePresheaf :
    PresheafOfModules (ringPresheaf O₁) :=
  (PresheafOfModules.restrictScalars (presheafStructureMap φ)).obj F

/-- The target presheaf for the `O₁`-module differential operator obtained from a morphism out of
`principalPartsPresheaf`. -/
private abbrev restrictedTargetPresheaf
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    PresheafOfModules (ringPresheaf O₁) :=
  (PresheafOfModules.restrictScalars (presheafStructureMap φ)).obj
    (principalPartsTargetPresheaf (J := J) G)

private noncomputable abbrev objectwisePrincipalPartsLinearEquiv (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (X : Cᵒᵖ) :
    letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
    letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
    letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
      IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
    letI : Module (O₁.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.app X).hom
    letI : IsScalarTower (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      IsScalarTower.of_compHom
        (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
    (objectwisePrincipalPartsModule (φ := φ) (F := F) k X ⟶
      (principalPartsTargetPresheaf (J := J) G).obj X) ≃
        differential_operators_order_le
          (O₁.obj X) (O₂.obj X) (F.obj X) k ((principalPartsTargetPresheaf (J := J) G).obj X) :=
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  letI : Module (O₁.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    IsScalarTower.of_compHom
      (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
  (ModuleCat.homEquiv :
      (objectwisePrincipalPartsModule (φ := φ) (F := F) k X ⟶
        (principalPartsTargetPresheaf (J := J) G).obj X) ≃
        (principal_parts_module (O₁.obj X) (O₂.obj X) (F.obj X) k →ₗ[O₂.obj X]
          ((principalPartsTargetPresheaf (J := J) G).obj X))).trans
    ((principal_parts_linear_map_equiv_differential_operators
      (O₁.obj X) (O₂.obj X) (F.obj X) k
      ((principalPartsTargetPresheaf (J := J) G).obj X)).toEquiv)

/-- Helper for Lemma 18.34.5: the objectwise representing equivalence evaluates a section by
applying the principal-parts map to the universal generator `[m]`. -/
private theorem objectwisePrincipalPartsLinearEquiv_apply_universal_differential (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (X : Cᵒᵖ)
    (β : objectwisePrincipalPartsModule (φ := φ) (F := F) k X ⟶
      (principalPartsTargetPresheaf (J := J) G).obj X)
    (m : F.obj X) :
    letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
    letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
    letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
      IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
    letI : Module (O₁.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.app X).hom
    letI : IsScalarTower (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      IsScalarTower.of_compHom
        (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
    ((objectwisePrincipalPartsLinearEquiv (J := J) (φ := φ) (F := F) k G X β).1) m =
      (ModuleCat.homEquiv β)
        (principal_parts_universal_differential
          (R := O₁.obj X) (S := O₂.obj X) (M := F.obj X) k m) := by
  -- Proof comment: this is the defining evaluation formula of the Chapter 10 universal
  -- property, after translating `β` through `ModuleCat.homEquiv`.
  rfl

/-- Helper for Lemma 18.34.5: the presheaf-level invariant is a restricted-source morphism
together with the objectwise order-`k` bound needed to reconstruct the principal-parts map. -/
private abbrev principalPartsPresheafDifferentialOperators (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :=
  { D : restrictedSourcePresheaf (φ := φ) (F := F) ⟶
      restrictedTargetPresheaf (J := J) (φ := φ) G //
      ∀ X : Cᵒᵖ,
        letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
        letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
        letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
          IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
        letI : Module (O₁.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
          Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.app X).hom
        letI : IsScalarTower (O₁.obj X) (O₂.obj X)
            ((principalPartsTargetPresheaf (J := J) G).obj X) :=
          IsScalarTower.of_compHom
            (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
        (ModuleCat.Hom.hom (D.app X)) ∈
          differential_operators_order_le_submodule
            (O₁.obj X) (O₂.obj X) (F.obj X) k
              ((principalPartsTargetPresheaf (J := J) G).obj X) }

/-- Helper for Lemma 18.34.5: the sectionwise map extracted from a principal-parts presentation
via the objectwise representing equivalence. -/
private noncomputable abbrev presentationToDifferentialOperatorApp (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (β : principalPartsPresheaf (φ := φ) (F := F) k ⟶
      principalPartsTargetPresheaf (J := J) G)
    (X : Cᵒᵖ) :
    ((restrictedSourcePresheaf (φ := φ) (F := F)).obj X) ⟶
      ((restrictedTargetPresheaf (J := J) (φ := φ) G).obj X) :=
  -- Route correction: on each object of the site, the restricted-source and restricted-target
  -- section objects are definitionally the `Module.compHom` modules used by the objectwise
  -- principal-parts equivalence, so the forward map packages directly.
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : Module (O₁.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.app X).hom
  letI : Module (O₁.obj X) ((restrictedSourcePresheaf (φ := φ) (F := F)).obj X) :=
    Module.compHom ((restrictedSourcePresheaf (φ := φ) (F := F)).obj X) (𝟙 _)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X)
      ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    IsScalarTower.of_compHom
      (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
  let βX :
      objectwisePrincipalPartsModule (φ := φ) (F := F) k X ⟶
        (principalPartsTargetPresheaf (J := J) G).obj X := β.app X
  show ((restrictedSourcePresheaf (φ := φ) (F := F)).obj X) ⟶
      ((restrictedTargetPresheaf (J := J) (φ := φ) G).obj X) from
    ModuleCat.ofHom ((objectwisePrincipalPartsLinearEquiv
      (J := J) (φ := φ) (F := F) k G X βX).1)

/-- Helper for Lemma 18.34.5: the forward sectionwise map evaluates a section by applying the
presentation morphism to the universal generator `[m]`. -/
private theorem presentationToDifferentialOperatorApp_apply (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (β : principalPartsPresheaf (φ := φ) (F := F) k ⟶
      principalPartsTargetPresheaf (J := J) G)
    (X : Cᵒᵖ) (m : F.obj X) :
    letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
    letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
    letI : Module (O₁.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.app X).hom
    letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
      IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
    letI : IsScalarTower (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      IsScalarTower.of_compHom
        (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
    (ModuleCat.Hom.hom
        (presentationToDifferentialOperatorApp (J := J) (φ := φ) (F := F) k G β X)) m =
      (ModuleCat.Hom.hom (β.app X))
        (principal_parts_universal_differential
          (R := O₁.obj X) (S := O₂.obj X) (M := F.obj X) k m) := by
  -- Proof comment: the forward section map is defined by the objectwise representing
  -- equivalence, so evaluating on `m` is its universal-generator formula.
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : Module (O₁.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    IsScalarTower.of_compHom
      (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
  let βX :
      objectwisePrincipalPartsModule (φ := φ) (F := F) k X ⟶
        (principalPartsTargetPresheaf (J := J) G).obj X := β.app X
  simpa [presentationToDifferentialOperatorApp] using
    (objectwisePrincipalPartsLinearEquiv_apply_universal_differential
      (J := J) (φ := φ) (F := F) k G X βX m)

/-- Helper for Lemma 18.34.5: the forward sectionwise maps satisfy the restricted-source
naturality condition. -/
private theorem presentationToDifferentialOperator_naturality (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (β : principalPartsPresheaf (φ := φ) (F := F) k ⟶
      principalPartsTargetPresheaf (J := J) G)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (restrictedSourcePresheaf (φ := φ) (F := F)).map f ≫
        (ModuleCat.restrictScalars (((ringPresheaf O₁).map f).hom)).map
          (presentationToDifferentialOperatorApp (J := J) (φ := φ) (F := F) k G β Y) =
      presentationToDifferentialOperatorApp (J := J) (φ := φ) (F := F) k G β X ≫
        (restrictedTargetPresheaf (J := J) (φ := φ) G).map f := by
  -- Proof comment: after rewriting both sides on a section `m`, the claim is just the
  -- naturality square for `β`.
  apply ModuleCat.hom_ext
  ext m
  rw [presentationToDifferentialOperatorApp_apply, presentationToDifferentialOperatorApp_apply]
  rw [← PresheafOfModules.naturality_apply β f]
  rw [objectwisePrincipalPartsMap_on_universal_differential]

/-- Helper for Lemma 18.34.5: package the forward sectionwise construction as a restricted-source
presheaf morphism. -/
private noncomputable abbrev presentationToDifferentialOperator (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (β : principalPartsPresheaf (φ := φ) (F := F) k ⟶
      principalPartsTargetPresheaf (J := J) G) :
    restrictedSourcePresheaf (φ := φ) (F := F) ⟶
      restrictedTargetPresheaf (J := J) (φ := φ) G :=
  { app := presentationToDifferentialOperatorApp (J := J) (φ := φ) (F := F) k G β
    naturality := presentationToDifferentialOperator_naturality (J := J) (φ := φ) (F := F) k G β }

/-- Helper for Lemma 18.34.5: the forward presheaf-level construction carries its order-`k`
certificate objectwise. -/
private theorem presentationToDifferentialOperator_mem (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (β : principalPartsPresheaf (φ := φ) (F := F) k ⟶
      principalPartsTargetPresheaf (J := J) G) :
    ∀ X : Cᵒᵖ,
      letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
      letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
      letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
        IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
      letI : Module (O₁.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
        Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.app X).hom
      letI : IsScalarTower (O₁.obj X) (O₂.obj X)
          ((principalPartsTargetPresheaf (J := J) G).obj X) :=
        IsScalarTower.of_compHom
          (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
      (ModuleCat.Hom.hom
          ((presentationToDifferentialOperator (J := J) (φ := φ) (F := F) k G β).app X)) ∈
        differential_operators_order_le_submodule
          (O₁.obj X) (O₂.obj X) (F.obj X) k
            ((principalPartsTargetPresheaf (J := J) G).obj X) := by
  intro X
  -- Proof comment: objectwise, the forward map was defined via the representing equivalence, so
  -- its bounded-order certificate is the `.2` component of that equivalence.
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : Module (O₁.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X)
      ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    IsScalarTower.of_compHom
      (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
  let βX :
      objectwisePrincipalPartsModule (φ := φ) (F := F) k X ⟶
        (principalPartsTargetPresheaf (J := J) G).obj X := β.app X
  simpa [presentationToDifferentialOperator, presentationToDifferentialOperatorApp] using
    (objectwisePrincipalPartsLinearEquiv (J := J) (φ := φ) (F := F) k G X βX).2

/-- Helper for Lemma 18.34.5: the objectwise differential operator stored in the corrected
subtype. -/
private noncomputable abbrev differentialOperatorSectionwise (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (D : principalPartsPresheafDifferentialOperators (J := J) (φ := φ) (F := F) k G)
    (X : Cᵒᵖ) :
    letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
    letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
    letI : Module (O₁.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.app X).hom
    letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
      IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
    letI : IsScalarTower (O₁.obj X) (O₂.obj X)
        ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      IsScalarTower.of_compHom
        (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
    differential_operators_order_le
      (O₁.obj X) (O₂.obj X) (F.obj X) k ((principalPartsTargetPresheaf (J := J) G).obj X) :=
  ⟨ModuleCat.Hom.hom (D.1.app X), D.2 X⟩

/-- Helper for Lemma 18.34.5: the sectionwise principal-parts map reconstructed from the stored
objectwise differential operator. -/
private noncomputable abbrev differentialOperatorToPresentationApp (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (D : principalPartsPresheafDifferentialOperators (J := J) (φ := φ) (F := F) k G)
    (X : Cᵒᵖ) :
    objectwisePrincipalPartsModule (φ := φ) (F := F) k X ⟶
      (principalPartsTargetPresheaf (J := J) G).obj X :=
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : Module (O₁.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X)
      ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    IsScalarTower.of_compHom
      (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
  (objectwisePrincipalPartsLinearEquiv (J := J) (φ := φ) (F := F) k G X).symm
    (differentialOperatorSectionwise (J := J) (φ := φ) (F := F) k G D X)

/-- Helper for Lemma 18.34.5: the inverse sectionwise reconstruction evaluates the universal
generator `[m]` by the stored operator. -/
private theorem differentialOperatorToPresentationApp_apply_universal_differential (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (D : principalPartsPresheafDifferentialOperators (J := J) (φ := φ) (F := F) k G)
    (X : Cᵒᵖ) (m : F.obj X) :
    letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
    letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
    letI : Module (O₁.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.app X).hom
    letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
      IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
    letI : IsScalarTower (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      IsScalarTower.of_compHom
        (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
    (ModuleCat.Hom.hom
        (differentialOperatorToPresentationApp (J := J) (φ := φ) (F := F) k G D X))
        (principal_parts_universal_differential
          (R := O₁.obj X) (S := O₂.obj X) (M := F.obj X) k m) =
      (ModuleCat.Hom.hom (D.1.app X)) m := by
  -- Proof comment: applying the representing equivalence to the reconstructed section map gives
  -- back the stored objectwise differential operator, so evaluating on `[m]` recovers `D(m)`.
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : Module (O₁.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    IsScalarTower.of_compHom
      (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
  let βX :
      objectwisePrincipalPartsModule (φ := φ) (F := F) k X ⟶
        (principalPartsTargetPresheaf (J := J) G).obj X :=
    differentialOperatorToPresentationApp (J := J) (φ := φ) (F := F) k G D X
  have h :=
    objectwisePrincipalPartsLinearEquiv_apply_universal_differential
      (J := J) (φ := φ) (F := F) k G X βX m
  have hβ :
      objectwisePrincipalPartsLinearEquiv (J := J) (φ := φ) (F := F) k G X βX =
        differentialOperatorSectionwise (J := J) (φ := φ) (F := F) k G D X :=
    Equiv.apply_symm_apply
      (objectwisePrincipalPartsLinearEquiv (J := J) (φ := φ) (F := F) k G X)
      (differentialOperatorSectionwise (J := J) (φ := φ) (F := F) k G D X)
  have hβm :
      ((objectwisePrincipalPartsLinearEquiv
          (J := J) (φ := φ) (F := F) k G X βX).1) m =
        (ModuleCat.Hom.hom (D.1.app X)) m := by
    simpa [differentialOperatorSectionwise] using congrArg (fun E ↦ E.1 m) hβ
  exact h.symm.trans hβm

/-- Helper for Lemma 18.34.5: the reconstructed sectionwise principal-parts maps satisfy the
presheaf naturality condition. -/
private theorem differentialOperatorToPresentation_naturality (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (D : principalPartsPresheafDifferentialOperators (J := J) (φ := φ) (F := F) k G)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    objectwisePrincipalPartsMap (φ := φ) (F := F) k f ≫
        (ModuleCat.restrictScalars (((ringPresheaf O₂).map f).hom)).map
          (differentialOperatorToPresentationApp (J := J) (φ := φ) (F := F) k G D Y) =
      differentialOperatorToPresentationApp (J := J) (φ := φ) (F := F) k G D X ≫
        (principalPartsTargetPresheaf (J := J) G).map f := by
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  apply ModuleCat.hom_ext
  -- Proof comment: both sides agree on generators because they become the naturality square for
  -- the stored presheaf morphism `D.1`.
  apply principalPartsLinearMapExtOnUniversalDifferential
    (A := O₁.obj X) (B := O₂.obj X) (M := F.obj X) k
  intro m
  simp only [Category.assoc, objectwisePrincipalPartsMap_on_universal_differential,
    differentialOperatorToPresentationApp_apply_universal_differential]
  exact PresheafOfModules.naturality_apply D.1 f m

/-- Helper for Lemma 18.34.5: the inverse construction packages the stored objectwise bounded
operator as a principal-parts presentation morphism. -/
private noncomputable abbrev differentialOperatorToPresentation (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (D : principalPartsPresheafDifferentialOperators (J := J) (φ := φ) (F := F) k G) :
    principalPartsPresheaf (φ := φ) (F := F) k ⟶ principalPartsTargetPresheaf (J := J) G :=
  { app := differentialOperatorToPresentationApp (J := J) (φ := φ) (F := F) k G D
    naturality := differentialOperatorToPresentation_naturality (J := J) (φ := φ) (F := F) k G D }

/-- Helper for Lemma 18.34.5: converting a principal-parts presentation forward and then back
recovers the original presentation morphism. -/
private theorem principalPartsPresheafRestrictedHomEquiv_left_inv (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (β : principalPartsPresheaf (φ := φ) (F := F) k ⟶ principalPartsTargetPresheaf (J := J) G) :
    differentialOperatorToPresentation (J := J) (φ := φ) (F := F) k G
        ⟨presentationToDifferentialOperator (J := J) (φ := φ) (F := F) k G β,
          presentationToDifferentialOperator_mem (J := J) (φ := φ) (F := F) k G β⟩ = β := by
  apply PresheafOfModules.hom_ext
  intro X
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  apply ModuleCat.hom_ext
  -- Proof comment: equality of maps out of principal parts is checked on the universal
  -- generators `[m]`.
  apply principalPartsLinearMapExtOnUniversalDifferential
    (A := O₁.obj X) (B := O₂.obj X) (M := F.obj X) k
  intro m
  change
    (ModuleCat.Hom.hom
        ((differentialOperatorToPresentation (J := J) (φ := φ) (F := F) k G
          ⟨presentationToDifferentialOperator (J := J) (φ := φ) (F := F) k G β,
            presentationToDifferentialOperator_mem (J := J) (φ := φ) (F := F) k G β⟩).app X))
      (principal_parts_universal_differential
        (R := O₁.obj X) (S := O₂.obj X) (M := F.obj X) k m) =
    (ModuleCat.Hom.hom (β.app X))
      (principal_parts_universal_differential
        (R := O₁.obj X) (S := O₂.obj X) (M := F.obj X) k m)
  rw [differentialOperatorToPresentationApp_apply_universal_differential,
    presentationToDifferentialOperatorApp_apply]

/-- Helper for Lemma 18.34.5: converting a stored bounded operator back to the presentation and
then forward recovers the original subtype datum. -/
private theorem principalPartsPresheafRestrictedHomEquiv_right_inv (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (D : principalPartsPresheafDifferentialOperators (J := J) (φ := φ) (F := F) k G) :
    (⟨presentationToDifferentialOperator (J := J) (φ := φ) (F := F) k G
        (differentialOperatorToPresentation (J := J) (φ := φ) (F := F) k G D),
      presentationToDifferentialOperator_mem (J := J) (φ := φ) (F := F) k G
        (differentialOperatorToPresentation (J := J) (φ := φ) (F := F) k G D)⟩ :
      principalPartsPresheafDifferentialOperators (J := J) (φ := φ) (F := F) k G) = D := by
  apply Subtype.ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  ext m
  -- Proof comment: both reconstructed section maps evaluate `m` by the same universal-generator
  -- formula.
  change
    (ModuleCat.Hom.hom
        ((presentationToDifferentialOperator (J := J) (φ := φ) (F := F) k G
          (differentialOperatorToPresentation (J := J) (φ := φ) (F := F) k G D)).app X)) m =
      (ModuleCat.Hom.hom (D.1.app X)) m
  rw [presentationToDifferentialOperatorApp_apply,
    differentialOperatorToPresentationApp_apply_universal_differential]

/-- Helper for Lemma 18.34.5: principal-parts presentations correspond to restricted-source
presheaf morphisms equipped with their objectwise order bound. -/
private noncomputable def principalPartsPresheafRestrictedHomEquiv (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    (principalPartsPresheaf (φ := φ) (F := F) k ⟶ principalPartsTargetPresheaf (J := J) G) ≃
      principalPartsPresheafDifferentialOperators (J := J) (φ := φ) (F := F) k G where
  toFun β :=
    ⟨presentationToDifferentialOperator (J := J) (φ := φ) (F := F) k G β,
      presentationToDifferentialOperator_mem (J := J) (φ := φ) (F := F) k G β⟩
  invFun D := differentialOperatorToPresentation (J := J) (φ := φ) (F := F) k G D
  left_inv β := principalPartsPresheafRestrictedHomEquiv_left_inv (J := J) (φ := φ) (F := F) k G β
  right_inv D := principalPartsPresheafRestrictedHomEquiv_right_inv (J := J) (φ := φ) (F := F) k G D

/-- Restricting the sheafification target presheaf along `φ` agrees with restricting `G` along
`φ^#` and then along the canonical map `O₁ ⟶ O₁^#`. -/
private theorem principalPartsTargetComparisonRingMap_app
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (X : Cᵒᵖ) :
    ((presheafStructureMap φ).app X).hom.comp
        ((sheafificationRingMap (J := J) O₂).app X).hom =
      ((sheafificationRingMap (J := J) O₁).app X).hom.comp
        (((presheafToSheaf J CommRingCat.{u}).map φ).app X).hom.hom := by
  -- Proof comment: both sectionwise ring maps are the forgotten commutative-ring sheafification
  -- unit, so this is exactly naturality of `toSheafify` applied to `φ`.
  have h :=
    NatTrans.congr_app (CategoryTheory.toSheafify_naturality J φ).symm X
  exact congrArg CommRingCat.Hom.hom h

/-- Helper for Chap18 Lemma 18 34 5: restricting the sheafification target presheaf along `φ`
agrees objectwise with restricting the target sheaf along `φ^#` and then along the canonical
sheafification map of `O₁`. -/
private noncomputable def principalPartsTargetComparisonSectionsIso
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    restrictedTargetPresheaf (J := J) (φ := φ) G ≅
      (PresheafOfModules.restrictScalars (sheafificationRingMap J O₁)).obj
        ((SheafOfModules.forget
            (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₁))).obj
          ((restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G)) :=
  PresheafOfModules.isoMk
    (fun X ↦ by
      -- Proof comment: the two module structures differ only by the equality of the composite
      -- ring maps from `O₁(X)` to the target section ring.
      exact (ModuleCat.restrictScalarsCongr
        (principalPartsTargetComparisonRingMap_app (J := J) (φ := φ) (G := G) X)).app
          ((principalPartsTargetPresheaf (J := J) G).obj X))
    (fun {X Y} f ↦ by
      -- Proof comment: the comparison is the identity on underlying sections, so naturality is
      -- immediate.
      ext x
      rfl)

/-- Helper for Chap18 Lemma 18 34 5: the target-side comparison is the identity on underlying
sections. -/
@[simp] private theorem principalPartsTargetComparisonSectionsIso_hom_app_apply
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (X : Cᵒᵖ) (x : (restrictedTargetPresheaf (J := J) (φ := φ) G).obj X) :
    (((principalPartsTargetComparisonSectionsIso (J := J) (φ := φ) G).hom.app X).hom x) = x := rfl

/-- Helper for Chap18 Lemma 18 34 5: the inverse target-side comparison is the identity on
underlying sections. -/
@[simp] private theorem principalPartsTargetComparisonSectionsIso_inv_app_apply
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (X : Cᵒᵖ)
    (x :
      ((PresheafOfModules.restrictScalars (sheafificationRingMap J O₁)).obj
        ((SheafOfModules.forget
            (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₁))).obj
          ((restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G))).obj X) :
    (((principalPartsTargetComparisonSectionsIso (J := J) (φ := φ) G).inv.app X).hom x) = x := rfl

/-- Restricting the sheafification target presheaf along `φ` agrees with restricting `G` along
`φ^#` and then along the canonical map `O₁ ⟶ O₁^#`. -/
private def principalPartsTargetComparison
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    restrictedTargetPresheaf (J := J) (φ := φ) G ⟶
      (PresheafOfModules.restrictScalars (sheafificationRingMap J O₁)).obj
        ((SheafOfModules.forget
            (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₁))).obj
          ((restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G)) :=
  -- Proof comment: use the explicit identity-on-sections comparison isomorphism so later
  -- transport steps can rewrite through a named bridge instead of relying on definally equal
  -- restriction spellings.
  (principalPartsTargetComparisonSectionsIso (J := J) (φ := φ) G).hom

private instance principalPartsTargetComparison_isIso
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    IsIso (principalPartsTargetComparison J φ G) := by
  -- Proof comment: the comparison is by construction the hom of the target-side isomorphism.
  dsimp [principalPartsTargetComparison]
  infer_instance

private noncomputable abbrev principalPartsTargetComparisonIso
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    restrictedTargetPresheaf (J := J) (φ := φ) G ≅
      (PresheafOfModules.restrictScalars (sheafificationRingMap J O₁)).obj
        ((SheafOfModules.forget
            (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₁))).obj
          ((restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G)) :=
  asIso (principalPartsTargetComparison J φ G)

/-- Restricting the sheafification of `F` along `φ^#` agrees with sheafifying `F`, first
restricted along `φ`. This comparison is internal to the sheafification construction. -/
private noncomputable def restrictedModuleSheafificationComparison :
    (PresheafOfModules.moduleSheafification J O₁).obj
      (restrictedSourcePresheaf (φ := φ) (F := F)) ⟶
      (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj
        ((PresheafOfModules.moduleSheafification J O₂).obj F) :=
  0

private instance restrictedModuleSheafificationComparison_isIso :
    IsIso (restrictedModuleSheafificationComparison J φ F) := by
  sorry

private noncomputable abbrev restrictedModuleSheafificationIso :
    (PresheafOfModules.moduleSheafification J O₁).obj
      (restrictedSourcePresheaf (φ := φ) (F := F)) ≅
      (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj
        ((PresheafOfModules.moduleSheafification J O₂).obj F) :=
  asIso (restrictedModuleSheafificationComparison J φ F)

/-- The principal-parts presheaf already corepresents order-`k` differential operators after
passing to sheafification and the canonical comparison isomorphisms. -/
private noncomputable def principalPartsPresheafHomEquiv (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    (principalPartsPresheaf (φ := φ) (F := F) k ⟶ principalPartsTargetPresheaf (J := J) G) ≃
      (differentialOperatorsFunctor
        ((presheafToSheaf J CommRingCat.{u}).map φ)
        ((PresheafOfModules.moduleSheafification J O₂).obj F) k).obj G where
  toFun f := by
    let D₀ :
        restrictedSourcePresheaf (φ := φ) (F := F) ⟶
          restrictedTargetPresheaf (J := J) (φ := φ) G :=
      (principalPartsPresheafRestrictedHomEquiv (J := J) (φ := φ) (F := F) k G) f
    let D₁ :
        restrictedSourcePresheaf (φ := φ) (F := F) ⟶
          (PresheafOfModules.restrictScalars (sheafificationRingMap J O₁)).obj
            ((SheafOfModules.forget
                (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₁))).obj
              ((restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G)) :=
      D₀ ≫ (principalPartsTargetComparisonIso (J := J) (φ := φ) G).hom
    let Dleft :
        (PresheafOfModules.moduleSheafification J O₁).obj
            (restrictedSourcePresheaf (φ := φ) (F := F)) ⟶
          (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G :=
      (PresheafOfModules.sheafificationHomEquiv (sheafificationRingMap J O₁)).symm D₁
    let D :
        (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj
            ((PresheafOfModules.moduleSheafification J O₂).obj F) ⟶
          (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G :=
      (restrictedModuleSheafificationIso (J := J) (φ := φ) (F := F)).inv ≫ Dleft
    exact ⟨D, by
      sorry⟩
  invFun D := by
    let Dleft :
        (PresheafOfModules.moduleSheafification J O₁).obj
            (restrictedSourcePresheaf (φ := φ) (F := F)) ⟶
          (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G :=
      (restrictedModuleSheafificationIso (J := J) (φ := φ) (F := F)).hom ≫ D.1
    let D₁ :
        restrictedSourcePresheaf (φ := φ) (F := F) ⟶
          (PresheafOfModules.restrictScalars (sheafificationRingMap J O₁)).obj
            ((SheafOfModules.forget
                (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₁))).obj
              ((restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G)) :=
      PresheafOfModules.sheafificationHomEquiv (sheafificationRingMap J O₁) Dleft
    let D₀ :
        restrictedSourcePresheaf (φ := φ) (F := F) ⟶
          restrictedTargetPresheaf (J := J) (φ := φ) G :=
      D₁ ≫ (principalPartsTargetComparisonIso (J := J) (φ := φ) G).inv
    let D₀' :
        principalPartsPresheafDifferentialOperators (J := J) (φ := φ) (F := F) k G :=
      ⟨D₀, by
        -- TODO: transport the order-`k` certificate on `D.1` back through the source and target
        -- comparison isomorphisms before applying the presheaf equivalence in the reverse
        -- direction.
        sorry⟩
    exact
      (principalPartsPresheafRestrictedHomEquiv (J := J) (φ := φ) (F := F) k G).symm D₀'
  left_inv f := by
    sorry
  right_inv D := by
    sorry

-- Proof sketch: on each object of the site, `principal_parts_module` represents order-`k`
-- differential operators by Lemma `10.133.3`. Sheafifying the resulting presheaf of principal
-- parts along `O₂ → O₂^#` and using the sheafification adjunction upgrades this sectionwise
-- universal property to the sheaf-level corepresentability statement from Lemma `18.34.3`.
/-- Lemma 18.34.5: after sheafifying `O₁`, `O₂`, and `F`, the sheaf associated to the presheaf
`U ↦ P^k_{O₂(U)/O₁(U)}(F(U))` is a module of principal parts of order `k` of `F^#` relative to
`O₁^# ⟶ O₂^#`. -/
@[stacks 09CV]
  noncomputable def principalParts_is_principal_parts_module_of_order (k : ℕ) :
    (differentialOperatorsFunctor
      ((presheafToSheaf J CommRingCat.{u}).map φ)
      ((PresheafOfModules.moduleSheafification J O₂).obj F) k).CorepresentableBy
      P^{k}_[φ](F) where
  homEquiv {G} :=
    (PresheafOfModules.sheafificationHomEquiv (sheafificationRingMap J O₂)).trans
      (principalPartsPresheafHomEquiv (J := J) (φ := φ) (F := F) k G)
  homEquiv_comp {G G'} α f := by
    sorry

end

end SheafOfModules.RingedSite
