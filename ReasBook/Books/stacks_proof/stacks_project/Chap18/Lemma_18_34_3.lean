import Mathlib
import StacksProject_2024.Chap18.Lemma_18_34_2
import StacksProject_2024.Chap10.Remark_10_133_7
import StacksProject_2024.Chap18.Definition_18_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open PresheafOfModules

noncomputable section

universe u

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 18.34.3:
- primary domain: principal-parts sheaves on a ringed site, viewed through the functor of
  differential operators of bounded order;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`,
  `TopCat.Sheaf.differentialOperatorsFunctor`,
  `Functor.IsCorepresentable`,
  `Functor.CorepresentableBy`,
  `TopCat.Sheaf.principalParts_is_principal_parts_module_of_order`;
- best owner abstraction: the covariant functor
  `differentialOperatorsFunctor φ F k` together with the canonical existence owner
  `(differentialOperatorsFunctor φ F k).IsCorepresentable`.

Primitive-vs-derived split:
- primitive data: the differential-operator predicate
  `IsDifferentialOperatorOfOrder φ D k`;
- derived API: postcomposition on order-`k` differential operators, the corepresenting
  differential operator attached to a chosen `CorepresentableBy` witness, the resulting
  factorization theorem, and fixed-object `CorepresentableBy` bridge data.

Source/core/bridge triage:
- `source-facing`: existence of a sheaf of principal parts of order `k` of `F` relative to `φ`;
- `core/canonical`: `differentialOperatorsFunctor φ F k` together with
  `(differentialOperatorsFunctor φ F k).IsCorepresentable`;
- `bridge/view`: `principalPartsDifferentialOperator hP` and the factorization theorem
  `principalParts_representsDifferentialOperators`.

This file should therefore expose the differential-operator functor and corepresentability as the
public owner abstraction, with `Functor.IsCorepresentable` as the main existence layer and
`Functor.CorepresentableBy` used only for fixed-object bridge statements.
-/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ : Sheaf J CommRingCat.{u}}

local notation "Mod(" O ")" => ringedSiteModuleCategory J O

/-- Helper for Lemma 18.34.3: the section algebra on `O₂(X)` induced by `φ`. -/
private abbrev siteSectionAlgebra (φ : O₁ ⟶ O₂) (X : Cᵒᵖ) :
    Algebra (O₁.obj.obj X) (O₂.obj.obj X) :=
  (φ.hom.app X).hom.toAlgebra

/-- Helper for Lemma 18.34.3: the restricted `O₁(X)`-module structure on `M(X)`. -/
private abbrev siteSectionModule (φ : O₁ ⟶ O₂) (M : Mod(O₂)) (X : Cᵒᵖ) :
    Module (O₁.obj.obj X) (M.val.obj X) :=
  Module.compHom (M.val.obj X) (φ.hom.app X).hom

/-- Helper for Lemma 18.34.3: the sectionwise scalar tower `O₁(X) → O₂(X) → M(X)`. -/
private abbrev siteSectionIsScalarTower (φ : O₁ ⟶ O₂) (M : Mod(O₂)) (X : Cᵒᵖ) :
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
    letI : Module (O₁.obj.obj X) (M.val.obj X) := siteSectionModule φ M X
    IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (M.val.obj X) :=
  by
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
    letI : Module (O₁.obj.obj X) (M.val.obj X) := siteSectionModule φ M X
    exact IsScalarTower.of_compHom (O₁.obj.obj X) (O₂.obj.obj X) (M.val.obj X)

/-- Helper for Lemma 18.34.3: the commuting scalar actions needed for objectwise composition. -/
private abbrev siteSectionSmulCommClass (φ : O₁ ⟶ O₂) (M : Mod(O₂)) (X : Cᵒᵖ) :
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
    letI : Module (O₁.obj.obj X) (M.val.obj X) := siteSectionModule φ M X
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (M.val.obj X) :=
      siteSectionIsScalarTower φ M X
    SMulCommClass (O₂.obj.obj X) (O₁.obj.obj X) (M.val.obj X) :=
  by
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
    letI : Module (O₁.obj.obj X) (M.val.obj X) := siteSectionModule φ M X
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (M.val.obj X) :=
      siteSectionIsScalarTower φ M X
    infer_instance

private abbrev differentialOperatorsOfOrder
    (φ : O₁ ⟶ O₂)
    (F : Mod(O₂)) (k : ℕ)
    (G : Mod(O₂)) :=
  { D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G //
    IsDifferentialOperatorOfOrder φ D k }

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Restriction of scalars sends an `O₂`-linear morphism to an order-`0` differential operator. -/
theorem isDifferentialOperatorOfOrder_restrictionAlong_map
    (φ : O₁ ⟶ O₂)
    {F G : Mod(O₂)} (f : F ⟶ G) :
    IsDifferentialOperatorOfOrder φ ((restrictionAlong φ).map f) 0 := by
  change ∀ X : Cᵒᵖ, _
  intro X
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (φ.hom.app X).hom.toAlgebra
  letI : Module (O₁.obj.obj X) (F.val.obj X) :=
    Module.compHom (F.val.obj X) (φ.hom.app X).hom
  letI : Module (O₁.obj.obj X) (G.val.obj X) :=
    Module.compHom (G.val.obj X) (φ.hom.app X).hom
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    IsScalarTower.of_compHom (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X)
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (G.val.obj X) :=
    IsScalarTower.of_compHom (O₁.obj.obj X) (O₂.obj.obj X) (G.val.obj X)
  letI : SMulCommClass ((ringSheaf J O₂).obj.obj X) (O₁.obj.obj X) (F.val.obj X) := by
    change SMulCommClass (O₂.obj.obj X) (O₁.obj.obj X) (F.val.obj X)
    infer_instance
  letI : SMulCommClass ((ringSheaf J O₂).obj.obj X) (O₁.obj.obj X) (G.val.obj X) := by
    change SMulCommClass (O₂.obj.obj X) (O₁.obj.obj X) (G.val.obj X)
    infer_instance
  let Dₓ : F.val.obj X →ₗ[O₁.obj.obj X] G.val.obj X := (((restrictionAlong φ).map f).val.app X).hom
  change Dₓ.IsDifferentialOperatorOfOrder ((ringSheaf J O₂).obj.obj X) 0
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro g m
  simpa using (f.val.app X).hom.map_smul g m

/-- Helper for Lemma 18.34.3: postcomposition with an `O₂`-linear morphism preserves
order-`k` differential operators. -/
private theorem differentialOperatorsFunctorPostcompose_mem
    (φ : O₁ ⟶ O₂)
    {F G G' : Mod(O₂)} {k : ℕ}
    (α : G ⟶ G')
    {D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G}
    (hD : IsDifferentialOperatorOfOrder φ D k) :
    IsDifferentialOperatorOfOrder φ (D ≫ (restrictionAlong φ).map α) k := by
  -- Proof comment: evaluate on each object of the site and use the objectwise composition theorem
  -- for differential operators, with the restriction of `α` contributing order `0`.
  intro X
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
  letI : Module (O₁.obj.obj X) (G.val.obj X) := siteSectionModule φ G X
  letI : Module (O₁.obj.obj X) (G'.val.obj X) := siteSectionModule φ G' X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    siteSectionIsScalarTower φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (G.val.obj X) :=
    siteSectionIsScalarTower φ G X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (G'.val.obj X) :=
    siteSectionIsScalarTower φ G' X
  letI : SMulCommClass (O₂.obj.obj X) (O₁.obj.obj X) (F.val.obj X) :=
    siteSectionSmulCommClass φ F X
  letI : SMulCommClass (O₂.obj.obj X) (O₁.obj.obj X) (G.val.obj X) :=
    siteSectionSmulCommClass φ G X
  letI : SMulCommClass (O₂.obj.obj X) (O₁.obj.obj X) (G'.val.obj X) :=
    siteSectionSmulCommClass φ G' X
  simpa [Nat.add_zero] using LinearMap.isDifferentialOperatorOfOrder_comp
    (isDifferentialOperatorOfOrder_app φ D hD X)
    (isDifferentialOperatorOfOrder_app φ ((restrictionAlong φ).map α)
      (isDifferentialOperatorOfOrder_restrictionAlong_map (φ := φ) α) X)

-- TODO: package the proved membership theorem above into the actual functorial map once Lean
-- accepts the direct reference from the structure field without the current elaboration glitch.
/-- Helper for Lemma 18.34.3: the map part of the differential-operator functor. -/
private abbrev differentialOperatorsFunctorMap
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ)
    {G G' : Mod(O₂)} (α : G ⟶ G') :
    differentialOperatorsOfOrder φ F k G → differentialOperatorsOfOrder φ F k G' :=
  fun D ↦
    ⟨D.1 ≫ (restrictionAlong φ).map α,
      differentialOperatorsFunctorPostcompose_mem (φ := φ) α D.2⟩

/-- The covariant functor of order-`k` differential operators out of `F`. -/
def differentialOperatorsFunctor
    (φ : O₁ ⟶ O₂)
    (F : Mod(O₂)) (k : ℕ) :
    Mod(O₂) ⥤ Type _ where
  obj G := differentialOperatorsOfOrder φ F k G
  map α := differentialOperatorsFunctorMap φ F k α
  map_id G := by
    funext D
    cases D
    rfl
  map_comp α β := by
    funext D
    cases D
    rfl

/-- The universal order-`k` differential operator attached to a chosen corepresenting sheaf. -/
def principalPartsDifferentialOperator
    {φ : O₁ ⟶ O₂} {F : Mod(O₂)} {k : ℕ}
    {P : Mod(O₂)}
    (hP : (differentialOperatorsFunctor φ F k).CorepresentableBy P) :
    (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj P :=
  (hP.homEquiv (𝟙 P)).1

/-- The corepresenting differential operator has order `k`. -/
theorem principalPartsDifferentialOperator_isDifferentialOperatorOfOrder
    {φ : O₁ ⟶ O₂} {F : Mod(O₂)} {k : ℕ}
    {P : Mod(O₂)}
    (hP : (differentialOperatorsFunctor φ F k).CorepresentableBy P) :
    IsDifferentialOperatorOfOrder φ (principalPartsDifferentialOperator hP) k :=
  (hP.homEquiv (𝟙 P)).2

/-- A corepresenting principal-parts sheaf represents order-`k` differential operators out of
`F` by `O₂`-linear morphisms out of that sheaf. -/
theorem principalParts_representsDifferentialOperators
    {φ : O₁ ⟶ O₂} {F : Mod(O₂)} {k : ℕ}
    {P : Mod(O₂)}
    (hP : (differentialOperatorsFunctor φ F k).CorepresentableBy P)
    (G : Mod(O₂))
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    (hD : IsDifferentialOperatorOfOrder φ D k) :
    ∃! α : P ⟶ G,
      principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map α = D := by
  let D' : (differentialOperatorsFunctor φ F k).obj G := ⟨D, hD⟩
  refine ⟨hP.homEquiv.symm D', ?_, ?_⟩
  · have hhomEquiv :
      (hP.homEquiv (hP.homEquiv.symm D')).1 =
        principalPartsDifferentialOperator hP ≫
          (restrictionAlong φ).map (hP.homEquiv.symm D') := by
      simpa [principalPartsDifferentialOperator] using
        congrArg Subtype.val
          (Functor.CorepresentableBy.homEquiv_eq hP (hP.homEquiv.symm D'))
    have h := congrArg Subtype.val (hP.homEquiv.apply_symm_apply D')
    rw [hhomEquiv] at h
    simpa [D'] using h
  · intro α hα
    apply hP.homEquiv.injective
    apply Subtype.ext
    calc
      (hP.homEquiv α).1 =
          principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map α := by
        simpa [principalPartsDifferentialOperator] using
          congrArg Subtype.val (Functor.CorepresentableBy.homEquiv_eq hP α)
      _ = D := hα
      _ = (hP.homEquiv (hP.homEquiv.symm D')).1 := by
        simpa [D'] using congrArg Subtype.val (hP.homEquiv.apply_symm_apply D').symm

/-- Helper for Lemma 18.34.3: the objectwise `k`-th principal-parts module over a site object. -/
private abbrev objectwisePrincipalPartsModule
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (X : Cᵒᵖ) :
    ModuleCat (O₂.obj.obj X) :=
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (φ.hom.app X).hom.toAlgebra
  letI : Module (O₁.obj.obj X) (F.val.obj X) :=
    Module.compHom (F.val.obj X) (φ.hom.app X).hom
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    IsScalarTower.of_compHom (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X)
  ModuleCat.of (O₂.obj.obj X)
    (principal_parts_module (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) k)

/-- Helper for Lemma 18.34.3: the universal class map `F(X) → P^k_{O₂(X)/O₁(X)}(F(X))`. -/
private abbrev objectwiseUniversalDifferential
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (X : Cᵒᵖ) :
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
    letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
      siteSectionIsScalarTower φ F X
    F.val.obj X →ₗ[O₁.obj.obj X] ↑(objectwisePrincipalPartsModule φ F k X) :=
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    siteSectionIsScalarTower φ F X
  principal_parts_universal_differential
    (R := O₁.obj.obj X) (S := O₂.obj.obj X) (M := F.val.obj X) k

/-- Helper for Lemma 18.34.3: the objectwise restriction map on principal-parts modules induced by
the restriction map on sections of `F`. -/
private abbrev objectwisePrincipalPartsMap
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    objectwisePrincipalPartsModule φ F k X ⟶
      (ModuleCat.restrictScalars (((ringSheaf J O₂).obj.map f).hom)).obj
        (objectwisePrincipalPartsModule φ F k Y) :=
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (φ.hom.app X).hom.toAlgebra
  letI : Module (O₁.obj.obj X) (F.val.obj X) :=
    Module.compHom (F.val.obj X) (φ.hom.app X).hom
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    IsScalarTower.of_compHom (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X)
  letI : Algebra (O₁.obj.obj Y) (O₂.obj.obj Y) := (φ.hom.app Y).hom.toAlgebra
  letI : Module (O₁.obj.obj Y) (F.val.obj Y) :=
    Module.compHom (F.val.obj Y) (φ.hom.app Y).hom
  letI : IsScalarTower (O₁.obj.obj Y) (O₂.obj.obj Y) (F.val.obj Y) :=
    IsScalarTower.of_compHom (O₁.obj.obj Y) (O₂.obj.obj Y) (F.val.obj Y)
  letI : Algebra (O₁.obj.obj X) (O₁.obj.obj Y) := ((O₁.obj.map f).hom).toAlgebra
  letI : Algebra (O₂.obj.obj X) (O₂.obj.obj Y) := ((O₂.obj.map f).hom).toAlgebra
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj Y) :=
    (((φ.hom.app Y).hom).comp ((O₁.obj.map f).hom)).toAlgebra
  letI : Module (O₁.obj.obj X) (F.val.obj Y) :=
    Module.compHom (F.val.obj Y) (((φ.hom.app Y).hom).comp ((O₁.obj.map f).hom))
  letI : Module (O₂.obj.obj X) (F.val.obj Y) :=
    Module.compHom (F.val.obj Y) ((O₂.obj.map f).hom)
  letI : IsScalarTower (O₁.obj.obj X) (O₁.obj.obj Y) (O₂.obj.obj Y) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (O₂.obj.obj Y) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (φ.hom.naturality f))
  letI : IsScalarTower (O₂.obj.obj X) (O₂.obj.obj Y) (F.val.obj Y) :=
    IsScalarTower.of_compHom (O₂.obj.obj X) (O₂.obj.obj Y) (F.val.obj Y)
  letI : IsScalarTower (O₁.obj.obj X) (O₁.obj.obj Y) (F.val.obj Y) :=
    IsScalarTower.of_compHom (O₁.obj.obj X) (O₁.obj.obj Y) (F.val.obj Y)
  let fXY : F.val.obj X →ₗ[O₂.obj.obj X] F.val.obj Y := (F.val.map f).hom
  ModuleCat.ofHom (principalPartsBaseChangeMap
    (A := O₁.obj.obj X) (B := O₂.obj.obj X)
    (A' := O₁.obj.obj Y) (B' := O₂.obj.obj Y)
    (k := k) fXY)

/-- Helper for Lemma 18.34.3: the site-level restriction map is literally the Chapter 10
principal-parts base-change map after installing the sectionwise scalar towers. -/
private theorem objectwisePrincipalPartsMap_typed
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    objectwisePrincipalPartsMap (J := J) φ F k f =
      letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (φ.hom.app X).hom.toAlgebra
      letI : Module (O₁.obj.obj X) (F.val.obj X) :=
        Module.compHom (F.val.obj X) (φ.hom.app X).hom
      letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
        IsScalarTower.of_compHom (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X)
      letI : Algebra (O₁.obj.obj Y) (O₂.obj.obj Y) := (φ.hom.app Y).hom.toAlgebra
      letI : Module (O₁.obj.obj Y) (F.val.obj Y) :=
        Module.compHom (F.val.obj Y) (φ.hom.app Y).hom
      letI : IsScalarTower (O₁.obj.obj Y) (O₂.obj.obj Y) (F.val.obj Y) :=
        IsScalarTower.of_compHom (O₁.obj.obj Y) (O₂.obj.obj Y) (F.val.obj Y)
      letI : Algebra (O₁.obj.obj X) (O₁.obj.obj Y) := ((O₁.obj.map f).hom).toAlgebra
      letI : Algebra (O₂.obj.obj X) (O₂.obj.obj Y) := ((O₂.obj.map f).hom).toAlgebra
      letI : Algebra (O₁.obj.obj X) (O₂.obj.obj Y) :=
        (((φ.hom.app Y).hom).comp ((O₁.obj.map f).hom)).toAlgebra
      letI : Module (O₁.obj.obj X) (F.val.obj Y) :=
        Module.compHom (F.val.obj Y) (((φ.hom.app Y).hom).comp ((O₁.obj.map f).hom))
      letI : Module (O₂.obj.obj X) (F.val.obj Y) :=
        Module.compHom (F.val.obj Y) ((O₂.obj.map f).hom)
      letI : IsScalarTower (O₁.obj.obj X) (O₁.obj.obj Y) (O₂.obj.obj Y) :=
        IsScalarTower.of_algebraMap_eq' rfl
      letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (O₂.obj.obj Y) :=
        IsScalarTower.of_algebraMap_eq'
          (congrArg CommRingCat.Hom.hom (φ.hom.naturality f))
      letI : IsScalarTower (O₂.obj.obj X) (O₂.obj.obj Y) (F.val.obj Y) :=
        IsScalarTower.of_compHom (O₂.obj.obj X) (O₂.obj.obj Y) (F.val.obj Y)
      letI : IsScalarTower (O₁.obj.obj X) (O₁.obj.obj Y) (F.val.obj Y) :=
        IsScalarTower.of_compHom (O₁.obj.obj X) (O₁.obj.obj Y) (F.val.obj Y)
      let fXY : F.val.obj X →ₗ[O₂.obj.obj X] F.val.obj Y := (F.val.map f).hom
      ModuleCat.ofHom (principalPartsBaseChangeMap
        (A := O₁.obj.obj X) (B := O₂.obj.obj X)
        (A' := O₁.obj.obj Y) (B' := O₂.obj.obj Y)
        (k := k) fXY) := by
  -- Proof comment: this theorem freezes the intended source-faithful normalization so later
  -- proofs can reason about the concrete Chapter 10 base-change map instead of unfolding the
  -- entire site-level definition again.
  rfl

/-- Helper for Lemma 18.34.3: linear maps out of principal parts are determined by the universal
generators `[m]`. -/
private theorem principal_parts_linearMap_ext_on_universal_differential
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
  -- Proof comment: every quotient class is a linear combination of the universal generators `[m]`.
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

/-- Helper for Lemma 18.34.3: the site restriction map sends the universal generator `[m]` to the
universal generator of the restricted section. -/
private theorem objectwisePrincipalPartsMap_on_universal_differential
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : F.val.obj X) :
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
    letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
      siteSectionIsScalarTower φ F X
    letI : Algebra (O₁.obj.obj Y) (O₂.obj.obj Y) := siteSectionAlgebra φ Y
    letI : Module (O₁.obj.obj Y) (F.val.obj Y) := siteSectionModule φ F Y
    letI : IsScalarTower (O₁.obj.obj Y) (O₂.obj.obj Y) (F.val.obj Y) :=
      siteSectionIsScalarTower φ F Y
    (ModuleCat.Hom.hom (objectwisePrincipalPartsMap (J := J) φ F k f))
        (principal_parts_universal_differential
          (R := O₁.obj.obj X) (S := O₂.obj.obj X) (M := F.val.obj X) k m) =
      principal_parts_universal_differential
        (R := O₁.obj.obj Y) (S := O₂.obj.obj Y) (M := F.val.obj Y) k
          ((F.val.map f).hom m) := by
  -- Proof comment: after freezing the site restriction map as the Chapter 10 base-change map,
  -- the image of `[m]` is the standard quotient-level `mapQ` computation.
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    siteSectionIsScalarTower φ F X
  letI : Algebra (O₁.obj.obj Y) (O₂.obj.obj Y) := siteSectionAlgebra φ Y
  letI : Module (O₁.obj.obj Y) (F.val.obj Y) := siteSectionModule φ F Y
  letI : IsScalarTower (O₁.obj.obj Y) (O₂.obj.obj Y) (F.val.obj Y) :=
    siteSectionIsScalarTower φ F Y
  letI : Algebra (O₁.obj.obj X) (O₁.obj.obj Y) := ((O₁.obj.map f).hom).toAlgebra
  letI : Algebra (O₂.obj.obj X) (O₂.obj.obj Y) := ((O₂.obj.map f).hom).toAlgebra
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj Y) :=
    (((φ.hom.app Y).hom).comp ((O₁.obj.map f).hom)).toAlgebra
  letI : Module (O₁.obj.obj X) (F.val.obj Y) :=
    Module.compHom (F.val.obj Y) (((φ.hom.app Y).hom).comp ((O₁.obj.map f).hom))
  letI : Module (O₂.obj.obj X) (F.val.obj Y) :=
    Module.compHom (F.val.obj Y) ((O₂.obj.map f).hom)
  letI : IsScalarTower (O₁.obj.obj X) (O₁.obj.obj Y) (O₂.obj.obj Y) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (O₂.obj.obj Y) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (φ.hom.naturality f))
  letI : IsScalarTower (O₂.obj.obj X) (O₂.obj.obj Y) (F.val.obj Y) :=
    IsScalarTower.of_compHom (O₂.obj.obj X) (O₂.obj.obj Y) (F.val.obj Y)
  letI : IsScalarTower (O₁.obj.obj X) (O₁.obj.obj Y) (F.val.obj Y) :=
    IsScalarTower.of_compHom (O₁.obj.obj X) (O₁.obj.obj Y) (F.val.obj Y)
  rw [objectwisePrincipalPartsMap_typed]
  simpa only [principal_parts_universal_differential] using
    (show
      (principalPartsBaseChangeMap
          (A := O₁.obj.obj X) (B := O₂.obj.obj X)
          (A' := O₁.obj.obj Y) (B' := O₂.obj.obj Y)
          (k := k) ((F.val.map f).hom))
          (principal_parts_universal_differential
            (R := O₁.obj.obj X) (S := O₂.obj.obj X) (M := F.val.obj X) k m) =
        principal_parts_universal_differential
          (R := O₁.obj.obj Y) (S := O₂.obj.obj Y) (M := F.val.obj Y) k
            ((F.val.map f).hom m) by
      simp only [principal_parts_universal_differential, Submodule.mapQ_apply])

-- TODO: prove the identity law by identifying the base-change map for `𝟙 X` with the identity
-- linear map on the quotient presentation of principal parts.
/-- Helper for Lemma 18.34.3: the objectwise principal-parts restriction map satisfies the identity
law of a presheaf of modules. -/
private theorem objectwisePrincipalPartsMap_id
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (X : Cᵒᵖ) :
    objectwisePrincipalPartsMap (J := J) φ F k (𝟙 X) =
      (ModuleCat.restrictScalarsId' (((ringSheaf J O₂).obj.map (𝟙 X)).hom)
        (congrArg RingCat.Hom.hom ((ringSheaf J O₂).obj.map_id X))).inv.app
        (objectwisePrincipalPartsModule φ F k X) := by
  -- Proof comment: maps out of principal parts are determined by the generators `[m]`, so the
  -- identity law reduces to checking the image of a single universal class.
  apply ModuleCat.hom_ext
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    siteSectionIsScalarTower φ F X
  apply principal_parts_linearMap_ext_on_universal_differential
    (A := O₁.obj.obj X) (B := O₂.obj.obj X) (M := F.val.obj X) k
  intro m
  have hmap :
      (ModuleCat.Hom.hom (F.val.map (𝟙 X))) m = m := by
    have hmap' :
        (ModuleCat.Hom.hom (F.val.map (𝟙 X))) m =
          (ModuleCat.Hom.hom
            ((ModuleCat.restrictScalarsId' (((ringSheaf J O₂).obj.map (𝟙 X)).hom)
              (congrArg RingCat.Hom.hom ((ringSheaf J O₂).obj.map_id X))).inv.app
              (F.val.obj X))) m := by
      exact congrArg (fun h ↦ (ModuleCat.Hom.hom h) m) (F.val.map_id X)
    calc
      (ModuleCat.Hom.hom (F.val.map (𝟙 X))) m =
          (ModuleCat.Hom.hom
            ((ModuleCat.restrictScalarsId' (((ringSheaf J O₂).obj.map (𝟙 X)).hom)
              (congrArg RingCat.Hom.hom ((ringSheaf J O₂).obj.map_id X))).inv.app
              (F.val.obj X))) m := hmap'
      _ = m := by
        exact ModuleCat.restrictScalarsId'App_inv_apply
          (((ringSheaf J O₂).obj.map (𝟙 X)).hom)
          (congrArg RingCat.Hom.hom ((ringSheaf J O₂).obj.map_id X))
          (F.val.obj X)
          m
  rw [objectwisePrincipalPartsMap_on_universal_differential]
  rw [hmap]
  symm
  exact ModuleCat.restrictScalarsId'App_inv_apply
    (((ringSheaf J O₂).obj.map (𝟙 X)).hom)
    (congrArg RingCat.Hom.hom ((ringSheaf J O₂).obj.map_id X))
    (objectwisePrincipalPartsModule φ F k X)
    (principal_parts_universal_differential
      (R := O₁.obj.obj X) (S := O₂.obj.obj X) (M := F.val.obj X) k m)

-- TODO: prove the composition law by transporting `principalPartsBaseChangeMap_comp` through
-- the module-category restriction-of-scalars coherence isomorphism.
/-- Helper for Lemma 18.34.3: the objectwise principal-parts restriction maps satisfy the
composition law of a presheaf of modules. -/
private theorem objectwisePrincipalPartsMap_comp
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ)
    {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    objectwisePrincipalPartsMap (J := J) φ F k (f ≫ g) =
      objectwisePrincipalPartsMap (J := J) φ F k f ≫
        (ModuleCat.restrictScalars (((ringSheaf J O₂).obj.map f).hom)).map
          (objectwisePrincipalPartsMap (J := J) φ F k g) ≫
        (ModuleCat.restrictScalarsComp' (((ringSheaf J O₂).obj.map f).hom)
          (((ringSheaf J O₂).obj.map g).hom)
          (((ringSheaf J O₂).obj.map (f ≫ g)).hom)
          (congrArg RingCat.Hom.hom ((ringSheaf J O₂).obj.map_comp f g))).inv.app
          (objectwisePrincipalPartsModule φ F k Z) := by
  -- Proof comment: as in the identity case, it is enough to compare both composites on the
  -- generators `[m]`, where the presheaf composition law for `F` gives the needed formula.
  apply ModuleCat.hom_ext
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    siteSectionIsScalarTower φ F X
  apply principal_parts_linearMap_ext_on_universal_differential
    (A := O₁.obj.obj X) (B := O₂.obj.obj X) (M := F.val.obj X) k
  intro m
  have hmap :
      (ModuleCat.Hom.hom (F.val.map (f ≫ g))) m =
        (ModuleCat.Hom.hom (F.val.map g)) ((ModuleCat.Hom.hom (F.val.map f)) m) := by
    simpa using congrArg (fun h ↦ (ModuleCat.Hom.hom h) m) (F.val.map_comp f g)
  have hfg :
      (ModuleCat.Hom.hom (objectwisePrincipalPartsMap (J := J) φ F k (f ≫ g)))
          (principal_parts_universal_differential
            (R := O₁.obj.obj X) (S := O₂.obj.obj X) (M := F.val.obj X) k m) =
        principal_parts_universal_differential
          (R := O₁.obj.obj Z) (S := O₂.obj.obj Z) (M := F.val.obj Z) k
          ((F.val.map (f ≫ g)).hom m) := by
    exact objectwisePrincipalPartsMap_on_universal_differential
      (J := J) φ F k (f ≫ g) m
  rw [hfg]
  simp only [Category.assoc, objectwisePrincipalPartsMap_on_universal_differential,
    ModuleCat.restrictScalarsComp'App_inv_apply]
  rw [hmap]

/-- Helper for Lemma 18.34.3: the presheaf of objectwise principal-parts modules. -/
private def sheafPrincipalPartsPresheaf
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) :
    PresheafOfModules (ringSheaf J O₂).obj where
  obj X := objectwisePrincipalPartsModule φ F k X
  map f := objectwisePrincipalPartsMap (J := J) φ F k f
  map_id X := objectwisePrincipalPartsMap_id (J := J) φ F k X
  map_comp f g := objectwisePrincipalPartsMap_comp (J := J) φ F k f g

/-- Helper for Lemma 18.34.3: the underlying `O₂`-module presheaf of a target sheaf, viewed via
restriction of scalars along the identity of `ringSheaf J O₂`. -/
private abbrev principalPartsTargetPresheaf
    (G : Mod(O₂)) :
    PresheafOfModules (ringSheaf J O₂).obj :=
  (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O₂).obj)).obj G.val

/-- Helper for Lemma 18.34.3: the sheafified principal-parts presheaf which is intended to
corepresent order-`k` differential operators out of `F`. -/
private abbrev sheafPrincipalParts
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) :
    Mod(O₂) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf J O₂).obj)).obj
    (sheafPrincipalPartsPresheaf (J := J) φ F k)

/-- Helper for Lemma 18.34.3: the sectionwise Chapter 10 universal property for the objectwise
principal-parts module, specialized to the actual presheaf target used later in the proof. -/
private noncomputable abbrev objectwisePrincipalPartsLinearEquiv
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ)
    (G : Mod(O₂)) (X : Cᵒᵖ) :
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
    letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
      siteSectionIsScalarTower φ F X
    letI : Module (O₁.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.hom.app X).hom
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X)
      ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      IsScalarTower.of_compHom
        (O₁.obj.obj X) (O₂.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
    (objectwisePrincipalPartsModule φ F k X ⟶
      (principalPartsTargetPresheaf (J := J) G).obj X) ≃
      differential_operators_order_le
        (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) k
          ((principalPartsTargetPresheaf (J := J) G).obj X) :=
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    siteSectionIsScalarTower φ F X
  letI : Module (O₁.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.hom.app X).hom
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X)
      ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    IsScalarTower.of_compHom
      (O₁.obj.obj X) (O₂.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
  -- Proof comment: the objectwise representing equivalence is the Chapter 10 equivalence,
  -- preceded by the standard `ModuleCat.homEquiv` identification of morphisms with linear maps.
  (ModuleCat.homEquiv :
      (objectwisePrincipalPartsModule φ F k X ⟶
        (principalPartsTargetPresheaf (J := J) G).obj X) ≃
          (principal_parts_module
            (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) k →ₗ[O₂.obj.obj X]
              ((principalPartsTargetPresheaf (J := J) G).obj X))).trans
    ((principal_parts_linear_map_equiv_differential_operators
      (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) k
      ((principalPartsTargetPresheaf (J := J) G).obj X)).toEquiv)

/-- Helper for Lemma 18.34.3: under the objectwise representing equivalence, the resulting
differential operator evaluates a section `m` by applying the original principal-parts map to the
universal generator `[m]`. -/
private theorem objectwisePrincipalPartsLinearEquiv_apply_universal_differential
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ)
    (G : Mod(O₂)) (X : Cᵒᵖ)
    (β : objectwisePrincipalPartsModule φ F k X ⟶
      (principalPartsTargetPresheaf (J := J) G).obj X)
    (m : F.val.obj X) :
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
    letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
      siteSectionIsScalarTower φ F X
    letI : Module (O₁.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.hom.app X).hom
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X)
      ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      IsScalarTower.of_compHom
        (O₁.obj.obj X) (O₂.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
    ((objectwisePrincipalPartsLinearEquiv (J := J) φ F k G X β).1) m =
      (ModuleCat.homEquiv β)
        (principal_parts_universal_differential
          (R := O₁.obj.obj X) (S := O₂.obj.obj X) (M := F.val.obj X) k m) := by
  -- Proof comment: this is the defining computation rule of the Chapter 10 representing
  -- equivalence on the universal generator `[m]`.
  rfl

/-- Helper for Lemma 18.34.3: the sectionwise map extracted from a presheaf morphism via the
objectwise principal-parts universal property. -/
private noncomputable abbrev presentationToDifferentialOperatorApp
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂))
    (β : sheafPrincipalPartsPresheaf (J := J) φ F k ⟶ principalPartsTargetPresheaf (J := J) G)
    (X : Cᵒᵖ) :
    (((restrictionAlong φ).obj F).val.obj X) ⟶ (((restrictionAlong φ).obj G).val.obj X) :=
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
  letI : Module (O₁.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.hom.app X).hom
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    siteSectionIsScalarTower φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X)
      ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    IsScalarTower.of_compHom
      (O₁.obj.obj X) (O₂.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
  let βX :
      objectwisePrincipalPartsModule φ F k X ⟶
        (principalPartsTargetPresheaf (J := J) G).obj X := β.app X
  show (((restrictionAlong φ).obj F).val.obj X) ⟶ (((restrictionAlong φ).obj G).val.obj X) from
    ModuleCat.ofHom ((objectwisePrincipalPartsLinearEquiv (J := J) φ F k G X βX).1)

/-- Helper for Lemma 18.34.3: the forward sectionwise map evaluates a section `m` by applying the
presheaf morphism to the universal generator `[m]`. -/
private theorem presentationToDifferentialOperatorApp_apply
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂))
    (β : sheafPrincipalPartsPresheaf (J := J) φ F k ⟶ principalPartsTargetPresheaf (J := J) G)
    (X : Cᵒᵖ) (m : F.val.obj X) :
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
    letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
    letI : Module (O₁.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.hom.app X).hom
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
      siteSectionIsScalarTower φ F X
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X)
      ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      IsScalarTower.of_compHom
        (O₁.obj.obj X) (O₂.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
    (ModuleCat.Hom.hom (presentationToDifferentialOperatorApp (J := J) φ F k G β X)) m =
      (ModuleCat.Hom.hom (β.app X))
        (principal_parts_universal_differential
          (R := O₁.obj.obj X) (S := O₂.obj.obj X) (M := F.val.obj X) k m) := by
  -- Proof comment: the forward section map is defined by the specialized objectwise equivalence,
  -- so evaluating it on `m` is exactly the universal-generator formula.
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
  letI : Module (O₁.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.hom.app X).hom
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    siteSectionIsScalarTower φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X)
      ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    IsScalarTower.of_compHom
      (O₁.obj.obj X) (O₂.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
  let βX :
      objectwisePrincipalPartsModule φ F k X ⟶
        (principalPartsTargetPresheaf (J := J) G).obj X := β.app X
  simpa [presentationToDifferentialOperatorApp] using
    (objectwisePrincipalPartsLinearEquiv_apply_universal_differential
      (J := J) φ F k G X βX m)

/-- Helper for Lemma 18.34.3: the forward sectionwise maps satisfy the restricted-source
naturality condition. -/
private theorem presentationToDifferentialOperator_naturality
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂))
    (β : sheafPrincipalPartsPresheaf (J := J) φ F k ⟶ principalPartsTargetPresheaf (J := J) G)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (((restrictionAlong φ).obj F).val.map f) ≫
        (ModuleCat.restrictScalars (((ringSheaf J O₁).obj.map f).hom)).map
          (presentationToDifferentialOperatorApp (J := J) φ F k G β Y) =
      presentationToDifferentialOperatorApp (J := J) φ F k G β X ≫
        (((restrictionAlong φ).obj G).val.map f) := by
  -- Proof comment: after rewriting both sides on a section `m`, the claim is exactly the
  -- naturality square for `β`, with the source rewritten through principal parts.
  apply ModuleCat.hom_ext
  ext m
  rw [presentationToDifferentialOperatorApp_apply, presentationToDifferentialOperatorApp_apply]
  rw [← PresheafOfModules.naturality_apply β f]
  rw [objectwisePrincipalPartsMap_on_universal_differential]

/-- Helper for Lemma 18.34.3: the forward construction from a presheaf morphism produces the
corresponding sheaf morphism after restriction of scalars. -/
private noncomputable abbrev presentationToDifferentialOperator
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂))
    (β : sheafPrincipalPartsPresheaf (J := J) φ F k ⟶ principalPartsTargetPresheaf (J := J) G) :
    (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G :=
  ⟨{ app := presentationToDifferentialOperatorApp (J := J) φ F k G β
      , naturality := presentationToDifferentialOperator_naturality (J := J) φ F k G β }⟩

/-- Helper for Lemma 18.34.3: the forward presheaf-level construction yields an order-`k`
differential operator objectwise. -/
private theorem presentationToDifferentialOperator_mem
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂))
    (β : sheafPrincipalPartsPresheaf (J := J) φ F k ⟶ principalPartsTargetPresheaf (J := J) G) :
    IsDifferentialOperatorOfOrder φ
      (presentationToDifferentialOperator (J := J) φ F k G β) k := by
  intro X
  -- Proof comment: objectwise, the forward map was defined by the representing equivalence, so
  -- its order-`k` bound is the `.2` component of that equivalence.
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
  letI : Module (O₁.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.hom.app X).hom
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    siteSectionIsScalarTower φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X)
      ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    IsScalarTower.of_compHom
      (O₁.obj.obj X) (O₂.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
  let βX :
      objectwisePrincipalPartsModule φ F k X ⟶
        (principalPartsTargetPresheaf (J := J) G).obj X := β.app X
  simpa [presentationToDifferentialOperator, presentationToDifferentialOperatorApp] using
    (objectwisePrincipalPartsLinearEquiv (J := J) φ F k G X βX).2

/-- Helper for Lemma 18.34.3: the sectionwise differential operator extracted from a sheaf-level
order-`k` differential operator. -/
private theorem differentialOperatorSectionwise_mem
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂))
    (D : (differentialOperatorsFunctor φ F k).obj G) (X : Cᵒᵖ) :
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
    letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
    letI : Module (O₁.obj.obj X) (G.val.obj X) := siteSectionModule φ G X
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
      siteSectionIsScalarTower φ F X
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (G.val.obj X) :=
      siteSectionIsScalarTower φ G X
    (ModuleCat.Hom.hom (D.1.val.app X)) ∈
      differential_operators_order_le_submodule
        (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) k (G.val.obj X) := by
  -- Proof comment: the site-level differential-operator predicate is defined objectwise.
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
  letI : Module (O₁.obj.obj X) (G.val.obj X) := siteSectionModule φ G X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    siteSectionIsScalarTower φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (G.val.obj X) :=
    siteSectionIsScalarTower φ G X
  simpa using D.2 X

/-- Helper for Lemma 18.34.3: the objectwise differential operator attached to a global order-`k`
sheaf differential operator. -/
private noncomputable abbrev differentialOperatorSectionwise
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂))
    (D : (differentialOperatorsFunctor φ F k).obj G) (X : Cᵒᵖ) :
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
    letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
    letI : Module (O₁.obj.obj X) (G.val.obj X) := siteSectionModule φ G X
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
      siteSectionIsScalarTower φ F X
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (G.val.obj X) :=
      siteSectionIsScalarTower φ G X
    differential_operators_order_le
      (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) k (G.val.obj X) :=
  ⟨(ModuleCat.Hom.hom (D.1.val.app X)),
    differentialOperatorSectionwise_mem (J := J) φ F k G D X⟩

/-- Helper for Lemma 18.34.3: the sectionwise presheaf morphism reconstructed from a sheaf-level
order-`k` differential operator. -/
private noncomputable abbrev differentialOperatorToPresentationApp
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂))
    (D : (differentialOperatorsFunctor φ F k).obj G) (X : Cᵒᵖ) :
    objectwisePrincipalPartsModule φ F k X ⟶ (principalPartsTargetPresheaf (J := J) G).obj X :=
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    siteSectionIsScalarTower φ F X
  letI : Module (O₁.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.hom.app X).hom
  letI :
      IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X)
        ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    IsScalarTower.of_compHom
      (O₁.obj.obj X) (O₂.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
  (objectwisePrincipalPartsLinearEquiv (J := J) φ F k G X).symm
    (differentialOperatorSectionwise (J := J) φ F k G D X)

/-- Helper for Lemma 18.34.3: the inverse sectionwise reconstruction evaluates the universal
generator `[m]` by the original differential operator. -/
private theorem differentialOperatorToPresentationApp_apply_universal_differential
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂))
    (D : (differentialOperatorsFunctor φ F k).obj G)
    (X : Cᵒᵖ) (m : F.val.obj X) :
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
    letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
    letI : Module (O₁.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.hom.app X).hom
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
      siteSectionIsScalarTower φ F X
    letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X)
      ((principalPartsTargetPresheaf (J := J) G).obj X) :=
      IsScalarTower.of_compHom
        (O₁.obj.obj X) (O₂.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
    (ModuleCat.Hom.hom (differentialOperatorToPresentationApp (J := J) φ F k G D X))
        (principal_parts_universal_differential
          (R := O₁.obj.obj X) (S := O₂.obj.obj X) (M := F.val.obj X) k m) =
      (ModuleCat.Hom.hom (D.1.val.app X)) m := by
  -- Proof comment: applying the representing equivalence to the reconstructed section map gives
  -- back the stored objectwise differential operator, so evaluating on `[m]` recovers `D(m)`.
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
  letI : Module (O₁.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    Module.compHom ((principalPartsTargetPresheaf (J := J) G).obj X) (φ.hom.app X).hom
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    siteSectionIsScalarTower φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X)
      ((principalPartsTargetPresheaf (J := J) G).obj X) :=
    IsScalarTower.of_compHom
      (O₁.obj.obj X) (O₂.obj.obj X) ((principalPartsTargetPresheaf (J := J) G).obj X)
  let βX :
      objectwisePrincipalPartsModule φ F k X ⟶
        (principalPartsTargetPresheaf (J := J) G).obj X :=
    differentialOperatorToPresentationApp (J := J) φ F k G D X
  have h :=
    objectwisePrincipalPartsLinearEquiv_apply_universal_differential
      (J := J) φ F k G X βX m
  have hβ :
      objectwisePrincipalPartsLinearEquiv (J := J) φ F k G X βX =
        differentialOperatorSectionwise (J := J) φ F k G D X :=
    Equiv.apply_symm_apply
      (objectwisePrincipalPartsLinearEquiv (J := J) φ F k G X)
      (differentialOperatorSectionwise (J := J) φ F k G D X)
  have hβm :
      ((objectwisePrincipalPartsLinearEquiv (J := J) φ F k G X βX).1) m =
        (ModuleCat.Hom.hom (D.1.val.app X)) m := by
    simpa [differentialOperatorSectionwise] using congrArg (fun E ↦ E.1 m) hβ
  exact h.symm.trans hβm

/-- Helper for Lemma 18.34.3: the reconstructed sectionwise principal-parts maps satisfy the
presheaf naturality condition. -/
private theorem differentialOperatorToPresentation_naturality
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂))
    (D : (differentialOperatorsFunctor φ F k).obj G)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    objectwisePrincipalPartsMap (J := J) φ F k f ≫
        (ModuleCat.restrictScalars (((ringSheaf J O₂).obj.map f).hom)).map
          (differentialOperatorToPresentationApp (J := J) φ F k G D Y) =
      differentialOperatorToPresentationApp (J := J) φ F k G D X ≫
        (principalPartsTargetPresheaf (J := J) G).map f := by
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    siteSectionIsScalarTower φ F X
  apply ModuleCat.hom_ext
  -- Proof comment: both sides agree on generators because they become the two sides of the
  -- naturality square for the sheaf morphism `D.1.val`.
  apply principal_parts_linearMap_ext_on_universal_differential k
  intro m
  simp only [Category.assoc, objectwisePrincipalPartsMap_on_universal_differential,
    differentialOperatorToPresentationApp_apply_universal_differential]
  exact PresheafOfModules.naturality_apply D.1.val f m

/-- Helper for Lemma 18.34.3: the inverse construction packages a sheaf differential operator as a
presheaf morphism out of the principal-parts presentation. -/
private noncomputable abbrev differentialOperatorToPresentation
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂))
    (D : (differentialOperatorsFunctor φ F k).obj G) :
    sheafPrincipalPartsPresheaf (J := J) φ F k ⟶ principalPartsTargetPresheaf (J := J) G :=
  { app := differentialOperatorToPresentationApp (J := J) φ F k G D
    naturality := differentialOperatorToPresentation_naturality (J := J) φ F k G D }

/-- Helper for Lemma 18.34.3: converting a presheaf morphism forward and then back recovers the
original presheaf morphism. -/
private theorem sheafPrincipalPartsPresentationHomEquiv_left_inv
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂))
    (β : sheafPrincipalPartsPresheaf (J := J) φ F k ⟶ principalPartsTargetPresheaf (J := J) G) :
    differentialOperatorToPresentation (J := J) φ F k G
        ⟨presentationToDifferentialOperator (J := J) φ F k G β,
          presentationToDifferentialOperator_mem (J := J) φ F k G β⟩ = β := by
  apply PresheafOfModules.hom_ext
  intro X
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := siteSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := siteSectionModule φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    siteSectionIsScalarTower φ F X
  apply ModuleCat.hom_ext
  -- Proof comment: equality of principal-parts maps is checked on the universal generators `[m]`.
  apply principal_parts_linearMap_ext_on_universal_differential k
  intro m
  rw [differentialOperatorToPresentationApp_apply_universal_differential,
    presentationToDifferentialOperatorApp_apply]

/-- Helper for Lemma 18.34.3: converting a sheaf differential operator to the principal-parts
presentation and back recovers the original differential operator. -/
private theorem sheafPrincipalPartsPresentationHomEquiv_right_inv
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂))
    (D : (differentialOperatorsFunctor φ F k).obj G) :
    (⟨presentationToDifferentialOperator (J := J) φ F k G
        (differentialOperatorToPresentation (J := J) φ F k G D),
      presentationToDifferentialOperator_mem (J := J) φ F k G
        (differentialOperatorToPresentation (J := J) φ F k G D)⟩ :
      (differentialOperatorsFunctor φ F k).obj G) = D := by
  apply Subtype.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  ext m
  -- Proof comment: both reconstructed section maps evaluate `m` by the same universal-generator
  -- formula.
  rw [presentationToDifferentialOperatorApp_apply,
    differentialOperatorToPresentationApp_apply_universal_differential]

/-- Helper for Lemma 18.34.3: morphisms from the principal-parts presheaf to a target presheaf are
equivalent to order-`k` differential operators into the corresponding sheaf. -/
private noncomputable def sheafPrincipalPartsPresentationHomEquiv
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ)
    (G : Mod(O₂)) :
    (sheafPrincipalPartsPresheaf (J := J) φ F k ⟶ principalPartsTargetPresheaf (J := J) G) ≃
      (differentialOperatorsFunctor φ F k).obj G :=
  { toFun := fun β ↦
      ⟨presentationToDifferentialOperator (J := J) φ F k G β,
        presentationToDifferentialOperator_mem (J := J) φ F k G β⟩
    invFun := differentialOperatorToPresentation (J := J) φ F k G
    left_inv := sheafPrincipalPartsPresentationHomEquiv_left_inv (J := J) φ F k G
    right_inv := sheafPrincipalPartsPresentationHomEquiv_right_inv (J := J) φ F k G }

/-- Helper for Lemma 18.34.3: postcomposing a presentation morphism with a target sheaf morphism
matches postcomposition on the corresponding differential operator. -/
private theorem sheafPrincipalPartsPresentationHomEquiv_naturality
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ)
    {G G' : Mod(O₂)} (α : G ⟶ G')
    (β : sheafPrincipalPartsPresheaf (J := J) φ F k ⟶ principalPartsTargetPresheaf (J := J) G) :
    sheafPrincipalPartsPresentationHomEquiv (J := J) φ F k G'
      (β ≫ (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O₂).obj)).map α.val) =
      (differentialOperatorsFunctor φ F k).map α
        (sheafPrincipalPartsPresentationHomEquiv (J := J) φ F k G β) := by
  apply Subtype.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  ext m
  -- Proof comment: both sides are literally `α_X` applied to the value of `β_X` on `[m]`.
  change
    (ModuleCat.Hom.hom
        (presentationToDifferentialOperatorApp (J := J) φ F k G'
          (β ≫ (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O₂).obj)).map α.val) X)) m =
      (ModuleCat.Hom.hom (((restrictionAlong φ).map α).val.app X))
        ((ModuleCat.Hom.hom (presentationToDifferentialOperatorApp (J := J) φ F k G β X)) m)
  rw [presentationToDifferentialOperatorApp_apply]
  rw [presentationToDifferentialOperatorApp_apply]
  rfl

/-- Helper for Lemma 18.34.3: the sheafification-based hom equivalence obtained by first applying
the sheafification adjunction and then the presheaf presentation equivalence. -/
private noncomputable abbrev sheafPrincipalPartsHomEquiv
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂)) :
    (sheafPrincipalParts (J := J) φ F k ⟶ G) ≃
      (differentialOperatorsFunctor φ F k).obj G :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O₂).obj)).trans
    (sheafPrincipalPartsPresentationHomEquiv (J := J) φ F k G)

/-- Helper for Lemma 18.34.3: the sheafification-based hom equivalence is natural in the target
sheaf. -/
private theorem sheafPrincipalPartsHomEquiv_comp
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ)
    {G G' : Mod(O₂)} (α : G ⟶ G')
    (f : sheafPrincipalParts (J := J) φ F k ⟶ G) :
    sheafPrincipalPartsHomEquiv (J := J) φ F k G' (f ≫ α) =
      (differentialOperatorsFunctor φ F k).map α
        (sheafPrincipalPartsHomEquiv (J := J) φ F k G f) := by
  have hsheaf :
      PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O₂).obj) (f ≫ α) =
        PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O₂).obj) f ≫
          (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O₂).obj)).map α.val := by
    -- Proof comment: `sheafificationHomEquiv` is the hom part of the sheafification adjunction,
    -- so right naturality transports postcomposition by `α` to the presheaf side.
    simpa [PresheafOfModules.sheafificationAdjunction_homEquiv_apply] using
      congrArg (fun h ↦ h)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).homEquiv_naturality_right)
          f α)
  -- Rewrite the adjunction image of `f ≫ α` and then invoke the presheaf-level naturality
  -- lemma proved above.
  rw [show sheafPrincipalPartsHomEquiv (J := J) φ F k G' (f ≫ α) =
      sheafPrincipalPartsPresentationHomEquiv (J := J) φ F k G'
        (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O₂).obj) (f ≫ α)) by rfl]
  rw [hsheaf]
  -- Proof comment: once the adjunction transports postcomposition to the presheaf side, the
  -- result is exactly the presheaf-level naturality statement for the presentation equivalence.
  exact sheafPrincipalPartsPresentationHomEquiv_naturality (J := J) φ F k α
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O₂).obj) f)

-- TODO: combine the sheafification adjunction with the presheaf-level equivalence above and the
-- target-side naturality from `differentialOperatorsFunctor.map`.
/-- Helper for Lemma 18.34.3: the sheafification of the principal-parts presheaf corepresents the
functor of order-`k` differential operators out of `F`. -/
private noncomputable def sheafPrincipalPartsCorepresentableBy
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) :
    (differentialOperatorsFunctor φ F k).CorepresentableBy
      (sheafPrincipalParts (J := J) φ F k) :=
  { homEquiv := fun {G} ↦ sheafPrincipalPartsHomEquiv (J := J) φ F k G
    homEquiv_comp := fun {_ _} α f ↦ sheafPrincipalPartsHomEquiv_comp (J := J) φ F k α f }

-- Proof sketch: construct the order-`k` principal-parts presheaf objectwise using the algebraic
-- principal-parts owner from Chapter 10, then sheafify it as an `O₂`-module sheaf. The induced
-- corepresentability witness is obtained by sheafifying the objectwise factorization bijection for
-- differential operators.
/-- Lemma 18.34.3: for a morphism `φ : O₁ ⟶ O₂` of sheaves of commutative rings on a site, an
`O₂`-module sheaf `F`, and `k : ℕ`, there exists an `O₂`-module sheaf of principal parts
`P^k_{O₂/O₁}(F)` corepresenting order-`k` differential operators out of `F`. Equivalently, for
every `O₂`-module sheaf `G`, order-`k` differential operators `F → G` are canonically in
bijection with `O₂`-linear morphisms `P^k_{O₂/O₁}(F) ⟶ G`, functorially in `G`. -/
-- TODO: finish by applying `sheafPrincipalPartsCorepresentableBy` once the presheaf-level
-- source-change equivalence and the resulting universe-polished witness are in place.
theorem exists_principal_parts_of_order
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) :
    (differentialOperatorsFunctor φ F k).IsCorepresentable := by
  -- Proof comment: the sheafification of the objectwise principal-parts presheaf already carries
  -- the required corepresentability witness.
  have hP :
      (differentialOperatorsFunctor φ F k).CorepresentableBy
        (sheafPrincipalParts (J := J) φ F k) :=
    sheafPrincipalPartsCorepresentableBy (J := J) (φ := φ) (F := F) k
  exact hP.isCorepresentable

end SheafOfModules.RingedSite
