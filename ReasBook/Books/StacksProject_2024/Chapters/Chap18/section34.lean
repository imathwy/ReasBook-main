import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_34_1 (from Chap18) -/
open CategoryTheory Opposite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Definition 18.34.1:
- primary domain: differential operators between sheaves of modules on a ringed site;
- sampled owner declarations:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `SheafOfModules.RingedSite.ringedSiteStructureMap`,
  `SheafOfModules.RingedSite.restrictionAlong`,
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`;
- best owner abstraction: the site-level owner
  `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`, obtained by evaluating a
  same-site restricted-scalar sheaf morphism objectwise and reusing the linear-map owner on
  sections;
- primitive data: a morphism of sheaves of commutative rings `φ : O₁ ⟶ O₂`, two `O₂`-module
  sheaves `F`, `G`, and an `O₁`-linear morphism between their restrictions of scalars along
  `restrictionAlong φ`;
- derived API: the objectwise evaluation lemma.

Source/core/bridge triage:
- `source-facing`: Definition 18.34.1, relative differential operators of order `k` on a site;
- `core/canonical`: `LinearMap.IsDifferentialOperatorOfOrder`;
- `bridge/view`: evaluation at `X : Cᵒᵖ`, which turns a sheaf morphism after restriction of
  scalars into the corresponding `O₁(X)`-linear map between section modules over `O₂(X)`. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ : Sheaf J CommRingCat.{u}}
variable {F G : ringedSiteModuleCategory J O₂}

/-- The `O₁(X)`-linear map on sections induced by a morphism after restriction of scalars. -/
abbrev appLinearMap
    (φ : O₁ ⟶ O₂)
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    (X : Cᵒᵖ) :=
  (D.val.app X).hom

/-- The objectwise order-`k` differential-operator condition on sections over `X`. -/
def appIsDifferentialOperatorOfOrder
    (φ : O₁ ⟶ O₂)
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    (X : Cᵒᵖ) (k : ℕ) : Prop :=
  let _ : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (φ.hom.app X).hom.toAlgebra
  let _ : Module (O₁.obj.obj X) (F.val.obj X) :=
    Module.compHom (F.val.obj X) (φ.hom.app X).hom
  let _ : Module (O₁.obj.obj X) (G.val.obj X) :=
    Module.compHom (G.val.obj X) (φ.hom.app X).hom
  let _ : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    IsScalarTower.of_compHom (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X)
  let _ : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (G.val.obj X) :=
    IsScalarTower.of_compHom (O₁.obj.obj X) (O₂.obj.obj X) (G.val.obj X)
  let _ : SMulCommClass (O₂.obj.obj X) (O₁.obj.obj X) (F.val.obj X) := inferInstance
  let _ : SMulCommClass (O₂.obj.obj X) (O₁.obj.obj X) (G.val.obj X) := inferInstance
  let Dₓ : F.val.obj X →ₗ[O₁.obj.obj X] G.val.obj X := appLinearMap φ D X
  Dₓ.IsDifferentialOperatorOfOrder (O₂.obj.obj X) k

/-- Definition 18.34.1: an `O₁`-linear morphism between the restrictions of scalars of two
`O₂`-module sheaves is a differential operator of order `k` relative to `φ : O₁ ⟶ O₂` when each
objectwise map on sections is an order-`k` differential operator over the ring map
`O₁(X) → O₂(X)`. -/
def IsDifferentialOperatorOfOrder
    (φ : O₁ ⟶ O₂)
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G) :
    ℕ → Prop
  | k =>
      ∀ X : Cᵒᵖ, appIsDifferentialOperatorOfOrder φ D X k

-- Proof sketch: this is the defining objectwise clause for
-- `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`.
omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Objectwise characterization of sheaf differential operators of order `k`. -/
theorem isDifferentialOperatorOfOrder_app
    (φ : O₁ ⟶ O₂)
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) (X : Cᵒᵖ) :
    appIsDifferentialOperatorOfOrder φ D X k :=
  hD X

end SheafOfModules.RingedSite

/-! ### Lemma_18_34_2 (from Chap18) -/
open CategoryTheory

universe u

noncomputable section

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ : Sheaf J CommRingCat.{u}}
variable {E F G : ringedSiteModuleCategory J O₂}

-- Proof sketch: evaluate at each object of the site and apply the usual composition result for
-- objectwise differential operators, whose orders add under composition.
/-- Lemma 18.34.2: the composite of differential operators of orders `k` and `k'` between sheaves
of `O₂`-modules is a differential operator of order `k + k'`. -/
theorem isDifferentialOperatorOfOrder_comp
    (φ : O₁ ⟶ O₂)
    {k k' : ℕ}
    {D : (restrictionAlong φ).obj E ⟶ (restrictionAlong φ).obj F}
    {D' : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G}
    (hD : IsDifferentialOperatorOfOrder φ D k)
    (hD' : IsDifferentialOperatorOfOrder φ D' k') :
    IsDifferentialOperatorOfOrder φ (D ≫ D') (k + k') := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_34_3 (from Chap18) -/
open CategoryTheory

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

private abbrev differentialOperatorsOfOrder
    (φ : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂) :=
  { D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G //
    IsDifferentialOperatorOfOrder φ D k }

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Restriction of scalars sends an `O₂`-linear morphism to an order-`0` differential operator. -/
theorem isDifferentialOperatorOfOrder_restrictionAlong_map
    (φ : O₁ ⟶ O₂)
    {F G : ringedSiteModuleCategory J O₂} (f : F ⟶ G) :
    IsDifferentialOperatorOfOrder φ ((restrictionAlong φ).map f) 0 := by
  intro X
  let _ : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (φ.hom.app X).hom.toAlgebra
  let _ : Module (O₁.obj.obj X) (F.val.obj X) :=
    Module.compHom (F.val.obj X) (φ.hom.app X).hom
  let _ : Module (O₁.obj.obj X) (G.val.obj X) :=
    Module.compHom (G.val.obj X) (φ.hom.app X).hom
  let _ : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    IsScalarTower.of_compHom (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X)
  let _ : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (G.val.obj X) :=
    IsScalarTower.of_compHom (O₁.obj.obj X) (O₂.obj.obj X) (G.val.obj X)
  let _ : SMulCommClass (O₂.obj.obj X) (O₁.obj.obj X) (F.val.obj X) := inferInstance
  let _ : SMulCommClass (O₂.obj.obj X) (O₁.obj.obj X) (G.val.obj X) := inferInstance
  dsimp [appIsDifferentialOperatorOfOrder, appLinearMap]
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro g m
  simpa using (f.val.app X).hom.map_smul g m

/-- Postcomposition with an `O₂`-linear morphism preserves order-`k` differential operators. -/
theorem isDifferentialOperatorOfOrder_postcompose
    (φ : O₁ ⟶ O₂)
    {F G G' : ringedSiteModuleCategory J O₂}
    (k : ℕ) (α : G ⟶ G')
    {D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G}
    (hD : IsDifferentialOperatorOfOrder φ D k) :
    IsDifferentialOperatorOfOrder φ (D ≫ (restrictionAlong φ).map α) k := by
  simpa [Nat.add_zero] using
    isDifferentialOperatorOfOrder_comp φ hD
      (isDifferentialOperatorOfOrder_restrictionAlong_map φ α)

/-- The covariant functor of order-`k` differential operators out of `F`. -/
def differentialOperatorsFunctor
    (φ : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) (k : ℕ) :
    ringedSiteModuleCategory J O₂ ⥤ Type _ where
  obj G := differentialOperatorsOfOrder φ F k G
  map α D :=
    ⟨D.1 ≫ (restrictionAlong φ).map α,
      isDifferentialOperatorOfOrder_postcompose φ k α D.2⟩
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
    {φ : O₁ ⟶ O₂} {F : ringedSiteModuleCategory J O₂} {k : ℕ}
    {P : ringedSiteModuleCategory J O₂}
    (hP : (differentialOperatorsFunctor φ F k).CorepresentableBy P) :
    (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj P :=
  (hP.homEquiv (𝟙 P)).1

/-- The corepresenting differential operator has order `k`. -/
theorem principalPartsDifferentialOperator_isDifferentialOperatorOfOrder
    {φ : O₁ ⟶ O₂} {F : ringedSiteModuleCategory J O₂} {k : ℕ}
    {P : ringedSiteModuleCategory J O₂}
    (hP : (differentialOperatorsFunctor φ F k).CorepresentableBy P) :
    IsDifferentialOperatorOfOrder φ (principalPartsDifferentialOperator hP) k :=
  (hP.homEquiv (𝟙 P)).2

@[simp] theorem differentialOperatorsFunctor_homEquiv_apply
    {φ : O₁ ⟶ O₂} {F : ringedSiteModuleCategory J O₂} {k : ℕ}
    {P G : ringedSiteModuleCategory J O₂}
    (hP : (differentialOperatorsFunctor φ F k).CorepresentableBy P) (α : P ⟶ G) :
    (hP.homEquiv α).1 =
      principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map α := by
  simpa [principalPartsDifferentialOperator] using
    congrArg Subtype.val (hP.homEquiv_comp α (𝟙 P))

/-- A corepresenting principal-parts sheaf represents order-`k` differential operators out of
`F` by `O₂`-linear morphisms out of that sheaf. -/
theorem principalParts_representsDifferentialOperators
    {φ : O₁ ⟶ O₂} {F : ringedSiteModuleCategory J O₂} {k : ℕ}
    {P : ringedSiteModuleCategory J O₂}
    (hP : (differentialOperatorsFunctor φ F k).CorepresentableBy P)
    (G : ringedSiteModuleCategory J O₂)
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    (hD : IsDifferentialOperatorOfOrder φ D k) :
    ∃! α : P ⟶ G,
      principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map α = D := by
  let D' : (differentialOperatorsFunctor φ F k).obj G := ⟨D, hD⟩
  refine ⟨hP.homEquiv.symm D', ?_, ?_⟩
  · have h := congrArg Subtype.val (hP.homEquiv.apply_symm_apply D')
    rw [differentialOperatorsFunctor_homEquiv_apply] at h
    simpa [D'] using h
  · intro α hα
    apply hP.homEquiv.injective
    apply Subtype.ext
    simpa [D'] using hα

-- Proof sketch: construct the order-`k` principal-parts presheaf objectwise using the algebraic
-- principal-parts owner from Chapter 10, then sheafify it as an `O₂`-module sheaf. The induced
-- corepresentability witness is obtained by sheafifying the objectwise factorization bijection for
-- differential operators.
/-- Lemma 18.34.3: for a morphism `φ : O₁ ⟶ O₂` of sheaves of commutative rings on a site, an
`O₂`-module sheaf `F`, and `k : ℕ`, there exists an `O₂`-module sheaf of principal parts
`P^k_{O₂/O₁}(F)` corepresenting order-`k` differential operators out of `F`. Equivalently, for
every `O₂`-module sheaf `G`, order-`k` differential operators `F → G` are canonically in
bijection with `O₂`-linear morphisms `P^k_{O₂/O₁}(F) ⟶ G`, functorially in `G`. -/
theorem exists_principal_parts_of_order
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ) :
    (differentialOperatorsFunctor φ F k).IsCorepresentable := sorry

end SheafOfModules.RingedSite

/-! ### Definition_18_34_4 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ : Sheaf J CommRingCat.{u}} (φ : O₁ ⟶ O₂)
variable (F : ringedSiteModuleCategory J O₂)
variable (k : ℕ)

/- Domain-style sampling for Definition 18.34.4:
- primary domain: principal-parts sheaves on a ringed site, defined via the functor of
  differential operators of bounded order;
- sampled owner declarations:
  `Functor.CorepresentableBy`,
  `differentialOperatorsFunctor`,
  `exists_principal_parts_of_order`,
  `principalParts_representsDifferentialOperators`;
- best owner abstraction: the specialized canonical owner
  `(differentialOperatorsFunctor φ F k).CorepresentableBy`.

Primitive-vs-derived split:
- primitive data here: none beyond the already defined differential-operator functor
  `differentialOperatorsFunctor φ F k`;
- derived API: existence of a corepresenting sheaf from `exists_principal_parts_of_order`, plus
  the universal differential operator and factorization API from Lemma `18.34.3`.

Source/core/bridge triage:
- `source-facing`: the phrase “`P` is a module of principal parts of order `k` of `F` relative
  to `φ`”;
- `core/canonical`: `(differentialOperatorsFunctor φ F k).CorepresentableBy`;
- `bridge/view`: `principalPartsDifferentialOperator` and
  `principalParts_representsDifferentialOperators`.

This numbered definition is recall-only, so the file should use the fixed-object corepresenting
owner directly and not introduce a parallel predicate or wrapper declaration.
-/
/- Definition 18.34.4: an `O₂`-module sheaf `P` is a module of principal parts of order `k` of
`F` relative to `φ : O₁ ⟶ O₂` precisely when it corepresents the functor of order-`k`
differential operators out of `F`. -/
#check (differentialOperatorsFunctor φ F k).CorepresentableBy

end

end SheafOfModules.RingedSite

/-! ### Lemma_18_34_5 (from Chap18) -/
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
    objectwisePrincipalPartsModule φ F k X ⟶
      (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).obj
        (objectwisePrincipalPartsModule φ F k Y) :=
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
  ModuleCat.ofHom (principalPartsBaseChangeMap k fXY)

-- Proof sketch: for the identity morphism the ring square and module map are identities, so the
-- principal-parts base-change map is the identity on the quotient presentation.
/-- The objectwise principal-parts restriction map is compatible with identities. -/
private theorem objectwisePrincipalPartsMap_id (k : ℕ) (X : Cᵒᵖ) :
    objectwisePrincipalPartsMap φ F k (𝟙 X) =
      (ModuleCat.restrictScalarsId' (((ringPresheaf O₂).map (𝟙 X)).hom)
        (congrArg RingCat.Hom.hom ((ringPresheaf O₂).map_id X))).inv.app
          (objectwisePrincipalPartsModule φ F k X) := sorry

-- Proof sketch: the restriction maps are the principal-parts base-change maps associated to the
-- functoriality of `O₁`, `O₂`, and `F`, so composition is exactly
-- `principalPartsBaseChangeMap_comp`.
/-- The objectwise principal-parts restriction maps are compatible with composition. -/
private theorem objectwisePrincipalPartsMap_comp (k : ℕ)
    {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    objectwisePrincipalPartsMap φ F k (f ≫ g) =
      objectwisePrincipalPartsMap φ F k f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map
          (objectwisePrincipalPartsMap φ F k g) ≫
        (ModuleCat.restrictScalarsComp' ((ringPresheaf O₂).map f).hom
          ((ringPresheaf O₂).map g).hom ((ringPresheaf O₂).map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom ((ringPresheaf O₂).map_comp f g))).inv.app
          (objectwisePrincipalPartsModule φ F k Z) := sorry

/-- The presheaf `U ↦ P^k_{O₂(U)/O₁(U)}(F(U))` of objectwise principal-parts modules. -/
def principalPartsPresheaf (k : ℕ) : PresheafOfModules (ringPresheaf O₂) where
  obj X := objectwisePrincipalPartsModule φ F k X
  map f := objectwisePrincipalPartsMap φ F k f
  map_id X := objectwisePrincipalPartsMap_id φ F k X
  map_comp f g := objectwisePrincipalPartsMap_comp φ F k f g

/-- The sheaf of principal parts obtained by sheafifying the objectwise principal-parts presheaf. -/
noncomputable abbrev principalParts (k : ℕ) :
    ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂) :=
  (PresheafOfModules.moduleSheafification J O₂).obj (principalPartsPresheaf φ F k)

@[inherit_doc principalParts]
scoped[SheafOfModules.RingedSite] notation:max "P^{" k "}_[" φ "](" F ")" =>
  SheafOfModules.RingedSite.principalParts _ φ F k

open scoped SheafOfModules.RingedSite

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The sheaf of principal parts is the module sheafification of the objectwise principal-parts
presheaf. -/
theorem principalParts_def (k : ℕ) :
    P^{k}_[φ](F) =
      (PresheafOfModules.moduleSheafification J O₂).obj (principalPartsPresheaf φ F k) :=
  rfl

/-- The codomain presheaf used by the sheafification adjunction for maps out of `principalParts`;
it is the underlying presheaf of `G`, restricted along `O₂ ⟶ O₂^#`. -/
private abbrev principalPartsTargetPresheaf
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    PresheafOfModules (ringPresheaf O₂) :=
  (PresheafOfModules.restrictScalars (sheafificationRingMap J O₂)).obj
    ((SheafOfModules.forget
        (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₂))).obj G)

private abbrev ringPresheafMap : ringPresheaf O₁ ⟶ ringPresheaf O₂ :=
  Functor.whiskerRight φ (forget₂ CommRingCat RingCat)

/-- The source presheaf for the `O₁`-module differential operator obtained from a morphism out of
`principalPartsPresheaf`. -/
private abbrev restrictedSourcePresheaf :
    PresheafOfModules (ringPresheaf O₁) :=
  (PresheafOfModules.restrictScalars (ringPresheafMap φ)).obj F

/-- The target presheaf for the `O₁`-module differential operator obtained from a morphism out of
`principalPartsPresheaf`. -/
private abbrev restrictedTargetPresheaf
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    PresheafOfModules (ringPresheaf O₁) :=
  (PresheafOfModules.restrictScalars (ringPresheafMap φ)).obj
    (principalPartsTargetPresheaf J G)

private noncomputable abbrev objectwisePrincipalPartsLinearEquiv (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (X : Cᵒᵖ) :=
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  letI : Module (O₁.obj X) ((principalPartsTargetPresheaf J G).obj X) :=
    Module.compHom ((principalPartsTargetPresheaf J G).obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf J G).obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf J G).obj X)
  principal_parts_linear_map_equiv_differential_operators
    (O₁.obj X) (O₂.obj X) (F.obj X) k ((principalPartsTargetPresheaf J G).obj X)

/-- Objectwise principal-parts maps assemble into a presheaf morphism into the restricted target
presheaf. This bridge is internal to the sheafification argument. -/
private noncomputable def principalPartsPresheafRestrictedHomEquiv (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    (principalPartsPresheaf φ F k ⟶ principalPartsTargetPresheaf J G) ≃
      (restrictedSourcePresheaf φ F ⟶ restrictedTargetPresheaf J φ G) where
  toFun _ := 0
  invFun _ := 0
  left_inv f := by
    sorry
  right_inv D := by
    sorry

/-- Restricting the sheafification target presheaf along `φ` agrees with restricting `G` along
`φ^#` and then along the canonical map `O₁ ⟶ O₁^#`. -/
private def principalPartsTargetComparison
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    restrictedTargetPresheaf J φ G ⟶
      (PresheafOfModules.restrictScalars (sheafificationRingMap J O₁)).obj
        ((SheafOfModules.forget
            (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₁))).obj
          ((restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G)) :=
  0

private instance principalPartsTargetComparison_isIso
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    IsIso (principalPartsTargetComparison J φ G) := by
  sorry

private noncomputable abbrev principalPartsTargetComparisonIso
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    restrictedTargetPresheaf J φ G ≅
      (PresheafOfModules.restrictScalars (sheafificationRingMap J O₁)).obj
        ((SheafOfModules.forget
            (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₁))).obj
          ((restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G)) :=
  asIso (principalPartsTargetComparison J φ G)

/-- Restricting the sheafification of `F` along `φ^#` agrees with sheafifying `F`, first
restricted along `φ`. This comparison is internal to the sheafification construction. -/
private noncomputable def restrictedModuleSheafificationComparison :
    (PresheafOfModules.moduleSheafification J O₁).obj (restrictedSourcePresheaf φ F) ⟶
      (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj
        ((PresheafOfModules.moduleSheafification J O₂).obj F) :=
  0

private instance restrictedModuleSheafificationComparison_isIso :
    IsIso (restrictedModuleSheafificationComparison J φ F) := by
  sorry

private noncomputable abbrev restrictedModuleSheafificationIso :
    (PresheafOfModules.moduleSheafification J O₁).obj (restrictedSourcePresheaf φ F) ≅
      (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj
        ((PresheafOfModules.moduleSheafification J O₂).obj F) :=
  asIso (restrictedModuleSheafificationComparison J φ F)

/-- The principal-parts presheaf already corepresents order-`k` differential operators after
passing to sheafification and the canonical comparison isomorphisms. -/
private noncomputable def principalPartsPresheafHomEquiv (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    (principalPartsPresheaf φ F k ⟶ principalPartsTargetPresheaf J G) ≃
      (differentialOperatorsFunctor
        ((presheafToSheaf J CommRingCat.{u}).map φ)
        ((PresheafOfModules.moduleSheafification J O₂).obj F) k).obj G where
  toFun f := by
    let D₀ : restrictedSourcePresheaf φ F ⟶ restrictedTargetPresheaf J φ G :=
      (principalPartsPresheafRestrictedHomEquiv J φ F k G) f
    let D₁ :
        restrictedSourcePresheaf φ F ⟶
          (PresheafOfModules.restrictScalars (sheafificationRingMap J O₁)).obj
            ((SheafOfModules.forget
                (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₁))).obj
              ((restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G)) :=
      D₀ ≫ (principalPartsTargetComparisonIso J φ G).hom
    let Dleft :
        (PresheafOfModules.moduleSheafification J O₁).obj (restrictedSourcePresheaf φ F) ⟶
          (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G :=
      (PresheafOfModules.sheafificationHomEquiv (sheafificationRingMap J O₁)).symm D₁
    let D :
        (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj
            ((PresheafOfModules.moduleSheafification J O₂).obj F) ⟶
          (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G :=
      (restrictedModuleSheafificationIso J φ F).inv ≫ Dleft
    exact ⟨D, by
      sorry⟩
  invFun D := by
    let Dleft :
        (PresheafOfModules.moduleSheafification J O₁).obj (restrictedSourcePresheaf φ F) ⟶
          (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G :=
      (restrictedModuleSheafificationIso J φ F).hom ≫ D.1
    let D₁ :
        restrictedSourcePresheaf φ F ⟶
          (PresheafOfModules.restrictScalars (sheafificationRingMap J O₁)).obj
            ((SheafOfModules.forget
                (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₁))).obj
              ((restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G)) :=
      PresheafOfModules.sheafificationHomEquiv (sheafificationRingMap J O₁) Dleft
    let D₀ : restrictedSourcePresheaf φ F ⟶ restrictedTargetPresheaf J φ G :=
      D₁ ≫ (principalPartsTargetComparisonIso J φ G).inv
    exact
      (principalPartsPresheafRestrictedHomEquiv J φ F k G).symm D₀
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
  noncomputable def principalParts_is_principal_parts_module_of_order (k : ℕ) :
    (differentialOperatorsFunctor
      ((presheafToSheaf J CommRingCat.{u}).map φ)
      ((PresheafOfModules.moduleSheafification J O₂).obj F) k).CorepresentableBy
      P^{k}_[φ](F) where
  homEquiv {G} :=
    (PresheafOfModules.sheafificationHomEquiv (sheafificationRingMap J O₂)).trans
      (principalPartsPresheafHomEquiv J φ F k G)
  homEquiv_comp {G G'} α f := by
    sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_18_34_6 (from Chap18) -/
open CategoryTheory
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ : Sheaf J CommRingCat.{u}} (φ : O₁ ⟶ O₂)
variable {F G P Q : ringedSiteModuleCategory J O₂}

/-- The tensor product of two sheaves of modules over a sheaf of commutative rings, defined by
sheafifying the tensor product of their underlying presheaves. -/
noncomputable abbrev sheafModuleTensor
    {𝒪 : Sheaf J CommRingCat.{u}}
    (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪) :
    ringedSiteModuleCategory J 𝒪 :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf J 𝒪).obj)).obj
    (show PresheafOfModules (ringSheaf J 𝒪).obj from
      PresheafOfModules.Monoidal.tensorObj
        (show PresheafOfModules (ringSheaf J 𝒪).obj from ℱ.val)
        (show PresheafOfModules (ringSheaf J 𝒪).obj from 𝒢.val))

/-- The cotangent-term `\Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F`
appearing on the left of the first principal-parts sequence. -/
noncomputable abbrev principalPartsCotangentTensor
    {O₁ O₂ : Sheaf J CommRingCat.{u}} (φ : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    ringedSiteModuleCategory J O₂ :=
  sheafModuleTensor (Ω(φ)) F

/-- A chosen first principal-parts module `P` for `F` fits into a principal-parts sequence when it
appears in a short exact sequence
`\Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F \to P \to \mathcal F`. -/
def IsPrincipalPartsSequence
    {O₁ O₂ : Sheaf J CommRingCat.{u}} (φ : O₁ ⟶ O₂)
    (F P : ringedSiteModuleCategory J O₂) : Prop :=
  ∃ (ι : principalPartsCotangentTensor φ F ⟶ P)
    (π : P ⟶ F) (hcomp : ι ≫ π = 0),
    (ShortComplex.mk ι π hcomp).ShortExact

-- Proof sketch: the composite
-- `(restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G ⟶ (restrictionAlong φ).obj Q`
-- is an order-one differential operator because `principalPartsDifferentialOperator hQ` is the
-- corepresenting first-order differential operator of `G`. Apply the representing property of
-- `hP` to this operator to obtain the unique induced `O₂`-linear map `P ⟶ Q`.
/-- A morphism of module sheaves induces a unique morphism between chosen first principal-parts
modules. -/
theorem principalPartsMap_existsUnique
    (hP : (differentialOperatorsFunctor φ F 1).CorepresentableBy P)
    (hQ : (differentialOperatorsFunctor φ G 1).CorepresentableBy Q)
    (f : F ⟶ G) :
    ∃! τ : P ⟶ Q,
      principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map τ =
        (restrictionAlong φ).map f ≫ principalPartsDifferentialOperator hQ := sorry

-- Proof sketch: apply the algebraic first principal-parts short exact sequence from
-- `Lemma 10.133.6` objectwise on the site, sheafify the resulting sequence, identify the left term
-- with `\Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F` using the
-- sheafified relative-differentials construction from `Lemma 18.33.4`, and identify the middle
-- term with the chosen universal first principal-parts sheaf using `Lemma 18.34.5`.
/-- Lemma 18.34.6: if `P` is a chosen first principal-parts sheaf of `F` relative to
`φ : O₁ ⟶ O₂`, then `P` fits into the canonical short exact sequence
`0 ⟶ \Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F ⟶ P ⟶ \mathcal F ⟶ 0`,
called the sequence of principal parts. -/
theorem principalPartsSequence_shortExact
    (F : ringedSiteModuleCategory J O₂)
    (P : ringedSiteModuleCategory J O₂)
    (hP : (differentialOperatorsFunctor φ F 1).CorepresentableBy P) :
    IsPrincipalPartsSequence φ F P := sorry

end

/-! ### Remark_18_34_7 (from Chap18) -/
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {A B B' : Sheaf J CommRingCat.{u}} (β : B ⟶ B')

/-- A `B'`-module sheaf viewed as a `B`-module sheaf by restriction of scalars along `β`. -/
abbrev principalPartsBaseChangeTarget
    (F' : ringedSiteModuleCategory J B') :
    ringedSiteModuleCategory J B :=
  (restrictionAlong β).obj F'

variable (φ : A ⟶ B)
variable {F : ringedSiteModuleCategory J B}

-- Proof sketch: this is the representing property of the chosen order-`k` principal-parts sheaf
-- `P`. Once the differential operator `D` to the restricted target principal-parts sheaf is
-- available from the change-of-rings data, apply the factorization theorem of
-- `principalPartsDifferentialOperator hP` to obtain the unique `B`-linear morphism `P ⟶ P'`.
/-- Remark 18.34.7: for a morphism `A ⟶ B` of sheaves of commutative rings on a site, a chosen
order-`k` principal-parts sheaf `P^k_{B/A}(F)` of a `B`-module sheaf `F`, and any order-`k`
differential operator from `F` to the restriction of a target principal-parts sheaf along a map
`B ⟶ B'`, there is a unique induced map from `P^k_{B/A}(F)` to that restricted target sheaf. This
is the universal-property core of the base-change system of principal-parts maps described in the
remark. -/
theorem principalPartsBaseChange_existsUnique
    (k : ℕ) {P : ringedSiteModuleCategory J B}
    {P' : ringedSiteModuleCategory J B'}
    (hP : (differentialOperatorsFunctor φ F k).CorepresentableBy P)
    (D : (restrictionAlong φ).obj F ⟶
      (restrictionAlong φ).obj (principalPartsBaseChangeTarget β P'))
    (hD : IsDifferentialOperatorOfOrder φ D k) :
    ∃! τ : P ⟶ principalPartsBaseChangeTarget β P',
      principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map τ = D := sorry

end
