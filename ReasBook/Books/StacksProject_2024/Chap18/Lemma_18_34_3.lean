import Mathlib
import StacksProject_2024.Chap18.Lemma_18_34_2

-- Declarations for this item will be appended below by the statement pipeline.

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
