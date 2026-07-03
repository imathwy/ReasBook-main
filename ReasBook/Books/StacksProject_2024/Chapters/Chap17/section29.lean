import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_29_1 (from Chap17) -/
open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
variable {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)}

/-
Domain-style sampling for Definition 17.29.1:
- primary domain: differential operators between sheaves of modules after restriction of scalars
  along a morphism of sheaves of commutative rings;
- sampled owner declarations:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `SheafOfModules.restrictScalars`,
  `ringSheafMap`,
  `LinearMap.IsDifferentialOperatorOfOrder`;
- best owner abstraction: the opens-site owner in `TopCat.Sheaf`, obtained by evaluating a
  restricted-scalar sheaf morphism on each open set and reusing the linear-map owner;
- primitive data: a morphism
  `D : (SheafOfModules.restrictScalars (ringSheafMap φ)).obj ℱ ⟶
    (SheafOfModules.restrictScalars (ringSheafMap φ)).obj 𝒢`;
- derived API: the order-zero sectionwise linearity criterion.

Source/core/bridge triage:
- `source-facing`: Definition 17.29.1, relative differential operators on a topological space;
- `core/canonical`: `LinearMap.IsDifferentialOperatorOfOrder`;
- `bridge/view`: evaluation of `D` on each open set `U`, yielding the sectionwise linear map
  `appLinearMap φ D U` and predicate `appIsDifferentialOperatorOfOrder φ D U k`.
-/

/-- The `\mathcal O_1(U)`-linear map on sections induced by `D`. -/
abbrev appLinearMap
    (φ : 𝒪₁ ⟶ 𝒪₂)
    (D : (SheafOfModules.restrictScalars (ringSheafMap φ)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap φ)).obj 𝒢)
    (U : (Opens X)ᵒᵖ) :=
  (D.val.app U).hom

/-- The objectwise order-`k` differential-operator condition on sections over `U`. -/
def appIsDifferentialOperatorOfOrder
    (φ : 𝒪₁ ⟶ 𝒪₂)
    (D : (SheafOfModules.restrictScalars (ringSheafMap φ)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap φ)).obj 𝒢)
    (U : (Opens X)ᵒᵖ) (k : ℕ) : Prop :=
  let _ : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := (φ.hom.app U).hom.toAlgebra
  let _ : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
    Module.compHom (ℱ.val.obj U) ((ringSheafMap φ).hom.app U).hom
  let _ : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) :=
    Module.compHom (𝒢.val.obj U) ((ringSheafMap φ).hom.app U).hom
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
  let _ : SMulCommClass (𝒪₂.obj.obj U) (𝒪₁.obj.obj U) (ℱ.val.obj U) := inferInstance
  let _ : SMulCommClass (𝒪₂.obj.obj U) (𝒪₁.obj.obj U) (𝒢.val.obj U) := inferInstance
  let DU : ℱ.val.obj U →ₗ[𝒪₁.obj.obj U] 𝒢.val.obj U := appLinearMap φ D U
  DU.IsDifferentialOperatorOfOrder (𝒪₂.obj.obj U) k

/-- Definition 17.29.1: an `\mathcal O_1`-linear morphism between the restrictions of scalars of
two `\mathcal O_2`-module sheaves is a differential operator of order `k` when each objectwise
map on sections is an order-`k` differential operator over
`\mathcal O_1(U) → \mathcal O_2(U)`. -/
def IsDifferentialOperatorOfOrder
    (φ : 𝒪₁ ⟶ 𝒪₂)
    (D : (SheafOfModules.restrictScalars (ringSheafMap φ)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap φ)).obj 𝒢) : ℕ → Prop
  | k => ∀ U : (Opens X)ᵒᵖ, appIsDifferentialOperatorOfOrder φ D U k

/-- Objectwise characterization of opens-site differential operators of order `k`. -/
theorem isDifferentialOperatorOfOrder_app
    (φ : 𝒪₁ ⟶ 𝒪₂)
    (D : (SheafOfModules.restrictScalars (ringSheafMap φ)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap φ)).obj 𝒢)
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) (U : (Opens X)ᵒᵖ) :
    appIsDifferentialOperatorOfOrder φ D U k :=
  hD U

end

end TopCat.Sheaf

/-! ### Lemma_17_29_2 (from Chap17) -/
open CategoryTheory Opposite TopologicalSpace TopCat.Sheaf

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
variable {ℱ 𝒢 ℋ : SheafOfModules (ringSheaf 𝒪₂)}

/- Domain-style sampling for Lemma 17.29.2:
- primary domain: differential operators between sheaves of modules relative to a morphism of ring
  sheaves;
- sampled owner declarations:
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`,
  `TopCat.Sheaf.appIsDifferentialOperatorOfOrder`,
  `TopCat.Sheaf.appLinearMap`,
  `LinearMap.isDifferentialOperatorOfOrder_comp`;
- best owner abstraction: the opens-site owner
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`, obtained by evaluating on opens and reusing the
  algebraic composition theorem;
- primitive data: a morphism
  `D : (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ ⟶
    (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj 𝒢`;
- derived API: closure of that owner under composition.

Source/core/bridge triage:
- `core/canonical`: `LinearMap.isDifferentialOperatorOfOrder_comp`;
- `source-facing`: the opens-site owner
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`;
- `bridge/view`: the opens-site specialization along `ringSheafMap varphi`.

This file should therefore reuse the algebraic composition theorem on each open set rather than
import a later same-site wrapper. -/

-- Proof sketch: evaluate both morphisms on an open set and apply the algebraic composition theorem
-- for differential operators over `𝒪₁(U) → 𝒪₂(U)`.
/-- Lemma 17.29.2: the composite of differential operators of orders `k` and `k'` between sheaves
of `\mathcal O_2`-modules is a differential operator of order `k + k'`. -/
theorem isDifferentialOperatorOfOrder_comp (varphi : 𝒪₁ ⟶ 𝒪₂)
    {k k' : ℕ}
    {D : (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj 𝒢}
    {D' : (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj 𝒢 ⟶
      (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℋ}
    (hD : IsDifferentialOperatorOfOrder varphi D k)
    (hD' : IsDifferentialOperatorOfOrder varphi D' k') :
    IsDifferentialOperatorOfOrder varphi (D ≫ D') (k + k') := by
  intro U
  let _ : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := (varphi.hom.app U).hom.toAlgebra
  let _ : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
    Module.compHom (ℱ.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) :=
    Module.compHom (𝒢.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : Module (𝒪₁.obj.obj U) (ℋ.val.obj U) :=
    Module.compHom (ℋ.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℋ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℋ.val.obj U)
  let _ : SMulCommClass (𝒪₂.obj.obj U) (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
    inferInstance
  let _ : SMulCommClass (𝒪₂.obj.obj U) (𝒪₁.obj.obj U) (𝒢.val.obj U) :=
    inferInstance
  let _ : SMulCommClass (𝒪₂.obj.obj U) (𝒪₁.obj.obj U) (ℋ.val.obj U) :=
    inferInstance
  let DU : ℱ.val.obj U →ₗ[𝒪₁.obj.obj U] 𝒢.val.obj U :=
    appLinearMap varphi D U
  let D'U : 𝒢.val.obj U →ₗ[𝒪₁.obj.obj U] ℋ.val.obj U :=
    appLinearMap varphi D' U
  simpa [appIsDifferentialOperatorOfOrder] using
    LinearMap.isDifferentialOperatorOfOrder_comp (D := DU) (D' := D'U) (hD U) (hD' U)

end

/-! ### Lemma_17_29_3 (from Chap17) -/
open CategoryTheory Opposite TopologicalSpace TopCat.Sheaf

noncomputable section

universe u

section

/- Domain triage:
- primary domain: sheaf-level differential operators and principal parts over a morphism of
  sheaves of commutative rings;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`,
  `isDifferentialOperatorOfOrder_comp` from `Lemma_17_29_2`,
  `principal_parts_linear_map_equiv_differential_operators` from `Chap10`,
  `Functor.IsCorepresentable` from mathlib's Yoneda API;
- best owner abstraction: the covariant functor
  `𝒢 ↦ { D : ((restrictScalars φ).obj ℱ ⟶ (restrictScalars φ).obj 𝒢) //
    IsDifferentialOperatorOfOrder φ D k }`
  together with the canonical existence owner `Functor.IsCorepresentable`;
- primitive data: the opens-site specialization of
  `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`;
- derived API: postcomposition on order-`k` differential operators and the existence of a
  corepresenting module sheaf.
-/

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X} (varphi : 𝒪₁ ⟶ 𝒪₂)
variable (ℱ : SheafOfModules (ringSheaf 𝒪₂))

private abbrev differentialOperatorsOfOrder (k : ℕ) (𝒢 : SheafOfModules 𝒪₂.ringSheaf) :=
  { D : (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj 𝒢 //
    IsDifferentialOperatorOfOrder varphi D k }

-- Proof sketch: after restriction of scalars, an `\mathcal O_2`-linear map remains sectionwise
-- `\mathcal O_2`-linear, so on every open set it is an order-zero differential operator.
/-- Restriction of scalars sends an `\mathcal O_2`-linear morphism to an order-`0` differential
operator. -/
theorem isDifferentialOperatorOfOrder_restrictScalars_map
    {𝒢 𝒢' : SheafOfModules 𝒪₂.ringSheaf} (α : 𝒢 ⟶ 𝒢') :
    IsDifferentialOperatorOfOrder varphi
      ((SheafOfModules.restrictScalars (ringSheafMap varphi)).map α) 0 := by
  simpa [SheafOfModules.RingedSite.restrictionAlong] using
    (SheafOfModules.RingedSite.isDifferentialOperatorOfOrder_restrictionAlong_map
      (J := Opens.grothendieckTopology X) varphi α)

-- Proof sketch: compose with the order-zero operator induced by `α` after restriction of
-- scalars and apply the canonical composition theorem from Lemma `17.29.2`.
/-- Postcomposition with an `\mathcal O_2`-linear morphism preserves differential operators of
order `k`. -/
theorem isDifferentialOperatorOfOrder_postcompose
    {𝒢 𝒢' : SheafOfModules 𝒪₂.ringSheaf}
    (k : ℕ) (α : 𝒢 ⟶ 𝒢')
    {D : (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj 𝒢}
    (hD : IsDifferentialOperatorOfOrder varphi D k) :
    IsDifferentialOperatorOfOrder varphi
      (D ≫ (SheafOfModules.restrictScalars (ringSheafMap varphi)).map α) k := by
  simpa [Nat.add_zero] using
    isDifferentialOperatorOfOrder_comp varphi hD
      (isDifferentialOperatorOfOrder_restrictScalars_map varphi α)

/-- The covariant functor of order-`k` differential operators out of `\mathcal F`. -/
def differentialOperatorsFunctor (k : ℕ) : SheafOfModules 𝒪₂.ringSheaf ⥤ Type _ where
  obj 𝒢 := differentialOperatorsOfOrder varphi ℱ k 𝒢
  map α D :=
    ⟨D.1 ≫ (SheafOfModules.restrictScalars (ringSheafMap varphi)).map α,
      isDifferentialOperatorOfOrder_postcompose varphi ℱ k α D.2⟩
  map_id 𝒢 := by
    funext D
    cases D
    rfl
  map_comp α β := by
    funext D
    cases D
    rfl

-- Proof sketch: repeat the construction sketched in the source and in Lemma `17.28.2` with the
-- free `\mathcal O_2`-module sheaf generated by `ℱ`, then quotient by the local sections
-- imposing additivity, `\mathcal O_1`-linearity, and vanishing of `(k + 1)`-fold commutators with
-- local `\mathcal O_2`-sections. The quotient universal property identifies maps out of the
-- quotient with order-`k` differential operators, and postcomposition gives the naturality in
-- `\mathcal G`.
/-- Lemma 17.29.3: for an `\mathcal O_2`-module sheaf `\mathcal F` and an integer `k \ge 0`,
there exists an `\mathcal O_2`-module sheaf
`\mathcal P^k_{\mathcal O_2/\mathcal O_1}(\mathcal F)` which represents differential operators of
order `k` out of `\mathcal F`; equivalently, for every `\mathcal O_2`-module sheaf
`\mathcal G`, morphisms
`\mathcal P^k_{\mathcal O_2/\mathcal O_1}(\mathcal F) \to \mathcal G` are canonically and
functorially identified with differential operators
`\mathcal F \to \mathcal G` of order `k`. -/
theorem exists_principal_parts_of_order
    (k : ℕ) :
    (differentialOperatorsFunctor varphi ℱ k).IsCorepresentable := sorry

end

/-! ### Definition_17_29_4 (from Chap17) -/
open CategoryTheory TopologicalSpace TopCat.Sheaf

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X} (varphi : 𝒪₁ ⟶ 𝒪₂)
variable (ℱ : SheafOfModules (ringSheaf 𝒪₂))
variable (k : ℕ)

/- Domain-style sampling for Definition 17.29.4:
- primary domain: sheaf-level principal parts and differential operators relative to
  `𝒪₁ ⟶ 𝒪₂`;
- sampled owner declarations:
  `Functor.CorepresentableBy`,
  `differentialOperatorsFunctor`,
  `exists_principal_parts_of_order`,
  `principal_parts_linear_map_equiv_differential_operators`;
- best owner abstraction: the specialized canonical owner
  `(differentialOperatorsFunctor varphi ℱ k).CorepresentableBy`.

Primitive-vs-derived split:
- primitive data here: none beyond the already defined differential-operator functor;
- derived API: existence of a corepresenting sheaf, already supplied by
  `exists_principal_parts_of_order`.

Source/core/bridge triage:
- `source-facing`: the phrase “`P` is a module of principal parts of order `k` of `ℱ`”;
- `core/canonical`: `(differentialOperatorsFunctor varphi ℱ k).CorepresentableBy`;
- `bridge/view`: the existence theorem in Lemma `17.29.3`.

This numbered definition is recall-only, so the file should use the canonical owner directly and
not keep a second existence theorem with the same interface under a new local name.
-/
/- Definition 17.29.4: a sheaf of `\mathcal O_2`-modules is a module of principal parts of order
`k` of `\mathcal F` relative to `\mathcal O_1 \to \mathcal O_2` precisely when it
corepresents the functor of differential operators of order `k` out of `\mathcal F`. -/
#check (differentialOperatorsFunctor varphi ℱ k).CorepresentableBy

end

/-! ### Lemma_17_29_5 (from Chap17) -/
open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

/- Domain-style sampling for Lemma 17.29.5:
- primary domain: sheafified principal parts of modules over a morphism of sheaves of commutative
  rings on a topological space;
- sampled owner declarations:
  `principal_parts_module`,
  `principalPartsBaseChangeMap`,
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`,
  `TopCat.Sheaf.relativeDifferentials`,
  `CategoryTheory.Functor.CorepresentableBy`;
- best owner abstraction: the source-facing sheafified owner `principalParts`, with
  `principalPartsPresheaf` as its presheaf-level bridge presentation;
- primitive data: the objectwise principal-parts module and its restriction maps assembling into
  `principalPartsPresheaf`;
- derived API: the sheafified owner `principalParts`, its defining equation `principalParts_def`,
  and the corepresentability theorem
  `principalParts_is_principal_parts_module_of_order`.

Source/core/bridge triage:
- `core/canonical`: the sectionwise algebraic owner `principal_parts_module` and its base-change
  map `principalPartsBaseChangeMap`;
- `source-facing`: the sheafified owner `principalParts`;
- `bridge/view`: the presheaf presentation `principalPartsPresheaf` and the defining equation
  `principalParts_def`.
-/

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}

/-- The morphism `𝒪₁(U) → 𝒪₂(U)` on an open set, viewed as an algebra structure. -/
private abbrev sectionAlgebra (varphi : 𝒪₁ ⟶ 𝒪₂) (U : (Opens X)ᵒᵖ) :
    Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) :=
  RingHom.toAlgebra (varphi.hom.app U).hom

/-- The `𝒪₂(U)`-module of sections of `ℱ` on `U`, restricted along `𝒪₁(U) → 𝒪₂(U)`. -/
private abbrev sectionModule (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂))
    (U : (Opens X)ᵒᵖ) : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
  Module.compHom (ℱ.val.obj U) (((ringSheafMap varphi).hom.app U).hom)

/-- The objectwise `k`-th principal-parts module on an open set. -/
private abbrev objectwisePrincipalPartsModule (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) (U : (Opens X)ᵒᵖ) :
    ModuleCat ((ringSheaf 𝒪₂).obj.obj U) :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  show ModuleCat ((ringSheaf 𝒪₂).obj.obj U) from
    ModuleCat.of (𝒪₂.obj.obj U)
      (principal_parts_module (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) k)

private theorem restrictionRing_isScalarTower_right {U V : (Opens X)ᵒᵖ}
    (varphi : 𝒪₁ ⟶ 𝒪₂) (i : U ⟶ V) :
    letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := RingHom.toAlgebra (varphi.hom.app U).hom
    letI : Algebra (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) := RingHom.toAlgebra (𝒪₂.obj.map i).hom
    letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj V) :=
      RingHom.toAlgebra (((varphi.hom.app V).hom).comp ((𝒪₁.obj.map i).hom))
    IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) := by
  sorry

private theorem restrictionModule_isScalarTower_right {U V : (Opens X)ᵒᵖ}
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (i : U ⟶ V) :
    letI : Algebra (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) := RingHom.toAlgebra (𝒪₂.obj.map i).hom
    letI : Module (𝒪₂.obj.obj U) (ℱ.val.obj V) := Module.compHom (ℱ.val.obj V) ((𝒪₂.obj.map i).hom)
    IsScalarTower (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) (ℱ.val.obj V) := by
  letI : Algebra (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) := RingHom.toAlgebra (𝒪₂.obj.map i).hom
  letI : Module (𝒪₂.obj.obj U) (ℱ.val.obj V) := Module.compHom (ℱ.val.obj V) ((𝒪₂.obj.map i).hom)
  exact IsScalarTower.of_compHom (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) (ℱ.val.obj V)

/-- The restriction map on objectwise principal-parts modules. -/
private abbrev objectwisePrincipalPartsRestriction (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    objectwisePrincipalPartsModule varphi ℱ k U ⟶
      (ModuleCat.restrictScalars ((ringSheaf 𝒪₂).obj.map i).hom).obj
        (objectwisePrincipalPartsModule varphi ℱ k V) :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  letI : Algebra (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) := sectionAlgebra varphi V
  letI : Module (𝒪₁.obj.obj V) (ℱ.val.obj V) := sectionModule varphi ℱ V
  letI : IsScalarTower (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V)
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) := RingHom.toAlgebra (𝒪₁.obj.map i).hom
  letI : Algebra (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) := RingHom.toAlgebra (𝒪₂.obj.map i).hom
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj V) :=
    RingHom.toAlgebra (((varphi.hom.app V).hom).comp ((𝒪₁.obj.map i).hom))
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj V) :=
    Module.compHom (ℱ.val.obj V) (((varphi.hom.app V).hom).comp ((𝒪₁.obj.map i).hom))
  letI : Module (𝒪₂.obj.obj U) (ℱ.val.obj V) := Module.compHom (ℱ.val.obj V) ((𝒪₂.obj.map i).hom)
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) :=
    restrictionRing_isScalarTower_right varphi i
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (ℱ.val.obj V) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (ℱ.val.obj V)
  letI : IsScalarTower (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
    restrictionModule_isScalarTower_right ℱ i
  let fUV : ℱ.val.obj U →ₗ[𝒪₂.obj.obj U] ℱ.val.obj V := (ℱ.val.map i).hom
  ModuleCat.ofHom (principalPartsBaseChangeMap k fUV)

-- Proof sketch: the base-change map for principal parts along the identity restriction on an open
-- set is the identity map on the quotient presentation, which matches the identity structure map
-- required in `PresheafOfModules`.
/-- The objectwise principal-parts restriction map is compatible with identity inclusions of opens. -/
private theorem objectwisePrincipalPartsRestriction_id (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) (U : (Opens X)ᵒᵖ) :
    objectwisePrincipalPartsRestriction varphi ℱ k (𝟙 U) =
      (ModuleCat.restrictScalarsId' (((ringSheaf 𝒪₂).obj).map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom (((ringSheaf 𝒪₂).obj).map_id U))).inv.app
          (objectwisePrincipalPartsModule varphi ℱ k U) := sorry

-- Proof sketch: the restriction maps are exactly the principal-parts base-change maps attached to
-- the restriction maps of `𝒪₁`, `𝒪₂`, and `ℱ`; their compatibility with composition is the
-- functoriality statement `principalPartsBaseChangeMap_comp`.
/-- The objectwise principal-parts restriction maps are compatible with composition of opens. -/
private theorem objectwisePrincipalPartsRestriction_comp (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    objectwisePrincipalPartsRestriction varphi ℱ k (i ≫ j) =
      objectwisePrincipalPartsRestriction varphi ℱ k i ≫
        (ModuleCat.restrictScalars (((ringSheaf 𝒪₂).obj).map i).hom).map
          (objectwisePrincipalPartsRestriction varphi ℱ k j) ≫
        (ModuleCat.restrictScalarsComp' (((ringSheaf 𝒪₂).obj).map i).hom
          (((ringSheaf 𝒪₂).obj).map j).hom (((ringSheaf 𝒪₂).obj).map (i ≫ j)).hom
          (congrArg RingCat.Hom.hom (((ringSheaf 𝒪₂).obj).map_comp i j))).inv.app
          (objectwisePrincipalPartsModule varphi ℱ k W) := sorry

/-- The presheaf `U ↦ P^k_{𝒪₂(U)/𝒪₁(U)}(ℱ(U))` of objectwise principal-parts modules. -/
def principalPartsPresheaf (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) :
    PresheafOfModules (ringSheaf 𝒪₂).obj :=
  { obj := objectwisePrincipalPartsModule varphi ℱ k
    map := objectwisePrincipalPartsRestriction varphi ℱ k
    map_id := objectwisePrincipalPartsRestriction_id varphi ℱ k
    map_comp := objectwisePrincipalPartsRestriction_comp varphi ℱ k }

/-- The sheaf `P^k_{𝒪₂/𝒪₁}(ℱ)` obtained by sheafifying the objectwise principal-parts presheaf. -/
noncomputable def principalParts (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) :
    SheafOfModules (ringSheaf 𝒪₂) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf 𝒪₂).obj)).obj
    (principalPartsPresheaf varphi ℱ k)

end

end TopCat.Sheaf
end

notation:max "P^{" k "}_[" φ "](" ℱ ")" =>
  TopCat.Sheaf.principalParts φ ℱ k

noncomputable section

namespace TopCat.Sheaf

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}

/-- The sheaf of principal parts is the sheafification of the objectwise principal-parts
presheaf. -/
theorem principalParts_def (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) :
    P^{k}_[varphi](ℱ) =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf 𝒪₂).obj)).obj
        (principalPartsPresheaf varphi ℱ k) := rfl

/-- The codomain presheaf used by the sheafification adjunction for maps out of `principalParts`;
it is just the underlying presheaf of `𝒢`, viewed through restriction of scalars along the
identity of `ringSheaf 𝒪₂`. -/
private abbrev principalPartsTargetPresheaf (𝒢 : SheafOfModules (ringSheaf 𝒪₂)) :
    PresheafOfModules (ringSheaf 𝒪₂).obj :=
  (PresheafOfModules.restrictScalars (𝟙 (ringSheaf 𝒪₂).obj)).obj 𝒢.val

private noncomputable abbrev objectwisePrincipalPartsLinearEquiv (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) (U : (Opens X)ᵒᵖ) :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
  principal_parts_linear_map_equiv_differential_operators
    (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) k (𝒢.val.obj U)

private noncomputable def principalPartsPresheafHomEquiv (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂)) :
    (principalPartsPresheaf varphi ℱ k ⟶ principalPartsTargetPresheaf 𝒢) ≃
      (differentialOperatorsFunctor varphi ℱ k).obj 𝒢 where
  toFun f := by
    let Dm :
        (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ ⟶
          (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj 𝒢 :=
      ⟨{
        app := fun U ↦
          letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
          letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
          letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
          letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
            IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
          letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
            IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
          let fU :
              principal_parts_module (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) k →ₗ[𝒪₂.obj.obj U]
                𝒢.val.obj U :=
            { toFun := (f.app U).hom
              map_add' := (f.app U).hom.map_add
              map_smul' := (f.app U).hom.map_smul }
          letI : Module ((ringSheaf 𝒪₁).obj.obj U) (ℱ.val.obj U) :=
            Module.compHom (ℱ.val.obj U) (((ringSheafMap varphi).hom.app U).hom)
          letI : Module ((ringSheaf 𝒪₁).obj.obj U) (𝒢.val.obj U) :=
            Module.compHom (𝒢.val.obj U) (((ringSheafMap varphi).hom.app U).hom)
          show ((SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ).val.obj U ⟶
              ((SheafOfModules.restrictScalars (ringSheafMap varphi)).obj 𝒢).val.obj U from
            ModuleCat.ofHom
              { toFun := ((objectwisePrincipalPartsLinearEquiv varphi ℱ 𝒢 k U fU).1)
                map_add' := ((objectwisePrincipalPartsLinearEquiv varphi ℱ 𝒢 k U fU).1).map_add
                map_smul' := ((objectwisePrincipalPartsLinearEquiv varphi ℱ 𝒢 k U fU).1).map_smul }
        naturality := by
          intro U V i
          sorry
      }⟩
    exact ⟨Dm, by
      sorry⟩
  invFun D := by
    refine
      {
        app := fun U ↦
          letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
          letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
          letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
          letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
            IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
          letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
            IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
          let DU : ℱ.val.obj U →ₗ[𝒪₁.obj.obj U] 𝒢.val.obj U :=
            { toFun := (D.1.val.app U).hom
              map_add' := (D.1.val.app U).hom.map_add
              map_smul' := (D.1.val.app U).hom.map_smul }
          ModuleCat.ofHom <|
            (objectwisePrincipalPartsLinearEquiv varphi ℱ 𝒢 k U).symm
              ⟨DU, by
                sorry⟩
        naturality := by
          intro U V i
          sorry
      }
  left_inv f := by
    sorry
  right_inv D := by
    sorry

-- Proof sketch: argue exactly as in Lemma `17.28.4`, replacing Kähler differentials by
-- `principal_parts_module`. On each open set, Lemma `10.133.3` gives the universal
-- principal-parts representation, and the sheafification adjunction upgrades these objectwise
-- universal properties to the sheaf-level representing property from Lemma `17.29.3`.
/-- Lemma 17.29.5: the sheaf `P^k_{𝒪₂/𝒪₁}(ℱ)`, equivalently the sheaf associated to the
presheaf `U ↦ P^k_{𝒪₂(U)/𝒪₁(U)}(ℱ(U))`, is a module of principal parts of order `k` of `ℱ`
relative to `𝒪₁ ⟶ 𝒪₂`. -/
noncomputable def principalParts_is_principal_parts_module_of_order
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) :
    (differentialOperatorsFunctor varphi ℱ k).CorepresentableBy
      P^{k}_[varphi](ℱ) where
  homEquiv {𝒢} :=
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒪₂).obj)).trans
      (principalPartsPresheafHomEquiv varphi ℱ k 𝒢)
  homEquiv_comp {𝒢 𝒢'} α f := by
    sorry

end

end TopCat.Sheaf
end

/-! ### Lemma_17_29_6 (from Chap17) -/
open CategoryTheory MonoidalCategory TopologicalSpace
open PresheafOfModules.DifferentialsConstruction
open TopCat.Sheaf

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
variable (varphi : 𝒪₁ ⟶ 𝒪₂)
variable (ℱ : SheafOfModules (ringSheaf 𝒪₂))
local infixr:70 " ⊗ " => _root_.moduleTensor

/-- The morphism `𝒪₁(U) → 𝒪₂(U)` on an open set, viewed as an algebra structure. -/
private abbrev sectionAlgebra (U : (Opens X)ᵒᵖ) :
    Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) :=
  RingHom.toAlgebra (varphi.hom.app U).hom

/-- The `𝒪₁(U)`-module structure on `ℱ(U)` induced by restriction of scalars along
`𝒪₁(U) → 𝒪₂(U)`. -/
private abbrev sectionModule (U : (Opens X)ᵒᵖ) :
    Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
  Module.compHom (ℱ.val.obj U) (((ringSheafMap varphi).hom.app U).hom)

/- Domain-style sampling for Lemma 17.29.6:
- primary domain: the first principal-parts exact sequence for sheaves of modules over a morphism
  of sheaves of commutative rings;
- sampled owner declarations:
  `TopCat.Sheaf.principalParts`,
  `TopCat.Sheaf.principalParts_is_principal_parts_module_of_order`,
  `TopCat.Sheaf.relativeDifferentials`,
  `_root_.moduleTensor`,
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
- `core/canonical`: `TopCat.Sheaf.principalParts`, `Ω(varphi)`, `_root_.moduleTensor`,
  `Functor.CorepresentableBy`, and `ShortComplex`;
- `bridge/view`: the sheafified cotangent comparison map and the naturality morphisms it induces.
-/

namespace TopCat.Sheaf.principalParts

-- Proof sketch: the identity on `ℱ`, viewed after restriction of scalars along
-- `ringSheafMap varphi`, is sectionwise `\mathcal O_2`-linear and hence an order-one
-- differential operator.
private theorem id_isDifferentialOperatorOfOrder_one :
    IsDifferentialOperatorOfOrder varphi
      (𝟙 ((SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ)) 1 := by
  sorry

/-- The canonical projection `P^1_{𝒪₂/𝒪₁}(ℱ) \to ℱ`, obtained from the representing property of
`P^{1}_[varphi](ℱ)` by evaluating at the identity differential operator of `ℱ`. -/
noncomputable def projection :
    P^{1}_[varphi](ℱ) ⟶ ℱ :=
  ((principalParts_is_principal_parts_module_of_order varphi ℱ 1).homEquiv).symm
    ⟨𝟙 ((SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ),
      id_isDifferentialOperatorOfOrder_one varphi ℱ⟩

/-- The universal order-one differential operator
`ℱ → P^{1}_[varphi](ℱ)` represented by first principal parts. -/
private noncomputable abbrev universalDifferentialOperator
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) :
    (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj (P^{1}_[varphi](ℱ)) :=
  ((principalParts_is_principal_parts_module_of_order varphi ℱ 1).homEquiv
    (𝟙 (P^{1}_[varphi](ℱ)))).1

private theorem universalDifferentialOperator_isDifferentialOperatorOfOrder
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) :
    IsDifferentialOperatorOfOrder varphi
      (universalDifferentialOperator varphi ℱ) 1 :=
  ((principalParts_is_principal_parts_module_of_order varphi ℱ 1).homEquiv
    (𝟙 (P^{1}_[varphi](ℱ)))).2

/-- The objectwise tensor-source presheaf
`U ↦ Ω[𝒪₂(U)⁄𝒪₁(U)] ⊗_{𝒪₂(U)} ℱ(U)` underlying the sheaf map to principal parts. -/
private abbrev tensorSourcePresheaf :
    PresheafOfModules (ringSheaf 𝒪₂).obj :=
  PresheafOfModules.Monoidal.tensorObj (relativeDifferentials' varphi.hom) ℱ.val

/-- The sectionwise canonical map
`Ω[𝒪₂(U)⁄𝒪₁(U)] ⊗_{𝒪₂(U)} ℱ(U) → P^1_{𝒪₂(U)/𝒪₁(U)}(ℱ(U))`,
assembled into a morphism of presheaves. -/
private noncomputable def cotangentToPresheaf :
    tensorSourcePresheaf varphi ℱ ⟶ principalPartsPresheaf varphi ℱ 1 where
  app U := by
    letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
    letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
    letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
      IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
    change
      ModuleCat.of (𝒪₂.obj.obj U)
          (TensorProduct (𝒪₂.obj.obj U)
            (KaehlerDifferential (𝒪₁.obj.obj U) (𝒪₂.obj.obj U)) (ℱ.val.obj U)) ⟶
        ModuleCat.of (𝒪₂.obj.obj U)
          (principal_parts_module (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) 1)
    exact
      ModuleCat.ofHom
        (principalPartsCotangentToPrincipalParts
          (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U))
  naturality := by
    intro U V i
    sorry

/-- The inverse of the sheafification counit for the underlying presheaf of `ℱ`. -/
private noncomputable abbrev sheafificationCounitInv :
    ℱ ⟶ (moduleSheafification 𝒪₂).obj ℱ.val :=
  by
    let e := asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒪₂).obj)).counit
    exact (e.symm.app ℱ).hom

/-- The canonical left map
`\Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F
  \to \mathcal P^1_{\mathcal O_2/\mathcal O_1}(\mathcal F)`,
obtained by sheafifying the sectionwise algebraic map from Lemma `10.133.6`. -/
noncomputable def cotangentTo :
    Ω(varphi) ⊗ ℱ ⟶ P^{1}_[varphi](ℱ) :=
  moduleTensorMap (𝟙 (Ω(varphi))) (sheafificationCounitInv ℱ) ≫
    (moduleSheafificationTensorIso 𝒪₂ (relativeDifferentials' varphi.hom) ℱ.val).hom ≫
    (moduleSheafification 𝒪₂).map (cotangentToPresheaf varphi ℱ)

-- Proof sketch: objectwise this is exactly the algebraic identity
-- `principalPartsCotangentToPrincipalParts ≫ principalPartsProjection = 0` from
-- Lemma `10.133.6`, transported through the sheafification/tensor comparisons above.
@[reassoc]
theorem cotangentTo_comp_projection :
    cotangentTo varphi ℱ ≫ projection varphi ℱ = 0 := by
  sorry

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

-- Proof sketch: apply the sectionwise short exact principal-parts sequence from
-- Lemma `10.133.6`, transport the source and middle terms through Lemmas `17.28.4` and `17.29.5`,
-- and identify the resulting right map with `projection`.
/-- Lemma 17.29.6: there is a canonical short exact sequence
`0 ⟶ \Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F
  ⟶ \mathcal P^1_{\mathcal O_2/\mathcal O_1}(\mathcal F) ⟶ \mathcal F ⟶ 0`,
called the sequence of principal parts. -/
theorem sequence_shortExact :
    (sequence varphi ℱ).ShortExact := by
  sorry

/-- The canonical map on first principal-parts sheaves induced by a morphism of
`\mathcal O_2`-module sheaves. -/
noncomputable def map
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    P^{1}_[varphi](ℱ) ⟶ P^{1}_[varphi](𝒢) :=
  ((principalParts_is_principal_parts_module_of_order varphi ℱ 1).homEquiv).symm
    ⟨(SheafOfModules.restrictScalars (ringSheafMap varphi)).map α ≫
        universalDifferentialOperator varphi 𝒢,
      by
        simpa [Nat.zero_add] using
          isDifferentialOperatorOfOrder_comp varphi
            (isDifferentialOperatorOfOrder_restrictScalars_map varphi α)
            (universalDifferentialOperator_isDifferentialOperatorOfOrder varphi 𝒢)⟩

-- Proof sketch: both sides are the sheafified version of the sectionwise naturality of
-- `Module.principalPartsProjection`.
@[reassoc]
theorem projection_naturality
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    map varphi α ≫ projection varphi 𝒢 =
      projection varphi ℱ ≫ α := by
  sorry

-- Proof sketch: both sides are the sheafified version of the sectionwise naturality of
-- `Module.principalPartsCotangentToPrincipalParts`.
@[reassoc]
theorem cotangentTo_naturality
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    moduleTensorMap (𝟙 (Ω(varphi))) α ≫ cotangentTo varphi 𝒢 =
      cotangentTo varphi ℱ ≫ map varphi α := by
  sorry

/-- The canonical morphism of principal-parts sequences induced by a morphism of
`\mathcal O_2`-module sheaves. -/
noncomputable def sequenceMap
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)} (α : ℱ ⟶ 𝒢) :
    sequence varphi ℱ ⟶ sequence varphi 𝒢 :=
  ShortComplex.homMk
    (moduleTensorMap (𝟙 (Ω(varphi))) α)
    (map varphi α)
    α
    (cotangentTo_naturality varphi α)
    (projection_naturality varphi α)

end TopCat.Sheaf.principalParts

end

/-! ### Remark_17_29_7 (from Chap17) -/
open CategoryTheory Opposite TopologicalSpace MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal
open PresheafOfModules.DifferentialsConstruction
open TopCat.Sheaf

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable {𝒜 𝒜' 𝒜'' : TopCat.Sheaf CommRingCat.{u} X}
variable {𝒝 𝒝' 𝒝'' : TopCat.Sheaf CommRingCat.{u} X}
local infixr:70 " ⊗ " => _root_.moduleTensor

-- Order-`k` differential operators are automatically order-`k + 1`.
theorem isDifferentialOperatorOfOrder_succ_of_isDifferentialOperatorOfOrder
    {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
    (varphi : 𝒪₁ ⟶ 𝒪₂)
    {ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)}
    {k : ℕ}
    {D : (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj 𝒢}
    (hD : IsDifferentialOperatorOfOrder varphi D k) :
    IsDifferentialOperatorOfOrder varphi D (k + 1) := by
  intro U
  let _ : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := (varphi.hom.app U).hom.toAlgebra
  let _ : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
    Module.compHom (ℱ.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) :=
    Module.compHom (𝒢.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
  let _ : SMulCommClass (𝒪₂.obj.obj U) (𝒪₁.obj.obj U) (ℱ.val.obj U) := inferInstance
  let _ : SMulCommClass (𝒪₂.obj.obj U) (𝒪₁.obj.obj U) (𝒢.val.obj U) := inferInstance
  let DU : ℱ.val.obj U →ₗ[𝒪₁.obj.obj U] 𝒢.val.obj U :=
    appLinearMap varphi D U
  have hDU :
      DU.IsDifferentialOperatorOfOrder (𝒪₂.obj.obj U) k := by
    simpa [DU, TopCat.Sheaf.appIsDifferentialOperatorOfOrder, TopCat.Sheaf.appLinearMap] using
      TopCat.Sheaf.isDifferentialOperatorOfOrder_app varphi D hD U
  have hmono :
      ∀ {n : ℕ} {D' : ℱ.val.obj U →ₗ[𝒪₁.obj.obj U] 𝒢.val.obj U},
        D'.IsDifferentialOperatorOfOrder (𝒪₂.obj.obj U) n →
          D'.IsDifferentialOperatorOfOrder (𝒪₂.obj.obj U) (n + 1) := by
    intro n D' hD'
    induction n generalizing D' with
    | zero =>
        rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff D' 0] at ⊢
        intro g
        have hg : D'.scalarCommutator g = 0 := hD' g
        rw [hg,
          LinearMap.isDifferentialOperatorOfOrder_zero_iff
            (0 : ℱ.val.obj U →ₗ[𝒪₁.obj.obj U] 𝒢.val.obj U)]
        intro g' m
        simp
    | succ n ih =>
        rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff D' n] at hD'
        rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff D' (n + 1)] at ⊢
        intro g
        exact ih (hD' g)
  have hsucc :
      DU.IsDifferentialOperatorOfOrder (𝒪₂.obj.obj U) (k + 1) := by
    exact hmono hDU
  simpa [TopCat.Sheaf.appIsDifferentialOperatorOfOrder, TopCat.Sheaf.appLinearMap] using hsucc

/- Domain-style sampling for Remark 17.29.7:
- primary domain: base change for the first principal-parts sequence on a fixed topological space;
- sampled owner declarations:
  `CategoryTheory.CommSq`,
  `TopCat.Sheaf.principalParts`,
  `TopCat.Sheaf.relativeDifferentialsMap`,
  `Functor.LaxMonoidal.μ`;
- best owner abstraction: the source-facing sheaf `P^{k}_[varphi](ℱ)`, with the algebraic
  `principalPartsBaseChangeMap` used only sectionwise as a bridge for the middle term,
  `relativeDifferentialsMap` supplying the canonical left edge on cotangent terms,
  the source-facing tensor owner `moduleTensor` bridged through sheafification to the presheaf
  comparison `Functor.LaxMonoidal.μ` for `PresheafOfModules.restrictScalars`, and `CommSq` as the
  canonical owner for the ring-square input;
- primitive data: a commutative square `CommSq a varphi varphi' β` of sheaves of rings and a
  `\mathcal B`-linear map
  `ℱ ⟶ β_* ℱ'`;
- derived API: the induced canonical sheaf morphism on principal parts; compatibility with further
  composition and with the principal-parts projection is theorem-shaped API derived from this
  owner.

Source/core/bridge triage:
- `source-facing`: the induced sheaf morphism
  `P^{k}_[varphi](ℱ) ⟶ β_* P^{k}_[varphi'](ℱ')`;
- `core/canonical`: the sheaf owner `TopCat.Sheaf.principalParts`;
- `bridge/view`: the `CommSq` input square and the objectwise algebraic map
  `principalPartsBaseChangeMap` on the presheaf presentation. -/

namespace TopCat.Sheaf.principalParts

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
    (α : ℱ ⟶ (SheafOfModules.restrictScalars (ringSheafMap β)).obj ℱ')
    (k : ℕ) (U : (Opens X)ᵒᵖ) :
    (principalPartsPresheaf varphi ℱ k).obj U ⟶
      ((PresheafOfModules.restrictScalars (ringSheafMap β).hom).obj
        (principalPartsPresheaf varphi' ℱ' k)).obj U := by
  let _ : Algebra (𝒜.obj.obj U) (𝒝.obj.obj U) := (varphi.hom.app U).hom.toAlgebra
  let _ : Algebra (𝒜.obj.obj U) (𝒜'.obj.obj U) := (a.hom.app U).hom.toAlgebra
  let _ : Algebra (𝒝.obj.obj U) (𝒝'.obj.obj U) := (β.hom.app U).hom.toAlgebra
  let _ : Algebra (𝒜'.obj.obj U) (𝒝'.obj.obj U) := (varphi'.hom.app U).hom.toAlgebra
  let _ : Algebra (𝒜.obj.obj U) (𝒝'.obj.obj U) :=
    ((β.hom.app U).hom.comp (varphi.hom.app U).hom).toAlgebra
  let _ : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (𝒝'.obj.obj U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (𝒜.obj.obj U) (𝒜'.obj.obj U) (𝒝'.obj.obj U) :=
    IsScalarTower.of_algebraMap_eq' (section_square_commutes sq U)
  let _ : Module (𝒜.obj.obj U) (ℱ.val.obj U) :=
    Module.compHom (ℱ.val.obj U) ((varphi.hom.app U).hom)
  let _ : Module (𝒜'.obj.obj U) (ℱ'.val.obj U) :=
    Module.compHom (ℱ'.val.obj U) ((varphi'.hom.app U).hom)
  let _ : Module (𝒝.obj.obj U) (ℱ'.val.obj U) :=
    Module.compHom (ℱ'.val.obj U) ((β.hom.app U).hom)
  let _ : Module (𝒜.obj.obj U) (ℱ'.val.obj U) :=
    Module.compHom (ℱ'.val.obj U) ((a.hom.app U).hom)
  let _ : IsScalarTower (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒜.obj.obj U) (𝒝.obj.obj U) (ℱ.val.obj U)
  let _ : IsScalarTower (𝒜'.obj.obj U) (𝒝'.obj.obj U) (ℱ'.val.obj U) :=
    IsScalarTower.of_compHom (𝒜'.obj.obj U) (𝒝'.obj.obj U) (ℱ'.val.obj U)
  let _ : IsScalarTower (𝒝.obj.obj U) (𝒝'.obj.obj U) (ℱ'.val.obj U) :=
    IsScalarTower.of_compHom (𝒝.obj.obj U) (𝒝'.obj.obj U) (ℱ'.val.obj U)
  let _ : IsScalarTower (𝒜.obj.obj U) (𝒜'.obj.obj U) (ℱ'.val.obj U) :=
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

/-- The objectwise principal-parts base-change maps assemble to a morphism of presheaves. -/
private def presheafBaseChange
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (SheafOfModules.restrictScalars (ringSheafMap β)).obj ℱ')
    (k : ℕ) :
    principalPartsPresheaf varphi ℱ k ⟶
      (PresheafOfModules.restrictScalars (ringSheafMap β).hom).obj
        (principalPartsPresheaf varphi' ℱ' k) where
  app U := sectionBaseChangeHom sq α k U
  naturality := by
    intro U V i
    sorry

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
      isDifferentialOperatorOfOrder_succ_of_isDifferentialOperatorOfOrder
        varphi Dk.2⟩

/-- Remark 17.29.7: a commutative square of sheaves of rings
`\mathcal A \to \mathcal B`, `\mathcal A' \to \mathcal B'` together with a
`\mathcal B`-linear map `\mathcal F \to \beta_* \mathcal F'` induces the canonical base-change
map on sheaves of principal parts
`\mathcal P^k_{\mathcal B/\mathcal A}(\mathcal F) \to
  \beta_* \mathcal P^k_{\mathcal B'/\mathcal A'}(\mathcal F')`. -/
private noncomputable def presentationBaseChangeMap
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (SheafOfModules.restrictScalars (ringSheafMap β)).obj ℱ')
    (k : ℕ) :
    P^{k}_[varphi](ℱ) ⟶
      (SheafOfModules.restrictScalars (ringSheafMap β)).obj (P^{k}_[varphi'](ℱ')) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝).obj)).homEquiv
      (principalPartsPresheaf varphi ℱ k)
      ((SheafOfModules.restrictScalars (ringSheafMap β)).obj
        (P^{k}_[varphi'](ℱ')))).symm
    (presheafBaseChange sq α k ≫
      (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝').obj)).unit.app
          (principalPartsPresheaf varphi' ℱ' k)))

/-- The differential operator represented by the presentation-level base-change map. -/
private noncomputable abbrev baseChangeDifferentialOperator
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (SheafOfModules.restrictScalars (ringSheafMap β)).obj ℱ')
    (k : ℕ) :=
  (principalParts_is_principal_parts_module_of_order varphi ℱ k).homEquiv
    (presentationBaseChangeMap sq α k)

/-- Remark 17.29.7: a commutative square of sheaves of rings
`\mathcal A \to \mathcal B`, `\mathcal A' \to \mathcal B'` together with a
`\mathcal B`-linear map `\mathcal F \to \beta_* \mathcal F'` induces the canonical base-change
map on sheaves of principal parts
`\mathcal P^k_{\mathcal B/\mathcal A}(\mathcal F) \to
  \beta_* \mathcal P^k_{\mathcal B'/\mathcal A'}(\mathcal F')`. -/
noncomputable def baseChangeMap
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (SheafOfModules.restrictScalars (ringSheafMap β)).obj ℱ')
    (k : ℕ) :
    P^{k}_[varphi](ℱ) ⟶
      (SheafOfModules.restrictScalars (ringSheafMap β)).obj (P^{k}_[varphi'](ℱ')) :=
  ((principalParts_is_principal_parts_module_of_order varphi ℱ k).homEquiv).symm
    (baseChangeDifferentialOperator sq α k)

/-- The induced base-change map on principal parts is compatible with the canonical truncation
maps `P^{k + 1} \to P^k`. -/
theorem truncateSucc_baseChange
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (SheafOfModules.restrictScalars (ringSheafMap β)).obj ℱ')
    (k : ℕ) :
    CommSq
      (baseChangeMap sq α (k + 1))
      (truncateSucc varphi ℱ k)
      ((SheafOfModules.restrictScalars (ringSheafMap β)).map (truncateSucc varphi' ℱ' k))
      (baseChangeMap sq α k) := by
  sorry

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
    (α : ℱ ⟶ (SheafOfModules.restrictScalars (ringSheafMap β)).obj ℱ')
    (α' : ℱ' ⟶ (SheafOfModules.restrictScalars (ringSheafMap β')).obj ℱ'')
    (k : ℕ) :
    baseChangeMap (CommSq.horiz_comp sq sq')
        (α ≫ (SheafOfModules.restrictScalars (ringSheafMap β)).map α') k =
      baseChangeMap sq α k ≫
        (SheafOfModules.restrictScalars (ringSheafMap β)).map
          (baseChangeMap sq' α' k) := by
  sorry

/-- The canonical base-change map on first principal parts is compatible with the projection in
the principal-parts sequence. -/
theorem projection_baseChange
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (SheafOfModules.restrictScalars (ringSheafMap β)).obj ℱ') :
    CommSq
      (baseChangeMap sq α 1)
      (projection varphi ℱ)
      ((SheafOfModules.restrictScalars (ringSheafMap β)).map (projection varphi' ℱ'))
      α := by
  sorry

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
    sorry

/-- The canonical tensor comparison for restriction of scalars, obtained by sheafifying the
sectionwise `Functor.LaxMonoidal.μ` comparison. -/
private noncomputable def restrictScalarsTensorComparison
    {β : 𝒝 ⟶ 𝒝'}
    (ℱ' 𝒢' : SheafOfModules (ringSheaf 𝒝')) :
    ((SheafOfModules.restrictScalars (ringSheafMap β)).obj ℱ') ⊗
      ((SheafOfModules.restrictScalars (ringSheafMap β)).obj 𝒢') ⟶
      (SheafOfModules.restrictScalars (ringSheafMap β)).obj (ℱ' ⊗ 𝒢') :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝).obj)).homEquiv
      (PresheafOfModules.Monoidal.tensorObj
        ((PresheafOfModules.restrictScalars (ringSheafMap β).hom).obj ℱ'.val)
        ((PresheafOfModules.restrictScalars (ringSheafMap β).hom).obj 𝒢'.val))
      ((SheafOfModules.restrictScalars (ringSheafMap β)).obj (ℱ' ⊗ 𝒢'))).symm
    (restrictScalarsTensorComparisonPresheaf ℱ' 𝒢' ≫
      (PresheafOfModules.restrictScalars (ringSheafMap β).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒝').obj)).unit.app
          (PresheafOfModules.Monoidal.tensorObj ℱ'.val 𝒢'.val)))

/-- The canonical base-change map on the cotangent term of the principal-parts sequence. -/
noncomputable def cotangentMap
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (SheafOfModules.restrictScalars (ringSheafMap β)).obj ℱ') :
    Ω(varphi) ⊗ ℱ ⟶
      (SheafOfModules.restrictScalars (ringSheafMap β)).obj (Ω(varphi') ⊗ ℱ') :=
  moduleTensorMap (relativeDifferentialsMap varphi varphi' a β sq) α ≫
    restrictScalarsTensorComparison (Ω(varphi')) ℱ'

/-- The canonical base-change maps on first principal parts fit into the left square of the
principal-parts sequence. -/
theorem cotangent_baseChange
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (SheafOfModules.restrictScalars (ringSheafMap β)).obj ℱ') :
    CommSq
      (cotangentMap sq α)
      (cotangentTo varphi ℱ)
      ((SheafOfModules.restrictScalars (ringSheafMap β)).map (cotangentTo varphi' ℱ'))
      (baseChangeMap sq α 1) := by
  sorry

/-- The canonical base-change maps on the first principal-parts sequence assemble to a morphism
of short complexes. -/
noncomputable abbrev baseChangeSequenceMap
    {varphi : 𝒜 ⟶ 𝒝} {varphi' : 𝒜' ⟶ 𝒝'}
    {a : 𝒜 ⟶ 𝒜'} {β : 𝒝 ⟶ 𝒝'}
    (sq : CommSq a varphi varphi' β)
    {ℱ : SheafOfModules (ringSheaf 𝒝)}
    {ℱ' : SheafOfModules (ringSheaf 𝒝')}
    (α : ℱ ⟶ (SheafOfModules.restrictScalars (ringSheafMap β)).obj ℱ') :
    sequence varphi ℱ ⟶
      (sequence varphi' ℱ').map (SheafOfModules.restrictScalars (ringSheafMap β)) :=
  ShortComplex.homMk
    (cotangentMap sq α)
    (baseChangeMap sq α 1)
    α
    (cotangent_baseChange sq α).w
    (projection_baseChange sq α).w

end TopCat.Sheaf.principalParts

end

/-! ### Definition_17_29_8 (from Chap17) -/
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X S : RingedSpace.{u}}
variable (f : X ⟶ S)
variable (ℱ 𝒢 : SheafOfModules.{u} (RingedSpace.ringCatSheaf X))
variable (k : ℕ)

/- Domain-style sampling for Definition 17.29.8:
- primary domain: relative differential operators between module sheaves on a morphism of ringed
  spaces;
- sampled owner declarations:
  `RingedSpace.Hom.inverseImageStructureSheafHomComm`,
  `RingedSpace.ringCatSheaf`,
  `IsDifferentialOperatorOfOrder`,
  `differentialOperatorsFunctor`,
  `Definition_17_28_10`'s ringed-space specialization pattern for `Ω[f]`;
- best owner abstraction: the Chapter 17 functor owner
  `(differentialOperatorsFunctor φ ℱ k).obj 𝒢`, specialized to the inverse-image structure-sheaf
  map `φ := RingedSpace.Hom.inverseImageStructureSheafHomComm f`;
- primitive data: only the ringed-space morphism `f`, the two `𝒪_X`-module sheaves `ℱ`, `𝒢`,
  and the order `k`;
- derived API: the subtype of morphisms together with the proof that they satisfy the relative
  order-`k` differential-operator condition.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization `Diff^k_{X/S}(ℱ, 𝒢)`;
- `core/canonical`: `(differentialOperatorsFunctor φ ℱ k).obj 𝒢`;
- `bridge/view`: specialization along
  `RingedSpace.Hom.inverseImageStructureSheafHomComm f`.

This numbered item only specializes the already-defined Chapter 17 owner to a morphism of ringed
spaces. The main entry should therefore be a direct canonical recall, not a parallel set-valued
wrapper. -/

/- Definition 17.29.8: for a morphism of ringed spaces `f : X ⟶ S`, the relative differential
operators `Diff^k_{X/S}(ℱ, 𝒢)` are the order-`k` differential operators from `ℱ` to `𝒢`
relative to the inverse-image structure-sheaf morphism
`RingedSpace.Hom.inverseImageStructureSheafHomComm f`. -/
#check
  (differentialOperatorsFunctor
    (RingedSpace.Hom.inverseImageStructureSheafHomComm f) ℱ k).obj 𝒢

end AlgebraicGeometry.RingedSpace
