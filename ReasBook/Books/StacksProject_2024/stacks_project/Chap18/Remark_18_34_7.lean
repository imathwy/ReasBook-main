import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import StacksProject_2024.Chap18.Definition_18_34_1
import StacksProject_2024.Chap18.Lemma_18_34_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
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

namespace SheafOfModules.RingedSite

local notation "Mod(" O ")" => ringedSiteModuleCategory J O

/-- Helper for Remark 18.34.7: order-`k` differential operators out of `F` with codomain `G`. -/
private abbrev differentialOperatorsOfOrder
    {O₁ O₂ : Sheaf J CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂)) :=
  { D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G //
    IsDifferentialOperatorOfOrder φ D k }

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Remark 18.34.7: restriction of scalars turns an `O₂`-linear morphism into an
order-`0` differential operator relative to `φ`. -/
private theorem isDifferentialOperatorOfOrder_restrictionAlong_map
    {O₁ O₂ : Sheaf J CommRingCat.{u}}
    (φ : O₁ ⟶ O₂)
    {F G : Mod(O₂)} (f : F ⟶ G) :
    IsDifferentialOperatorOfOrder φ ((restrictionAlong φ).map f) 0 := by
  -- Proof comment: evaluate on sections and use the linear-algebra characterization of
  -- order-`0` differential operators as scalar-linear maps over the ambient ring.
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

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Remark 18.34.7: postcomposition with an `O₂`-linear morphism preserves bounded
differential operators. -/
private theorem differentialOperatorsFunctorPostcompose_mem
    {O₁ O₂ : Sheaf J CommRingCat.{u}}
    (φ : O₁ ⟶ O₂)
    {F G G' : Mod(O₂)} {k : ℕ}
    (α : G ⟶ G')
    {D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G}
    (hD : IsDifferentialOperatorOfOrder φ D k) :
    IsDifferentialOperatorOfOrder φ (D ≫ (restrictionAlong φ).map α) k := by
  -- Proof comment: compose the given operator with the order-`0` operator coming from `α`.
  simpa [Nat.add_zero] using
    isDifferentialOperatorOfOrder_comp (φ := φ) (D := D)
      (D' := (restrictionAlong φ).map α) hD
      (isDifferentialOperatorOfOrder_restrictionAlong_map (φ := φ) α)

/-- Helper for Remark 18.34.7: the map part of the bounded-differential-operator functor. -/
private abbrev differentialOperatorsFunctorMap
    {O₁ O₂ : Sheaf J CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ)
    {G G' : Mod(O₂)} (α : G ⟶ G') :
    differentialOperatorsOfOrder φ F k G → differentialOperatorsOfOrder φ F k G' :=
  fun D ↦
    ⟨D.1 ≫ (restrictionAlong φ).map α,
      differentialOperatorsFunctorPostcompose_mem (φ := φ) α D.2⟩

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Remark 18.34.7: the differential-operator map associated to the identity is the
identity function. -/
private theorem differentialOperatorsFunctor_map_id
    {O₁ O₂ : Sheaf J CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) (G : Mod(O₂)) :
    differentialOperatorsFunctorMap φ F k (𝟙 G) = id := by
  -- Proof comment: the subtype data is definitionally unchanged after composing with `𝟙`.
  funext D
  cases D
  rfl

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Remark 18.34.7: postcomposition of codomain maps matches functorial composition
on bounded differential operators. -/
private theorem differentialOperatorsFunctor_map_comp
    {O₁ O₂ : Sheaf J CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ)
    {G G' G'' : Mod(O₂)} (α : G ⟶ G') (β : G' ⟶ G'') :
    differentialOperatorsFunctorMap φ F k (α ≫ β) =
      differentialOperatorsFunctorMap φ F k β ∘ differentialOperatorsFunctorMap φ F k α := by
  -- Proof comment: both sides are definitionally the same postcomposition on the underlying map.
  funext D
  cases D
  rfl

/-- Helper for Remark 18.34.7: the covariant functor sending `G` to order-`k` differential
operators from `F` to `G`. -/
def differentialOperatorsFunctor
    {O₁ O₂ : Sheaf J CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) (F : Mod(O₂)) (k : ℕ) :
    Mod(O₂) ⥤ Type _ where
  obj G := differentialOperatorsOfOrder φ F k G
  map α := differentialOperatorsFunctorMap φ F k α
  map_id G := differentialOperatorsFunctor_map_id φ F k G
  map_comp α β := differentialOperatorsFunctor_map_comp φ F k α β

/-- Helper for Remark 18.34.7: the universal order-`k` differential operator attached to a
chosen corepresenting object. -/
def principalPartsDifferentialOperator
    {O₁ O₂ : Sheaf J CommRingCat.{u}} {φ : O₁ ⟶ O₂} {F : Mod(O₂)} {k : ℕ}
    {P : Mod(O₂)}
    (hP : (differentialOperatorsFunctor φ F k).CorepresentableBy P) :
    (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj P :=
  (hP.homEquiv (𝟙 P)).1

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Remark 18.34.7: under the representing equivalence, a morphism `α : P ⟶ G`
corresponds to postcomposing the universal differential operator by `α`. -/
private theorem homEquiv_apply_eq_principalPartsDifferentialOperator_comp
    {O₁ O₂ : Sheaf J CommRingCat.{u}} {φ : O₁ ⟶ O₂} {F : Mod(O₂)} {k : ℕ}
    {P : Mod(O₂)}
    (hP : (differentialOperatorsFunctor φ F k).CorepresentableBy P)
    {G : Mod(O₂)} (α : P ⟶ G) :
    (hP.homEquiv α).1 =
      principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map α := by
  -- Proof comment: unwrap the `CorepresentableBy` naturality statement and forget the proof field.
  simpa [principalPartsDifferentialOperator] using
    congrArg Subtype.val (Functor.CorepresentableBy.homEquiv_eq hP α)

end SheafOfModules.RingedSite

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
      principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map τ = D := by
  -- Route correction: rebuild the minimal principal-parts corepresentability API locally so this
  -- proof no longer depends on the broken later import `Lemma_18_34_3`.
  let D' : (differentialOperatorsFunctor φ F k).obj (principalPartsBaseChangeTarget β P') :=
    ⟨D, hD⟩
  refine ⟨hP.homEquiv.symm D', ?_, ?_⟩
  · -- Proof comment: the representing equivalence sends the chosen factorization back to `D`.
    have hhomEquiv :
        (hP.homEquiv (hP.homEquiv.symm D')).1 =
          principalPartsDifferentialOperator hP ≫
            (restrictionAlong φ).map (hP.homEquiv.symm D') := by
      exact homEquiv_apply_eq_principalPartsDifferentialOperator_comp hP (hP.homEquiv.symm D')
    have h := congrArg Subtype.val (hP.homEquiv.apply_symm_apply D')
    rw [hhomEquiv] at h
    simpa [D'] using h
  · intro τ hτ
    -- Proof comment: uniqueness follows because equal composites have equal images under
    -- the representing equivalence, and `homEquiv` is injective.
    apply hP.homEquiv.injective
    apply Subtype.ext
    calc
      (hP.homEquiv τ).1 =
          principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map τ := by
        exact homEquiv_apply_eq_principalPartsDifferentialOperator_comp hP τ
      _ = D := hτ
      _ = (hP.homEquiv (hP.homEquiv.symm D')).1 := by
        simpa [D'] using congrArg Subtype.val (hP.homEquiv.apply_symm_apply D').symm

end
