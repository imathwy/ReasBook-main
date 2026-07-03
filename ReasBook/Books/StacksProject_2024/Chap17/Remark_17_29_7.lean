import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap17.Lemma_17_28_8
import StacksProject_2024.Chap17.Lemma_17_29_6

-- Declarations for this item will be appended below by the statement pipeline.

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
