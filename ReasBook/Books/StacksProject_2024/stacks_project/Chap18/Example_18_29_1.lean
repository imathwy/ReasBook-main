import Mathlib
import StacksProject_2024.Chap18.LocallyDirectSummandOfFiniteFree

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/- Domain-style sampling for Example 18.29.1:
- primary domain: duality for sheaves of modules on a ringed site, expressed through the canonical
  tensor/internal-Hom comparison and the resulting left-duality datum;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `ihom.ev`,
  `MonoidalClosed.uncurry`,
  `CategoryTheory.Retract`,
  `CategoryTheory.ExactPairing`,
  `CategoryTheory.BraidedCategory.exactPairing_swap`;
- best owner abstraction: the ambient owner is `ringedSiteModuleCategory J 𝒪`, the source-facing
  local hypothesis is the local retract owner below, the tensor-to-endomorphism comparison is
  induced directly by the closed-structure evaluation, and the left-duality datum is the braided
  bridge packaged by `ExactPairing (ℱ ⟶[Mod] (𝟙_ _)) ℱ`;
- primitive data: a module `ℱ : ringedSiteModuleCategory J 𝒪`, the local retract condition on
  iterated slice sites, and the canonical internal-Hom object `ℱ ⟶[Mod] (𝟙_ _)`;
- derived API: the source-facing explicit split-map reformulation, the tensor-to-endomorphism
  comparison, its isomorphism statement, and the induced exact pairing.

Source/core/bridge triage:
- `source-facing`: the local direct-summand hypothesis and the textbook tensor-to-endomorphism
  statement;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`, `Retract`, `ihom`, and `ExactPairing`;
- `bridge/view`: the explicit split-map companion theorem and the exact pairing obtained by
  swapping the canonical right-dual-style pairing.

The local direct-summand owner therefore uses `Retract` as primitive data, matching the chapter 17
owner style, while the explicit maps `ι` and `π` remain a companion view rather than the main
public owner.
-/

section Duality

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
variable [BraidedCategory (ringedSiteModuleCategory J 𝒪)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "𝒪Mod" => (𝟙_ Mod : Mod)
set_option quotPrecheck false in
local notation A " ⟶[Mod] " B:10 => ((ihom A).obj B)
private abbrev tensorObj (A B : Mod) : Mod :=
  (MonoidalCategoryStruct.tensorObj A B : Mod)

/-- The canonical tensor-to-endomorphism morphism
`\mathcal F \otimes_\mathcal O \mathcal H\!om_\mathcal O(\mathcal F, \mathcal O) \to
\mathcal H\!om_\mathcal O(\mathcal F, \mathcal F)`. -/
noncomputable def unitInternalHomTensorToEnd (ℱ : Mod) :
    tensorObj ℱ (ℱ ⟶[Mod] 𝒪Mod) ⟶ (ℱ ⟶[Mod] ℱ) :=
  MonoidalClosed.curry
    ((β_ (tensorObj ℱ (ℱ ⟶[Mod] 𝒪Mod)) ℱ).inv ≫
      (α_ ℱ (ℱ ⟶[Mod] 𝒪Mod) ℱ).hom ≫
      ℱ ◁ ((β_ (ℱ ⟶[Mod] 𝒪Mod) ℱ).hom ≫ (ihom.ev ℱ).app 𝒪Mod) ≫
      (ρ_ ℱ).hom)

section IsLocallyDirectSummandOfFiniteFree

/-- Helper for Example 18.29.1: a morphism of ringed-site modules is an isomorphism once every
objectwise evaluation map is an isomorphism. -/
private theorem isIso_ofEvaluationMapIsIso
    {M N : Mod} (φ : M ⟶ N)
    (hφ : ∀ U : Cᵒᵖ, IsIso ((SheafOfModules.evaluation (ringSheaf J 𝒪) U).map φ)) :
    IsIso φ := by
  have hIsoPresheaf :
      IsIso
        ((sheafToPresheaf J AddCommGrpCat).map
          ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map φ)) := by
    -- Proof comment: after forgetting module structure and the sheaf condition, evaluation is
    -- just objectwise application, so the hypothesis gives an isomorphism on each component.
    refine (NatTrans.isIso_iff_isIso_app _).2 ?_
    intro U
    let _ : IsIso ((SheafOfModules.evaluation (ringSheaf J 𝒪) U).map φ) := hφ U
    let _ := Functor.map_isIso
      (forget₂ (ModuleCat ((ringSheaf J 𝒪).1.obj U)) AddCommGrpCat)
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) U).map φ)
    simpa [SheafOfModules.evaluation, SheafOfModules.toSheaf]
  have hIsoToSheaf :
      IsIso ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map φ) := by
    -- Proof comment: the sheaf-to-presheaf forgetful functor reflects isomorphisms, so the
    -- presheaf-level isomorphism already upgrades to an isomorphism of additive sheaves.
    let _ :
        IsIso
          ((sheafToPresheaf J AddCommGrpCat).map
            ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map φ)) :=
      hIsoPresheaf
    exact isIso_of_reflects_iso
      ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map φ)
      (sheafToPresheaf J AddCommGrpCat)
  -- Proof comment: finally reflect the additive-sheaf isomorphism back to module sheaves.
  let _ : IsIso ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map φ) := hIsoToSheaf
  exact isIso_of_reflects_iso φ (SheafOfModules.toSheaf (ringSheaf J 𝒪))

/-- Helper for Example 18.29.1: evaluating a morphism at `U` is terminal evaluation on the slice
over `U.unop`. -/
private theorem evaluationOverTerminalMapEq
    (U : Cᵒᵖ) {M N : Mod} (φ : M ⟶ N) :
    (SheafOfModules.evaluation (ringSheaf J 𝒪) U).map φ =
      (SheafOfModules.evaluation ((ringSheaf J 𝒪).over U.unop)
          (Opposite.op (Over.mk (𝟙 U.unop)))).map
        ((SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U.unop))).map φ) := by
  -- Proof comment: after restricting to the slice over `U.unop`, evaluating at `U` is
  -- definitionally evaluation at the terminal object `U ⟶ U`.
  rfl

-- Proof sketch: the statement is local on the ringed site. On a cover where `ℱ` is a retract of a
-- finite free module, the comparison is an isomorphism for the finite free module and hence also
-- for its retract; then descend the local isomorphisms.
/-- Example 18.29.1: if every local restriction of `\mathcal F` becomes a direct summand of a
finite free module on a covering, then the canonical map
`\mathcal F \otimes_\mathcal O \mathcal H\!om_\mathcal O(\mathcal F, \mathcal O) \to
\mathcal H\!om_\mathcal O(\mathcal F, \mathcal F)` is an isomorphism. -/
theorem isIso_unitInternalHomTensorToEnd_of_locallyDirectSummandOfFiniteFree
    (ℱ : Mod)
    [IsLocallyDirectSummandOfFiniteFree ℱ] :
    IsIso (unitInternalHomTensorToEnd ℱ) := by
  -- Route correction: reduce the global comparison to objectwise evaluation and then rewrite each
  -- objectwise goal as terminal evaluation on the slice over `U.unop`.
  refine isIso_ofEvaluationMapIsIso (φ := unitInternalHomTensorToEnd ℱ) ?_
  intro U
  rw [evaluationOverTerminalMapEq (U := U) (φ := unitInternalHomTensorToEnd ℱ)]
  -- TODO: prove the slice-terminal comparison by choosing the local retract cover on `U.unop`,
  -- showing the comparison is an isomorphism for finite free charts, and transporting that fact
  -- along the chosen retracts.
  sorry

/-- The coevaluation morphism
`\eta : \mathcal O \to \mathcal F \otimes_\mathcal O \mathcal H\!om_\mathcal O(\mathcal F,
\mathcal O)` obtained by transporting the identity endomorphism of `\mathcal F` across the
canonical tensor-to-endomorphism isomorphism. -/
private noncomputable def unitInternalHomCoevaluation
    (ℱ : Mod)
    [IsIso (unitInternalHomTensorToEnd ℱ)] :
    𝒪Mod ⟶ tensorObj ℱ (ℱ ⟶[Mod] 𝒪Mod) :=
  MonoidalClosed.curry' (𝟙 ℱ) ≫
    inv (unitInternalHomTensorToEnd ℱ)

section ExactPairingBridge

/-- The braided transpose of the canonical closed-structure evaluation, used only to build the
exact-pairing bridge from the tensor-to-endomorphism isomorphism. -/
private abbrev unitInternalHomEvaluation (ℱ : Mod) :
    tensorObj (ℱ ⟶[Mod] 𝒪Mod) ℱ ⟶ 𝒪Mod :=
  (β_ _ _).hom ≫ (ihom.ev ℱ).app 𝒪Mod

/-- Helper for Example 18.29.1: the coevaluation was defined by transporting the identity of `ℱ`
across the inverse of the tensor-to-endomorphism comparison, so composing back with that
comparison recovers `curry' (𝟙 ℱ)`. -/
private theorem unitInternalHomCoevaluation_comp_tensorToEnd
    (ℱ : Mod)
    [IsIso (unitInternalHomTensorToEnd ℱ)] :
    unitInternalHomCoevaluation ℱ ≫ unitInternalHomTensorToEnd ℱ =
      MonoidalClosed.curry' (𝟙 ℱ) := by
  -- Cancel the inverse introduced in the definition of the coevaluation.
  simp [unitInternalHomCoevaluation, Category.assoc]

/-- Helper for Example 18.29.1: the curried identity of `ℱ` evaluates to the left unitor after
braiding the internal-Hom factor past `ℱ`. -/
private theorem unitInternalHomTensorToEnd_braided_uncurry
    (ℱ : Mod) :
    (β_ (tensorObj ℱ (ℱ ⟶[Mod] 𝒪Mod)) ℱ).hom ≫
        MonoidalClosed.uncurry (unitInternalHomTensorToEnd ℱ) =
      unitInternalHomTensorToEnd ℱ ▷ ℱ ≫
        (β_ ((ihom ℱ).obj ℱ) ℱ).hom ≫
        (ihom.ev ℱ).app ℱ := by
  -- Rewrite `uncurry` as evaluation on the left tensor factor, then move the comparison morphism
  -- past the braiding by naturality.
  rw [MonoidalClosed.uncurry_eq]
  simpa [tensorObj, Category.assoc] using
    congrArg
      (fun k ↦ k ≫ (ihom.ev ℱ).app ℱ)
      (braiding_naturality (unitInternalHomTensorToEnd ℱ) (𝟙 ℱ)).symm

/-- Helper for Example 18.29.1: after postcomposing with the right unitor, evaluating against the
explicit internal-Hom dual agrees with evaluating after the tensor-to-endomorphism comparison. -/
private theorem unitInternalHom_explicitEvaluation_expand
    (ℱ : Mod) :
    (α_ ℱ (ℱ ⟶[Mod] 𝒪Mod) ℱ).hom ≫
        ℱ ◁ unitInternalHomEvaluation ℱ ≫
        (ρ_ ℱ).hom =
      (α_ ℱ (ℱ ⟶[Mod] 𝒪Mod) ℱ).hom ≫
        ℱ ◁ (β_ (ℱ ⟶[Mod] 𝒪Mod) ℱ).hom ≫
        ℱ ◁ (ihom.ev ℱ).app 𝒪Mod ≫
        (ρ_ ℱ).hom := by
  -- Unfold the explicit evaluation once so the remaining blocker is purely braided coherence on
  -- the `(ℱ, ℱ ⟶[Mod] 𝒪Mod, ℱ)` factors.
  simp [unitInternalHomEvaluation, Category.assoc]

private theorem unitInternalHom_explicitEvaluation_uncurry_suffix
    (ℱ : Mod) :
    (α_ ℱ (ℱ ⟶[Mod] 𝒪Mod) ℱ).hom ≫
        ℱ ◁ unitInternalHomEvaluation ℱ ≫
        (ρ_ ℱ).hom =
      (β_ (tensorObj ℱ (ℱ ⟶[Mod] 𝒪Mod)) ℱ).hom ≫
        MonoidalClosed.uncurry (unitInternalHomTensorToEnd ℱ) := by
  -- First expand the explicit evaluation, then rewrite the braided `uncurry` target using the
  -- tensor-left braiding formula and the closed-structure `uncurry_curry` normalization.
  calc
    (α_ ℱ (ℱ ⟶[Mod] 𝒪Mod) ℱ).hom ≫
        ℱ ◁ unitInternalHomEvaluation ℱ ≫
        (ρ_ ℱ).hom =
      (α_ ℱ (ℱ ⟶[Mod] 𝒪Mod) ℱ).hom ≫
        ℱ ◁ (β_ (ℱ ⟶[Mod] 𝒪Mod) ℱ).hom ≫
        ℱ ◁ (ihom.ev ℱ).app 𝒪Mod ≫
        (ρ_ ℱ).hom := by
          simpa using unitInternalHom_explicitEvaluation_expand ℱ
    _ =
      (β_ (tensorObj ℱ (ℱ ⟶[Mod] 𝒪Mod)) ℱ).hom ≫
        MonoidalClosed.uncurry (unitInternalHomTensorToEnd ℱ) := by
          rw [unitInternalHomTensorToEnd, MonoidalClosed.uncurry_curry]
          simp [tensorObj, Category.assoc]

/-- Helper for Example 18.29.1: after postcomposing with the right unitor, evaluating against the
explicit internal-Hom dual agrees with evaluating after the tensor-to-endomorphism comparison. -/
private theorem unitInternalHom_explicitEvaluation_comp_rightUnitor
    (ℱ : Mod) :
    (α_ ℱ (ℱ ⟶[Mod] 𝒪Mod) ℱ).hom ≫
        ℱ ◁ unitInternalHomEvaluation ℱ ≫
        (ρ_ ℱ).hom =
      unitInternalHomTensorToEnd ℱ ▷ ℱ ≫
        (β_ ((ihom ℱ).obj ℱ) ℱ).hom ≫
        (ihom.ev ℱ).app ℱ := by
  -- Route correction: first identify the explicit suffix with the braided `uncurry` normal form,
  -- then apply the generic braided `uncurry` comparison for `unitInternalHomTensorToEnd`.
  calc
    (α_ ℱ (ℱ ⟶[Mod] 𝒪Mod) ℱ).hom ≫
        ℱ ◁ unitInternalHomEvaluation ℱ ≫
        (ρ_ ℱ).hom =
      (β_ (tensorObj ℱ (ℱ ⟶[Mod] 𝒪Mod)) ℱ).hom ≫
        MonoidalClosed.uncurry (unitInternalHomTensorToEnd ℱ) := by
          simpa using unitInternalHom_explicitEvaluation_uncurry_suffix ℱ
    _ =
      unitInternalHomTensorToEnd ℱ ▷ ℱ ≫
        (β_ ((ihom ℱ).obj ℱ) ℱ).hom ≫
        (ihom.ev ℱ).app ℱ := by
          simpa [Category.assoc] using unitInternalHomTensorToEnd_braided_uncurry ℱ

/-- Helper for Example 18.29.1: the curried identity of `ℱ` evaluates to the left unitor after
braiding the internal-Hom factor past `ℱ`. -/
private theorem unitInternalHom_curry'_id_whiskerRight_evaluation
    (ℱ : Mod) :
    MonoidalClosed.curry' (𝟙 ℱ) ▷ ℱ ≫
        (β_ ((ihom ℱ).obj ℱ) ℱ).hom ≫
        (ihom.ev ℱ).app ℱ =
      (λ_ ℱ).hom := by
  -- Rewrite the curried identity as `curry' (𝟙 ℱ)` and then evaluate it directly.
  calc
    MonoidalClosed.curry' (𝟙 ℱ) ▷ ℱ ≫
        (β_ ((ihom ℱ).obj ℱ) ℱ).hom ≫
        (ihom.ev ℱ).app ℱ =
      (β_ 𝒪Mod ℱ).hom ≫
        ℱ ◁ MonoidalClosed.curry' (𝟙 ℱ) ≫
        (ihom.ev ℱ).app ℱ := by
          simp [Category.assoc]
    _ = (β_ 𝒪Mod ℱ).hom ≫ (ρ_ ℱ).hom := by
      -- The universal evaluation identity collapses the curried identity map.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ (β_ 𝒪Mod ℱ).hom ≫ k)
          (MonoidalClosed.whiskerLeft_curry'_ihom_ev_app (𝟙 ℱ))
    _ = (λ_ ℱ).hom := by
      -- The final braiding-right-unitor coherence is standard in a braided monoidal category.
      simpa [Category.assoc] using braiding_rightUnitor ℱ

/-- Helper for Example 18.29.1: the closed-category identity morphism is the curried identity on
`ℱ`. -/
private theorem unitInternalHom_id_eq_curry'_id
    (ℱ : Mod) :
    MonoidalClosed.id ℱ = MonoidalClosed.curry' (𝟙 ℱ) := by
  -- Compare the two candidate identity morphisms after uncurrying.
  apply MonoidalClosed.uncurry_injective
  simp [MonoidalClosed.id]

/-- Helper for Example 18.29.1: once the left-triangle suffix has inserted
`(ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomTensorToEnd ℱ`, the coevaluation prefix can be transported to
the closed-category identity morphism on `ℱ`. -/
private theorem unitInternalHom_coevaluation_whiskerLeft_comp_tensorToEnd
    (ℱ : Mod)
    [IsIso (unitInternalHomTensorToEnd ℱ)] :
    (ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomCoevaluation ℱ ≫
        (ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomTensorToEnd ℱ =
      (ℱ ⟶[Mod] 𝒪Mod) ◁ MonoidalClosed.id ℱ := by
  -- Whisker the defining coevaluation/comparison identity by the dual object, then rewrite the
  -- resulting curried identity into the canonical closed-category identity.
  calc
    (ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomCoevaluation ℱ ≫
        (ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomTensorToEnd ℱ =
      (ℱ ⟶[Mod] 𝒪Mod) ◁ MonoidalClosed.curry' (𝟙 ℱ) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ (ℱ ⟶[Mod] 𝒪Mod) ◁ k)
              (unitInternalHomCoevaluation_comp_tensorToEnd ℱ)
    _ = (ℱ ⟶[Mod] 𝒪Mod) ◁ MonoidalClosed.id ℱ := by
      rw [unitInternalHom_id_eq_curry'_id]

/-- Helper for Example 18.29.1: once the tensor-to-endomorphism comparison has been inserted,
the remaining left-triangle tail is the canonical precomposition action of
`\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal F, \mathcal F)` on
`\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal F, \mathcal O)`. -/
private abbrev unitInternalHom_left_triangle_inserted_tail
    (ℱ : Mod) :
    tensorObj (ℱ ⟶[Mod] 𝒪Mod) ((ihom ℱ).obj ℱ) ⟶ (ℱ ⟶[Mod] 𝒪Mod) :=
  -- This is the canonical precomposition action of endomorphisms of `ℱ` on the dual object
  -- `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal F, \mathcal O)`, written in source order by
  -- inserting the braiding once.
  (β_ (ℱ ⟶[Mod] 𝒪Mod) ((ihom ℱ).obj ℱ)).hom ≫
    MonoidalClosed.comp ℱ ℱ 𝒪Mod

/-- Helper for Example 18.29.1: after rewriting the left-triangle suffix in terms of the inserted
composition tail, the remaining closed-category identity collapses to the right unitor. -/
private theorem unitInternalHom_left_triangle_id_tail
    (ℱ : Mod) :
    (ℱ ⟶[Mod] 𝒪Mod) ◁ MonoidalClosed.id ℱ ≫
        unitInternalHom_left_triangle_inserted_tail ℱ =
      (ρ_ (ℱ ⟶[Mod] 𝒪Mod)).hom := by
  -- Move the inserted identity across the braiding by naturality, then apply the closed-category
  -- identity-composition law and the braided left-unitor coherence.
  have hNat :
      (ℱ ⟶[Mod] 𝒪Mod) ◁ MonoidalClosed.id ℱ ≫
          (β_ (ℱ ⟶[Mod] 𝒪Mod) ((ihom ℱ).obj ℱ)).hom =
        (β_ (ℱ ⟶[Mod] 𝒪Mod) 𝒪Mod).hom ≫
          MonoidalClosed.id ℱ ▷ (ℱ ⟶[Mod] 𝒪Mod) := by
    simpa [Category.assoc] using
      (CategoryTheory.BraidedCategory.braiding_naturality
        (𝟙 (ℱ ⟶[Mod] 𝒪Mod)) (MonoidalClosed.id ℱ)).symm
  have hIdComp :
      MonoidalClosed.id ℱ ▷ (ℱ ⟶[Mod] 𝒪Mod) ≫
          MonoidalClosed.comp ℱ ℱ 𝒪Mod =
        (λ_ (ℱ ⟶[Mod] 𝒪Mod)).hom := by
    -- `id_comp` says that composing with the internal identity does nothing.
    apply (cancel_epi (λ_ (ℱ ⟶[Mod] 𝒪Mod)).inv).1
    simpa [Category.assoc] using MonoidalClosed.id_comp ℱ 𝒪Mod
  calc
    (ℱ ⟶[Mod] 𝒪Mod) ◁ MonoidalClosed.id ℱ ≫
        (β_ (ℱ ⟶[Mod] 𝒪Mod) ((ihom ℱ).obj ℱ)).hom ≫
        MonoidalClosed.comp ℱ ℱ 𝒪Mod =
      (β_ (ℱ ⟶[Mod] 𝒪Mod) 𝒪Mod).hom ≫
        MonoidalClosed.id ℱ ▷ (ℱ ⟶[Mod] 𝒪Mod) ≫
        MonoidalClosed.comp ℱ ℱ 𝒪Mod := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ MonoidalClosed.comp ℱ ℱ 𝒪Mod)
              hNat
    _ =
      (β_ (ℱ ⟶[Mod] 𝒪Mod) 𝒪Mod).hom ≫
        (λ_ (ℱ ⟶[Mod] 𝒪Mod)).hom := by
          rw [hIdComp]
    _ = (ρ_ (ℱ ⟶[Mod] 𝒪Mod)).hom := by
      simpa using CategoryTheory.braiding_leftUnitor (ℱ ⟶[Mod] 𝒪Mod)

/-- Helper for Example 18.29.1: after postcomposing with the left unitor on
`\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal F, \mathcal O)`, the remaining left-triangle
suffix is just the explicit braiding/evaluation composite defining
`unitInternalHomEvaluation ℱ`. -/
private theorem unitInternalHom_left_triangle_suffix_expand
    (ℱ : Mod) :
    (α_ _ _ _).inv ≫
        unitInternalHomEvaluation ℱ ▷ (ℱ ⟶[Mod] 𝒪Mod) ≫
        (λ_ (ℱ ⟶[Mod] 𝒪Mod)).hom =
      (α_ _ _ _).inv ≫
        (β_ (ℱ ⟶[Mod] 𝒪Mod) ℱ).hom ▷ (ℱ ⟶[Mod] 𝒪Mod) ≫
        (ihom.ev ℱ).app 𝒪Mod ▷ (ℱ ⟶[Mod] 𝒪Mod) ≫
        (λ_ (ℱ ⟶[Mod] 𝒪Mod)).hom := by
  -- Unfold the explicit evaluation morphism once so the remaining blocker is purely coherence.
  simp [unitInternalHomEvaluation, Category.assoc]

/-- Helper for Example 18.29.1: the inserted left-triangle tail is literally the braiding
followed by the curried enriched composition morphism `comp ℱ ℱ 𝒪`. -/
private theorem unitInternalHom_left_triangle_inserted_tail_expand
    (ℱ : Mod) :
    unitInternalHom_left_triangle_inserted_tail ℱ =
      (β_ (ℱ ⟶[Mod] 𝒪Mod) ((ihom ℱ).obj ℱ)).hom ≫
        MonoidalClosed.curry (MonoidalClosed.compTranspose ℱ ℱ 𝒪Mod) := by
  -- Rewrite `comp` once to expose the curried composition tail needed by the blocked bridge.
  rw [unitInternalHom_left_triangle_inserted_tail, MonoidalClosed.comp_eq]

-- TODO: after exposing `compTranspose`, the remaining blocker is the explicit tensor-level
-- braiding/associator coherence between the two evaluation branches.
/-- Helper for Example 18.29.1: after expanding `compTranspose`, the remaining left-triangle
comparison is the explicit tensor-level braiding/associator coherence bridge. -/
private theorem unitInternalHom_left_triangle_inserted_tail_tensor_coherence
    (ℱ : Mod) :
    ℱ ◁
          (ℱ ⟶[Mod] 𝒪Mod) ◁
            MonoidalClosed.curry
              ((α_ ℱ ℱ (ℱ ⟶[Mod] 𝒪Mod)).inv ≫
                (β_ ℱ ℱ).inv ▷ (ℱ ⟶[Mod] 𝒪Mod) ≫
                (α_ ℱ ℱ (ℱ ⟶[Mod] 𝒪Mod)).hom ≫
                ℱ ◁ (ihom.ev ℱ).app 𝒪Mod ≫
                (ρ_ ℱ).hom) ≫
        ℱ ◁ (β_ (ℱ ⟶[Mod] 𝒪Mod) ((ihom ℱ).obj ℱ)).hom ≫
        (α_ ℱ ((ihom ℱ).obj ℱ) (ℱ ⟶[Mod] 𝒪Mod)).inv ≫
        (ihom.ev ℱ).app ℱ ▷ (ℱ ⟶[Mod] 𝒪Mod) ≫
        (ihom.ev ℱ).app 𝒪Mod =
      ℱ ◁
          ((α_ (ℱ ⟶[Mod] 𝒪Mod) ℱ (ℱ ⟶[Mod] 𝒪Mod)).inv ≫
            (β_ (ℱ ⟶[Mod] 𝒪Mod) ℱ).hom ▷ (ℱ ⟶[Mod] 𝒪Mod) ≫
            (ihom.ev ℱ).app 𝒪Mod ▷ (ℱ ⟶[Mod] 𝒪Mod) ≫
            (λ_ (ℱ ⟶[Mod] 𝒪Mod)).hom) ≫
        (ihom.ev ℱ).app 𝒪Mod := sorry

/-- Helper for Example 18.29.1: once the tensor-level coherence is repackaged through `curry`,
the inserted left-triangle tail rewrites into the stable closed-monoidal normal form. -/
private theorem unitInternalHom_left_triangle_inserted_tail_curry_normal_form
    (ℱ : Mod) :
    (ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomTensorToEnd ℱ ≫
        (β_ (ℱ ⟶[Mod] 𝒪Mod) ((ihom ℱ).obj ℱ)).hom ≫
        MonoidalClosed.curry (MonoidalClosed.compTranspose ℱ ℱ 𝒪Mod) =
      (α_ (ℱ ⟶[Mod] 𝒪Mod) ℱ (ℱ ⟶[Mod] 𝒪Mod)).inv ≫
        (β_ (ℱ ⟶[Mod] 𝒪Mod) ℱ).hom ▷ (ℱ ⟶[Mod] 𝒪Mod) ≫
        (ihom.ev ℱ).app 𝒪Mod ▷ (ℱ ⟶[Mod] 𝒪Mod) ≫
        (λ_ (ℱ ⟶[Mod] 𝒪Mod)).hom := by
  -- Proof comment: compare both sides after applying `uncurry`, where the hidden
  -- `compTranspose` transport becomes the explicit tensor-level evaluation composite.
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_eq]
  -- Route correction: unfold `compTranspose` only after the outer `uncurry` transport is visible,
  -- so the rewrite matches the true whiskered source type of the composition transpose.
  rw [MonoidalClosed.compTranspose_eq]
  -- Proof comment: the remaining transport has been isolated as the explicit tensor-level
  -- coherence bridge in the preceding helper.
  simpa [unitInternalHomTensorToEnd, tensorObj, Category.assoc, MonoidalClosed.comp_eq] using
    unitInternalHom_left_triangle_inserted_tail_tensor_coherence ℱ

/-- Helper for Example 18.29.1: after factoring away the coevaluation prefix, the remaining
left-triangle transport problem is a suffix-only closed-monoidal comparison between the explicit
evaluation tail and the inserted internal-composition tail. -/
private theorem unitInternalHom_left_triangle_suffix_uncurry_normal_form
    (ℱ : Mod) :
    (α_ _ _ _).inv ≫
        unitInternalHomEvaluation ℱ ▷ (ℱ ⟶[Mod] 𝒪Mod) ≫
        (λ_ (ℱ ⟶[Mod] 𝒪Mod)).hom =
      (ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomTensorToEnd ℱ ≫
        unitInternalHom_left_triangle_inserted_tail ℱ := by
  -- Route correction: rewrite the explicit suffix and the inserted tail into the common
  -- curry-normal form, then compare those normal forms directly.
  rw [unitInternalHom_left_triangle_suffix_expand,
    unitInternalHom_left_triangle_inserted_tail_expand]
  simpa [Category.assoc] using
    (unitInternalHom_left_triangle_inserted_tail_curry_normal_form ℱ).symm

/-- Helper for Example 18.29.1: after postcomposing the first triangle with the left unitor on
`ℱ ⟶[Mod] 𝒪Mod`, the remaining work is the suffix-only comparison between the explicit evaluation
tail and the inserted internal-composition tail. -/
private theorem unitInternalHom_coevaluation_post_leftUnitor
    (ℱ : Mod)
    [IsIso (unitInternalHomTensorToEnd ℱ)] :
    (ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomCoevaluation ℱ ≫
        (α_ _ _ _).inv ≫
        unitInternalHomEvaluation ℱ ▷ (ℱ ⟶[Mod] 𝒪Mod) ≫
        (λ_ (ℱ ⟶[Mod] 𝒪Mod)).hom =
      (ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomCoevaluation ℱ ≫
        (ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomTensorToEnd ℱ ≫
        (β_ (ℱ ⟶[Mod] 𝒪Mod) ((ihom ℱ).obj ℱ)).hom ≫
        MonoidalClosed.comp ℱ ℱ 𝒪Mod := by
  -- Reattach the coevaluation prefix to the suffix-only comparison, which is now isolated as the
  -- sole remaining coherence blocker.
  simpa [unitInternalHom_left_triangle_inserted_tail, Category.assoc] using
    congrArg
      (fun k ↦ (ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomCoevaluation ℱ ≫ k)
      (unitInternalHom_left_triangle_suffix_uncurry_normal_form ℱ)

-- Proof sketch: after applying the tensor-to-endomorphism isomorphism, the first triangle
-- identity becomes the statement that the coevaluation corresponds to the identity of the dual.
private theorem unitInternalHom_coevaluation_evaluation
    (ℱ : Mod)
    [IsIso (unitInternalHomTensorToEnd ℱ)] :
    (ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomCoevaluation ℱ ≫
        (α_ _ _ _).inv ≫
        unitInternalHomEvaluation ℱ ▷ (ℱ ⟶[Mod] 𝒪Mod) =
      (ρ_ (ℱ ⟶[Mod] 𝒪Mod)).hom ≫
        (λ_ (ℱ ⟶[Mod] 𝒪Mod)).inv := by
  -- Route correction: reduce the first triangle to a post-left-unitor suffix bridge, then
  -- transport the coevaluation prefix to the closed-category identity and collapse the remaining
  -- inserted tail with `MonoidalClosed.id_comp`.
  apply (cancel_mono (λ_ (ℱ ⟶[Mod] 𝒪Mod)).hom).1
  calc
    (ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomCoevaluation ℱ ≫
        (α_ _ _ _).inv ≫
        unitInternalHomEvaluation ℱ ▷ (ℱ ⟶[Mod] 𝒪Mod) ≫
        (λ_ (ℱ ⟶[Mod] 𝒪Mod)).hom =
      (ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomCoevaluation ℱ ≫
        (ℱ ⟶[Mod] 𝒪Mod) ◁ unitInternalHomTensorToEnd ℱ ≫
        (β_ (ℱ ⟶[Mod] 𝒪Mod) ((ihom ℱ).obj ℱ)).hom ≫
        MonoidalClosed.comp ℱ ℱ 𝒪Mod := by
          simpa [Category.assoc] using unitInternalHom_coevaluation_post_leftUnitor ℱ
    _ =
      (ℱ ⟶[Mod] 𝒪Mod) ◁ MonoidalClosed.id ℱ ≫
        (β_ (ℱ ⟶[Mod] 𝒪Mod) ((ihom ℱ).obj ℱ)).hom ≫
        MonoidalClosed.comp ℱ ℱ 𝒪Mod := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫
                (β_ (ℱ ⟶[Mod] 𝒪Mod) ((ihom ℱ).obj ℱ)).hom ≫
                MonoidalClosed.comp ℱ ℱ 𝒪Mod)
              (unitInternalHom_coevaluation_whiskerLeft_comp_tensorToEnd ℱ)
    _ = (ρ_ (ℱ ⟶[Mod] 𝒪Mod)).hom := by
      simpa using unitInternalHom_left_triangle_id_tail ℱ
    _ =
      ((ρ_ (ℱ ⟶[Mod] 𝒪Mod)).hom ≫
        (λ_ (ℱ ⟶[Mod] 𝒪Mod)).inv) ≫
        (λ_ (ℱ ⟶[Mod] 𝒪Mod)).hom := by
          simp [Category.assoc]

-- Proof sketch: transporting the identity of `ℱ` across the same tensor-to-endomorphism
-- isomorphism yields the second triangle identity.
private theorem unitInternalHom_evaluation_coevaluation
    (ℱ : Mod)
    [IsIso (unitInternalHomTensorToEnd ℱ)] :
    unitInternalHomCoevaluation ℱ ▷ ℱ ≫
        (α_ _ _ _).hom ≫
        ℱ ◁ unitInternalHomEvaluation ℱ =
      (λ_ ℱ).hom ≫ (ρ_ ℱ).inv := by
  -- Route correction: reduce the triangle identity to the universal evaluation identity for the
  -- curried identity map, leaving only the comparison/evaluation bridge as a suffix lemma.
  apply (cancel_mono (ρ_ ℱ).hom).1
  have hCoevComp :
      unitInternalHomCoevaluation ℱ ≫ unitInternalHomTensorToEnd ℱ =
        MonoidalClosed.curry' (𝟙 ℱ) := by
    -- The coevaluation is defined using the inverse of the comparison morphism.
    simpa using unitInternalHomCoevaluation_comp_tensorToEnd ℱ
  have hEval :
      unitInternalHomCoevaluation ℱ ▷ ℱ ≫
          unitInternalHomTensorToEnd ℱ ▷ ℱ ≫
          (β_ ((ihom ℱ).obj ℱ) ℱ).hom ≫
          (ihom.ev ℱ).app ℱ =
        (λ_ ℱ).hom := by
    have hWhisker :
        unitInternalHomCoevaluation ℱ ▷ ℱ ≫
            unitInternalHomTensorToEnd ℱ ▷ ℱ ≫
            (β_ ((ihom ℱ).obj ℱ) ℱ).hom ≫
            (ihom.ev ℱ).app ℱ =
          MonoidalClosed.curry' (𝟙 ℱ) ▷ ℱ ≫
            (β_ ((ihom ℱ).obj ℱ) ℱ).hom ≫
            (ihom.ev ℱ).app ℱ := by
      -- Whisker the defining equality of the coevaluation by `ℱ`.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ▷ ℱ ≫
            (β_ ((ihom ℱ).obj ℱ) ℱ).hom ≫
            (ihom.ev ℱ).app ℱ)
          hCoevComp
    exact hWhisker.trans (unitInternalHom_curry'_id_whiskerRight_evaluation ℱ)
  have hBridge :
      unitInternalHomCoevaluation ℱ ▷ ℱ ≫
          (α_ _ _ _).hom ≫
          ℱ ◁ unitInternalHomEvaluation ℱ ≫
          (ρ_ ℱ).hom =
        unitInternalHomCoevaluation ℱ ▷ ℱ ≫
          unitInternalHomTensorToEnd ℱ ▷ ℱ ≫
          (β_ ((ihom ℱ).obj ℱ) ℱ).hom ≫
          (ihom.ev ℱ).app ℱ := by
    -- Reattach the coevaluation prefix to the suffix-only evaluation bridge.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ unitInternalHomCoevaluation ℱ ▷ ℱ ≫ k)
        (unitInternalHom_explicitEvaluation_comp_rightUnitor ℱ)
  have hMain :
      unitInternalHomCoevaluation ℱ ▷ ℱ ≫
          (α_ _ _ _).hom ≫
          ℱ ◁ unitInternalHomEvaluation ℱ ≫
          (ρ_ ℱ).hom =
        (λ_ ℱ).hom := by
    exact hBridge.trans hEval
  simpa using hMain.trans (by simp)

@[reducible] private noncomputable def unitInternalHomExactPairingOfIsIso
    (ℱ : Mod)
    [IsIso (unitInternalHomTensorToEnd ℱ)] :
    ExactPairing (ℱ ⟶[Mod] 𝒪Mod) ℱ :=
  letI : ExactPairing ℱ (ℱ ⟶[Mod] 𝒪Mod) :=
    { coevaluation' := unitInternalHomCoevaluation ℱ
      evaluation' := unitInternalHomEvaluation ℱ
      coevaluation_evaluation' := unitInternalHom_coevaluation_evaluation ℱ
      evaluation_coevaluation' := unitInternalHom_evaluation_coevaluation ℱ }
  BraidedCategory.exactPairing_swap ℱ (ℱ ⟶[Mod] 𝒪Mod)

/-- Example 18.29.1 also yields that
`\mathcal H\!om_\mathcal O(\mathcal F, \mathcal O)` is a left dual of `\mathcal F`. In Lean this
left-duality datum is packaged by `CategoryTheory.ExactPairing`. -/
noncomputable instance
    (ℱ : Mod)
    [IsLocallyDirectSummandOfFiniteFree ℱ] :
    ExactPairing (ℱ ⟶[Mod] 𝒪Mod) ℱ :=
  letI : IsIso (unitInternalHomTensorToEnd ℱ) :=
    isIso_unitInternalHomTensorToEnd_of_locallyDirectSummandOfFiniteFree ℱ
  unitInternalHomExactPairingOfIsIso ℱ

end ExactPairingBridge
end IsLocallyDirectSummandOfFiniteFree
end Duality

end SheafOfModules.RingedSite
