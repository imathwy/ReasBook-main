import StacksProject_2024.stacks_project.Chap21.Lemma_21_34_3_Owner
import StacksProject_2024.stacks_project.Chap21.Example_21_48_2_Core

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section DualitySetup

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

open SheafOfModules.RingedSite.CochainComplex

/-- The dual complex `F^∨ = Hom(F, 𝟙_)` on cochain complexes of `𝒪`-modules on a ringed site,
realized as internal Hom into the tensor unit. -/
noncomputable abbrev ringedSiteModuleComplexDual
    [MonoidalCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) : Cpx :=
  (ihom F).obj (𝟙_ Cpx)

@[inherit_doc ringedSiteModuleComplexDual]
notation:max F:max "^∨" => ringedSiteModuleComplexDual F

/-- The canonical morphism `K ⊗ F^∨ ⟶ Hom(F, K)`. -/
private noncomputable def ringedSiteModuleComplexEvaluationHom
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F K : Cpx) :
    K ⊗ F^∨ ⟶ (ihom F).obj K :=
  ringedSiteModuleComplexTensorInternalHomComparison K (𝟙_ Cpx) F ≫
    (ihom F).map (ρ_ K).hom

/-- The canonical tensor-to-endomorphism morphism `F ⊗ F^∨ ⟶ Hom(F, F)`. -/
noncomputable abbrev ringedSiteModuleComplexDualTensorToEnd
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    F ⊗ F^∨ ⟶ (ihom F).obj F :=
  ringedSiteModuleComplexEvaluationHom F F

/-- The source-facing evaluation morphism `F^∨ ⊗ F ⟶ 𝟙_` for the internal-Hom dual complex. -/
noncomputable def ringedSiteModuleComplexDualEvaluation
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    F^∨ ⊗ F ⟶ 𝟙_ Cpx :=
  (β_ F^∨ F).hom ≫
    (ihom.ev F).app (𝟙_ Cpx)

/-- The source-facing coevaluation morphism `𝟙_ ⟶ F ⊗ F^∨` obtained from `𝟙 F` via the
tensor-to-endomorphism isomorphism. -/
noncomputable def ringedSiteModuleComplexDualCoevaluation
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx)
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    𝟙_ Cpx ⟶ F ⊗ F^∨ :=
  MonoidalClosed.curry' (𝟙 F) ≫
    inv (ringedSiteModuleComplexDualTensorToEnd F)

omit [HasWeakSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat]
  [∀ U : C, (J.over U).HasSheafCompose
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat] in
/-- Composing the coevaluation with the canonical comparison recovers the curried identity of
`F`. This is the defining specification of `ringedSiteModuleComplexDualCoevaluation`. -/
@[reassoc, simp]
theorem ringedSiteModuleComplexDualCoevaluation_comp_tensorToEnd
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx)
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    ringedSiteModuleComplexDualCoevaluation F ≫ ringedSiteModuleComplexDualTensorToEnd F =
      MonoidalClosed.curry' (𝟙 F) := by
  simp [ringedSiteModuleComplexDualCoevaluation]

/-- Helper for Example 21.48.2: uncurrying the source-facing evaluation morphism recovers the
tensor-unit specialization of the canonical tensor/internal-Hom comparison, followed by the right
unitor in the target internal Hom. -/
@[simp] private theorem ringedSiteModuleComplexEvaluationHom_uncurry
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F K : Cpx) :
    MonoidalClosed.uncurry (ringedSiteModuleComplexEvaluationHom F K) =
      (α_ F K F^∨).inv ≫
        (β_ F K).hom ▷ F^∨ ≫
        (α_ K F F^∨).hom ≫
        K ◁ (ihom.ev F).app (𝟙_ Cpx) ≫
        (ρ_ K).hom := by
  -- Proof comment: the repaired source-facing owner is now the canonical Chapter 21 comparison
  -- specialized at the tensor unit, so its `uncurry` formula is exactly the owner theorem plus
  -- the natural-right transport through the right unitor.
  rw [ringedSiteModuleComplexEvaluationHom, MonoidalClosed.uncurry_natural_right]
  simpa using ringedSiteModuleComplexTensorInternalHomComparison_uncurry K (𝟙_ Cpx) F

/-- Helper for Example 21.48.2: a morphism of `𝒪`-modules is an isomorphism once every objectwise
evaluation map is an isomorphism. -/
private theorem isIso_ofEvaluationMapIsIso
    {M N : Mod} (φ : M ⟶ N)
    (hφ : ∀ U : Cᵒᵖ, IsIso ((SheafOfModules.evaluation (ringSheaf J 𝒪) U).map φ)) :
    IsIso φ := by
  have hIsoPresheaf :
      IsIso
        ((sheafToPresheaf J AddCommGrpCat).map
          ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map φ)) := by
    -- Proof comment: after forgetting module structure and the sheaf condition, objectwise
    -- evaluation is just componentwise application, so the hypotheses give a presheaf isomorphism.
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
    -- presheaf-level isomorphism already upgrades to an additive-sheaf isomorphism.
    let _ :
        IsIso
          ((sheafToPresheaf J AddCommGrpCat).map
            ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map φ)) :=
      hIsoPresheaf
    exact isIso_of_reflects_iso
      ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map φ)
      (sheafToPresheaf J AddCommGrpCat)
  -- Proof comment: reflect the additive-sheaf isomorphism back to the original category of
  -- `𝒪`-modules.
  let _ : IsIso ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map φ) := hIsoToSheaf
  exact isIso_of_reflects_iso φ (SheafOfModules.toSheaf (ringSheaf J 𝒪))

/-- Helper for Example 21.48.2: a morphism of complexes of `𝒪`-modules is an isomorphism once
every objectwise evaluation complex map is an isomorphism. -/
private theorem isIso_ofEvaluationComplexMapIsIso
    {M N : Cpx} (φ : M ⟶ N)
    (hφ : ∀ U : Cᵒᵖ,
      IsIso
        ((((SheafOfModules.evaluation (ringSheaf J 𝒪) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ))) :
    IsIso φ := by
  let hcomp : ∀ n : ℤ, IsIso (φ.f n) := by
    intro n
    refine isIso_ofEvaluationMapIsIso (φ := φ.f n) ?_
    intro U
    let EvalU :
        Cpx ⥤ CochainComplex (ModuleCat ((ringSheaf J 𝒪).1.obj U)) ℤ :=
      (SheafOfModules.evaluation (ringSheaf J 𝒪) U).mapHomologicalComplex (ComplexShape.up ℤ)
    let _ : IsIso (EvalU.map φ) := hφ U
    -- Proof comment: the degree-`n` component of the evaluated complex map is exactly the
    -- evaluation of the degree-`n` morphism.
    simpa using
      (Functor.map_isIso
        (HomologicalComplex.eval (ModuleCat ((ringSheaf J 𝒪).1.obj U)) (ComplexShape.up ℤ) n)
        (EvalU.map φ))
  letI : ∀ n : ℤ, IsIso (φ.f n) := hcomp
  -- Proof comment: a morphism of cochain complexes is an isomorphism once all of its components
  -- are isomorphisms.
  exact HomologicalComplex.Hom.isIso_of_components φ

/-- Helper for Example 21.48.2: evaluating a morphism of cochain complexes at `U` is terminal
evaluation on the localized ringed site over `U.unop`. -/
private theorem evaluationOverTerminalComplexMapEq
    (U : Cᵒᵖ) {M N : Cpx} (φ : M ⟶ N) :
    (((SheafOfModules.evaluation (ringSheaf J 𝒪) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) =
      (((SheafOfModules.evaluation ((ringSheaf J 𝒪).over U.unop)
          (Opposite.op (Over.mk (𝟙 U.unop)))).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (((ringedSiteLocalizedRestriction J 𝒪 U.unop).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ)) := by
  -- Proof comment: after restricting to the slice over `U.unop`, evaluation at `U` is
  -- definitionally evaluation at the terminal object `U ⟶ U`.
  rfl

/-- The canonical tensor-to-endomorphism map is an isomorphism for a complex that is locally
strictly perfect on a ringed site. -/
theorem isIso_ringedSiteModuleComplexDualTensorToEnd_of_isLocallyStrictlyPerfect
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx)
    (hF : IsLocallyStrictlyPerfect F) :
    IsIso (ringedSiteModuleComplexDualTensorToEnd F) := by
  -- Route correction: reduce the global comparison to objectwise evaluation, then rewrite each
  -- objectwise goal as terminal evaluation on the slice over `U.unop`.
  refine isIso_ofEvaluationComplexMapIsIso (φ := ringedSiteModuleComplexDualTensorToEnd F) ?_
  intro U
  rw [evaluationOverTerminalComplexMapEq (U := U) (φ := ringedSiteModuleComplexDualTensorToEnd F)]
  -- TODO: identify this terminal evaluation with the Chapter 15 tensor-to-endomorphism comparison
  -- on terminal sections of the restricted complex, then use the cover from `hF.out U.unop`,
  -- `CochainComplex.IsStrictlyPerfect.bounded`, and
  -- `moduleGlobalSections_mem_finiteProjectiveModuleProperty` to show the evaluated comparison is
  -- an isomorphism on the slice.
  sorry

/-- A locally strictly perfect complex carries the canonical comparison-map isomorphism needed to
form the dual coevaluation map. -/
instance ringedSiteModuleComplexDualTensorToEnd_isIso_of_isLocallyStrictlyPerfect
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    {F : Cpx} [hF : IsLocallyStrictlyPerfect F] :
    IsIso (ringedSiteModuleComplexDualTensorToEnd F) :=
  isIso_ringedSiteModuleComplexDualTensorToEnd_of_isLocallyStrictlyPerfect F hF

/-- Helper for Example 21.48.2: braiding the comparison map past the source complex turns the
uncurried tensor-to-endomorphism comparison into the book-order evaluation composite. -/
private theorem ringedSiteModuleComplexDualTensorToEndBraidedUncurry
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    (β_ (F ⊗ F^∨) F).hom ≫
        MonoidalClosed.uncurry (ringedSiteModuleComplexDualTensorToEnd F) =
      ringedSiteModuleComplexDualTensorToEnd F ▷ F ≫
        (β_ ((ihom F).obj F) F).hom ≫
        (ihom.ev F).app F := by
  -- Proof comment: rewrite `uncurry` as the evaluation of the internal-Hom morphism and then
  -- move the comparison map across the braiding by naturality.
  rw [MonoidalClosed.uncurry_eq]
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ k ≫ (ihom.ev F).app F)
      (braiding_naturality (ringedSiteModuleComplexDualTensorToEnd F) (𝟙 F)).symm

/-- Helper for Example 21.48.2: expanding the explicit evaluation morphism isolates the braided
coherence block and leaves the internal evaluation tail untouched. -/
private theorem ringedSiteModuleComplexDualExplicitEvaluationExpand
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    (α_ F F^∨ F).hom ≫ F ◁ ringedSiteModuleComplexDualEvaluation F ≫ (ρ_ F).hom =
      (α_ F F^∨ F).hom ≫
        F ◁ (β_ F^∨ F).hom ≫
        F ◁ (ihom.ev F).app (𝟙_ Cpx) ≫
        (ρ_ F).hom := by
  -- Proof comment: unfold the explicit evaluation once so the remaining work is purely braided
  -- coherence on the `F`, `F^∨`, and `F` factors.
  simp [ringedSiteModuleComplexDualEvaluation, Category.assoc]

/-- Helper for Example 21.48.2: the self-braiding of `F ⊗ F` squares to the identity, as expected
in the symmetric Koszul braiding on cochain complexes. -/
private theorem ringedSiteModuleComplexBraidingSelfSquareCanonical
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    (β_ F F).hom ≫ (β_ F F).hom = 𝟙 (F ⊗ F) := by
  -- Proof comment: when both tensor factors are `F`, the inverse braiding of `β_ F F` is again
  -- `β_ F F`, so the ordinary `hom_inv_id` identity gives the required square.
  -- TODO: identify the self-braiding inverse with the same morphism in the concrete cochain
  -- complex braiding, then apply `Iso.hom_inv_id`.
  sorry

/-- Helper for Example 21.48.2: the residual braiding-associator composite on
`((F ⊗ F^∨) ⊗ F)` collapses to the book-order evaluation braid. -/
private theorem ringedSiteModuleComplexDualExplicitEvaluationHexagon
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    (β_ (F ⊗ F^∨) F).hom ≫
        (α_ F F F^∨).inv ≫
        (β_ F F).hom ▷ F^∨ ≫
        (α_ F F F^∨).hom =
      (α_ F F^∨ F).hom ≫
        F ◁ (β_ F^∨ F).hom := by
  -- Proof comment: specialize the reverse hexagon to `(F, F^∨, F)` and then collapse the extra
  -- self-braiding square using symmetry on `F ⊗ F`.
  apply (cancel_epi (α_ F F^∨ F).inv).1
  have hHex :
      (α_ F F^∨ F).inv ≫
          (β_ (F ⊗ F^∨) F).hom ≫
          (α_ F F F^∨).inv =
        F ◁ (β_ F^∨ F).hom ≫
          (α_ F F F^∨).inv ≫
          (β_ F F).hom ▷ F^∨ := by
    simpa using (BraidedCategory.hexagon_reverse F F^∨ F)
  have hSym :
      (β_ F F).hom ▷ F^∨ ≫
          (β_ F F).hom ▷ F^∨ =
        𝟙 ((F ⊗ F) ⊗ F^∨) := by
    calc
      (β_ F F).hom ▷ F^∨ ≫
          (β_ F F).hom ▷ F^∨ =
        ((β_ F F).hom ≫ (β_ F F).hom) ▷ F^∨ := by
          rw [comp_whiskerRight]
      _ = 𝟙 ((F ⊗ F) ⊗ F^∨) := by
        simpa using
          congrArg
            (fun k ↦ k ▷ F^∨)
            (ringedSiteModuleComplexBraidingSelfSquareCanonical F)
  calc
    (α_ F F^∨ F).inv ≫
        ((β_ (F ⊗ F^∨) F).hom ≫
          (α_ F F F^∨).inv ≫
          (β_ F F).hom ▷ F^∨ ≫
          (α_ F F F^∨).hom) =
      ((α_ F F^∨ F).inv ≫
          (β_ (F ⊗ F^∨) F).hom ≫
          (α_ F F F^∨).inv) ≫
        (β_ F F).hom ▷ F^∨ ≫
        (α_ F F F^∨).hom := by
          simp [Category.assoc]
    _ =
      (F ◁ (β_ F^∨ F).hom ≫
          (α_ F F F^∨).inv ≫
          (β_ F F).hom ▷ F^∨) ≫
        (β_ F F).hom ▷ F^∨ ≫
        (α_ F F F^∨).hom := by
          rw [hHex]
    _ =
      F ◁ (β_ F^∨ F).hom ≫
        (α_ F F F^∨).inv ≫
        ((β_ F F).hom ▷ F^∨ ≫
          (β_ F F).hom ▷ F^∨) ≫
        (α_ F F F^∨).hom := by
          simp [Category.assoc]
    _ = (α_ F F^∨ F).inv ≫
          (α_ F F^∨ F).hom ≫
          F ◁ (β_ F^∨ F).hom := by
      simp [hSym, Category.assoc]

/-- Helper for Example 21.48.2: the explicit evaluation composite is the braided normal form of
the uncurried tensor-to-endomorphism comparison. -/
private theorem ringedSiteModuleComplexDualExplicitEvaluation_braidedNormalForm
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    (α_ F F^∨ F).hom ≫
        F ◁ (β_ F^∨ F).hom ≫
        F ◁ (ihom.ev F).app (𝟙_ Cpx) ≫
        (ρ_ F).hom =
      (β_ (F ⊗ F^∨) F).hom ≫
        (α_ F F F^∨).inv ≫
        (β_ F F).hom ▷ F^∨ ≫
        (α_ F F F^∨).hom ≫
        F ◁ (ihom.ev F).app (𝟙_ Cpx) ≫
        (ρ_ F).hom := by
  -- Proof comment: normalize the braiding/associator block with the specialized hexagon while
  -- leaving the final evaluation and right unitor tail untouched.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ k ≫ F ◁ (ihom.ev F).app (𝟙_ Cpx) ≫ (ρ_ F).hom)
      (ringedSiteModuleComplexDualExplicitEvaluationHexagon F).symm

/-- Helper for Example 21.48.2: the braided explicit-evaluation normal form is exactly the
braided `uncurry` of `ringedSiteModuleComplexDualTensorToEnd`. -/
private theorem ringedSiteModuleComplexDualExplicitEvaluation_uncurry_bridge
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    (β_ (F ⊗ F^∨) F).hom ≫
        (α_ F F F^∨).inv ≫
        (β_ F F).hom ▷ F^∨ ≫
        (α_ F F F^∨).hom ≫
        F ◁ (ihom.ev F).app (𝟙_ Cpx) ≫
        (ρ_ F).hom =
      (β_ (F ⊗ F^∨) F).hom ≫
        MonoidalClosed.uncurry (ringedSiteModuleComplexDualTensorToEnd F) := by
  -- Proof comment: reuse the repaired `uncurry` formula for the source-facing evaluation owner,
  -- then postcompose it with the same outer braiding seen in the explicit suffix.
  have hUncurry :
      MonoidalClosed.uncurry (ringedSiteModuleComplexDualTensorToEnd F) =
        (α_ F F F^∨).inv ≫
          (β_ F F).hom ▷ F^∨ ≫
          (α_ F F F^∨).hom ≫
          F ◁ (ihom.ev F).app (𝟙_ Cpx) ≫
          (ρ_ F).hom := by
    simpa using ringedSiteModuleComplexEvaluationHom_uncurry F F
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ (β_ (F ⊗ F^∨) F).hom ≫ k)
      hUncurry.symm

/-- Helper for Example 21.48.2: after expanding the explicit evaluation suffix, the resulting
book-order composite is exactly the braided `uncurry` of the tensor-to-endomorphism comparison. -/
private theorem ringedSiteModuleComplexDualExplicitEvaluationUncurrySuffix
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    (α_ F F^∨ F).hom ≫ F ◁ ringedSiteModuleComplexDualEvaluation F ≫ (ρ_ F).hom =
      (β_ (F ⊗ F^∨) F).hom ≫
        MonoidalClosed.uncurry (ringedSiteModuleComplexDualTensorToEnd F) := by
  -- Proof comment: expand the explicit evaluation, normalize the braided middle block, and then
  -- identify the result with the repaired `uncurry` formula for the comparison map.
  calc
    (α_ F F^∨ F).hom ≫ F ◁ ringedSiteModuleComplexDualEvaluation F ≫ (ρ_ F).hom =
      (α_ F F^∨ F).hom ≫
        F ◁ (β_ F^∨ F).hom ≫
        F ◁ (ihom.ev F).app (𝟙_ Cpx) ≫
        (ρ_ F).hom := by
          simpa using ringedSiteModuleComplexDualExplicitEvaluationExpand F
    _ =
      (β_ (F ⊗ F^∨) F).hom ≫
        (α_ F F F^∨).inv ≫
        (β_ F F).hom ▷ F^∨ ≫
        (α_ F F F^∨).hom ≫
        F ◁ (ihom.ev F).app (𝟙_ Cpx) ≫
        (ρ_ F).hom := by
          simpa using ringedSiteModuleComplexDualExplicitEvaluation_braidedNormalForm F
    _ =
      (β_ (F ⊗ F^∨) F).hom ≫
        MonoidalClosed.uncurry (ringedSiteModuleComplexDualTensorToEnd F) := by
          simpa using ringedSiteModuleComplexDualExplicitEvaluation_uncurry_bridge F

/-- Helper for Example 21.48.2: after postcomposing with the right unitor, the explicit evaluation
suffix is the whiskered tensor-to-endomorphism comparison followed by internal evaluation. -/
private theorem dualEvaluationSuffix_eq_whiskeredTensorToEnd
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    (α_ F F^∨ F).hom ≫ F ◁ ringedSiteModuleComplexDualEvaluation F ≫ (ρ_ F).hom =
      ringedSiteModuleComplexDualTensorToEnd F ▷ F ≫
        (β_ ((ihom F).obj F) F).hom ≫
        (ihom.ev F).app F := by
  -- Route correction: first identify the explicit suffix with the braided `uncurry` normal form,
  -- then apply the generic braided `uncurry` comparison for `ringedSiteModuleComplexDualTensorToEnd`.
  calc
    (α_ F F^∨ F).hom ≫ F ◁ ringedSiteModuleComplexDualEvaluation F ≫ (ρ_ F).hom =
      (β_ (F ⊗ F^∨) F).hom ≫
        MonoidalClosed.uncurry (ringedSiteModuleComplexDualTensorToEnd F) := by
          simpa using ringedSiteModuleComplexDualExplicitEvaluationUncurrySuffix F
    _ =
      ringedSiteModuleComplexDualTensorToEnd F ▷ F ≫
        (β_ ((ihom F).obj F) F).hom ≫
        (ihom.ev F).app F := by
          simpa [Category.assoc] using
            ringedSiteModuleComplexDualTensorToEndBraidedUncurry F

/-- Helper for Example 21.48.2: the closed-category identity morphism is the curried identity on
`F`. -/
private theorem ringedSiteModuleComplexDualId_eq_curry'_id
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    MonoidalClosed.id F = MonoidalClosed.curry' (𝟙 F) := by
  -- Proof comment: compare the two candidate identity morphisms after uncurrying.
  apply MonoidalClosed.uncurry_injective
  simp [MonoidalClosed.id]

/-- Helper for Example 21.48.2: whiskering the coevaluation/comparison identity on the left by the
dual object turns the first-triangle coevaluation prefix into the closed-category identity. -/
private theorem ringedSiteModuleComplexDualCoevaluation_whiskerLeft_comp_tensorToEnd
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx)
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    F^∨ ◁ ringedSiteModuleComplexDualCoevaluation F ≫
        F^∨ ◁ ringedSiteModuleComplexDualTensorToEnd F =
      F^∨ ◁ MonoidalClosed.id F := by
  -- Proof comment: whisker the defining coevaluation/comparison identity by the dual object, then
  -- rewrite the resulting curried identity into the canonical closed-category identity.
  have hBase :
      ringedSiteModuleComplexDualCoevaluation F ≫ ringedSiteModuleComplexDualTensorToEnd F =
        MonoidalClosed.id F := by
    calc
      ringedSiteModuleComplexDualCoevaluation F ≫ ringedSiteModuleComplexDualTensorToEnd F =
        MonoidalClosed.curry' (𝟙 F) := by
          simpa using ringedSiteModuleComplexDualCoevaluation_comp_tensorToEnd F
      _ = MonoidalClosed.id F := by
        rw [ringedSiteModuleComplexDualId_eq_curry'_id]
  rw [← MonoidalCategory.whiskerLeft_comp]
  simpa using congrArg (fun k ↦ F^∨ ◁ k) hBase

/-- Helper for Example 21.48.2: once the tensor-to-endomorphism comparison has been inserted,
the remaining left-triangle tail is the canonical precomposition action on the dual object. -/
private abbrev ringedSiteModuleComplexDualLeftTriangleInsertedTail
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    F^∨ ⊗ (ihom F).obj F ⟶ F^∨ :=
  (β_ F^∨ ((ihom F).obj F)).hom ≫
    MonoidalClosed.comp F F (𝟙_ Cpx)

/-- Helper for Example 21.48.2: after postcomposing with the left unitor on `F^∨`, the remaining
left-triangle suffix is the explicit braiding/evaluation composite defining the evaluation map. -/
private theorem ringedSiteModuleComplexDual_leftTriangle_suffix_expand
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    (α_ F^∨ F F^∨).inv ≫
        ringedSiteModuleComplexDualEvaluation F ▷ F^∨ ≫
        (λ_ F^∨).hom =
      (α_ F^∨ F F^∨).inv ≫
        (β_ F^∨ F).hom ▷ F^∨ ≫
        (ihom.ev F).app (𝟙_ Cpx) ▷ F^∨ ≫
        (λ_ F^∨).hom := by
  -- Proof comment: unfold the explicit evaluation once so the remaining blocker is pure braided
  -- coherence at the suffix level.
  simp [ringedSiteModuleComplexDualEvaluation, Category.assoc]

/-- Helper for Example 21.48.2: the inserted left-triangle tail is the braiding followed by the
curried internal-composition morphism. -/
private theorem ringedSiteModuleComplexDual_leftTriangle_inserted_tail_expand
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    ringedSiteModuleComplexDualLeftTriangleInsertedTail F =
      (β_ F^∨ ((ihom F).obj F)).hom ≫
        MonoidalClosed.curry (MonoidalClosed.compTranspose F F (𝟙_ Cpx)) := by
  -- Proof comment: rewrite `comp` once to expose the curried composition tail needed by the
  -- suffix comparison.
  rw [ringedSiteModuleComplexDualLeftTriangleInsertedTail, MonoidalClosed.comp_eq]

/-- Helper for Example 21.48.2: uncurrying the tensor-unit specialization of the canonical
tensor/internal-Hom comparison recovers the normalized evaluation suffix before the final right
unitor in the target internal Hom. -/
private theorem ringedSiteModuleComplexTensorInternalHomComparison_toEnd_uncurry
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    MonoidalClosed.uncurry
        (ringedSiteModuleComplexTensorInternalHomComparison F (𝟙_ Cpx) F) =
      (α_ F F F^∨).inv ≫
        (β_ F F).hom ▷ F^∨ ≫
        (α_ F F F^∨).hom ≫
        F ◁ (ihom.ev F).app (𝟙_ Cpx) := by
  -- Proof comment: this is exactly the owner-level `uncurry` formula specialized to the tensor
  -- unit and the internal-Hom dual `F^∨ = (ihom F).obj (𝟙_ Cpx)`.
  simpa using
    ringedSiteModuleComplexTensorInternalHomComparison_uncurry F (𝟙_ Cpx) F

/-- Helper for Example 21.48.2: the tensor-to-endomorphism comparison is the curry of the
normalized uncurried evaluation suffix. -/
private theorem ringedSiteModuleComplexDualTensorToEnd_eq_curry_uncurry_normal_form
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    ringedSiteModuleComplexDualTensorToEnd F =
      MonoidalClosed.curry
        ((α_ F F F^∨).inv ≫
          (β_ F F).hom ▷ F^∨ ≫
          (α_ F F F^∨).hom ≫
          F ◁ (ihom.ev F).app (𝟙_ Cpx) ≫
          (ρ_ F).hom) := by
  -- Proof comment: compare the two morphisms after uncurrying, where the repaired evaluation
  -- owner is already in the canonical Chapter 21 normal form.
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry]
  simpa using ringedSiteModuleComplexEvaluationHom_uncurry F F

/-- Helper for Example 21.48.2: after expanding the inserted tail, the remaining suffix problem is
the closed-monoidal transport comparison between the whiskered curried comparison and the
book-order evaluation composite. -/
private theorem ringedSiteModuleComplexDual_leftTriangle_inserted_tail_curry_normal_form
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    F^∨ ◁
        MonoidalClosed.curry
          ((α_ F F F^∨).inv ≫
            (β_ F F).hom ▷ F^∨ ≫
            (α_ F F F^∨).hom ≫
            F ◁ (ihom.ev F).app (𝟙_ Cpx) ≫
            (ρ_ F).hom) ≫
        (β_ F^∨ ((ihom F).obj F)).hom ≫
        MonoidalClosed.curry (MonoidalClosed.compTranspose F F (𝟙_ Cpx)) =
      (α_ F^∨ F F^∨).inv ≫
        (β_ F^∨ F).hom ▷ F^∨ ≫
        (ihom.ev F).app (𝟙_ Cpx) ▷ F^∨ ≫
        (λ_ F^∨).hom := by
  -- Proof comment: push both sides through `uncurry`, where the transport becomes the same
  -- tensor-level associator/braiding computation as in the Chapter 15 model proof.
  -- TODO: after pushing both sides through `MonoidalClosed.uncurry`, isolate the remaining
  -- transport as the specific tensor-level coherence between the inserted composition tail and the
  -- book-order evaluation suffix.
  sorry

/-- Helper for Example 21.48.2: after factoring away the coevaluation prefix, the remaining
left-triangle suffix is exactly the comparison between the explicit evaluation tail and the
inserted internal-composition tail. -/
private theorem ringedSiteModuleComplexDual_leftTriangle_postunitor_bridge_via_uncurry
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx)
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    F^∨ ◁ ringedSiteModuleComplexDualCoevaluation F ≫
        (α_ F^∨ F F^∨).inv ≫
        ringedSiteModuleComplexDualEvaluation F ▷ F^∨ ≫
        (λ_ F^∨).hom =
      F^∨ ◁ ringedSiteModuleComplexDualCoevaluation F ≫
        F^∨ ◁ ringedSiteModuleComplexDualTensorToEnd F ≫
        ringedSiteModuleComplexDualLeftTriangleInsertedTail F := by
  -- Proof comment: rewrite both suffixes into the same curry/uncurry normal form before
  -- reattaching the coevaluation prefix.
  rw [ringedSiteModuleComplexDual_leftTriangle_suffix_expand,
    ringedSiteModuleComplexDualTensorToEnd_eq_curry_uncurry_normal_form,
    ringedSiteModuleComplexDual_leftTriangle_inserted_tail_expand]
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ F^∨ ◁ ringedSiteModuleComplexDualCoevaluation F ≫ k)
      (ringedSiteModuleComplexDual_leftTriangle_inserted_tail_curry_normal_form F).symm

/-- Helper for Example 21.48.2: after rewriting the left-triangle suffix in terms of the inserted
composition tail, the remaining closed-category identity collapses to the right unitor. -/
private theorem ringedSiteModuleComplexDual_leftTriangle_id_tail
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx) :
    F^∨ ◁ MonoidalClosed.id F ≫
        ringedSiteModuleComplexDualLeftTriangleInsertedTail F =
      (ρ_ F^∨).hom := by
  -- Proof comment: move the inserted identity across the braiding by naturality, then apply the
  -- closed-category `id_comp` law and the braided left-unitor coherence.
  have hNat :
      F^∨ ◁ MonoidalClosed.id F ≫
          (β_ F^∨ ((ihom F).obj F)).hom =
        (β_ F^∨ (𝟙_ Cpx)).hom ≫
          MonoidalClosed.id F ▷ F^∨ := by
    simpa [Category.assoc] using
      (CategoryTheory.BraidedCategory.braiding_naturality
        (𝟙 F^∨) (MonoidalClosed.id F)).symm
  have hIdComp :
      MonoidalClosed.id F ▷ F^∨ ≫
          MonoidalClosed.comp F F (𝟙_ Cpx) =
        (λ_ F^∨).hom := by
    -- Proof comment: `id_comp` says that composing with the internal identity does nothing.
    apply (cancel_epi (λ_ F^∨).inv).1
    simpa [Category.assoc] using MonoidalClosed.id_comp F (𝟙_ Cpx)
  calc
    F^∨ ◁ MonoidalClosed.id F ≫
        (β_ F^∨ ((ihom F).obj F)).hom ≫
        MonoidalClosed.comp F F (𝟙_ Cpx) =
      (β_ F^∨ (𝟙_ Cpx)).hom ≫
        MonoidalClosed.id F ▷ F^∨ ≫
        MonoidalClosed.comp F F (𝟙_ Cpx) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ MonoidalClosed.comp F F (𝟙_ Cpx))
              hNat
    _ = (β_ F^∨ (𝟙_ Cpx)).hom ≫
          (λ_ F^∨).hom := by
            rw [hIdComp]
    _ = (ρ_ F^∨).hom := by
      simpa using CategoryTheory.braiding_leftUnitor F^∨

/-- The source-facing coevaluation and evaluation maps of the internal-Hom dual satisfy the first
triangle identity. -/
theorem ringedSiteModuleComplexDual_coevaluation_evaluation
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx)
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    F^∨ ◁ ringedSiteModuleComplexDualCoevaluation F ≫
        (α_ _ _ _).inv ≫
        ringedSiteModuleComplexDualEvaluation F ▷ F^∨ =
      (ρ_ F^∨).hom ≫
        (λ_ F^∨).inv := by
  -- Route correction: postcompose with the left unitor, replace the suffix by the inserted
  -- tensor-to-endomorphism bridge, and then collapse the remaining tail with `id_comp`.
  apply (cancel_mono (λ_ F^∨).hom).1
  calc
    F^∨ ◁ ringedSiteModuleComplexDualCoevaluation F ≫
        (α_ _ _ _).inv ≫
        ringedSiteModuleComplexDualEvaluation F ▷ F^∨ ≫
        (λ_ F^∨).hom =
      F^∨ ◁ ringedSiteModuleComplexDualCoevaluation F ≫
        F^∨ ◁ ringedSiteModuleComplexDualTensorToEnd F ≫
        ringedSiteModuleComplexDualLeftTriangleInsertedTail F := by
          simpa [Category.assoc] using
            ringedSiteModuleComplexDual_leftTriangle_postunitor_bridge_via_uncurry F
    _ =
      F^∨ ◁ MonoidalClosed.id F ≫
        ringedSiteModuleComplexDualLeftTriangleInsertedTail F := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ ringedSiteModuleComplexDualLeftTriangleInsertedTail F)
              (ringedSiteModuleComplexDualCoevaluation_whiskerLeft_comp_tensorToEnd F)
    _ = (ρ_ F^∨).hom := by
      simpa using ringedSiteModuleComplexDual_leftTriangle_id_tail F
    _ = ((ρ_ F^∨).hom ≫ (λ_ F^∨).inv) ≫ (λ_ F^∨).hom := by
      simp [Category.assoc]

/-- The source-facing coevaluation and evaluation maps of the internal-Hom dual satisfy the second
triangle identity. -/
theorem ringedSiteModuleComplexDual_evaluation_coevaluation
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx)
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    ringedSiteModuleComplexDualCoevaluation F ▷ F ≫
        (α_ _ _ _).hom ≫
        F ◁ ringedSiteModuleComplexDualEvaluation F =
      (λ_ F).hom ≫ (ρ_ F).inv := by
  -- Route correction: rewrite the suffix through the named tensor-to-endomorphism bridge, then
  -- whisker the coevaluation/comparison identity by `F` and close with the universal evaluation
  -- identity for `curry' (𝟙 F)`.
  apply (cancel_mono (ρ_ F).hom).1
  have hCoevComp :
      ringedSiteModuleComplexDualCoevaluation F ≫
          ringedSiteModuleComplexDualTensorToEnd F =
        MonoidalClosed.curry' (𝟙 F) := by
    -- Proof comment: the coevaluation is defined using the inverse of the comparison map.
    simpa using ringedSiteModuleComplexDualCoevaluation_comp_tensorToEnd F
  have hEval :
      ringedSiteModuleComplexDualCoevaluation F ▷ F ≫
          ringedSiteModuleComplexDualTensorToEnd F ▷ F ≫
          (β_ ((ihom F).obj F) F).hom ≫
          (ihom.ev F).app F =
        (λ_ F).hom := by
    have hWhisker :
        ringedSiteModuleComplexDualCoevaluation F ▷ F ≫
            ringedSiteModuleComplexDualTensorToEnd F ▷ F ≫
            (β_ ((ihom F).obj F) F).hom ≫
            (ihom.ev F).app F =
          MonoidalClosed.curry' (𝟙 F) ▷ F ≫
            (β_ ((ihom F).obj F) F).hom ≫
            (ihom.ev F).app F := by
      -- Proof comment: whisker the coevaluation/comparison identity by the source complex.
      have hWhiskerBase :
          (ringedSiteModuleComplexDualCoevaluation F ≫
              ringedSiteModuleComplexDualTensorToEnd F) ▷ F =
            MonoidalClosed.curry' (𝟙 F) ▷ F := by
        exact congrArg (fun k ↦ k ▷ F) hCoevComp
      calc
        ringedSiteModuleComplexDualCoevaluation F ▷ F ≫
            ringedSiteModuleComplexDualTensorToEnd F ▷ F ≫
            (β_ ((ihom F).obj F) F).hom ≫
            (ihom.ev F).app F =
          (ringedSiteModuleComplexDualCoevaluation F ≫
              ringedSiteModuleComplexDualTensorToEnd F) ▷ F ≫
            (β_ ((ihom F).obj F) F).hom ≫
            (ihom.ev F).app F := by
              rw [comp_whiskerRight]
              simp [Category.assoc]
        _ =
          MonoidalClosed.curry' (𝟙 F) ▷ F ≫
            (β_ ((ihom F).obj F) F).hom ≫
            (ihom.ev F).app F := by
              rw [hWhiskerBase]
    have hIdUnit :
        MonoidalClosed.curry' (𝟙 F) ▷ F ≫
            (β_ ((ihom F).obj F) F).hom ≫
            (ihom.ev F).app F =
          (λ_ F).hom := by
      -- Proof comment: the curried identity evaluates to the left unitor after the standard
      -- braided coherence rewrite.
      calc
        MonoidalClosed.curry' (𝟙 F) ▷ F ≫
            (β_ ((ihom F).obj F) F).hom ≫
            (ihom.ev F).app F =
          (β_ (𝟙_ Cpx) F).hom ≫
            F ◁ MonoidalClosed.curry' (𝟙 F) ≫
            (ihom.ev F).app F := by
              simp [Category.assoc]
        _ = (β_ (𝟙_ Cpx) F).hom ≫ (ρ_ F).hom := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ (β_ (𝟙_ Cpx) F).hom ≫ k)
              (MonoidalClosed.whiskerLeft_curry'_ihom_ev_app (𝟙 F))
        _ = (λ_ F).hom := by
          simpa [Category.assoc] using braiding_rightUnitor F
    exact hWhisker.trans hIdUnit
  have hBridge :
      ringedSiteModuleComplexDualCoevaluation F ▷ F ≫
          (α_ _ _ _).hom ≫
          F ◁ ringedSiteModuleComplexDualEvaluation F ≫
          (ρ_ F).hom =
        ringedSiteModuleComplexDualCoevaluation F ▷ F ≫
          ringedSiteModuleComplexDualTensorToEnd F ▷ F ≫
          (β_ ((ihom F).obj F) F).hom ≫
          (ihom.ev F).app F := by
    -- Proof comment: the explicit evaluation suffix is now replaced by the whiskered comparison
    -- tail recorded in `dualEvaluationSuffix_eq_whiskeredTensorToEnd`.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ ringedSiteModuleComplexDualCoevaluation F ▷ F ≫ k)
        (dualEvaluationSuffix_eq_whiskeredTensorToEnd F)
  have hMain :
      ringedSiteModuleComplexDualCoevaluation F ▷ F ≫
          (α_ _ _ _).hom ≫
          F ◁ ringedSiteModuleComplexDualEvaluation F ≫
          (ρ_ F).hom =
        (λ_ F).hom := by
    exact hBridge.trans hEval
  simpa [Category.assoc] using hMain.trans (by simp [Category.assoc])

-- LeanSearch recall: `CategoryTheory.HasLeftDual.exact` and `CategoryTheory.ExactPairing.mk`
-- confirm that `ExactPairing X Y` packages `X` as a left dual of `Y`.
/-- Once `ringedSiteModuleComplexDualTensorToEnd F` is an isomorphism, the internal-Hom dual
complex carries its canonical exact pairing with `F`. -/
@[reducible] private noncomputable def ringedSiteModuleComplexDualExactPairingOfIsIso
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    (F : Cpx)
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    ExactPairing F^∨ F :=
  letI : ExactPairing F F^∨ :=
    { coevaluation' := ringedSiteModuleComplexDualCoevaluation F
      evaluation' := ringedSiteModuleComplexDualEvaluation F
      coevaluation_evaluation' := ringedSiteModuleComplexDual_coevaluation_evaluation F
      evaluation_coevaluation' := ringedSiteModuleComplexDual_evaluation_coevaluation F }
  BraidedCategory.exactPairing_swap F F^∨

/-- Example 21.48.2: if the cochain complex `F` is locally strictly perfect, then the internal-Hom
dual `F^∨ = Hom(F, 𝟙_)`, together with the canonical coevaluation and evaluation morphisms, is a
left dual of `F`. In Lean this left-duality datum is packaged by `CategoryTheory.ExactPairing`. -/
@[stacks 0FPR]
noncomputable instance ringedSiteModuleComplexDualExactPairing
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    {F : Cpx} [IsLocallyStrictlyPerfect F] :
    ExactPairing F^∨ F :=
  ringedSiteModuleComplexDualExactPairingOfIsIso F

/-- The first triangle identity for the canonical coevaluation and evaluation morphisms of the
internal-Hom dual of a locally strictly perfect cochain complex. -/
@[stacks 0FPR]
theorem ringedSiteModuleComplexDual_coevaluation_evaluation_of_isLocallyStrictlyPerfect
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    {F : Cpx} [IsLocallyStrictlyPerfect F] :
    F^∨ ◁ ringedSiteModuleComplexDualCoevaluation F ≫
        (α_ _ _ _).inv ≫
        ringedSiteModuleComplexDualEvaluation F ▷ F^∨ =
      (ρ_ F^∨).hom ≫
        (λ_ F^∨).inv := by
  simpa using ringedSiteModuleComplexDual_coevaluation_evaluation F

/-- The second triangle identity for the canonical coevaluation and evaluation morphisms of the
internal-Hom dual of a locally strictly perfect cochain complex. -/
@[stacks 0FPR]
theorem ringedSiteModuleComplexDual_evaluation_coevaluation_of_isLocallyStrictlyPerfect
    [MonoidalCategory Cpx]
    [BraidedCategory Cpx]
    [MonoidalClosed Cpx]
    {F : Cpx} [IsLocallyStrictlyPerfect F] :
    ringedSiteModuleComplexDualCoevaluation F ▷ F ≫
        (α_ _ _ _).hom ≫
        F ◁ ringedSiteModuleComplexDualEvaluation F =
      (λ_ F).hom ≫ (ρ_ F).inv := by
  simpa using ringedSiteModuleComplexDual_evaluation_coevaluation F

end DualitySetup

end SheafOfModules.RingedSite
