import Mathlib
import StacksProject_2024.stacks_project.Chap18.Lemma_18_23_3
import StacksProject_2024.stacks_project.Chap18.Lemma_18_27_5
import StacksProject_2024.stacks_project.Chap18.Lemma_18_30_1
import StacksProject_2024.stacks_project.Chap18.Remark_18_27_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 18.31.4:
- primary domain: pullback of internal-Hom sheaves along a flat morphism of ringed sites;
- sampled owner declarations:
  `CategoryTheory.expComparison`,
  `RingedSite.Hom.pullbackInternalHomComparison`,
  `RingedSite.Hom.(^*)`,
  `exactFunctor`,
  `SheafOfModules.IsFinitePresentation`;
- best owner abstraction: the ambient owner is the pullback functor `(f^*)`; when the stronger
  Cartesian-closed comparison owner `CategoryTheory.expComparison` is available, the comparison of
  Remark 18.27.3 is its ringed-site bridge component. The source-facing theorem remains stated for
  that bridge because the generic mathlib owner currently carries extra ambient assumptions not
  present in the textbook statement;
- primitive data: a morphism of ringed sites `f` and module sheaves `ℱ 𝒢`;
- derived API: the statement that the source-facing comparison morphism is an isomorphism when
  `ℱ` is finitely presented and pullback along `f` is exact.

Source/core/bridge triage:
- `source-facing`: the isomorphism statement for the comparison morphism;
- `core/canonical`: `RingedSite.Hom.(^*)`, `exactFunctor _ _ (f^*)`,
  `SheafOfModules.IsFinitePresentation`, and, under the stronger generic comparison hypotheses,
  `CategoryTheory.expComparison`;
- `bridge/view`: `RingedSite.Hom.pullbackInternalHomComparison`, with the monoidality of `f^*`
  supplied by the canonical owner `SheafOfModules.pullback f.structureSheafMap`. -/

variable {X Y : RingedSite} (f : X ⟶ Y)
variable [MonoidalCategory (SheafOfModules Y.structureSheaf)]
variable [MonoidalClosed (SheafOfModules Y.structureSheaf)]
variable [MonoidalCategory (SheafOfModules X.structureSheaf)]
variable [MonoidalClosed (SheafOfModules X.structureSheaf)]
variable [(SheafOfModules.pullback f.structureSheafMap).Monoidal]

/-- Helper for Lemma 18.31.4: a morphism of module sheaves on a ringed site is an isomorphism
once all of its objectwise evaluation maps are isomorphisms. -/
private theorem isIso_ofEvaluationMapIsIso
    {M N : SheafOfModules X.structureSheaf} (φ : M ⟶ N)
    (hφ : ∀ U : Xᵒᵖ, IsIso ((SheafOfModules.evaluation X.structureSheaf U).map φ)) :
    IsIso φ := by
  have hIsoPresheaf :
      IsIso
        ((sheafToPresheaf X.siteTopology AddCommGrpCat).map
          ((SheafOfModules.toSheaf X.structureSheaf).map φ)) := by
    -- Proof comment: after forgetting module structure and the sheaf condition, evaluation is
    -- just objectwise application, so the hypothesis gives an isomorphism on each component.
    refine (NatTrans.isIso_iff_isIso_app _).2 ?_
    intro U
    let _ : IsIso ((SheafOfModules.evaluation X.structureSheaf U).map φ) := hφ U
    let _ := Functor.map_isIso
      (forget₂ (ModuleCat (X.structureSheaf.1.obj U)) AddCommGrpCat)
      ((SheafOfModules.evaluation X.structureSheaf U).map φ)
    simpa [SheafOfModules.evaluation, SheafOfModules.toSheaf]
  have hIsoToSheaf :
      IsIso ((SheafOfModules.toSheaf X.structureSheaf).map φ) := by
    -- Proof comment: the sheaf-to-presheaf forgetful functor reflects isomorphisms, so the
    -- presheaf-level isomorphism already upgrades to an isomorphism of additive sheaves.
    letI :
        IsIso
          ((sheafToPresheaf X.siteTopology AddCommGrpCat).map
            ((SheafOfModules.toSheaf X.structureSheaf).map φ)) :=
      hIsoPresheaf
    exact isIso_of_reflects_iso
      ((SheafOfModules.toSheaf X.structureSheaf).map φ)
      (sheafToPresheaf X.siteTopology AddCommGrpCat)
  -- Proof comment: finally reflect the additive-sheaf isomorphism back to module sheaves.
  letI : IsIso ((SheafOfModules.toSheaf X.structureSheaf).map φ) := hIsoToSheaf
  exact isIso_of_reflects_iso φ (SheafOfModules.toSheaf X.structureSheaf)

/-- Helper for Lemma 18.31.4: objectwise evaluation at `U` agrees with terminal evaluation on the
slice over `U.unop`. -/
private theorem evaluationOverTerminalMapEq
    (U : Xᵒᵖ) {M N : SheafOfModules X.structureSheaf} (φ : M ⟶ N) :
    (SheafOfModules.evaluation X.structureSheaf U).map φ =
      (SheafOfModules.evaluation (X.structureSheaf.over U.unop)
          (Opposite.op (Over.mk (𝟙 U.unop)))).map
        ((SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U.unop))).map φ) := by
  -- Proof comment: after restricting to the slice, evaluating at `U` is definitionally the
  -- terminal component `U ⟶ U`.
  rfl

/-- Helper for Lemma 18.31.4: in any slice ringed site, restricting a terminal value along the
unique maps from the terminal object is compatible with all restriction maps. -/
private theorem overSectionsFromTerminalNaturality
    {Z : RingedSite} {U : Z} {M : SheafOfModules (Z.structureSheaf.over U)}
    (m : M.val.obj (Opposite.op (Over.mk (𝟙 U)))) :
    ∀ V Y : (Over U)ᵒᵖ, ∀ g : V ⟶ Y,
      M.val.map g (M.val.map ((Over.mkIdTerminal.from V.unop).op) m) =
        M.val.map ((Over.mkIdTerminal.from Y.unop).op) m := by
  intro V Y g
  -- Proof comment: every object of the slice has a unique map to the terminal object.
  have h :
      (Over.mkIdTerminal.from V.unop).op ≫ g = (Over.mkIdTerminal.from Y.unop).op := by
    apply Quiver.Hom.unop_inj
    simp only [Quiver.Hom.unop_op]
    exact Over.mkIdTerminal.hom_ext
      (g.unop ≫ Over.mkIdTerminal.from V.unop)
      (Over.mkIdTerminal.from Y.unop)
  rw [← PresheafOfModules.map_comp_apply, h]

/-- Helper for Lemma 18.31.4: a terminal value determines a section on a slice site by
restriction from the terminal object. -/
private noncomputable def overSectionsFromTerminal
    {Z : RingedSite} {U : Z} (M : SheafOfModules (Z.structureSheaf.over U))
    (m : M.val.obj (Opposite.op (Over.mk (𝟙 U)))) :
    M.sections :=
  M.val.sectionsMk
    (fun V ↦ M.val.map ((Over.mkIdTerminal.from V.unop).op) m)
    (overSectionsFromTerminalNaturality (M := M) m)

/-- Helper for Lemma 18.31.4: a slice section is determined by its value at the terminal object. -/
private theorem overSectionsEquivTerminal_leftInv
    {Z : RingedSite} {U : Z} {M : SheafOfModules (Z.structureSheaf.over U)}
    (s : M.sections) :
    overSectionsFromTerminal M (s.1 (Opposite.op (Over.mk (𝟙 U)))) = s := by
  -- Proof comment: every component is obtained by restricting the terminal component.
  ext V
  simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from V.unop).op)

/-- Helper for Lemma 18.31.4: evaluating the reconstructed section at the terminal object recovers
the original terminal value. -/
private theorem overSectionsEquivTerminal_rightInv
    {Z : RingedSite} {U : Z} {M : SheafOfModules (Z.structureSheaf.over U)}
    (m : M.val.obj (Opposite.op (Over.mk (𝟙 U)))) :
    (overSectionsFromTerminal M m).1 (Opposite.op (Over.mk (𝟙 U))) = m := by
  -- Proof comment: the terminal object only maps to itself by the identity.
  change M.val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
  have h :
      Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
    Over.mkIdTerminal.hom_ext _ _
  simpa using M.val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 18.31.4: evaluating at the terminal object gives an equivalence between slice
sections and terminal values. -/
private noncomputable def overSectionsEquivTerminal
    {Z : RingedSite} {U : Z} (M : SheafOfModules (Z.structureSheaf.over U)) :
    M.sections ≃ M.val.obj (Opposite.op (Over.mk (𝟙 U))) :=
  { toFun := fun s ↦ s.1 (Opposite.op (Over.mk (𝟙 U)))
    invFun := overSectionsFromTerminal M
    left_inv := overSectionsEquivTerminal_leftInv (M := M)
    right_inv := overSectionsEquivTerminal_rightInv (M := M) }

/-- Helper for Lemma 18.31.4: under terminal evaluation, a section map is exactly the terminal
component of the underlying sheaf morphism. -/
private theorem overSectionsEquivTerminal_sectionsMap
    {Z : RingedSite} {U : Z} {M N : SheafOfModules (Z.structureSheaf.over U)}
    (ψ : M ⟶ N) (s : M.sections) :
    overSectionsEquivTerminal N (SheafOfModules.sectionsMap ψ s) =
      (ψ.val.app (Opposite.op (Over.mk (𝟙 U)))) (overSectionsEquivTerminal M s) := by
  -- Proof comment: both sides are definitionally the terminal evaluation of the mapped section.
  rfl

/-- Helper for Lemma 18.31.4: the inverse terminal-evaluation equivalence is natural in the
module-sheaf morphism. -/
private theorem sectionsMap_overSectionsEquivTerminal_symm
    {Z : RingedSite} {U : Z} {M N : SheafOfModules (Z.structureSheaf.over U)}
    (ψ : M ⟶ N) (m : M.val.obj (Opposite.op (Over.mk (𝟙 U)))) :
    SheafOfModules.sectionsMap ψ ((overSectionsEquivTerminal M).symm m) =
      (overSectionsEquivTerminal N).symm ((ψ.val.app (Opposite.op (Over.mk (𝟙 U)))) m) := by
  -- Proof comment: compare both sections after applying terminal evaluation.
  apply (overSectionsEquivTerminal N).injective
  rw [overSectionsEquivTerminal_sectionsMap]
  simp

/-- Helper for Lemma 18.31.4: on a slice ringed site, sections of an internal-Hom sheaf are
naturally equivalent to morphisms from the source sheaf. -/
private noncomputable def overSectionsEquivHom
    {Z : RingedSite} {U : Z} (M N : SheafOfModules (Z.structureSheaf.over U)) :
    (((ihom M).obj N).sections) ≃ (M ⟶ N) := by
  -- Proof comment: first identify sections with the terminal value on the slice, then reinterpret
  -- that value through the internal-Hom unit and adjunction.
  exact (overSectionsEquivTerminal ((ihom M).obj N)).symm.trans <|
    (((((ihom M).obj N).unitHomEquiv).symm).trans <|
      by
        simpa using
          ((((ihom.adjunction M).homEquiv
              (SheafOfModules.unit (Z.structureSheaf.over U)) N).symm).trans
            (((λ_ M).symm.homCongr (Iso.refl N)))))

/-- Helper for Lemma 18.31.4: under `overSectionsEquivHom`, mapping sections of internal Hom by a
target morphism is postcomposition on the corresponding sheaf morphisms. -/
private theorem sectionsMap_overSectionsEquivHom_symm
    {Z : RingedSite} {U : Z} (M : SheafOfModules (Z.structureSheaf.over U))
    {N₁ N₂ : SheafOfModules (Z.structureSheaf.over U)} (f : N₁ ⟶ N₂) (g : M ⟶ N₁) :
    SheafOfModules.sectionsMap ((ihom M).map f) ((overSectionsEquivHom M N₁).symm g) =
      (overSectionsEquivHom M N₂).symm (g ≫ f) := by
  -- Proof comment: compare both sections after applying the terminal-evaluation/Hom
  -- equivalence on the slice.
  apply (overSectionsEquivHom M N₂).injective
  rw [overSectionsEquivTerminal_sectionsMap]
  change (((ihom M).obj N₂).unitHomEquiv
      (((((ihom.adjunction M).homEquiv
          (SheafOfModules.unit (Z.structureSheaf.over U)) N₁).symm).trans
        (((λ_ M).symm.homCongr (Iso.refl N₁)))).symm g ≫
          (ihom M).map f)) =
    (((ihom M).obj N₂).unitHomEquiv
      (((((ihom.adjunction M).homEquiv
          (SheafOfModules.unit (Z.structureSheaf.over U)) N₂).symm).trans
        (((λ_ M).symm.homCongr (Iso.refl N₂)))).symm (g ≫ f)))
  congr 1
  dsimp
  rw [(ihom.adjunction M).homEquiv_naturality_right_symm]
  simp

/-- Helper for Lemma 18.31.4: evaluation at an object of a slice site is terminal evaluation on
the iterated slice over that object. -/
private theorem evaluationOverTerminalMapEqOver
    {Z : RingedSite} {U : Z} (V : (Over U)ᵒᵖ)
    {M N : SheafOfModules (Z.structureSheaf.over U)} (φ : M ⟶ N) :
    (SheafOfModules.evaluation (Z.structureSheaf.over U) V).map φ =
      (SheafOfModules.evaluation ((Z.structureSheaf.over U).over V.unop)
          (Opposite.op (Over.mk (𝟙 V.unop)))).map
        ((SheafOfModules.pushforward (𝟙 ((Z.structureSheaf.over U).over V.unop))).map φ) := by
  -- Proof comment: after restricting once more to the iterated slice, evaluating at `V` is
  -- definitionally the terminal component `V ⟶ V`.
  rfl

/-- Helper for Lemma 18.31.4: on a slice site, an isomorphism on sections already implies an
isomorphism on terminal evaluation. -/
private theorem isIso_evaluationOverTerminal_of_isIso_sectionsMap
    {Z : RingedSite} {U : Z} {M N : SheafOfModules (Z.structureSheaf.over U)} (ψ : M ⟶ N)
    [IsIso (SheafOfModules.sectionsMap ψ)] :
    IsIso
      ((SheafOfModules.evaluation (Z.structureSheaf.over U)
          (Opposite.op (Over.mk (𝟙 U)))).map ψ) := by
  -- Proof comment: terminal evaluation is equivalent to taking sections on the slice, and the
  -- helper equivalence `overSectionsEquivTerminal` transports bijectivity of `sectionsMap ψ`.
  let hSections :
      Function.Bijective (SheafOfModules.sectionsMap ψ) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  apply (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro x y hxy
    let sx := (overSectionsEquivTerminal M).symm x
    let sy := (overSectionsEquivTerminal M).symm y
    have hEval :
        overSectionsEquivTerminal N (SheafOfModules.sectionsMap ψ sx) =
          overSectionsEquivTerminal N (SheafOfModules.sectionsMap ψ sy) := by
      simpa [sx, sy] using hxy
    have hSectionsEq : SheafOfModules.sectionsMap ψ sx = SheafOfModules.sectionsMap ψ sy := by
      exact (overSectionsEquivTerminal N).injective hEval
    have hsxy : sx = sy := hSections.1 hSectionsEq
    exact (overSectionsEquivTerminal M).injective hsxy
  · intro y
    obtain ⟨s, hs⟩ := hSections.2 ((overSectionsEquivTerminal N).symm y)
    refine ⟨overSectionsEquivTerminal M s, ?_⟩
    have hImage :
        overSectionsEquivTerminal N (SheafOfModules.sectionsMap ψ s) = y := by
      simpa [hs] using congrArg (overSectionsEquivTerminal N) hs
    simpa using hImage

/-- Helper for Lemma 18.31.4: on a slice site, an isomorphism of module sheaves induces an
isomorphism on global sections. -/
private theorem isIso_sectionsMap_of_isIso
    {Z : RingedSite} {U : Z} {M N : SheafOfModules (Z.structureSheaf.over U)} (ψ : M ⟶ N)
    [IsIso ψ] :
    IsIso (SheafOfModules.sectionsMap ψ) := by
  have hTerminal :
      Function.Bijective
        ((SheafOfModules.evaluation (Z.structureSheaf.over U)
          (Opposite.op (Over.mk (𝟙 U)))).map ψ) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  apply (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro s t hst
    -- Proof comment: compare the two sections after terminal evaluation, where `ψ` is already a
    -- bijection because evaluation preserves isomorphisms.
    apply (overSectionsEquivTerminal M).injective
    have hTerminalEq :
        overSectionsEquivTerminal N (SheafOfModules.sectionsMap ψ s) =
          overSectionsEquivTerminal N (SheafOfModules.sectionsMap ψ t) := by
      simpa using congrArg (overSectionsEquivTerminal N) hst
    simpa [overSectionsEquivTerminal_sectionsMap] using hTerminalEq
  · intro s
    -- Proof comment: lift the terminal value of `s` through the evaluated isomorphism and then
    -- reconstruct the corresponding global section via `overSectionsEquivTerminal`.
    obtain ⟨m, hm⟩ := hTerminal.2 (overSectionsEquivTerminal N s)
    refine ⟨(overSectionsEquivTerminal M).symm m, ?_⟩
    apply (overSectionsEquivTerminal N).injective
    rw [overSectionsEquivTerminal_sectionsMap]
    simpa using hm

/-- Helper for Lemma 18.31.4: after restricting to the slice over `U`, it remains to prove that
the comparison map induces an isomorphism on sections of that slice. -/
private theorem localizedComparison_sectionsMap_isIso
    (ℱ 𝒢 : SheafOfModules Y.structureSheaf)
    [ℱ.IsFinitePresentation] [exactFunctor _ _ (f^*)] (U : Xᵒᵖ) :
    IsIso
      (SheafOfModules.sectionsMap
        ((SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U.unop))).map
          (pullbackInternalHomComparison f ℱ 𝒢))) := by
  let ψ :
      ((SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U.unop))).obj
        ((f^*).obj ((ihom ℱ).obj 𝒢))) ⟶
        ((SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U.unop))).obj
          ((ihom ((f^*).obj ℱ)).obj ((f^*).obj 𝒢))) :=
    ((SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U.unop))).map
      (pullbackInternalHomComparison f ℱ 𝒢))
  -- Route correction: do not first ask for a sheaf-level `IsIso ψ`. The theorem only needs the
  -- induced map on sections of the slice, so the real frontier is direct bijectivity there.
  apply (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2
  -- TODO: `overSectionsEquivHom` now reduces slice sections of internal-Hom sheaves to actual
  -- morphisms on the slice. The remaining blocker is the transport step identifying that induced
  -- Hom-set map for `ψ` with the chartwise pullback map coming from the localized morphisms of
  -- Lemma `18.20.1`, after rewriting restricted internal-Hom sheaves with
  -- `PresheafOfModules.localHomSheaf_overIsomorphic`. Once that normalization is in place, prove
  -- chartwise bijectivity from finite presentations and finish the global sections statement by
  -- `SheafOfModules.RingedSite.coverSectionCechExact`.
  sorry

/-- Helper for Lemma 18.31.4: once the restricted comparison on the slice over `U` is an
isomorphism on sections, its terminal evaluation on that slice is an isomorphism as well. -/
private theorem localizedComparison_terminalEvaluation_isIso
    (ℱ 𝒢 : SheafOfModules Y.structureSheaf)
    [ℱ.IsFinitePresentation] [exactFunctor _ _ (f^*)] (U : Xᵒᵖ) :
    IsIso
      ((SheafOfModules.evaluation (X.structureSheaf.over U.unop)
          (Opposite.op (Over.mk (𝟙 U.unop)))).map
        ((SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U.unop))).map
          (pullbackInternalHomComparison f ℱ 𝒢))) := by
  -- Proof comment: terminal evaluation on the slice is equivalent to taking sections there, so
  -- the preceding sections-level helper upgrades immediately to the terminal component.
  let _ := localizedComparison_sectionsMap_isIso (f := f) ℱ 𝒢 U
  exact isIso_evaluationOverTerminal_of_isIso_sectionsMap
    ((SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U.unop))).map
      (pullbackInternalHomComparison f ℱ 𝒢))

/-- Helper for Lemma 18.31.4: a chosen presentation packages its relations as a morphism between
the relation free module and the generator free module. -/
private noncomputable def presentationRelationMap
    {Z : RingedSite} {ℱ : SheafOfModules Z.structureSheaf} (P : ℱ.Presentation) :
    (SheafOfModules.free (R := Z.structureSheaf) P.relations.I) ⟶
      (SheafOfModules.free (R := Z.structureSheaf) P.generators.I) :=
  P.relations.π ≫ kernel.ι P.generators.π

/-- Helper for Lemma 18.31.4: the presentation relation map is a complex with the generator
surjection. -/
private theorem presentationRelationMap_comp_generators
    {Z : RingedSite} {ℱ : SheafOfModules Z.structureSheaf} (P : ℱ.Presentation) :
    presentationRelationMap P ≫ P.generators.π = 0 := by
  -- Proof comment: the chosen relations already land in the kernel of the generator map.
  simp [presentationRelationMap]

/-- Helper for Lemma 18.31.4: the chosen generators of a presentation exhibit the target as the
cokernel of the relation map. -/
private theorem presentationGenerators_isCokernel
    {Z : RingedSite} {ℱ : SheafOfModules Z.structureSheaf} (P : ℱ.Presentation) :
    IsColimit
      (CokernelCofork.ofπ P.generators.π
        (presentationRelationMap_comp_generators (P := P))) := by
  -- Proof comment: `P.isColimit` is already the cokernel statement for the explicit relation map
  -- used in this file.
  simpa [presentationRelationMap] using P.isColimit

/-- Helper for Lemma 18.31.4: the short complex attached to a chosen presentation is exact. -/
private theorem presentationShortComplexExact
    {Z : RingedSite} {ℱ : SheafOfModules Z.structureSheaf} (P : ℱ.Presentation) :
    (ShortComplex.mk (presentationRelationMap P) P.generators.π
      (presentationRelationMap_comp_generators (P := P))).Exact := by
  let S : ShortComplex (SheafOfModules Z.structureSheaf) :=
    ShortComplex.mk (presentationRelationMap P) P.generators.π
      (presentationRelationMap_comp_generators (P := P))
  -- Proof comment: exactness is the standard "second map is a cokernel" criterion applied to the
  -- packaged presentation cokernel.
  simpa [S] using
    ShortComplex.exact_of_g_is_cokernel S (presentationGenerators_isCokernel (P := P))

/-- Helper for Lemma 18.31.4: restricting a finite global presentation to a slice keeps the same
finite generator and relation index types. -/
private theorem presentationRestrict_isFinite
    {Z : RingedSite} {ℱ : SheafOfModules Z.structureSheaf} (P : ℱ.Presentation) [P.IsFinite]
    (U : Z) :
    ((P.map (SheafOfModules.pushforward (𝟙 (Z.structureSheaf.over U))) (by rfl))).IsFinite := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: `Presentation.map` keeps the chosen generator basis, up to the standard
    -- transported slice presentation.
    dsimp [SheafOfModules.Presentation.map, SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.generatorsOfIsCokernelFree]
    change Finite P.generators.I
    infer_instance
  · -- Proof comment: the same unfolding shows that the relation basis is unchanged as well.
    dsimp [SheafOfModules.Presentation.map, SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.relationsOfIsCokernelFree]
    infer_instance

/-- Helper for Lemma 18.31.4: a finite global presentation upgrades a sheaf of modules to the
owner predicate `IsFinitePresentation`. -/
private theorem isFinitePresentation_of_finite_presentation
    {Z : RingedSite} {ℱ : SheafOfModules Z.structureSheaf} (P : ℱ.Presentation) [P.IsFinite] :
    ℱ.IsFinitePresentation := by
  -- Proof comment: use the trivial-cover quasicoherent data carried by `P`; each restricted
  -- presentation stays finite by the previous helper.
  refine ⟨P.quasicoherentData, ?_⟩
  constructor
  intro U
  simpa using presentationRestrict_isFinite (P := P) U

/-- Helper for Lemma 18.31.4: exact pullback sends a finite free module sheaf to the free sheaf on
the same finite index type. -/
private noncomputable def pullbackFiniteFreeIso
    (I : Type u) [Finite I] [exactFunctor _ _ (f^*)] :
    (f^*).obj (SheafOfModules.free (R := Y.structureSheaf) I) ≅
      SheafOfModules.free (R := X.structureSheaf) I :=
  -- Proof comment: exactness gives preservation of finite coproducts, so `mapFree` upgrades the
  -- monoidal unit comparison to the desired free-sheaf comparison.
  SheafOfModules.mapFree
    (F := (f^*))
    (η := (Functor.Monoidal.εIso (f^*)).symm)
    I

/-- Helper for Lemma 18.31.4: the finite-free pullback comparison sends each pulled-back basis map
to the basis map on the target free sheaf through the monoidal unit comparison. -/
private theorem pullbackFiniteFreeIso_hom_ιFree
    (I : Type u) [Finite I] [exactFunctor _ _ (f^*)] (i : I) :
    (f^*).map (SheafOfModules.ιFree (R := Y.structureSheaf) i) ≫
        (pullbackFiniteFreeIso (f := f) I).hom =
      (Functor.Monoidal.εIso (f^*)).symm.hom ≫
        SheafOfModules.ιFree (R := X.structureSheaf) i := by
  -- Proof comment: this is exactly the basis-vector computation built into `mapFree`.
  simpa [pullbackFiniteFreeIso] using
    (SheafOfModules.map_ιFree_mapFree_hom
      (F := (f^*)) (η := (Functor.Monoidal.εIso (f^*)).symm) (I := I) (i := i))

-- Proof sketch: the statement is local on `X`, so after localizing one may choose a finite free
-- presentation of `ℱ`. Exact pullback, internal Hom is left exact in the first
-- variable, and for finite free sources the comparison map is visibly an isomorphism. Applying
-- these facts to the presentation diagram and using the five lemma gives the result.
--
-- API note: `pullbackInternalHomComparison` is the source-facing bridge/view of the ambient
-- pullback comparison; the generic owner `CategoryTheory.expComparison` in mathlib currently
-- requires additional Cartesian-closed comparison data that is not part of this textbook-facing
-- statement.
/-- Lemma 18.31.4: for a flat morphism of ringed sites
`f : (\mathcal C, \mathcal O_\mathcal C) \to (\mathcal D, \mathcal O_\mathcal D)` and
`\mathcal O_\mathcal D`-modules `\mathcal F`, `\mathcal G`, if `\mathcal F` is finitely
presented, then the canonical map of Remark 18.27.3
`f^*\mathcal H\!\mathit{om}_{\mathcal O_\mathcal D}(\mathcal F, \mathcal G) ⟶
\mathcal H\!\mathit{om}_{\mathcal O_\mathcal C}(f^*\mathcal F, f^*\mathcal G)`
is an isomorphism. -/
theorem isIso_pullbackInternalHomComparison
    (ℱ 𝒢 : SheafOfModules Y.structureSheaf)
    [ℱ.IsFinitePresentation] [exactFunctor _ _ (f^*)] :
    IsIso (pullbackInternalHomComparison f ℱ 𝒢) := by
  -- Route correction: the first blocked attempt died on missing build artifacts before theorem
  -- elaboration. With the file now elaborating, the stable reduction is: prove the claim
  -- objectwise, rewrite each objectwise goal to terminal evaluation on a slice, and then replace
  -- terminal evaluation by the induced map on slice sections.
  refine isIso_ofEvaluationMapIsIso (X := X) (φ := pullbackInternalHomComparison f ℱ 𝒢) ?_
  intro U
  have hterminal :
      IsIso
        ((SheafOfModules.evaluation (X.structureSheaf.over U.unop)
            (Opposite.op (Over.mk (𝟙 U.unop)))).map
          ((SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U.unop))).map
            (pullbackInternalHomComparison f ℱ 𝒢))) :=
    localizedComparison_terminalEvaluation_isIso (f := f) ℱ 𝒢 U
  -- Proof comment: rewrite ambient evaluation at `U` into terminal evaluation on the slice and
  -- reuse the slice-site isomorphism.
  simpa [evaluationOverTerminalMapEq (X := X) (U := U)
      (φ := pullbackInternalHomComparison f ℱ 𝒢)] using hterminal

end RingedSite.Hom
