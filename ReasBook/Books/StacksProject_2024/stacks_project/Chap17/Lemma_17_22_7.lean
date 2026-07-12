import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Sites.Monoidal
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_11_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u w

namespace SheafOfModules

/- Domain-style sampling for Lemma 17.22.7:
- primary domain: internal Hom in the closed monoidal category of sheaves of modules over a sheaf
  of rings, together with its interaction with filtered colimits;
- sampled owner declarations:
  `colimit.post`,
  `ihom`,
  `SheafOfModules.IsFinitePresentation`;
- best owner abstraction: the canonical comparison morphism is the generic categorical owner
  `colimit.post`, specialized here to the right adjoint `ihom ℱ`;
- primitive data: a ring-valued sheaf `𝒪`, a module sheaf `ℱ`, and a diagram `𝒢`;
- derived API: the specialized `colimit.post 𝒢 (ihom ℱ)` morphism and the finitely presented
  isomorphism theorem.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization in `AlgebraicGeometry.RingedSpace`;
- `core/canonical`: the owner-level declarations below in `SheafOfModules`;
- `bridge/view`: specialization along `𝒪 = (RingedSpace.ringCatSheaf X)`. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J RingCat.{u}}
variable {Λ : Type w} [SmallCategory Λ]
variable [MonoidalCategory (SheafOfModules 𝒪)] [MonoidalClosed (SheafOfModules 𝒪)]

omit [MonoidalCategory (SheafOfModules 𝒪)] [MonoidalClosed (SheafOfModules 𝒪)] in
/-- Helper for Lemma 17.22.7: mapping a finite global presentation along restriction to an object
of the site preserves finiteness of the presentation. -/
private theorem presentation_map_isFinite
    [HasBinaryProducts C]
    [HasSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat]
    {ℱ : SheafOfModules 𝒪} (P : ℱ.Presentation) [P.IsFinite] (X : C) :
    ((P.map (pushforward (𝟙 (𝒪.over X))) (by rfl))).IsFinite := by
  -- `Presentation.map` keeps the same generator and relation index types, so finiteness is
  -- inherited directly from the original presentation.
  refine ⟨?_, ?_⟩
  · dsimp [SheafOfModules.Presentation.map, SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.generatorsOfIsCokernelFree]
    refine ⟨?_⟩
    change Finite P.generators.I
    infer_instance
  · dsimp [SheafOfModules.Presentation.map, SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.relationsOfIsCokernelFree]
    infer_instance

omit [MonoidalCategory (SheafOfModules 𝒪)] [MonoidalClosed (SheafOfModules 𝒪)] in
/-- Helper for Lemma 17.22.7: a finite global presentation on a ringed site upgrades a sheaf of
modules to the owner predicate `IsFinitePresentation`. -/
private theorem isFinitePresentation_of_finite_presentation
    [HasBinaryProducts C]
    [HasSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat]
    {ℱ : SheafOfModules 𝒪} (P : ℱ.Presentation) [P.IsFinite] :
    ℱ.IsFinitePresentation := by
  -- Use the trivial-cover quasicoherent data attached to `P`; each restricted presentation stays
  -- finite by the previous helper.
  refine ⟨P.quasicoherentData, ?_⟩
  constructor
  intro X
  simpa using presentation_map_isFinite (P := P) X

/-- Helper for Lemma 17.22.7: for a fixed target module, source-variable internal Hom is
left exact on sheaves of modules. -/
private theorem internalHom_leftExact_in_source
    [BraidedCategory (SheafOfModules 𝒪)]
    (𝒢 : SheafOfModules 𝒪) :
    leftExactFunctor (SheafOfModules 𝒪)ᵒᵖ (SheafOfModules 𝒪)
      (((MonoidalClosed.internalHom).flip.obj 𝒢 : (SheafOfModules 𝒪)ᵒᵖ ⥤ SheafOfModules 𝒪)) := by
  -- Proof comment: specialize the generic braided closed-monoidal owner theorem asserting that
  -- source-variable internal Hom preserves all limits, then restrict to finite limits.
  letI : PreservesLimits
      (((MonoidalClosed.internalHom).flip.obj 𝒢) : (SheafOfModules 𝒪)ᵒᵖ ⥤ SheafOfModules 𝒪) :=
    { preservesLimitsOfShape := fun {I} _ ↦ by
        exact MonoidalClosed.preservesLimitsOfShape_internalHom_flip_obj
          (A := SheafOfModules 𝒪) (I := I) 𝒢 }
  simpa [leftExactFunctor_iff] using
    (PreservesLimits.preservesFiniteLimits
      (((MonoidalClosed.internalHom).flip.obj 𝒢 : (SheafOfModules 𝒪)ᵒᵖ ⥤ SheafOfModules 𝒪)))

/-- Helper for Lemma 17.22.7: if `A ⟶ B ⟶ C ⟶ 0` is exact, then source-variable internal Hom into
`𝒢` sends it to an exact sequence starting with a monomorphism. -/
private theorem internalHom_exact_in_source
    [BraidedCategory (SheafOfModules 𝒪)]
    {S : ShortComplex (SheafOfModules 𝒪)} (hS : S.Exact ∧ Epi S.g)
    (𝒢 : SheafOfModules 𝒪)
    [((MonoidalClosed.internalHom).flip.obj 𝒢 :
        (SheafOfModules 𝒪)ᵒᵖ ⥤ SheafOfModules 𝒪).PreservesZeroMorphisms] :
    (S.op.map ((MonoidalClosed.internalHom).flip.obj 𝒢)).Exact ∧
      Mono ((S.op.map ((MonoidalClosed.internalHom).flip.obj 𝒢)).f) := by
  -- Proof comment: apply the canonical left-exactness criterion to the opposite short complex
  -- `S.op`, where the hypothesis `Epi S.g` becomes the required monomorphism on the first map.
  let hAb : Abelian (SheafOfModules 𝒪) := inferInstance
  let hAbOp : Abelian (SheafOfModules 𝒪)ᵒᵖ :=
    CategoryTheory.instAbelianOpposite (SheafOfModules 𝒪)
  let hF := internalHom_leftExact_in_source (𝒪 := 𝒪) 𝒢
  let F : (SheafOfModules 𝒪)ᵒᵖ ⥤ SheafOfModules 𝒪 :=
    ((MonoidalClosed.internalHom).flip.obj 𝒢 : (SheafOfModules 𝒪)ᵒᵖ ⥤ SheafOfModules 𝒪)
  letI : F.Additive :=
    @CategoryTheory.functor_additive_of_leftExact_or_rightExact
      (SheafOfModules 𝒪)ᵒᵖ _ hAbOp
      (SheafOfModules 𝒪) _ hAb
      F (.inl hF)
  have hmap := ((Functor.preservesFiniteLimits_tfae F).out 3 1).1 <| by
    simpa [leftExactFunctor_iff] using hF
  simpa using hmap S.op ⟨hS.1.op, by simpa using hS.2⟩

/-- Helper for Lemma 17.22.7: the relation morphism of a chosen presentation is the explicit map
from the free relation sheaf into the free generator sheaf factoring through the kernel of the
generator surjection. -/
private noncomputable def presentationRelationMap
    {ℱ : SheafOfModules 𝒪} (P : ℱ.Presentation) :
    (SheafOfModules.free (R := 𝒪) P.relations.I) ⟶
      (SheafOfModules.free (R := 𝒪) P.generators.I) :=
  P.relations.π ≫ kernel.ι P.generators.π

/-- Helper for Lemma 17.22.7: the presentation relation map forms a complex with the generator
surjection. -/
private theorem presentationRelationMap_comp_generators
    {ℱ : SheafOfModules 𝒪} (P : ℱ.Presentation) :
    presentationRelationMap P ≫ P.generators.π = 0 := by
  -- Proof comment: the chosen relations already land in the kernel of the generator map.
  simp [presentationRelationMap]

/-- Helper for Lemma 17.22.7: the chosen generators of a presentation exhibit the target as the
cokernel of the explicit relation map. -/
private theorem presentationGenerators_isCokernel
    {ℱ : SheafOfModules 𝒪} (P : ℱ.Presentation) :
    IsColimit
      (CokernelCofork.ofπ P.generators.π
        (presentationRelationMap_comp_generators (P := P))) := by
  -- Proof comment: `P.isColimit` is already the cokernel statement for this explicit relation
  -- map.
  simpa [presentationRelationMap] using P.isColimit

/-- Helper for Lemma 17.22.7: the short complex attached to a chosen presentation is exact. -/
private theorem presentationShortComplexExact
    {ℱ : SheafOfModules 𝒪} (P : ℱ.Presentation) :
    (ShortComplex.mk (presentationRelationMap P) P.generators.π
      (presentationRelationMap_comp_generators (P := P))).Exact := by
  let S : ShortComplex (SheafOfModules 𝒪) :=
    ShortComplex.mk (presentationRelationMap P) P.generators.π
      (presentationRelationMap_comp_generators (P := P))
  -- Proof comment: exactness is the standard "second map is a cokernel" criterion for the
  -- packaged presentation cokernel.
  simpa [S] using
    ShortComplex.exact_of_g_is_cokernel S (presentationGenerators_isCokernel (P := P))

/-- Helper for Lemma 17.22.7: applying source-variable internal Hom to the presentation short
complex yields an exact sequence beginning with a monomorphism. -/
private theorem internalHom_presentation_exact_in_source
    [BraidedCategory (SheafOfModules 𝒪)]
    {ℱ : SheafOfModules 𝒪} (P : ℱ.Presentation)
    (𝒢 : SheafOfModules 𝒪)
    [((MonoidalClosed.internalHom).flip.obj 𝒢 :
        (SheafOfModules 𝒪)ᵒᵖ ⥤ SheafOfModules 𝒪).PreservesZeroMorphisms] :
    let S : ShortComplex (SheafOfModules 𝒪) :=
      ShortComplex.mk (presentationRelationMap P) P.generators.π
        (presentationRelationMap_comp_generators (P := P))
    (S.op.map ((MonoidalClosed.internalHom).flip.obj 𝒢)).Exact ∧
      Mono ((S.op.map ((MonoidalClosed.internalHom).flip.obj 𝒢)).f) := by
  let S : ShortComplex (SheafOfModules 𝒪) :=
    ShortComplex.mk (presentationRelationMap P) P.generators.π
      (presentationRelationMap_comp_generators (P := P))
  -- Proof comment: the presentation short complex is exact with epic second map, so the
  -- left-exactness helper for source-variable internal Hom applies directly.
  exact internalHom_exact_in_source (S := S)
    ⟨presentationShortComplexExact (P := P), inferInstance⟩ 𝒢

omit [MonoidalCategory (SheafOfModules 𝒪)] [MonoidalClosed (SheafOfModules 𝒪)] in
/-- Helper for Lemma 17.22.7: a morphism of sheaves of modules is an isomorphism once all of its
objectwise evaluation maps are isomorphisms. -/
private theorem isIso_of_evaluation_map_isIso
    {M N : SheafOfModules 𝒪} (f : M ⟶ N)
    (hf : ∀ U : Cᵒᵖ, IsIso ((SheafOfModules.evaluation 𝒪 U).map f)) :
    IsIso f := by
  have hIsoPresheaf :
      IsIso ((sheafToPresheaf J AddCommGrpCat).map ((SheafOfModules.toSheaf 𝒪).map f)) := by
    -- Proof comment: after forgetting the module structure and then the sheaf condition,
    -- `evaluation` is just objectwise application, so the hypothesis gives an isomorphism on each
    -- presheaf component.
    refine (NatTrans.isIso_iff_isIso_app _).2 ?_
    intro U
    let _ : IsIso ((SheafOfModules.evaluation 𝒪 U).map f) := hf U
    let _ := Functor.map_isIso
      (forget₂ (ModuleCat (𝒪.1.obj U)) AddCommGrpCat)
      ((SheafOfModules.evaluation 𝒪 U).map f)
    simpa [SheafOfModules.evaluation, SheafOfModules.toSheaf]
  have hIsoToSheaf : IsIso ((SheafOfModules.toSheaf 𝒪).map f) := by
    -- Proof comment: the sheaf-to-presheaf forgetful functor reflects isomorphisms, so the
    -- underlying presheaf isomorphism already upgrades to an isomorphism of abelian sheaves.
    letI :
        IsIso ((sheafToPresheaf J AddCommGrpCat).map ((SheafOfModules.toSheaf 𝒪).map f)) :=
      hIsoPresheaf
    exact isIso_of_reflects_iso ((SheafOfModules.toSheaf 𝒪).map f)
      (sheafToPresheaf J AddCommGrpCat)
  -- Proof comment: finally reflect the abelian-sheaf isomorphism back through the forgetful
  -- functor from module sheaves to sheaves of abelian groups.
  letI : IsIso ((SheafOfModules.toSheaf 𝒪).map f) := hIsoToSheaf
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf 𝒪)

omit [MonoidalCategory (SheafOfModules 𝒪)] [MonoidalClosed (SheafOfModules 𝒪)] in
/-- Helper for Lemma 17.22.7: evaluating a sheaf of modules at `U` is the same as evaluating its
restriction to the slice `J.over U.unop` at the terminal object `U ⟶ U`. -/
private theorem evaluation_over_terminal_obj_eq
    (U : Cᵒᵖ) (M : SheafOfModules 𝒪) :
    (SheafOfModules.evaluation 𝒪 U).obj M =
      (SheafOfModules.evaluation (𝒪.over U.unop) (Opposite.op (Over.mk (𝟙 U.unop)))).obj
        (M.over U.unop) := by
  -- Proof comment: both sides are definitionally the same module obtained by evaluating the
  -- restricted sheaf on the terminal slice object `U ⟶ U`.
  rfl

omit [MonoidalCategory (SheafOfModules 𝒪)] [MonoidalClosed (SheafOfModules 𝒪)] in
/-- Helper for Lemma 17.22.7: objectwise evaluation of a morphism agrees with terminal evaluation
of its restriction to the slice over `U`. -/
private theorem evaluation_over_terminal_map_eq
    (U : Cᵒᵖ) {M N : SheafOfModules 𝒪} (f : M ⟶ N) :
    (SheafOfModules.evaluation 𝒪 U).map f =
      (SheafOfModules.evaluation (𝒪.over U.unop) (Opposite.op (Over.mk (𝟙 U.unop)))).map
        ((SheafOfModules.pushforward (𝟙 (𝒪.over U.unop))).map f) := by
  -- Proof comment: after identifying the source and target objects by the previous definitional
  -- equality, the evaluation map is literally the terminal component of the restricted morphism.
  rfl

/-- Helper for Lemma 17.22.7: sections of a sheaf of modules on the slice over `U` are recovered
by evaluating at the terminal object `U ⟶ U`. -/
private noncomputable def overSectionsEquivEvaluation
    {U : C} (M : SheafOfModules (𝒪.over U)) :
    M.sections ≃
      (SheafOfModules.evaluation (𝒪.over U) (Opposite.op (Over.mk (𝟙 U)))).obj M where
  toFun s := s.1 (op (Over.mk (𝟙 U)))
  invFun m :=
    M.val.sectionsMk
      (fun V ↦ M.val.map ((Over.mkIdTerminal.from V.unop).op) m)
      (fun V W f ↦ by
        -- Proof comment: every object of `Over U` has a unique map to the terminal object.
        have h :
            (Over.mkIdTerminal.from V.unop).op ≫ f =
              (Over.mkIdTerminal.from W.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from V.unop)
            (Over.mkIdTerminal.from W.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    -- Proof comment: a section is determined by its restrictions from the terminal object.
    ext V
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from V.unop).op)
  right_inv m := by
    -- Proof comment: the reconstructed section evaluates back to the original terminal value.
    change M.val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h :
        Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using M.val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 17.22.7: under the terminal-evaluation equivalence on the slice, a section
map is exactly the terminal evaluation of the corresponding sheaf morphism. -/
private theorem overSectionsEquivEvaluation_sectionsMap
    {U : C} {M N : SheafOfModules (𝒪.over U)}
    (ψ : M ⟶ N) (s : M.sections) :
    overSectionsEquivEvaluation (𝒪 := 𝒪) N (SheafOfModules.sectionsMap ψ s) =
      (SheafOfModules.evaluation (𝒪.over U) (Opposite.op (Over.mk (𝟙 U))) ⋙
          forget (ModuleCat ((𝒪.over U).obj (Opposite.op (Over.mk (𝟙 U)))))).map ψ
        (overSectionsEquivEvaluation (𝒪 := 𝒪) M s) := by
  -- Proof comment: both sides are the terminal component of the mapped section.
  rfl

/-- Helper for Lemma 17.22.7: terminal evaluation of an internal-Hom sheaf on the slice computes
the represented Hom-set out of the source sheaf. -/
private noncomputable def homEquivEvaluationOverTerminalInternalHom
    {U : C} (M N : SheafOfModules (𝒪.over U)) :
    ((SheafOfModules.evaluation (𝒪.over U) (Opposite.op (Over.mk (𝟙 U))) ⋙
        forget (ModuleCat ((𝒪.over U).obj (Opposite.op (Over.mk (𝟙 U)))))).obj
      ((ihom M).obj N)) ≃
      (M ⟶ N) := by
  -- Proof comment: first reinterpret terminal evaluation as a section, then as a map from the
  -- unit object, and finally uncurry across the closed structure on the slice.
  exact (overSectionsEquivEvaluation (𝒪 := 𝒪) ((ihom M).obj N)).symm.trans <|
    (((((ihom M).obj N).unitHomEquiv).symm).trans <|
      by
        simpa using
          ((((ihom.adjunction M).homEquiv (SheafOfModules.unit (𝒪.over U)) N).symm).trans
            (((λ_ M).symm.homCongr (Iso.refl N)))))

/-- Helper for Lemma 17.22.7: the terminal-evaluation/internal-Hom equivalence is natural in the
target sheaf. -/
private theorem homEquivEvaluationOverTerminalInternalHom_naturality
    {U : C} (M : SheafOfModules (𝒪.over U))
    {N₁ N₂ : SheafOfModules (𝒪.over U)} (f : N₁ ⟶ N₂) (g : M ⟶ N₁) :
    ((SheafOfModules.evaluation (𝒪.over U) (Opposite.op (Over.mk (𝟙 U))) ⋙
          forget (ModuleCat ((𝒪.over U).obj (Opposite.op (Over.mk (𝟙 U)))))).map
        ((ihom M).map f))
      ((homEquivEvaluationOverTerminalInternalHom (𝒪 := 𝒪) M N₁).symm g) =
      (homEquivEvaluationOverTerminalInternalHom (𝒪 := 𝒪) M N₂).symm (g ≫ f) := by
  -- Proof comment: convert terminal evaluation to sections, then this is exactly right
  -- naturality of the internal-Hom adjunction followed by simplification of the left unitor.
  change overSectionsEquivEvaluation (𝒪 := 𝒪) ((ihom M).obj N₂)
      (SheafOfModules.sectionsMap ((ihom M).map f)
        (((((ihom M).obj N₁).unitHomEquiv).symm
          (((((ihom.adjunction M).homEquiv (SheafOfModules.unit (𝒪.over U)) N₁).symm).trans
            (((λ_ M).symm.homCongr (Iso.refl N₁)))).symm g))))
    =
      overSectionsEquivEvaluation (𝒪 := 𝒪) ((ihom M).obj N₂)
        (((((ihom M).obj N₂).unitHomEquiv).symm
          (((((ihom.adjunction M).homEquiv (SheafOfModules.unit (𝒪.over U)) N₂).symm).trans
            (((λ_ M).symm.homCongr (Iso.refl N₂)))).symm (g ≫ f)))) 
  rw [overSectionsEquivEvaluation_sectionsMap]
  change (((ihom M).obj N₂).unitHomEquiv
      (((((ihom.adjunction M).homEquiv (SheafOfModules.unit (𝒪.over U)) N₁).symm).trans
        (((λ_ M).symm.homCongr (Iso.refl N₁)))).symm g ≫
          (ihom M).map f)) =
    (((ihom M).obj N₂).unitHomEquiv
      (((((ihom.adjunction M).homEquiv (SheafOfModules.unit (𝒪.over U)) N₂).symm).trans
        (((λ_ M).symm.homCongr (Iso.refl N₂)))).symm (g ≫ f)))
  congr 1
  dsimp
  rw [(ihom.adjunction M).homEquiv_naturality_right_symm]
  simp

/-- Helper for Lemma 17.22.7: terminal evaluation of internal Hom on the slice is naturally
isomorphic to the represented functor. -/
private noncomputable def coyonedaIsoEvaluationOverTerminalInternalHom
    {U : C} (M : SheafOfModules (𝒪.over U)) :
    coyoneda.obj (Opposite.op M) ≅
      ihom M ⋙
        (SheafOfModules.evaluation (𝒪.over U) (Opposite.op (Over.mk (𝟙 U))) ⋙
          forget (ModuleCat ((𝒪.over U).obj (Opposite.op (Over.mk (𝟙 U)))))) := by
  refine NatIso.ofComponents (fun N ↦ ?_) ?_
  · let e := (homEquivEvaluationOverTerminalInternalHom (𝒪 := 𝒪) M N).symm
    let _ : IsIso e := (ConcreteCategory.isIso_iff_bijective _).2 e.bijective
    exact asIso e
  · intro N₁ N₂ f
    ext g
    simpa using
      (homEquivEvaluationOverTerminalInternalHom_naturality (𝒪 := 𝒪) M f g).symm

/-- Helper for Lemma 17.22.7: transport `colimit.post` across a natural isomorphism of target
functors. -/
private theorem colimitPost_eq_of_natIso
    {D E : SheafOfModules 𝒪 ⥤ Type (max u w)} (e : D ≅ E)
    (F : Λ ⥤ SheafOfModules 𝒪) [HasColimit F] :
    colimit.post F E =
      (HasColimit.isoOfNatIso (Functor.isoWhiskerLeft F e)).inv ≫
        colimit.post F D ≫ e.app (colimit F) := by
  -- Proof comment: both morphisms are the unique colimit comparison maps with the same stagewise
  -- composites.
  apply colimit.hom_ext
  intro i
  simp

/-- Helper for Lemma 17.22.7: after applying a colimit-preserving functor, `colimit.post` is the
canonical colimit comparison for the whiskered target functor. -/
private theorem functor_map_colimitPost_eq
    {D : Type u} [Category.{u} D] {K : SheafOfModules 𝒪 ⥤ D}
    [PreservesColimits K] (F : Λ ⥤ SheafOfModules 𝒪)
    (G : SheafOfModules 𝒪 ⥤ SheafOfModules 𝒪) [HasColimit F] [HasColimit (F ⋙ G)] :
    K.map (colimit.post F G) =
      (preservesColimitIso K (F ⋙ G)).hom ≫ colimit.post F (G ⋙ K) := by
  -- Proof comment: both arrows out of `K.obj (colimit (F ⋙ G))` agree on each colimit coprojection.
  apply colimit.hom_ext
  intro i
  simp

-- Proof sketch: finite presentation is local on the ringed site, so after restricting to a cover
-- one may choose a finite free presentation of `ℱ`. Internal Hom from such a presentation is the
-- kernel of a morphism between finite direct sums, and filtered colimits commute with those finite
-- sums and preserve exactness, forcing the canonical comparison morphism to be an isomorphism.
/-- If `ℱ` is a finitely presented `\mathcal O`-module and `𝒢` is a filtered diagram of
`\mathcal O`-modules, then the canonical morphism
`colim_λ ℋom_𝒪(ℱ, 𝒢_λ) ⟶ ℋom_𝒪(ℱ, colim_λ 𝒢_λ)` is an isomorphism. -/
theorem isIso_internalHomColimitComparison_of_isFinitePresentation
    [IsFiltered Λ]
    (ℱ : SheafOfModules 𝒪) [ℱ.IsFinitePresentation]
    (𝒢 : Λ ⥤ SheafOfModules 𝒪)
    [HasColimit 𝒢] [HasColimit (𝒢 ⋙ ihom ℱ)] :
    IsIso (colimit.post 𝒢 (ihom ℱ)) := by
  -- Route correction: instead of rebuilding the finite-presentation kernel argument inside each
  -- slice, use that finite presentation already gives categorical finite presentability. On every
  -- slice, terminal evaluation of internal Hom is naturally the represented functor, so the
  -- desired comparison reduces to filtered-colimit preservation of `coyoneda`.
  refine isIso_of_evaluation_map_isIso (𝒪 := 𝒪) (f := colimit.post 𝒢 (ihom ℱ)) ?_
  intro U
  let F : SheafOfModules (𝒪.over U.unop) := ℱ.over U.unop
  let D : Λ ⥤ SheafOfModules (𝒪.over U.unop) :=
    𝒢 ⋙ SheafOfModules.pushforward (𝟙 (𝒪.over U.unop))
  let E :
      SheafOfModules (𝒪.over U.unop) ⥤
        Type (max u w) :=
    SheafOfModules.evaluation (𝒪.over U.unop) (Opposite.op (Over.mk (𝟙 U.unop))) ⋙
      forget (ModuleCat ((𝒪.over U.unop).obj (Opposite.op (Over.mk (𝟙 U.unop)))))
  let e : coyoneda.obj (Opposite.op F) ≅ ihom F ⋙ E :=
    coyonedaIsoEvaluationOverTerminalInternalHom (𝒪 := 𝒪) F
  have hCoy : IsIso (colimit.post D (coyoneda.obj (Opposite.op F))) := by
    let _ : IsFinitelyPresentable F := inferInstance
    let _ : PreservesFilteredColimits (coyoneda.obj (Opposite.op F)) :=
      (isFinitelyPresentable_iff_preservesFilteredColimits :
        IsFinitelyPresentable F ↔
          PreservesFilteredColimits (coyoneda.obj (Opposite.op F))).mp inferInstance
    -- The represented functor of a finitely presentable object preserves filtered colimits.
    infer_instance
  have hComposite :
      IsIso (colimit.post D (ihom F ⋙ E)) := by
    -- Proof comment: transport the represented-functor comparison across the natural isomorphism
    -- between `Hom(F,-)` and terminal evaluation of internal Hom on the slice.
    rw [colimitPost_eq_of_natIso (𝒪 := 𝒪.over U.unop) (Λ := Λ) (e := e) (F := D)]
    infer_instance
  have hUnderlying :
      IsIso
        ((SheafOfModules.evaluation (𝒪.over U.unop) (Opposite.op (Over.mk (𝟙 U.unop))) ⋙
            forget
              (ModuleCat ((𝒪.over U.unop).obj (Opposite.op (Over.mk (𝟙 U.unop)))))).map
          (colimit.post D (ihom F))) := by
    -- Proof comment: evaluation at the terminal object preserves colimits, so after applying the
    -- evaluation/forgetful functor we are exactly in the composite-functor comparison above.
    rw [functor_map_colimitPost_eq (𝒪 := 𝒪.over U.unop) (Λ := Λ) (K := E) (F := D) (G := ihom F)]
    infer_instance
  have hterminal :
      IsIso
        ((SheafOfModules.evaluation (𝒪.over U.unop) (Opposite.op (Over.mk (𝟙 U.unop)))).map
          ((SheafOfModules.pushforward (𝟙 (𝒪.over U.unop))).map
            (colimit.post 𝒢 (ihom ℱ)))) := by
    -- Proof comment: the forgetful functor from modules to types reflects isomorphisms, so the
    -- underlying bijective comparison obtained above upgrades to an isomorphism in `ModuleCat`.
    change IsIso ((SheafOfModules.evaluation (𝒪.over U.unop)
      (Opposite.op (Over.mk (𝟙 U.unop))) ⋙
        forget
          (ModuleCat ((𝒪.over U.unop).obj (Opposite.op (Over.mk (𝟙 U.unop)))))).map
      ((SheafOfModules.pushforward (𝟙 (𝒪.over U.unop))).map
        (colimit.post 𝒢 (ihom ℱ)))
    exact isIso_of_reflects_iso
      ((SheafOfModules.evaluation (𝒪.over U.unop) (Opposite.op (Over.mk (𝟙 U.unop)))).map
        ((SheafOfModules.pushforward (𝟙 (𝒪.over U.unop))).map
          (colimit.post 𝒢 (ihom ℱ))))
      (forget
        (ModuleCat ((𝒪.over U.unop).obj (Opposite.op (Over.mk (𝟙 U.unop))))))
  -- Proof comment: the preceding transport lemma rewrites ambient evaluation at `U` into terminal
  -- evaluation on the slice, so the slice-level isomorphism upgrades directly to the original
  -- objectwise comparison map.
  simpa [evaluation_over_terminal_map_eq (𝒪 := 𝒪) (U := U)
      (f := colimit.post 𝒢 (ihom ℱ))] using hterminal

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {Λ : Type w} [SmallCategory Λ] [IsFiltered Λ]
    [MonoidalCategory (RingedSpace.Modules X)] [MonoidalClosed (RingedSpace.Modules X)]
local notation "ModX" => RingedSpace.Modules X

variable (ℱ : ModX) [ℱ.IsFinitePresentation]
variable (𝒢 : Λ ⥤ ModX)
  [HasColimit 𝒢] [HasColimit (𝒢 ⋙ ihom ℱ)]

/- Lemma 17.22.7, source-facing bridge/view specialization: for a ringed space `X`, the
comparison morphism
`colim_\lambda \mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G_\lambda) ⟶
\mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F, colim_\lambda \mathcal G_\lambda)`
is covered exactly by
`SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation`
on `(RingedSpace.Modules X)`. -/
example :
  IsIso (colimit.post 𝒢 (ihom ℱ))
    := SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation ℱ 𝒢

end AlgebraicGeometry.RingedSpace
