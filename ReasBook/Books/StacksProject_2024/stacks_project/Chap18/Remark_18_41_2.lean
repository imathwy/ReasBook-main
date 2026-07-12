import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_28_1
import StacksProject_2024.Chap18.Lemma_18_14_2
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory

section

variable {C : Type u} [Category.{u} C]
variable {J : GrothendieckTopology C}
variable [HasBinaryProducts C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- Helper for Remark 18.41.2: the localized structure sheaf `\mathcal O_U`, regarded only as
its underlying abelian sheaf on the slice site. -/
abbrev localizedStructureAbelianSheaf :
    (J : GrothendieckTopology C) → (𝒪 : Sheaf J CommRingCat.{u}) → (U : C) →
      Sheaf (J.over U) AddCommGrpCat.{u} :=
  fun J 𝒪 U ↦
    (SheafOfModules.toSheaf ((SheafOfModules.RingedSite.ringSheaf J 𝒪).over U)).obj
      (SheafOfModules.RingedSite.unitModule (J.over U) (𝒪.over U))

namespace LocalizedStructureAbelianSheaf

set_option quotPrecheck false in
scoped notation:max 𝒪:max "_[" U "]" =>
  CategoryTheory.localizedStructureAbelianSheaf _ 𝒪 U

end LocalizedStructureAbelianSheaf

end

open scoped LocalizedStructureAbelianSheaf

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [HasBinaryProducts C] [HasBinaryProducts D]
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (f : C ⥤ D) [f.IsContinuous JC JD]
variable (𝒪D : Sheaf JD CommRingCat.{u}) (U : C)
variable [HasWeakSheafify (JD.over (f.obj U)) AddCommGrpCat.{u}]
variable [∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}, (Over.post f).op.HasLeftKanExtension F]

/-- Helper for Remark 18.41.2: the standard comparison between pullback along `Over.post f` and
restriction to the slice site. -/
private abbrev overPullbackPushforwardIso :
    JD.overPullback RingCat.{u} (f.obj U) ⋙
        (Over.post f).sheafPushforwardContinuous RingCat.{u}
          (JC.over U) (JD.over (f.obj U)) ≅
      f.sheafPushforwardContinuous RingCat.{u} JC JD ⋙
        JC.overPullback RingCat.{u} U :=
  (Over.post f).sheafPushforwardContinuousComp (Over.forget (f.obj U))
      RingCat.{u} (JC.over U) (JD.over (f.obj U)) JD ≪≫
    eqToIso (by rfl) ≪≫
    ((Over.forget U).sheafPushforwardContinuousComp f
      RingCat.{u} (JC.over U) JC JD).symm

/-- Helper for Remark 18.41.2: the right-adjoint form of the localized comparison map. -/
private abbrev localizedComparisonRightAdjointMap_hom :
    SheafOfModules.unit
        ((SheafOfModules.RingedSite.ringSheaf JC
          ((f.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)).over U) ⟶
      (SheafOfModules.pushforward
          (((overPullbackPushforwardIso (f := f) (U := U)).symm.app
            (SheafOfModules.RingedSite.ringSheaf JD 𝒪D)).hom)).obj
        (SheafOfModules.RingedSite.unitModule (JD.over (f.obj U)) (𝒪D.over (f.obj U))) :=
  SheafOfModules.unitToPushforwardObjUnit
    (((overPullbackPushforwardIso (f := f) (U := U)).symm.app
      (SheafOfModules.RingedSite.ringSheaf JD 𝒪D)).hom)

/-- Helper for Remark 18.41.2: the right-adjoint form of the comparison on localized structure
sheaves. -/
private abbrev localizedComparisonRightAdjointMap :
    (((f.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)_[U]) ⟶
      ((Over.post f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (JC.over U) (JD.over (f.obj U))).obj
        ((𝒪D)_[f.obj U]) :=
  (SheafOfModules.toSheaf ((SheafOfModules.RingedSite.ringSheaf JC
      ((f.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)).over U)).map
    (localizedComparisonRightAdjointMap_hom f 𝒪D U)

/-- Helper for Remark 18.41.2: the slice-site comparison map from `18.41.2.1`. -/
private abbrev localizedComparisonOnStructureSheavesAux :
    ((Over.post f).sheafPullback AddCommGrpCat.{u}
        (JC.over U) (JD.over (f.obj U))).obj
      (((f.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)_[U]) ⟶
    (𝒪D)_[f.obj U] :=
  (((Over.post f).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (JC.over U) (JD.over (f.obj U))).homEquiv _ _).symm
    (localizedComparisonRightAdjointMap f 𝒪D U)

/-- Helper for Remark 18.41.2: applying the slice-site lower-shriek adjunction to the localized
comparison recovers its right-adjoint form. -/
private theorem localizedComparisonOnStructureSheavesAux_homEquiv :
    ((Over.post f).sheafAdjunctionContinuous AddCommGrpCat.{u}
        (JC.over U) (JD.over (f.obj U))).homEquiv _ _
      (localizedComparisonOnStructureSheavesAux f 𝒪D U) =
    localizedComparisonRightAdjointMap f 𝒪D U := by
  simpa [localizedComparisonOnStructureSheavesAux] using
    (Equiv.apply_symm_apply
      (((Over.post f).sheafAdjunctionContinuous AddCommGrpCat.{u}
          (JC.over U) (JD.over (f.obj U))).homEquiv _ _)
      (localizedComparisonRightAdjointMap f 𝒪D U))

end

end CategoryTheory

open scoped CategoryTheory.LocalizedStructureAbelianSheaf

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/-- Helper for Remark 18.41.2: the localized structure module `\mathcal O_U` on the slice site,
extended by zero to a sheaf of `\mathcal O`-modules on the ambient site. -/
abbrev localizedStructureModuleExtensionByZero :
    SheafOfModules (ringSheaf J 𝒪) :=
  (SheafOfModules.pullback (𝟙 ((ringSheaf J 𝒪).over U))).obj
    (SheafOfModules.unit ((ringSheaf J 𝒪).over U))

namespace LocalizedStructureModuleExtensionByZero

set_option quotPrecheck false in
scoped notation:max "j![" 𝒪:max ", " U:max "]" =>
  SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero _ 𝒪 U

end LocalizedStructureModuleExtensionByZero

/-- Helper for Remark 18.41.2: sections of the pulled-back sheaf over the slice terminal object are
the same as sections of the original sheaf over `U`. -/
private noncomputable def localizedSectionsEquivEvaluation
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    (SheafOfModules.over ℱ U).sections ≃
      (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ where
  toFun s := s.1 (op (Over.mk (𝟙 U)))
  invFun m :=
    (SheafOfModules.over ℱ U).val.sectionsMk
      (fun X ↦ (SheafOfModules.over ℱ U).val.map ((Over.mkIdTerminal.from X.unop).op) m)
      (fun X Y f ↦ by
        have h :
            (Over.mkIdTerminal.from X.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from X.unop)
            (Over.mkIdTerminal.from Y.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    ext X
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from X.unop).op)
  right_inv m := by
    -- Proof comment: evaluating the reconstructed section at the terminal object recovers the
    -- original value.
    change
      (SheafOfModules.over ℱ U).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h : Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using
      (SheafOfModules.over ℱ U).val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Remark 18.41.2: morphisms from `j_{U!}\mathcal O_U` into a module sheaf are
equivalent to sections over `U`. -/
noncomputable def localizedStructureModuleExtensionByZero_homEquiv
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    (localizedStructureModuleExtensionByZero J 𝒪 U ⟶ ℱ) ≃
      (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ :=
  (((SheafOfModules.pullbackPushforwardAdjunction
      (𝟙 ((ringSheaf J 𝒪).over U))).homEquiv
      (SheafOfModules.unit ((ringSheaf J 𝒪).over U)) ℱ).trans
    (SheafOfModules.over ℱ U).unitHomEquiv).trans
    (localizedSectionsEquivEvaluation J 𝒪 U ℱ)

end SheafOfModules.RingedSite

open _root_.SheafOfModules.RingedSite
  (ringSheaf localizedStructureModuleExtensionByZero localizedStructureModuleExtensionByZero_homEquiv)
open scoped SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero

namespace SheafOfModules

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable [HasBinaryProducts C] [HasBinaryProducts D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : C, HasWeakSheafify (JD.over (u.obj U)) AddCommGrpCat.{u}]
variable [∀ U : C, ∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}, (Over.post u).op.HasLeftKanExtension F]
variable (𝒪D : Sheaf JD CommRingCat.{u})

/-- The inverse-image structure sheaf `g^{-1}\mathcal O_\mathcal D`, viewed as a
`CommRingCat`-valued sheaf on `\mathcal C`. -/
abbrev inverseImageCommRingSheaf
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] (𝒪D : Sheaf JD CommRingCat.{u}) :
    Sheaf JC CommRingCat.{u} :=
  (u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D

/-- The inverse-image structure sheaf `g^{-1} \mathcal O_\mathcal D`, viewed as a
`RingCat`-valued sheaf on `\mathcal C`. -/
abbrev inverseImageRingSheaf
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] (𝒪D : Sheaf JD CommRingCat.{u}) :
    Sheaf JC RingCat.{u} :=
  ringSheaf JC ((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)

/-- Helper for Remark 18.41.2: the inverse-image structure sheaf on `\mathcal C`, viewed in
`CommRingCat`. -/
private abbrev sourceCommRingSheaf :
    Sheaf JC CommRingCat.{u} :=
  inverseImageCommRingSheaf (JC := JC) (JD := JD) u 𝒪D

/-- Helper for Remark 18.41.2: the inverse-image structure sheaf on `\mathcal C`, viewed in
`RingCat`. -/
private abbrev sourceRingSheaf :
    Sheaf JC RingCat.{u} :=
  inverseImageRingSheaf (JC := JC) (JD := JD) u 𝒪D

/-- The inverse-image functor on `\mathcal O_\mathcal D`-modules induced by the identity map on
`g^{-1}\mathcal O_\mathcal D`. -/
abbrev moduleInverseImage
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] (𝒪D : Sheaf JD CommRingCat.{u}) :
    SheafOfModules (ringSheaf JD 𝒪D) ⥤
      SheafOfModules (sourceRingSheaf (u := u) (𝒪D := 𝒪D)) :=
  SheafOfModules.pushforward
    (𝟙 (sourceRingSheaf (u := u) (𝒪D := 𝒪D)))

/-- The chosen lower shriek `g_! : \mathrm{Mod}(g^{-1}\mathcal O_\mathcal D) \to
\mathrm{Mod}(\mathcal O_\mathcal D)`, defined as the left adjoint of the inverse-image functor on
modules from Lemma `18.41.1`. -/
abbrev moduleLowerShriek
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] (𝒪D : Sheaf JD CommRingCat.{u}) :
    SheafOfModules (sourceRingSheaf (u := u) (𝒪D := 𝒪D)) ⥤
      SheafOfModules (ringSheaf JD 𝒪D) :=
  SheafOfModules.pullback
    (𝟙 (sourceRingSheaf (u := u) (𝒪D := 𝒪D)))

/-- The localized comparison morphism
`(g')^{Ab}_! \mathcal O_U \to \mathcal O_{u(U)}` from `18.41.2.1`, viewed in the fixed setup of
this remark. -/
abbrev localizedComparisonOnStructureSheaves
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] (𝒪D : Sheaf JD CommRingCat.{u}) (U : C) :
    ((Over.post u).sheafPullback AddCommGrpCat.{u}
        (JC.over U) (JD.over (u.obj U))).obj
      (((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)_[U]) ⟶
    (𝒪D)_[u.obj U] :=
  CategoryTheory.localizedComparisonOnStructureSheavesAux u 𝒪D U

/-- The local criterion from `18.41.2.1`: every slice-site comparison
`(g')^{Ab}_! \mathcal O_U \to \mathcal O_{u(U)}` is an isomorphism. -/
abbrev localizedComparisonMapsAreIso : Prop :=
  ∀ U : C,
    IsIso
      ((localizedComparisonOnStructureSheaves (u := u) (𝒪D := 𝒪D) U) :
        ((Over.post u).sheafPullback AddCommGrpCat.{u}
            (JC.over U) (JD.over (u.obj U))).obj
          (((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)_[U]) ⟶
        (𝒪D)_[u.obj U])

/-- The fixed-context local hypothesis that all comparison maps from `18.41.2.1` are
isomorphisms. -/
abbrev localizedComparisonCondition : Prop :=
  ∀ U : C,
    IsIso
      ((localizedComparisonOnStructureSheaves (u := u) (𝒪D := 𝒪D) U) :
        ((Over.post u).sheafPullback AddCommGrpCat.{u}
            (JC.over U) (JD.over (u.obj U))).obj
          (((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)_[U]) ⟶
        (𝒪D)_[u.obj U])

/-- Helper for Remark 18.41.2: forgetting the module inverse-image functor to abelian sheaves
gives the usual inverse-image functor on underlying additive sheaves. -/
lemma moduleInverseImage_comp_toSheaf_eq :
    moduleInverseImage u 𝒪D ⋙
        SheafOfModules.toSheaf (sourceRingSheaf (u := u) (𝒪D := 𝒪D)) =
      SheafOfModules.toSheaf (ringSheaf JD 𝒪D) ⋙
        u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD :=
  rfl

/-- Helper for Remark 18.41.2: the extension-by-zero Hom/evaluation equivalence is natural in the
target module sheaf on an arbitrary ringed site. -/
private theorem localizedStructureModuleExtensionByZeroHomEquivNaturalityLocal
    {E : Type u} [Category.{u} E] [HasBinaryProducts E]
    {J : GrothendieckTopology E}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {𝒪 : Sheaf J CommRingCat.{u}}
    (U : E) {ℱ 𝒢 : SheafOfModules (ringSheaf J 𝒪)}
    (β : j![𝒪, U] ⟶ ℱ) (α : ℱ ⟶ 𝒢) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U 𝒢 (β ≫ α) =
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ β) := by
  -- Proof comment: the owner equivalence is assembled functorially in the target sheaf.
  rfl

/-- Helper for Remark 18.41.2: morphisms out of a coproduct of extension-by-zero generators are
equivalent to families of chosen sections. -/
private noncomputable def localizedStructureModuleExtensionByZeroCoproductHomEquivLocal
    {E : Type u} [Category.{u} E] [HasBinaryProducts E]
    {J : GrothendieckTopology E}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {𝒪 : Sheaf J CommRingCat.{u}}
    {I : Type u} (U : I → E) (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ((∐ fun i : I ↦ j![𝒪, (U i)]) ⟶ ℱ) ≃
      (∀ i : I, (SheafOfModules.evaluation (ringSheaf J 𝒪) (op (U i))).obj ℱ) where
  toFun α i :=
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ
      (Sigma.ι (fun i : I ↦ j![𝒪, (U i)]) i ≫ α)
  invFun s :=
    Sigma.desc
      (fun i : I ↦
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ).symm (s i))
  left_inv α := by
    -- Proof comment: a coproduct morphism is determined by its restrictions to the summands.
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_desc]
    exact Equiv.symm_apply_apply
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ)
      (Sigma.ι (fun i : I ↦ j![𝒪, (U i)]) i ≫ α)
  right_inv s := by
    -- Proof comment: evaluating the reconstructed morphism on each summand recovers the
    -- prescribed section.
    funext i
    change
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ
          (Sigma.ι (fun k : I ↦ j![𝒪, (U k)]) i ≫
            Sigma.desc
              (fun k : I ↦
                (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U k) ℱ).symm
                  (s k))) =
        s i
    rw [Limits.Sigma.ι_desc]
    exact Equiv.apply_symm_apply
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ)
      (s i)

/-- Helper for Remark 18.41.2: every module sheaf admits an epimorphism from a coproduct of the
standard generators `j_{U!}\mathcal O_U`. -/
private theorem existsEpiFromGeneratorCoproduct
    {E : Type u} [Category.{u} E] [HasBinaryProducts E]
    {J : GrothendieckTopology E}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {𝒪 : Sheaf J CommRingCat.{u}}
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ∃ (I : Type u) (U : I → E)
      (φ : (∐ fun i : I ↦ j![𝒪, (U i)]) ⟶ ℱ), Epi φ := by
  let I : Type u := Σ U : E, (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ
  let U : I → E := fun i ↦ i.1
  let φ : (∐ fun i : I ↦ j![𝒪, (U i)]) ⟶ ℱ :=
    (localizedStructureModuleExtensionByZeroCoproductHomEquivLocal U ℱ).symm
      (fun i ↦ i.2)
  refine ⟨I, U, φ, ?_⟩
  refine ⟨?_⟩
  intro 𝒢 α β hαβ
  -- Proof comment: test equality on the summand indexed by the given local section.
  ext V s
  let i : I := ⟨V.unop, s⟩
  have hcomp := congrArg
    (fun ψ ↦ localizedStructureModuleExtensionByZeroCoproductHomEquivLocal U 𝒢 ψ)
    hαβ
  have hi := congrFun hcomp i
  have hi' :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) ≫ α) =
        localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) ≫ β) := by
    simpa [localizedStructureModuleExtensionByZeroCoproductHomEquivLocal] using hi
  have hφi :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ
          (Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) = s := by
    let hφfam := Equiv.apply_symm_apply
      (localizedStructureModuleExtensionByZeroCoproductHomEquivLocal U ℱ)
      (fun j : I ↦ j.2)
    have hφi' := congrFun hφfam i
    simpa [I, U, i, φ, localizedStructureModuleExtensionByZeroCoproductHomEquivLocal] using hφi'
  have hleft :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) ≫ α) =
        ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op (U i))).map α) s := by
    rw [localizedStructureModuleExtensionByZeroHomEquivNaturalityLocal
      (J := J) (𝒪 := 𝒪) (U := U i)
      (β := Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) (α := α)]
    rw [hφi]
  have hright :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) ≫ β) =
        ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op (U i))).map β) s := by
    rw [localizedStructureModuleExtensionByZeroHomEquivNaturalityLocal
      (J := J) (𝒪 := 𝒪) (U := U i)
      (β := Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) (α := β)]
    rw [hφi]
  rw [hleft, hright] at hi'
  simpa [I, U, i] using hi'

/-- Helper for Remark 18.41.2: an epimorphism together with an epimorphic cover of its kernel
realizes the target as the cokernel of the composite map. -/
private noncomputable def cokernelIsoOfEpiKernelCover
    {E : Type u} [Category.{u} E]
    {J : GrothendieckTopology E}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {𝒪 : Sheaf J CommRingCat.{u}}
    {A K X : SheafOfModules (ringSheaf J 𝒪)} (φ : A ⟶ X) (ψ : K ⟶ kernel φ)
    [Epi φ] [Epi ψ] :
    X ≅ cokernel (ψ ≫ kernel.ι φ) := by
  let Mod := SheafOfModules (ringSheaf J 𝒪)
  let _ : Abelian Mod := SheafOfModules.instAbelian (ringSheaf J 𝒪)
  let S : ShortComplex Mod :=
    ShortComplex.mk (ψ ≫ kernel.ι φ) φ (by simp [Category.assoc, kernel.condition])
  let T : ShortComplex Mod :=
    ShortComplex.mk (kernel.ι φ) φ (by simp)
  have hTExact : T.Exact := by
    -- Proof comment: the canonical kernel row is exact by the kernel universal property.
    simpa [T] using ShortComplex.exact_of_f_is_kernel T (kernelIsKernel φ)
  let η : S ⟶ T :=
    { τ₁ := ψ
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, T, Category.assoc]
      comm₂₃ := by simp [S, T] }
  have hSExact : S.Exact := by
    -- Proof comment: exactness descends across the epimorphic left comparison `ψ`.
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono η).2 hTExact
  obtain ⟨hcolim⟩ := (S.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hSExact, inferInstance⟩
  -- Proof comment: compare the explicit cokernel point with the chosen cokernel of
  -- `ψ ≫ kernel.ι φ`.
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (ψ ≫ kernel.ι φ)) hcolim

/-- Helper for Remark 18.41.2: the canonical comparison from abelian lower shriek after forgetting
to forgetting after module lower shriek, obtained as the mate of the evident inverse-image square.
-/
noncomputable def lowerShriekToSheafComparison :
    SheafOfModules.toSheaf (sourceRingSheaf (u := u) (𝒪D := 𝒪D)) ⋙
        u.sheafPullback AddCommGrpCat.{u} JC JD ⟶
      moduleLowerShriek u 𝒪D ⋙
        SheafOfModules.toSheaf (ringSheaf JD 𝒪D) :=
  -- Proof comment: the right-adjoint square is definitional after forgetting module structure, so
  -- `mateEquiv` produces the desired comparison on the chosen left adjoints.
  ((mateEquiv
      (SheafOfModules.pullbackPushforwardAdjunction
        (𝟙 (sourceRingSheaf (u := u) (𝒪D := 𝒪D))))
      (u.sheafAdjunctionContinuous AddCommGrpCat.{u} JC JD)).symm
      (show
        TwoSquare
          (moduleInverseImage u 𝒪D)
          (SheafOfModules.toSheaf (ringSheaf JD 𝒪D))
          (SheafOfModules.toSheaf (sourceRingSheaf (u := u) (𝒪D := 𝒪D)))
          (u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD) from
        TwoSquare.mk
          (moduleInverseImage u 𝒪D)
          (SheafOfModules.toSheaf (ringSheaf JD 𝒪D))
          (SheafOfModules.toSheaf (sourceRingSheaf (u := u) (𝒪D := 𝒪D)))
          (u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD)
          (eqToHom (show
            moduleInverseImage u 𝒪D ⋙
                SheafOfModules.toSheaf (sourceRingSheaf (u := u) (𝒪D := 𝒪D)) =
              SheafOfModules.toSheaf (ringSheaf JD 𝒪D) ⋙
                u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD by
            rfl)))).natTrans

/-- Helper for Remark 18.41.2: every source module sheaf admits a two-step cokernel presentation
by coproducts of the standard generators `j_{U!}\mathcal O_U`. -/
lemma exists_generator_cokernelPresentation
    (ℱ : SheafOfModules
      (sourceRingSheaf (u := u) (𝒪D := 𝒪D))) :
    ∃ (I K : Type u) (U : I → C) (V : K → C)
      (r :
        (∐ fun k : K ↦
          j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), (V k)]) ⟶
          (∐ fun i : I ↦
            j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), (U i)])),
      Nonempty (ℱ ≅ cokernel r) := by
  rcases existsEpiFromGeneratorCoproduct
      (J := JC) (𝒪 := sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)) ℱ with
    ⟨I, U, φ, hφ⟩
  rcases existsEpiFromGeneratorCoproduct
      (J := JC) (𝒪 := sourceCommRingSheaf (u := u) (𝒪D := 𝒪D))
      (kernel φ) with
    ⟨K, V, ψ, hψ⟩
  letI : Epi φ := hφ
  letI : Epi ψ := hψ
  let r :
      (∐ fun k : K ↦
        j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), (V k)]) ⟶
        (∐ fun i : I ↦
          j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), (U i)]) :=
    ψ ≫ kernel.ι φ
  -- Proof comment: the first epimorphism covers `ℱ`, the second covers its kernel, and the
  -- standard epi-kernel-cover package identifies `ℱ` with the resulting cokernel.
  refine ⟨I, K, U, V, r, ?_⟩
  exact ⟨by
    simpa [r] using
    (cokernelIsoOfEpiKernelCover
      (J := JC)
      (𝒪 := sourceCommRingSheaf (u := u) (𝒪D := 𝒪D))
      (φ := φ) (ψ := ψ))⟩

/-- Helper for Remark 18.41.2: the lower-shriek image of the standard generator is represented by
the standard target generator in the module category. -/
private noncomputable def moduleLowerShriekGeneratorHomEquiv
    (U : C) (ℱ : SheafOfModules (ringSheaf JD 𝒪D)) :
    ((moduleLowerShriek u 𝒪D).obj
        (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U]) ⟶ ℱ) ≃
      (j![𝒪D, (u.obj U)] ⟶ ℱ) :=
  (((SheafOfModules.pullbackPushforwardAdjunction
      (𝟙 (sourceRingSheaf (u := u) (𝒪D := 𝒪D)))).homEquiv _ _).trans
      (localizedStructureModuleExtensionByZero_homEquiv JC
        (sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)) U
        ((moduleInverseImage u 𝒪D).obj ℱ))).trans
    ((Equiv.refl _).trans
      (localizedStructureModuleExtensionByZero_homEquiv JD 𝒪D (u.obj U) ℱ).symm)

/-- Helper for Remark 18.41.2: the extension-by-zero Hom/evaluation equivalence is natural in the
target module sheaf on the source site. -/
private theorem localizedStructureModuleExtensionByZeroHomEquivSourceNaturality
    (U : C)
    {ℱ 𝒢 : SheafOfModules
      (sourceRingSheaf (u := u) (𝒪D := 𝒪D))}
    (β :
      j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U] ⟶ ℱ)
    (α : ℱ ⟶ 𝒢) :
    localizedStructureModuleExtensionByZero_homEquiv JC
        (sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)) U 𝒢 (β ≫ α) =
      ((SheafOfModules.evaluation
          (sourceRingSheaf (u := u) (𝒪D := 𝒪D)) (op U)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv JC
          (sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)) U ℱ β) := by
  -- Proof comment: the owner equivalence is defined functorially in the target sheaf.
  rfl

/-- Helper for Remark 18.41.2: the extension-by-zero Hom/evaluation equivalence is natural in the
target module sheaf on the target site. -/
private theorem localizedStructureModuleExtensionByZeroHomEquivTargetSymmNaturality
    (U : C) {ℱ 𝒢 : SheafOfModules (ringSheaf JD 𝒪D)}
    (s : (SheafOfModules.evaluation (ringSheaf JD 𝒪D) (op (u.obj U))).obj ℱ)
    (α : ℱ ⟶ 𝒢) :
    (localizedStructureModuleExtensionByZero_homEquiv JD 𝒪D (u.obj U) 𝒢).symm
        (((SheafOfModules.evaluation (ringSheaf JD 𝒪D) (op (u.obj U))).map α) s) =
      (localizedStructureModuleExtensionByZero_homEquiv JD 𝒪D (u.obj U) ℱ).symm s ≫ α := by
  -- Proof comment: apply the forward equivalence and use the corresponding right naturality.
  apply (localizedStructureModuleExtensionByZero_homEquiv JD 𝒪D (u.obj U) 𝒢).injective
  rw [localizedStructureModuleExtensionByZeroHomEquivNaturalityLocal
    (J := JD) (𝒪 := 𝒪D) (U := u.obj U)
    (β := (localizedStructureModuleExtensionByZero_homEquiv JD 𝒪D (u.obj U) ℱ).symm s)
    (α := α)]
  simp

/-- Helper for Remark 18.41.2: the generator Hom-equivalence is natural in the target module
sheaf. -/
private theorem moduleLowerShriekGeneratorHomEquivNaturality
    (U : C) {ℱ 𝒢 : SheafOfModules (ringSheaf JD 𝒪D)}
    (β :
      (moduleLowerShriek u 𝒪D).obj
          (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U]) ⟶ ℱ)
    (α : ℱ ⟶ 𝒢) :
    moduleLowerShriekGeneratorHomEquiv (u := u) (𝒪D := 𝒪D) U 𝒢 (β ≫ α) =
      moduleLowerShriekGeneratorHomEquiv (u := u) (𝒪D := 𝒪D) U ℱ β ≫ α := by
  -- Proof comment: each stage of the composite equivalence is right-natural.
  simp [moduleLowerShriekGeneratorHomEquiv,
    localizedStructureModuleExtensionByZeroHomEquivSourceNaturality,
    localizedStructureModuleExtensionByZeroHomEquivTargetSymmNaturality]

/-- Helper for Remark 18.41.2: the chosen forward map from the generator image to the target
generator. -/
private noncomputable def moduleLowerShriekGeneratorHom
    (U : C) :
    (moduleLowerShriek u 𝒪D).obj
        (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U]) ⟶
      j![𝒪D, (u.obj U)] :=
  (moduleLowerShriekGeneratorHomEquiv (u := u) (𝒪D := 𝒪D) U
    (j![𝒪D, (u.obj U)])).symm (𝟙 _)

/-- Helper for Remark 18.41.2: the chosen inverse map from the target generator to the generator
image. -/
private noncomputable def moduleLowerShriekGeneratorInv
    (U : C) :
    j![𝒪D, (u.obj U)] ⟶
      (moduleLowerShriek u 𝒪D).obj
        (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U]) :=
  moduleLowerShriekGeneratorHomEquiv (u := u) (𝒪D := 𝒪D) U
    ((moduleLowerShriek u 𝒪D).obj
      (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U])) (𝟙 _)

/-- Helper for Remark 18.41.2: the chosen forward and inverse maps are mutually inverse on the
generator image. -/
private theorem moduleLowerShriekGeneratorHom_inv_id
    (U : C) :
    moduleLowerShriekGeneratorHom (u := u) (𝒪D := 𝒪D) U ≫
        moduleLowerShriekGeneratorInv (u := u) (𝒪D := 𝒪D) U =
      𝟙 ((moduleLowerShriek u 𝒪D).obj
        (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U])) := by
  -- Proof comment: apply the representing equivalence and reduce to the identity on the target
  -- generator.
  apply (moduleLowerShriekGeneratorHomEquiv (u := u) (𝒪D := 𝒪D) U
    ((moduleLowerShriek u 𝒪D).obj
      (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U]))).injective
  simp [moduleLowerShriekGeneratorInv, moduleLowerShriekGeneratorHom,
    moduleLowerShriekGeneratorHomEquivNaturality]

/-- Helper for Remark 18.41.2: the chosen forward and inverse maps are mutually inverse on the
target generator. -/
private theorem moduleLowerShriekGeneratorInv_hom_id
    (U : C) :
    moduleLowerShriekGeneratorInv (u := u) (𝒪D := 𝒪D) U ≫
        moduleLowerShriekGeneratorHom (u := u) (𝒪D := 𝒪D) U =
      𝟙 (j![𝒪D, (u.obj U)]) := by
  -- Proof comment: apply the representing equivalence and reduce to the identity on the source
  -- generator image.
  apply (moduleLowerShriekGeneratorHomEquiv (u := u) (𝒪D := 𝒪D) U
    (j![𝒪D, (u.obj U)])).injective
  simp [moduleLowerShriekGeneratorInv, moduleLowerShriekGeneratorHom,
    moduleLowerShriekGeneratorHomEquivNaturality]

/-- Helper for Remark 18.41.2: the module lower-shriek sends the standard source generator to the
standard target generator through a canonical module isomorphism. -/
noncomputable def moduleLowerShriekGeneratorIso
    (U : C) :
    (moduleLowerShriek u 𝒪D).obj
        (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U]) ≅
      j![𝒪D, (u.obj U)] where
  hom := moduleLowerShriekGeneratorHom (u := u) (𝒪D := 𝒪D) U
  inv := moduleLowerShriekGeneratorInv (u := u) (𝒪D := 𝒪D) U
  hom_inv_id := moduleLowerShriekGeneratorHom_inv_id (u := u) (𝒪D := 𝒪D) U
  inv_hom_id := moduleLowerShriekGeneratorInv_hom_id (u := u) (𝒪D := 𝒪D) U

/-- Helper for Remark 18.41.2: forgetting the module generator isomorphism rigidifies the codomain
of the generator comparison in the additive sheaf category. -/
private noncomputable abbrev toSheafModuleLowerShriekGeneratorIso
    (U : C) :
    (SheafOfModules.toSheaf (ringSheaf JD 𝒪D)).mapIso
      (moduleLowerShriekGeneratorIso (u := u) (𝒪D := 𝒪D) U) :=
  (SheafOfModules.toSheaf (ringSheaf JD 𝒪D)).mapIso
    (moduleLowerShriekGeneratorIso (u := u) (𝒪D := 𝒪D) U)

/-- Helper for Remark 18.41.2: after rigidifying the codomain by the forgotten generator
isomorphism, the generator component of the global comparison is exactly the localized comparison
map from `18.41.2.1`. -/
private theorem generatorComparison_comp_generatorIso
    (U : C) :
    ((lowerShriekToSheafComparison u 𝒪D).app
      (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U])) ≫
        (toSheafModuleLowerShriekGeneratorIso (u := u) (𝒪D := 𝒪D) U).hom =
      localizedComparisonOnStructureSheaves (u := u) (𝒪D := 𝒪D) U := by
  -- Proof comment: move the equality to the slice-site right-adjoint Hom-set, where both sides
  -- normalize to the same canonical comparison map.
  apply ((Over.post u).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (JC.over U) (JD.over (u.obj U))).homEquiv _ _.injective
  simpa [localizedComparisonOnStructureSheaves, lowerShriekToSheafComparison,
    toSheafModuleLowerShriekGeneratorIso, moduleLowerShriekGeneratorIso,
    moduleLowerShriekGeneratorHom, moduleLowerShriekGeneratorInv,
    moduleLowerShriekGeneratorHomEquiv, moduleInverseImage_comp_toSheaf_eq] using
    (CategoryTheory.localizedComparisonOnStructureSheavesAux_homEquiv u 𝒪D U)

/-- Helper for Remark 18.41.2: if the localized comparison map from `18.41.2.1` is an
isomorphism for `U`, then the global comparison on the generator `j_{U!}\mathcal O_U` is an
isomorphism as well. -/
lemma comparisonAppIsIsoOfGenerator
    (hlocal :
      ∀ U : C,
        IsIso
          ((localizedComparisonOnStructureSheaves (u := u) (𝒪D := 𝒪D) U) :
            ((Over.post u).sheafPullback AddCommGrpCat.{u}
                (JC.over U) (JD.over (u.obj U))).obj
              (((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)_[U]) ⟶
            (𝒪D)_[u.obj U]))
    (U : C) :
    IsIso ((lowerShriekToSheafComparison u 𝒪D).app
      (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U])) := by
  -- Proof comment: identify the generator component with the globalized form of the localized
  -- comparison map, then read off the result from `hlocal U`.
  -- Route correction: the old route stalled because the codomain lived in the wrong spelling
  -- world. The new route first rigidifies that codomain via `moduleLowerShriekGeneratorIso`.
  let e := toSheafModuleLowerShriekGeneratorIso (u := u) (𝒪D := 𝒪D) U
  have hcomp :
      IsIso
        (((lowerShriekToSheafComparison u 𝒪D).app
          (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U])) ≫ e.hom) := by
    -- Proof comment: rewrite the composite to the localized comparison map from `18.41.2.1`.
    rw [generatorComparison_comp_generatorIso (u := u) (𝒪D := 𝒪D) U]
    exact hlocal U
  let _ :
      IsIso
        (((lowerShriekToSheafComparison u 𝒪D).app
          (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U])) ≫ e.hom) := hcomp
  have hrewrite :
      (lowerShriekToSheafComparison u 𝒪D).app
          (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U]) =
        (((lowerShriekToSheafComparison u 𝒪D).app
          (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U])) ≫ e.hom) ≫ inv e.hom := by
    -- Proof comment: undo the postcomposition with the rigidifying iso.
    rw [Category.assoc, IsIso.hom_inv_id_assoc]
  -- Proof comment: the generator comparison is a composite of the already-known isomorphism above
  -- with the inverse of the rigidifying isomorphism.
  simpa [hrewrite] using
    (inferInstance :
      IsIso
        ((((lowerShriekToSheafComparison u 𝒪D).app
          (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U])) ≫ e.hom) ≫ inv e.hom))

/-- Helper for Remark 18.41.2: once the comparison is an isomorphism on every generator, it is an
isomorphism on every coproduct of generators. -/
lemma comparisonAppIsIsoOfGeneratorCoproduct
    (hgen :
      ∀ U : C,
        IsIso ((lowerShriekToSheafComparison u 𝒪D).app
          (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U])))
    {I : Type u} (U : I → C) :
    IsIso ((lowerShriekToSheafComparison u 𝒪D).app
      (∐ fun i : I ↦
        j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), (U i)])) := by
  -- Proof comment: package the stagewise generator isomorphisms into a natural isomorphism of
  -- discrete diagrams and pass to colimits using preservation of coproducts by both left
  -- adjoints.
  let G : Discrete I ⥤
      SheafOfModules (sourceRingSheaf (u := u) (𝒪D := 𝒪D)) :=
    Discrete.functor
      (fun i ↦ j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), (U i)])
  let τ := lowerShriekToSheafComparison u 𝒪D
  let _ :
      PreservesColimitsOfShape (Discrete I)
        (SheafOfModules.toSheaf (sourceRingSheaf (u := u) (𝒪D := 𝒪D)) ⋙
          u.sheafPullback AddCommGrpCat.{u} JC JD) := by
    infer_instance
  let _ :
      PreservesColimitsOfShape (Discrete I)
        (moduleLowerShriek u 𝒪D ⋙
          SheafOfModules.toSheaf (ringSheaf JD 𝒪D)) := by
    infer_instance
  have hτ : ∀ j : Discrete I, IsIso ((Functor.whiskerLeft G τ).app j) := by
    intro j
    simpa [G, τ] using hgen (U j.as)
  letI : IsIso (Functor.whiskerLeft G τ) :=
    NatIso.isIso_of_isIso_app (Functor.whiskerLeft G τ)
  -- Proof comment: once the whiskered comparison is a natural isomorphism, its component at the
  -- coproduct object is an isomorphism because both comparison functors preserve this colimit.
  simpa [G, τ] using
    isIso_app_coconePt_of_preservesColimit G τ (colimit.cocone G) (colimit.isColimit G)

/-- Helper for Remark 18.41.2: if a module sheaf is presented as a cokernel of a map between
coproducts of generators, then the comparison is an isomorphism on that module sheaf. -/
lemma comparisonAppIsIsoOfCokernelPresentation
    (hcoprod :
      ∀ {I : Type u} (U : I → C),
        IsIso ((lowerShriekToSheafComparison u 𝒪D).app
          (∐ fun i : I ↦
            j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), (U i)])))
    {I K : Type u}
    (U : I → C) (V : K → C)
    (r :
      (∐ fun k : K ↦
        j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), (V k)]) ⟶
        (∐ fun i : I ↦
          j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), (U i)]))
    (ℱ : SheafOfModules
      (sourceRingSheaf (u := u) (𝒪D := 𝒪D)))
    (hℱ : ℱ ≅ cokernel r) :
    IsIso ((lowerShriekToSheafComparison u 𝒪D).app ℱ) := by
  -- Proof comment: compare the two preserved cokernel cocones for `r`, deduce the result for
  -- `cokernel r`, and then transport across the presentation isomorphism `hℱ`.
  let D :
      WalkingParallelPair ⥤
        SheafOfModules (sourceRingSheaf (u := u) (𝒪D := 𝒪D)) :=
    parallelPair r 0
  let F :=
    SheafOfModules.toSheaf (sourceRingSheaf (u := u) (𝒪D := 𝒪D)) ⋙
      u.sheafPullback AddCommGrpCat.{u} JC JD
  let G :=
    moduleLowerShriek u 𝒪D ⋙
      SheafOfModules.toSheaf (ringSheaf JD 𝒪D)
  let τ := lowerShriekToSheafComparison u 𝒪D
  let _ : PreservesColimitsOfShape WalkingParallelPair F := by
    infer_instance
  let _ : PreservesColimitsOfShape WalkingParallelPair G := by
    infer_instance
  have hτ : ∀ j : WalkingParallelPair, IsIso ((Functor.whiskerLeft D τ).app j) := by
    intro j
    cases j
    · simpa [D, τ] using hcoprod V
    · simpa [D, τ] using hcoprod U
  letI : IsIso (Functor.whiskerLeft D τ) :=
    NatIso.isIso_of_isIso_app (Functor.whiskerLeft D τ)
  have hcok : IsIso (τ.app (cokernel r)) := by
    -- Proof comment: the whiskered comparison is an isomorphism on each diagram object, so it is
    -- an isomorphism at the colimit point `cokernel r`.
    simpa [D, τ] using
      isIso_app_coconePt_of_preservesColimit D τ (colimit.cocone D) (colimit.isColimit D)
  letI : IsIso (τ.app (cokernel r)) := hcok
  have htransport :
      τ.app ℱ = F.map hℱ.hom ≫ τ.app (cokernel r) ≫ inv (G.map hℱ.hom) := by
    -- Proof comment: rewrite the comparison at `ℱ` using naturality along the presentation
    -- isomorphism `hℱ`.
    calc
      τ.app ℱ = τ.app ℱ ≫ G.map hℱ.hom ≫ inv (G.map hℱ.hom) := by
        rw [Category.assoc, IsIso.hom_inv_id_assoc]
      _ = F.map hℱ.hom ≫ τ.app (cokernel r) ≫ inv (G.map hℱ.hom) := by
        rw [(lowerShriekToSheafComparison u 𝒪D).naturality hℱ.hom, Category.assoc]
  -- Proof comment: `τ.app ℱ` is conjugate to the already-known cokernel comparison by functorial
  -- images of the presentation isomorphism.
  simpa [F, G, τ, htransport] using
    (inferInstance :
      IsIso (F.map hℱ.hom ≫ τ.app (cokernel r) ≫ inv (G.map hℱ.hom)))

-- Proof sketch: the proof of Lemma `18.41.1` constructs the comparison from abelian lower shriek
-- followed by forgetfulness to forgetting after module lower shriek by checking the generating
-- modules `j_{U!}\mathcal O_U`. If each localized comparison map
-- `compare_on_localizations u 𝒪D U` is an isomorphism, then the comparison is an isomorphism on
-- those generators, hence the induced transformation of functors is a natural isomorphism.
/-- Remark 18.41.2: in general the square formed by lower shriek on modules, lower shriek on
underlying abelian sheaves, and the forgetful functors need not commute. However, if for every
object `U` of `\mathcal C` the localized comparison morphism
`(g')^{Ab}_! \mathcal O_U \to \mathcal O_{u(U)}` from `18.41.2.1` is an isomorphism, then the
comparison between `g^{Ab}_! ∘ forget` and `forget ∘ g_!` is a natural isomorphism. -/
theorem lowerShriek_toSheaf_comparison_exists_of_compare_on_localizations
    (hlocal :
      ∀ U : C,
        IsIso
          ((localizedComparisonOnStructureSheaves (u := u) (𝒪D := 𝒪D) U) :
            ((Over.post u).sheafPullback AddCommGrpCat.{u}
                (JC.over U) (JD.over (u.obj U))).obj
              (((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)_[U]) ⟶
            (𝒪D)_[u.obj U])) :
    ∃ comparison :
      SheafOfModules.toSheaf
        (sourceRingSheaf (u := u) (𝒪D := 𝒪D)) ⋙
        u.sheafPullback AddCommGrpCat.{u} JC JD ⟶
        moduleLowerShriek u 𝒪D ⋙
          SheafOfModules.toSheaf (ringSheaf JD 𝒪D),
      ∀ ℱ, IsIso (comparison.app ℱ) := by
  refine ⟨lowerShriekToSheafComparison u 𝒪D, ?_⟩
  intro ℱ
  -- Route correction: the remaining step is to prove that the canonical mate above is an
  -- isomorphism on the generators `j![𝒪, U]` via `18.41.2.1`, then bootstrap along the
  -- two-step cokernel presentation now isolated in `exists_generator_cokernelPresentation`.
  have hgen :
      ∀ U : C,
        IsIso ((lowerShriekToSheafComparison u 𝒪D).app
          (j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), U])) := by
    intro U
    exact comparisonAppIsIsoOfGenerator (u := u) (𝒪D := 𝒪D) hlocal U
  have hcoprod :
      ∀ {I : Type u} (U : I → C),
        IsIso ((lowerShriekToSheafComparison u 𝒪D).app
          (∐ fun i : I ↦
            j![(sourceCommRingSheaf (u := u) (𝒪D := 𝒪D)), (U i)])) := by
    intro I U
    exact comparisonAppIsIsoOfGeneratorCoproduct (u := u) (𝒪D := 𝒪D) hgen U
  rcases exists_generator_cokernelPresentation (u := u) (𝒪D := 𝒪D) ℱ with
    ⟨I, K, U, V, r, ⟨hℱ⟩⟩
  exact comparisonAppIsIsoOfCokernelPresentation
    (u := u) (𝒪D := 𝒪D) hcoprod U V r ℱ hℱ

end

end SheafOfModules
