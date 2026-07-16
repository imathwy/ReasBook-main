import Mathlib
import StacksProject_2024.stacks_project.Chap07.Lemma_7_35_3
import StacksProject_2024.stacks_project.Chap18.Remark_18_19_6
import StacksProject_2024.stacks_project.Chap18.Remark_18_19_7
import StacksProject_2024.stacks_project.Chap18.Lemma_18_36_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasBinaryProducts C]
variable [LocallySmall.{u} C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)
variable (p : GrothendieckTopology.Point.{u} J)

/- Domain-style sampling:
- primary domain: stalks of extension by zero for sheaves of modules on ringed sites;
- sampled owner declarations:
  `ringedSiteLocalizedExtensionByZero`,
  `ringedSiteLocalizedExtensionByZero_toSheaf`,
  `SheafOfModules.toSheaf`,
  `GrothendieckTopology.Point.sheafFiber`,
  `localizationLowerShriek_sheafFiberIsoSigma_pointOver_sheafFiber`;
- best owner abstraction: the Chapter 18 source-facing owner
  `ringedSiteLocalizedExtensionByZero J 𝒪 U`;
- primitive data: the structure sheaf `𝒪`, the object `U`, the point `p`, and the localized
  module `𝒢`;
- derived API: the stalk decomposition of the underlying additive sheaf of `j_{U!} 𝒢` as a
  coproduct over the localized points `p.over x`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma computing the additive stalk of `j_{U!} 𝒢` as a coproduct
    over localized points `p.over x`;
  `core/canonical`: `ringedSiteLocalizedExtensionByZero J 𝒪 U`,
    `SheafOfModules.toSheaf`, `ringSheaf`, `p.sheafFiber`, and the localized-point owners
    `p.over x`;
  `bridge/view`: `ringedSiteLocalizedExtensionByZero_toSheaf J 𝒪 U`, which identifies the
    underlying additive sheaf of the Chapter 18 owner with the Chapter 7 sheaf-level lower
    shriek, and the Chapter 7 stalk decomposition it feeds into. -/

/-- Objectwise stalk comparison induced by `ringedSiteLocalizedExtensionByZero_toSheaf`: after
forgetting the module structure, the stalk of the Chapter 18 extension-by-zero owner agrees
canonically with the stalk of the underlying additive sheaf-level lower shriek along `Over.star U`.
-/
noncomputable abbrev ringedSiteLocalizedExtensionByZero_toSheaf_stalkIso
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    (((ringedSiteLocalizedExtensionByZero J 𝒪 U) ⋙
          SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber).obj 𝒢) ≅
      ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
            (Over.star U).sheafPushforwardContinuous AddCommGrpCat.{u} J (J.over U) ⋙
            p.sheafFiber).obj 𝒢) :=
  (Functor.isoWhiskerRight (ringedSiteLocalizedExtensionByZero_toSheaf J 𝒪 U)
    (p.sheafFiber)).app 𝒢

/-- Helper for Lemma 18.38.1: the explicit presheaf lower-shriek model from Remark 18.19.7 for
the underlying additive presheaf of a localized module sheaf. -/
noncomputable abbrev localizedExtensionByZeroPresheafModel
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ((Over.forget U).op.lan.obj
    (((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).obj 𝒢).obj))

/-- Helper for Lemma 18.38.1: the slice-site module sheaf `𝒢` contributes only through its
underlying additive presheaf on `Over U`. -/
noncomputable abbrev localizedUnderlyingAdditivePresheaf
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).obj 𝒢).obj)

/-- Helper for Lemma 18.38.1: objectwise, the explicit Remark 18.19.7 presheaf model of
`j_{U!} 𝒢` is the coproduct over arrows `V ⟶ U` of the corresponding underlying presheaf-module
sections of `𝒢`. -/
noncomputable def localizedExtensionByZeroPresheafModel_objIsoSigma
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) (V : C) :
    (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢).obj (op V) ≅
      (∐ fun φ : V ⟶ U ↦
        (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢).obj (op (Over.mk φ))) := by
  -- The explicit presheaf model is the underlying additive presheaf of the presheaf-level
  -- extension-by-zero owner from Remark 18.19.7, so its values are the stated coproducts.
  simpa [localizedExtensionByZeroPresheafModel, localizedUnderlyingAdditivePresheaf] using
    (PresheafLocalizedExtensionByZero.localized_leftKanExtension_eval_iso_coproduct
      (U := U) (A := localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢) V)

/-- Helper for Lemma 18.38.1: under the explicit Remark 18.19.7 coproduct model, the summand
indexed by `φ : V ⟶ U` becomes the primitive left-Kan unit component at `op (Over.mk φ)`. -/
@[reassoc]
private lemma presheafLocalizedExtensionByZero_objIsoSigma_inv_ι_eq_leftKanUnit
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U))
    (V : C) (φ : V ⟶ U) :
    Limits.Sigma.ι
        (fun ψ : V ⟶ U ↦
          (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢).obj (op (Over.mk ψ)))
        φ ≫
      (localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 V).inv =
        ((Over.forget U).op.leftKanExtensionUnit
          (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢)).app (op (Over.mk φ)) := by
  -- Proof comment: unfold the chosen coproduct comparison only far enough to expose the canonical
  -- left-Kan colimit comparison. For the distinguished indexing object attached to `φ`, the
  -- selected summand injection is exactly the corresponding unit component.
  let Xφ : CostructuredArrow (Over.forget U).op (op V) :=
    CostructuredArrow.mk
      (show (Over.forget U).op.obj (op (Over.mk φ)) ⟶ op V from 𝟙 (op V))
  simpa [localizedExtensionByZeroPresheafModel_objIsoSigma,
    PresheafLocalizedExtensionByZero.localized_leftKanExtension_eval_iso_coproduct,
    localizedExtensionByZeroPresheafModel, localizedUnderlyingAdditivePresheaf, Xφ,
    Category.assoc] using
    ((Over.forget U).op.ι_leftKanExtensionObjIsoColimit_inv
      (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢) (op V) Xφ)

/-- Helper for Lemma 18.38.1: after rewriting the explicit Remark 18.19.7 model objectwise as a
coproduct over arrows into `U`, restriction along `f : V ⟶ W` sends the `φ : W ⟶ U` generator to
the `(f ≫ φ)` generator via the corresponding restriction map of the localized underlying
presheaf. -/
@[reassoc]
private lemma presheafLocalizedExtensionByZero_objIsoSigma_naturality_addCommGrp
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U))
    {V W : C} (f : V ⟶ W) (φ : W ⟶ U) :
    Limits.Sigma.ι
        (fun ψ : W ⟶ U ↦
          (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢).obj (op (Over.mk ψ)))
        φ ≫
      (localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 W).inv ≫
      (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢).map f.op ≫
      (localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 V).hom =
        (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢).map (Over.homMk f).op ≫
          Limits.Sigma.ι
            (fun ψ : V ⟶ U ↦
              (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢).obj (op (Over.mk ψ)))
            (f ≫ φ) := by
  -- Proof comment: this is the generatorwise naturality of the Remark 18.19.7 sigma model.
  -- We isolate it once here so the later fiber-descent arguments only use explicit generators.
  let A : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u} := localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢
  -- Route correction: the blocked coproduct naturality is easier one level lower, where the
  -- selected summand is the primitive left-Kan unit at `op (Over.mk φ)`.
  calc
    Limits.Sigma.ι
          (fun ψ : W ⟶ U ↦
            (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢).obj (op (Over.mk ψ)))
          φ ≫
        (localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 W).inv ≫
        (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢).map f.op ≫
        (localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 V).hom
        =
      ((Over.forget U).op.leftKanExtensionUnit A).app (op (Over.mk φ)) ≫
        (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢).map f.op ≫
        (localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 V).hom := by
          rw [presheafLocalizedExtensionByZero_objIsoSigma_inv_ι_eq_leftKanUnit
            (𝒪 := 𝒪) (U := U) (𝒢 := 𝒢) (V := W) (φ := φ)]
    _ =
      A.map (Over.homMk f).op ≫
        ((Over.forget U).op.leftKanExtensionUnit A).app (op (Over.mk (f ≫ φ))) ≫
        (localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 V).hom := by
          simpa [A, localizedExtensionByZeroPresheafModel, Category.assoc] using
            (((Over.forget U).op.leftKanExtensionUnit A).naturality
              ((Over.homMk f).op)).symm
    _ =
      (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢).map (Over.homMk f).op ≫
        Limits.Sigma.ι
          (fun ψ : V ⟶ U ↦
            (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢).obj (op (Over.mk ψ)))
          (f ≫ φ) := by
            simpa [A, Category.assoc] using
              (presheafLocalizedExtensionByZero_objIsoSigma_inv_ι_eq_leftKanUnit_assoc
                (𝒪 := 𝒪) (U := U) (𝒢 := 𝒢) (V := V) (φ := f ≫ φ)
                ((localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 V).hom)).symm

/-- Helper for Lemma 18.38.1: at a localized point `p.over x`, pulling an additive presheaf back
along `Over.forget U` and then taking the presheaf fiber computes the same colimit as taking the
ambient presheaf fiber at `p`. -/
private noncomputable def point_over_overPullback_presheafFiberObjIso_addCommGrp
    (x : p.fiber.obj U) (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (p.over x).presheafFiber.obj ((Over.forget U).op ⋙ P) ≅ p.presheafFiber.obj P := by
  -- The localized point and the ambient point are indexed by equivalent filtered element
  -- categories, so their presheaf-fiber colimits coincide.
  let e := FunctorToTypes.fromOverFunctorElementsEquivalence p.fiber x
  let t :=
    (p.presheafFiberCocone P).whisker (Over.forget (p.fiber.elementsMk U x)).op
  have ht : IsColimit t := by
    exact
      (Functor.Final.isColimitWhiskerEquiv (Over.forget (p.fiber.elementsMk U x)).op
        (p.presheafFiberCocone P)).symm
        (p.isColimitPresheafFiberCocone P)
  have ht' : IsColimit (t.whisker e.functor.op) := by
    exact (Functor.Final.isColimitWhiskerEquiv e.functor.op t).symm ht
  let c1 := (p.over x).isColimitPresheafFiberCocone ((Over.forget U).op ⋙ P)
  simpa [e, t] using IsColimit.coconePointUniqueUpToIso c1 ht'

/-- Helper for Lemma 18.38.1: the comparison map from a localized-point presheaf fiber to the
ambient presheaf fiber sends the generator indexed by `(V, y)` to the corresponding ambient
generator indexed by `y`. -/
@[reassoc]
private lemma point_over_overPullback_presheafFiberObjIso_addCommGrp_hom_fac
    (x : p.fiber.obj U) (P : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (V : Over U) (y : (p.over x).fiber.obj V) :
    (p.over x).toPresheafFiber V y ((Over.forget U).op ⋙ P) ≫
      (point_over_overPullback_presheafFiberObjIso_addCommGrp (U := U) (p := p) x P).hom =
        p.toPresheafFiber V.left y.1 P := by
  -- Both sides are induced by the same cocone leg after identifying the two final indexing
  -- categories used to compute the stalk.
  let e := FunctorToTypes.fromOverFunctorElementsEquivalence p.fiber x
  let t :=
    (p.presheafFiberCocone P).whisker (Over.forget (p.fiber.elementsMk U x)).op
  have ht : IsColimit t := by
    exact
      (Functor.Final.isColimitWhiskerEquiv (Over.forget (p.fiber.elementsMk U x)).op
        (p.presheafFiberCocone P)).symm
        (p.isColimitPresheafFiberCocone P)
  have ht' : IsColimit (t.whisker e.functor.op) := by
    exact (Functor.Final.isColimitWhiskerEquiv e.functor.op t).symm ht
  let c1 := (p.over x).isColimitPresheafFiberCocone ((Over.forget U).op ⋙ P)
  simpa [point_over_overPullback_presheafFiberObjIso_addCommGrp, e, t] using
    IsColimit.comp_coconePointUniqueUpToIso_hom c1 ht' (op (Functor.elementsMk _ V y))

attribute [simp] point_over_overPullback_presheafFiberObjIso_addCommGrp_hom_fac
attribute [simp] point_over_overPullback_presheafFiberObjIso_addCommGrp_hom_fac_assoc

/-- Helper for Lemma 18.38.1: pulling an additive presheaf back to the slice site and then taking
the localized-point fiber agrees functorially with taking the ambient-point fiber. -/
noncomputable def point_over_overPullback_presheafFiberIso_addCommGrp
    (x : p.fiber.obj U) :
    (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ AddCommGrpCat.{u}).obj (Over.forget U).op ⋙
        (p.over x).presheafFiber ≅
      p.presheafFiber := by
  refine NatIso.ofComponents (fun P ↦ ?_) ?_
  · exact point_over_overPullback_presheafFiberObjIso_addCommGrp (U := U) (p := p) x P
  · intro P Q f
    apply (p.over x).presheafFiber_hom_ext
    intro V y
    -- The two composites agree on every generator of the localized presheaf fiber.
    change
      (p.over x).toPresheafFiber V y ((Over.forget U).op ⋙ P) ≫
          (p.over x).presheafFiber.map ((Over.forget U).op.whiskerLeft f) ≫
          (point_over_overPullback_presheafFiberObjIso_addCommGrp (U := U) (p := p) x Q).hom =
        (p.over x).toPresheafFiber V y ((Over.forget U).op ⋙ P) ≫
          (point_over_overPullback_presheafFiberObjIso_addCommGrp (U := U) (p := p) x P).hom ≫
          p.presheafFiber.map f
    repeat rw [← Category.assoc]
    rw [(p.over x).toPresheafFiber_naturality (((Over.forget U).op.whiskerLeft f)) V y]
    rw [Category.assoc]
    rw [point_over_overPullback_presheafFiberObjIso_addCommGrp_hom_fac]
    rw [point_over_overPullback_presheafFiberObjIso_addCommGrp_hom_fac]
    simpa using (p.toPresheafFiber_naturality f V.left y.1).symm

/-- Helper for Lemma 18.38.1: the presheaf fiber of the underlying additive presheaf of a
localized module sheaf at the point `p.over x` agrees with the corresponding sheaf fiber. -/
noncomputable def pointOver_underlyingPresheafFiberIsoSheafFiber
    (x : p.fiber.obj U)
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    (p.over x).presheafFiber.obj
      (((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).obj 𝒢).obj) ≅
      ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
          (p.over x).sheafFiber).obj 𝒢) :=
  (((p.over x).presheafToSheafCompSheafFiberIso AddCommGrpCat.{u}).app
      (((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).obj 𝒢).obj)).symm ≪≫
    (p.over x).sheafFiber.mapIso
      (sheafificationIso
        ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).obj 𝒢)).symm

/-- Helper for Lemma 18.38.1: taking coproducts of the localized-point presheaf-fiber/sheaf-fiber
comparisons gives the desired coproduct comparison on the target side. -/
noncomputable def coproduct_pointOver_underlyingPresheafFiberIsoSheafFiber
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    (∐ fun x : p.fiber.obj U ↦
      (p.over x).presheafFiber.obj
        (((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).obj 𝒢).obj)) ≅
      (∐ fun x : p.fiber.obj U ↦
        ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
            (p.over x).sheafFiber).obj 𝒢)) :=
  show colimit
      (Discrete.functor
        (fun x : p.fiber.obj U ↦
          (p.over x).presheafFiber.obj
            (((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).obj 𝒢).obj))) ≅
      colimit
        (Discrete.functor
          (fun x : p.fiber.obj U ↦
            ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
                (p.over x).sheafFiber).obj 𝒢))) from
    HasColimit.isoOfNatIso <|
      Discrete.natIso fun x : Discrete (p.fiber.obj U) ↦
        pointOver_underlyingPresheafFiberIsoSheafFiber 𝒪 U p x.as 𝒢

/-- Helper for Lemma 18.38.1: after forgetting module structure, the Chapter 18 extension-by-zero
owner agrees at the stalk with the canonical Chapter 7 lower-shriek owner
`(Over.forget U).sheafPullback`. -/
noncomputable def ringedSiteLocalizedExtensionByZero_stalkIsoSheafPullback
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    (((ringedSiteLocalizedExtensionByZero J 𝒪 U) ⋙
        SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber).obj 𝒢) ≅
      p.sheafFiber.obj
        (((Over.forget U).sheafPullback AddCommGrpCat.{u} (J.over U) J).obj
          ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).obj 𝒢)) := by
  -- Proof comment: first forget module structure via Remark 18.19.6, then switch from the
  -- continuous direct image along `Over.star U` to the canonical lower-shriek owner along
  -- `Over.forget U` using the left-adjoint comparison of Lemma 7.23.1.
  refine ringedSiteLocalizedExtensionByZero_toSheaf_stalkIso 𝒪 U p 𝒢 ≪≫ ?_
  simpa using
    p.sheafFiber.mapIso
      (((sheafPullbackIso_sheafPushforwardContinuous_of_continuous_leftAdjoint
          (u := Over.forget U)
          (w := Over.star U)
          (adj := Over.forgetAdjStar U)
          (A := AddCommGrpCat.{u})).symm).app
        ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).obj 𝒢))

/-- Helper for Lemma 18.38.1: the canonical additive lower-shriek owner along `Over.forget U`
agrees with the associated sheaf of the explicit left-Kan presheaf model from Remark 18.19.7. -/
noncomputable def localizedLowerShriekAssociatedSheafIsoAddCommGrp
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    (((Over.forget U).sheafPullback AddCommGrpCat.{u} (J.over U) J).obj
      ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).obj 𝒢)) ≅
      (presheafToSheaf J AddCommGrpCat.{u}).obj
        (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢) := by
  let η :=
    ((Over.forget U).op.lan).map
      (toSheafify (J.over U) (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢))
  letI : IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map η) := by
    infer_instance
  -- Proof comment: this is the additive-group analogue of Chapter 7, Lemma 7.27.1. We compare
  -- the chosen lower-shriek owner with the sheafified left-Kan extension and then simplify the
  -- left-Kan object to the explicit Remark 18.19.7 presheaf model.
  exact
    (CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso
      (Over.forget U) AddCommGrpCat.{u} (J.over U) J).app
        ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).obj 𝒢) ≪≫
      eqToIso rfl ≪≫
        (asIso ((presheafToSheaf J AddCommGrpCat.{u}).map η)).symm

/-- Helper for Lemma 18.38.1: after replacing the sheaf fiber of the additive lower shriek by the
fiber of its underlying presheaf, the remaining source-proof step is the coproduct decomposition
over the localized points `p.over x`. -/
noncomputable def ringedSiteLocalizedExtensionByZero_stalkIsoPresheafModel
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    (((ringedSiteLocalizedExtensionByZero J 𝒪 U) ⋙
        SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber).obj 𝒢) ≅
      p.presheafFiber.obj (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢) := by
  -- Route correction: the source proof computes the stalk of the explicit Remark 18.19.7
  -- presheaf model, so this bridge must first transport the sheaf-level owner to that model.
  -- The owner transport now factors through the canonical lower-shriek owner and then through the
  -- additive associated-sheaf comparison for the explicit left-Kan model.
  refine ringedSiteLocalizedExtensionByZero_stalkIsoSheafPullback 𝒪 U p 𝒢 ≪≫ ?_
  refine p.sheafFiber.mapIso (localizedLowerShriekAssociatedSheafIsoAddCommGrp 𝒪 U 𝒢) ≪≫ ?_
  exact (p.presheafToSheafCompSheafFiberIso AddCommGrpCat.{u}).app
    (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢)

/-- Helper for Lemma 18.38.1: at a stage `(V, y)` of the ambient presheaf fiber, the explicit
Remark 18.19.7 coproduct model is sent to the coproduct of localized fibers by placing the
`φ : V ⟶ U` summand into the localized point indexed by `p.fiber.map φ y`. -/
private noncomputable def localizedExtensionByZero_presheafFiberForwardStage
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U))
    (V : C) (y : p.fiber.obj V) :
    (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢).obj (op V) ⟶
      (∐ fun x : p.fiber.obj U ↦
        (p.over x).presheafFiber.obj (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢)) :=
  (localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 V).hom ≫
    Limits.Sigma.desc (fun φ : V ⟶ U ↦
      (p.over (p.fiber.map φ y)).toPresheafFiber (Over.mk φ) ⟨y, rfl⟩
          (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢) ≫
        Limits.Sigma.ι
          (fun x : p.fiber.obj U ↦
            (p.over x).presheafFiber.obj (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢))
          (p.fiber.map φ y))

/-- Helper for Lemma 18.38.1: the forward stage maps are compatible with the presheaf-fiber
relations, so they descend to a map from the ambient presheaf fiber. -/
private lemma localizedExtensionByZero_presheafFiber_forward_desc_compatible
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U))
    ⦃V W : C⦄ (f : V ⟶ W) (y : p.fiber.obj V) :
    (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢).map f.op ≫
        localizedExtensionByZero_presheafFiberForwardStage 𝒪 U p 𝒢 V y =
      localizedExtensionByZero_presheafFiberForwardStage 𝒪 U p 𝒢 W (p.fiber.map f y) := by
  -- Proof comment: after rewriting the ambient model as a coproduct over arrows to `U`, each
  -- generator is transported by the restriction formula above and then by localized-fiber
  -- naturality for `p.over (p.fiber.map (f ≫ φ) y)`.
  refine (cancel_epi ((localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 W).inv)).1 ?_
  -- Proof comment: once we move the ambient restriction through the sigma-model comparison,
  -- equality is checked on each `φ : W ⟶ U` summand separately.
  apply Limits.Sigma.hom_ext
  intro φ
  have hy : p.fiber.map (f ≫ φ) y = p.fiber.map φ (p.fiber.map f y) := by
    simpa using congr_fun (Functor.map_comp p.fiber f φ) y
  rw [Category.assoc]
  rw [localizedExtensionByZero_presheafFiberForwardStage, Category.assoc]
  rw [← Category.assoc]
  rw [presheafLocalizedExtensionByZero_objIsoSigma_naturality_addCommGrp
    (𝒪 := 𝒪) (U := U) (𝒢 := 𝒢) (f := f) (φ := φ)]
  rw [Category.assoc]
  rw [Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
  rw [hy]
  rw [← Category.assoc]
  rw [(p.over (p.fiber.map φ (p.fiber.map f y))).toPresheafFiber_w
    (Over.homMk f) ⟨y, by simpa [hy]⟩ (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢)]
  simp [localizedExtensionByZero_presheafFiberForwardStage, Category.assoc, hy]

/-- Helper for Lemma 18.38.1: the localized-point stage family defining the backward map satisfies
the presheaf-fiber descent relations. -/
@[reassoc]
private lemma localizedPointPresheafFiber_to_localizedExtensionByZero_presheafFiber_compatible
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U))
    (x : p.fiber.obj U) {V W : Over U} (g : V ⟶ W) (z : (p.over x).fiber.obj V) :
    (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢).map g.op ≫
        Limits.Sigma.ι
            (fun φ : V.left ⟶ U ↦
              (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢).obj (op (Over.mk φ)))
            V.hom ≫
      (localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 V.left).inv ≫
      p.toPresheafFiber V.left z.1 (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢) =
    Limits.Sigma.ι
          (fun φ : W.left ⟶ U ↦
            (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢).obj (op (Over.mk φ)))
          W.hom ≫
        (localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 W.left).inv ≫
        p.toPresheafFiber W.left ((p.over x).fiber.map g z).1
          (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢) := by
  -- Proof comment: rewrite the chosen `V.hom` summand as the transport of the `W.hom` summand
  -- along `g.left`, then finish with ambient presheaf-fiber functoriality.
  have hg : V.hom = g.left ≫ W.hom := Over.w g
  rw [hg]
  rw [← Category.assoc]
  rw [presheafLocalizedExtensionByZero_objIsoSigma_naturality_addCommGrp
    (𝒪 := 𝒪) (U := U) (𝒢 := 𝒢) (f := g.left) (φ := W.hom)]
  rw [Category.assoc]
  simpa using
    (p.toPresheafFiber_w g.left z.1 (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢))

/-- Helper for Lemma 18.38.1: each localized-point presheaf fiber includes into the ambient
presheaf fiber by inserting a local section into the summand indexed by the underlying arrow to
`U` and then using the ambient fiber generator at the same point value. -/
noncomputable def localizedPointPresheafFiber_to_localizedExtensionByZero_presheafFiber
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U))
    (x : p.fiber.obj U) :
    (p.over x).presheafFiber.obj (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢) ⟶
      p.presheafFiber.obj (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢) :=
  (p.over x).presheafFiberDesc
    (fun V z ↦
      Limits.Sigma.ι
          (fun φ : V.left ⟶ U ↦
            (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢).obj (op (Over.mk φ)))
          V.hom ≫
        (localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 V.left).inv ≫
        p.toPresheafFiber V.left z.1 (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢))
    (localizedPointPresheafFiber_to_localizedExtensionByZero_presheafFiber_compatible
      𝒪 U p 𝒢 x)

/-- Helper for Lemma 18.38.1: the ambient presheaf fiber maps to the coproduct of localized-point
presheaf fibers by descending the stagewise generator formula. -/
private noncomputable def localizedExtensionByZero_presheafFiberForward
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    p.presheafFiber.obj (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢) ⟶
      (∐ fun x : p.fiber.obj U ↦
        (p.over x).presheafFiber.obj (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢)) :=
  p.presheafFiberDesc
    (localizedExtensionByZero_presheafFiberForwardStage 𝒪 U p 𝒢)
    (localizedExtensionByZero_presheafFiber_forward_desc_compatible 𝒪 U p 𝒢)

/-- Helper for Lemma 18.38.1: each localized-point presheaf fiber includes into the ambient
presheaf fiber, and the coproduct of these inclusions gives the backward map. -/
private noncomputable def localizedExtensionByZero_presheafFiberBackward
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    (∐ fun x : p.fiber.obj U ↦
      (p.over x).presheafFiber.obj (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢)) ⟶
        p.presheafFiber.obj (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢) :=
  Limits.Sigma.desc
    (localizedPointPresheafFiber_to_localizedExtensionByZero_presheafFiber 𝒪 U p 𝒢)

/-- Helper for Lemma 18.38.1: on ambient generators, the forward map followed by the backward map
returns the original presheaf-fiber generator. -/
private lemma localizedExtensionByZero_presheafFiber_forward_backward_id
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    localizedExtensionByZero_presheafFiberForward 𝒪 U p 𝒢 ≫
      localizedExtensionByZero_presheafFiberBackward 𝒪 U p 𝒢 =
        𝟙 (p.presheafFiber.obj (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢)) := by
  -- Proof comment: both endomorphisms of the ambient presheaf fiber are determined by the
  -- generators `p.toPresheafFiber V y`, and on each generator the inserted localized summand is
  -- sent back to the same ambient generator.
  apply p.presheafFiber_hom_ext
  intro V y
  rw [← Category.assoc]
  rw [p.toPresheafFiber_presheafFiberDesc
    (localizedExtensionByZero_presheafFiberForwardStage 𝒪 U p 𝒢)
    (localizedExtensionByZero_presheafFiber_forward_desc_compatible 𝒪 U p 𝒢)]
  refine (cancel_epi ((localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 V).inv)).1 ?_
  apply Limits.Sigma.hom_ext
  intro φ
  rw [Category.assoc]
  rw [localizedExtensionByZero_presheafFiberForwardStage, Category.assoc, Limits.Sigma.ι_desc]
  rw [localizedExtensionByZero_presheafFiberBackward, Limits.Sigma.ι_desc]
  simp [localizedPointPresheafFiber_to_localizedExtensionByZero_presheafFiber, Category.assoc]

/-- Helper for Lemma 18.38.1: on each localized coproduct summand, the backward map followed by
the forward map returns the original localized generator. -/
private lemma localizedExtensionByZero_presheafFiber_backward_forward_id
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    localizedExtensionByZero_presheafFiberBackward 𝒪 U p 𝒢 ≫
      localizedExtensionByZero_presheafFiberForward 𝒪 U p 𝒢 =
        𝟙 (∐ fun x : p.fiber.obj U ↦
          (p.over x).presheafFiber.obj (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢)) := by
  -- Proof comment: both endomorphisms of the coproduct are determined by the summand injections,
  -- and inside each localized summand by the canonical generators.
  apply Limits.Sigma.hom_ext
  intro x
  apply (p.over x).presheafFiber_hom_ext
  intro V z
  rw [← Category.assoc]
  rw [Limits.Sigma.ι_desc]
  rw [localizedPointPresheafFiber_to_localizedExtensionByZero_presheafFiber]
  rw [(p.over x).toPresheafFiber_presheafFiberDesc
    (fun V z ↦
      Limits.Sigma.ι
          (fun φ : V.left ⟶ U ↦
            (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢).obj (op (Over.mk φ)))
          V.hom ≫
        (localizedExtensionByZeroPresheafModel_objIsoSigma 𝒪 U 𝒢 V.left).inv ≫
        p.toPresheafFiber V.left z.1 (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢))
    (localizedPointPresheafFiber_to_localizedExtensionByZero_presheafFiber_compatible
      𝒪 U p 𝒢 x)]
  rw [Category.assoc]
  rw [p.toPresheafFiber_presheafFiberDesc
    (localizedExtensionByZero_presheafFiberForwardStage 𝒪 U p 𝒢)
    (localizedExtensionByZero_presheafFiber_forward_desc_compatible 𝒪 U p 𝒢)]
  rw [localizedExtensionByZero_presheafFiberForward, localizedExtensionByZero_presheafFiberForwardStage]
  simp [Category.assoc, z.2]

/-- Helper for Lemma 18.38.1: the presheaf-fiber of the explicit Remark 18.19.7 lower-shriek
model decomposes as the coproduct of the localized-point presheaf fibers. -/
noncomputable def localizedExtensionByZero_presheafFiberIsoCoproductOfLocalizedPointPresheafFibers
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    p.presheafFiber.obj (localizedExtensionByZeroPresheafModel 𝒪 U 𝒢) ≅
      (∐ fun x : p.fiber.obj U ↦
        (p.over x).presheafFiber.obj (localizedUnderlyingAdditivePresheaf 𝒪 U 𝒢)) :=
  { hom := localizedExtensionByZero_presheafFiberForward 𝒪 U p 𝒢
    inv := localizedExtensionByZero_presheafFiberBackward 𝒪 U p 𝒢
    hom_inv_id := localizedExtensionByZero_presheafFiber_forward_backward_id 𝒪 U p 𝒢
    inv_hom_id := localizedExtensionByZero_presheafFiber_backward_forward_id 𝒪 U p 𝒢 }

/-- Lemma 18.38.1: for a ringed site `(\mathcal C, \mathcal O)`, a point `p` of `\mathcal C`,
an object `U : \mathcal C`, and an `\mathcal O_U`-module `\mathcal G`, the stalk at `p` of the
underlying additive sheaf of `j_{U!} \mathcal G` is canonically isomorphic to the coproduct of
the stalks of `\mathcal G` at the localized points `p.over x` for `x : p.fiber.obj U`; by Sites,
Lemma `7.35.2`, this is equivalently the coproduct over the points of `\mathcal C / U` lying
over `p`. Since the localized summands live over varying stalk rings `(𝒪_U)_{p.over x}`, the
canonical common codomain is the additive fiber functor `p.sheafFiber`. This is the main
source-facing `Iso`; the proposition-level `IsIsomorphic` form below is only a companion. -/
noncomputable def ringedSiteLocalizedExtensionByZero_toSheaf_stalkIsoCoproductOfLocalizedPointStalks
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    (((ringedSiteLocalizedExtensionByZero J 𝒪 U) ⋙
        SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber).obj 𝒢) ≅
      (∐ fun x : p.fiber.obj U ↦
        ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
            (p.over x).sheafFiber).obj 𝒢)) := by
  -- Route correction: first transport the theorem left-hand side to the explicit Remark 18.19.7
  -- presheaf model, then perform the stalk regrouping there, and finally pass from localized
  -- presheaf fibers to localized sheaf fibers.
  refine ringedSiteLocalizedExtensionByZero_stalkIsoPresheafModel 𝒪 U p 𝒢 ≪≫ ?_
  refine localizedExtensionByZero_presheafFiberIsoCoproductOfLocalizedPointPresheafFibers
      𝒪 U p 𝒢 ≪≫ ?_
  exact coproduct_pointOver_underlyingPresheafFiberIsoSheafFiber 𝒪 U p 𝒢

theorem ringedSiteLocalizedExtensionByZero_toSheaf_stalk_isomorphic_coproduct_of_localizedPointStalks
    (𝒢 : ringedSiteModuleCategory.{u, u, u} (J.over U) (𝒪.over U)) :
    IsIsomorphic
      (((ringedSiteLocalizedExtensionByZero J 𝒪 U) ⋙
          SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber).obj 𝒢)
      (∐ fun x : p.fiber.obj U ↦
        ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
            (p.over x).sheafFiber).obj 𝒢)) := by
  exact ⟨ringedSiteLocalizedExtensionByZero_toSheaf_stalkIsoCoproductOfLocalizedPointStalks
    𝒪 U p 𝒢⟩

end
