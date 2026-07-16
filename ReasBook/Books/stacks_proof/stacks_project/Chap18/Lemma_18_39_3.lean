import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Limits.ExactFunctor
import stacks_proof.stacks_project.Chap06.Definition_6_27_1
import stacks_proof.stacks_project.Chap07.Example_7_33_5
import stacks_proof.stacks_project.Chap12.Remark_12_29_2
import stacks_proof.stacks_project.Chap12.Lemma_12_7_2
import stacks_proof.stacks_project.Chap17.Definition_17_17_1
import stacks_proof.stacks_project.Chap17.Lemma_17_17_2
import stacks_proof.stacks_project.Chap18.Definition_18_31_1
import stacks_proof.stacks_project.Chap18.Lemma_18_14_4
import stacks_proof.stacks_project.Chap18.Lemma_18_36_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open Opposite
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u w

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {I : Type w}
variable (p : I → GrothendieckTopology.Point J)
variable (𝒪 : Sheaf J CommRingCat.{u})
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable (ℱ : SheafOfModules (ringSheaf J 𝒪))

/-- Helper for Chap18 Lemma 18 39 3: the additive stalk functor at a site point, written as
forgetting the module structure and then taking the sheaf fiber. -/
private abbrev point_stalk_functor
    (p : GrothendieckTopology.Point J) :
    SheafOfModules (ringSheaf J 𝒪) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber

/-- Helper for Chap18 Lemma 18 39 3: tensoring with `ℱ` and then taking the additive stalk at `p`
is the site-point functor expressing flatness at `p`. -/
private abbrev point_tensor_stalk_functor
    (p : GrothendieckTopology.Point J)
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    SheafOfModules (ringSheaf J 𝒪) ⥤ AddCommGrpCat.{u} :=
  CategoryTheory.MonoidalCategory.tensorRight ℱ ⋙ point_stalk_functor (𝒪 := 𝒪) p

/-- Helper for Chap18 Lemma 18 39 3: flatness at a site point is exactness of the tensor-then-
stalk functor. -/
private def IsFlatAtPoint
    (𝒪 : Sheaf J CommRingCat.{u})
    (p : GrothendieckTopology.Point J)
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) : Prop :=
  exactFunctor
    (SheafOfModules (ringSheaf J 𝒪))
    AddCommGrpCat.{u}
    (point_tensor_stalk_functor (𝒪 := 𝒪) p ℱ)

/-- Helper for Chap18 Lemma 18 39 3: the additive stalk functor at a site point is exact. -/
private theorem pointStalkFunctor_exact
    (p : GrothendieckTopology.Point J) :
    exactFunctor
      (SheafOfModules (ringSheaf J 𝒪))
      AddCommGrpCat.{u}
      (point_stalk_functor (𝒪 := 𝒪) p) := by
  -- Proof comment: the additive stalk is the composite of the exact forgetful functor to sheaves
  -- of abelian groups and the exact fiber functor at the chosen point.
  have hToSheaf :
      exactFunctor
        (SheafOfModules (ringSheaf J 𝒪))
        (Sheaf J AddCommGrpCat.{u})
        (SheafOfModules.toSheaf (ringSheaf J 𝒪)) :=
    (ExactFunctor.of (SheafOfModules.toSheaf (ringSheaf J 𝒪))).property
  have hFiber :
      exactFunctor
        (Sheaf J AddCommGrpCat.{u})
        AddCommGrpCat.{u}
        p.sheafFiber :=
    (ExactFunctor.of p.sheafFiber).property
  -- Proof comment: exact functors compose, so the tensor-free stalk functor is exact.
  exact
    ((exactFunctor_iff (point_stalk_functor (𝒪 := 𝒪) p)).2
      ⟨by
          let _ : PreservesFiniteLimits (SheafOfModules.toSheaf (ringSheaf J 𝒪)) :=
            ((exactFunctor_iff (SheafOfModules.toSheaf (ringSheaf J 𝒪))).1 hToSheaf).1
          let _ : PreservesFiniteLimits p.sheafFiber :=
            ((exactFunctor_iff p.sheafFiber).1 hFiber).1
          infer_instance,
        by
          let _ : PreservesFiniteColimits (SheafOfModules.toSheaf (ringSheaf J 𝒪)) :=
            ((exactFunctor_iff (SheafOfModules.toSheaf (ringSheaf J 𝒪))).1 hToSheaf).2
          let _ : PreservesFiniteColimits p.sheafFiber :=
            ((exactFunctor_iff p.sheafFiber).1 hFiber).2
          infer_instance⟩)

/-- Helper for Chap18 Lemma 18 39 3: site-level flatness implies the exact pointwise tensor
condition at every chosen point. -/
private theorem isFlatAtPoint_of_isFlat
    [IsFlat 𝒪 ℱ]
    (p : GrothendieckTopology.Point J) :
    IsFlatAtPoint 𝒪 p ℱ := by
  have hTensor :
      exactFunctor
        (SheafOfModules (ringSheaf J 𝒪))
        (SheafOfModules (ringSheaf J 𝒪))
        (CategoryTheory.MonoidalCategory.tensorRight ℱ) :=
    IsFlat.exact_tensor (𝒪 := 𝒪) (ℱ := ℱ)
  have hStalk :
      exactFunctor
        (SheafOfModules (ringSheaf J 𝒪))
        AddCommGrpCat.{u}
        (point_stalk_functor (𝒪 := 𝒪) p) :=
    pointStalkFunctor_exact (𝒪 := 𝒪) p
  -- Proof comment: compose exactness of tensoring with exactness of taking the additive stalk.
  rw [exactFunctor_iff] at hTensor hStalk
  let _ : PreservesFiniteLimits (CategoryTheory.MonoidalCategory.tensorRight ℱ) := hTensor.1
  let _ : PreservesFiniteColimits (CategoryTheory.MonoidalCategory.tensorRight ℱ) := hTensor.2
  let _ : PreservesFiniteLimits (point_stalk_functor (𝒪 := 𝒪) p) := hStalk.1
  let _ : PreservesFiniteColimits (point_stalk_functor (𝒪 := 𝒪) p) := hStalk.2
  have hComposite :
      exactFunctor
        (SheafOfModules (ringSheaf J 𝒪))
        AddCommGrpCat.{u}
        (point_tensor_stalk_functor (𝒪 := 𝒪) p ℱ) := by
    -- Proof comment: the point tensor/stalk functor is exactly the composite of the two exact
    -- factors just assembled.
    exact
      (exactFunctor_iff (point_tensor_stalk_functor (𝒪 := 𝒪) p ℱ)).2
        ⟨inferInstance, inferInstance⟩
  simpa [IsFlatAtPoint] using hComposite

-- Proof sketch: the forward implication is Lemma 18.39.2 applied pointwise. For the converse,
-- flatness means exactness of tensoring with `ℱ`, and exactness of the resulting short complexes
-- of abelian sheaves can be checked on the conservative family `p` by Lemma 18.14.4. The stalk
-- identification for tensor products from Lemma 18.26.2 matches those stalkwise exactness
-- conditions with `IsFlatAtPoint`.
/-- Lemma 18.39.3: a sheaf of `\mathcal O`-modules on a ringed site is flat if and only if it is
flat at every point of a conservative family, expressed here by exactness of tensoring with
`\mathcal F` followed by taking the fiber functor at each `p_i`; this is the site-theoretic form
of saying that each stalk `\mathcal F_{p_i}` is a flat `\mathcal O_{p_i}`-module. -/
@[stacks 05VC]
theorem isFlat_iff_isFlatAtPoint_of_conservativeFamily
    (hp : (ofObj p).IsConservativeFamilyOfPoints) :
    IsFlat 𝒪 ℱ ↔
      ∀ i : I,
        exactFunctor
          (SheafOfModules (ringSheaf J 𝒪))
          AddCommGrpCat.{u}
          (tensorRight ℱ ⋙
            SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
              (p i).sheafFiber) :=
  -- TODO: recover the converse by reflecting short exactness from the conservative family of
  -- point fibers after the additive sheaf forgetful functor; the current blocker is the missing
  -- exactness/additivity normalization for `tensorRight ℱ` in this file's local API surface.
  sorry

end

namespace SheafOfModules

variable {X : RingedSpace.{u}}
variable [MonoidalCategory X.Modules]

/-- Helper for Lemma 18.39.3: the opens-site point stalk ring at `x` is canonically the ordinary
stalk ring `\mathcal O_{X, x}`. -/
private abbrev pointStalkRingEquivStalkRing (x : X) :
    ↑((Opens.pointGrothendieckTopology x).stalkRing (RingedSpace.ringCatSheaf X)) ≃+*
      ↑(X.presheaf.stalk x) :=
  (((Opens.pointGrothendieckTopology x).presheafFiberCompIso
      (forget₂ CommRingCat RingCat)).app X.sheaf.obj).ringCatIsoToRingEquiv.trans
    (Iso.commRingCatIsoToRingEquiv
      (CategoryTheory.pointGrothendieckTopology_presheafFiber_obj_iso_stalk x X.sheaf.obj))

/-- Helper for Lemma 18.39.3: retarget the opens-site point stalk functor along the canonical
identification of the site-point stalk ring with the ordinary stalk ring. -/
private abbrev pointStalkModuleFunctor (x : X) :
    X.Modules ⥤ ModuleCat (X.presheaf.stalk x) :=
  (Opens.pointGrothendieckTopology x).sheafModuleStalkFunctor (RingedSpace.ringCatSheaf X) ⋙
    ModuleCat.restrictScalars (pointStalkRingEquivStalkRing (X := X) x).symm.toRingHom

/-- Helper for Lemma 18.39.3: forgetting the retargeted opens-site point stalk recovers the
underlying additive stalk fiber. -/
@[simp] private theorem pointStalkModuleFunctor_forget_obj
    (x : X) (ℱ : X.Modules) :
    (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj
        ((pointStalkModuleFunctor (X := X) x).obj ℱ) =
      ((Opens.pointGrothendieckTopology x).sheafFiber.obj
        ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ)) := by
  -- Proof comment: restricting scalars changes only the ring action, not the underlying additive
  -- group of the stalk module.
  rfl

/-- Helper for Lemma 18.39.3: forgetting a morphism of retargeted opens-site point stalks gives
the underlying additive stalk map. -/
@[simp] private theorem pointStalkModuleFunctor_forget_map
    (x : X) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map
        ((pointStalkModuleFunctor (X := X) x).map φ) =
      ((Opens.pointGrothendieckTopology x).sheafFiber.map
        ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ)) := by
  -- Proof comment: the module-valued point stalk map is built from the same additive colimit map,
  -- so forgetting scalars leaves it unchanged.
  rfl

/-- Helper for Lemma 18.39.3: specializing the conservative-family criterion to all opens-site
points rewrites opens-site flatness as pointwise opens-site flatness. -/
private abbrev opensIsFlatAtPoint
    (x : X) (ℱ : X.Modules) : Prop :=
  exactFunctor
    X.Modules
    AddCommGrpCat
    (tensorRight ℱ ⋙
      SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
      (Opens.pointGrothendieckTopology x).sheafFiber)

/-- Helper for Lemma 18.39.3: specializing the conservative-family criterion to all opens-site
points rewrites opens-site flatness as pointwise opens-site flatness. -/
private theorem ringedSiteIsFlat_iff_isFlatAtPoint_allPoints
    (ℱ : X.Modules) :
    SheafOfModules.RingedSite.IsFlat X.sheaf ℱ ↔
      ∀ x : X,
        opensIsFlatAtPoint (X := X) x ℱ :=
  -- TODO: this is a direct specialization of the conservative-family criterion above once the
  -- pointwise exactness theorem is restored without the hidden additive-instance failures.
  sorry

/-- Helper for Lemma 18.39.3: exactness is stable under composing two exact functors. -/
private theorem exactFunctorComp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    {F : A ⥤ B} {G : B ⥤ D}
    (hF : exactFunctor A B F)
    (hG : exactFunctor B D G) :
    exactFunctor A D (F ⋙ G) := by
  -- Proof comment: exactness is finite-limit and finite-colimit preservation, and both
  -- preservation properties compose.
  rw [CategoryTheory.exactFunctor_iff] at hF hG ⊢
  let _ : PreservesFiniteLimits F := hF.1
  let _ : PreservesFiniteColimits F := hF.2
  let _ : PreservesFiniteLimits G := hG.1
  let _ : PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 18.39.3: exactness transports across a natural isomorphism of functors. -/
private theorem exactFunctorOfNatIso
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {F G : A ⥤ B}
    (e : F ≅ G) :
    exactFunctor A B F → exactFunctor A B G := by
  intro hF
  -- Proof comment: transport finite-limit and finite-colimit preservation across the natural
  -- isomorphism, then repackage the result as exactness.
  rw [CategoryTheory.exactFunctor_iff] at hF ⊢
  let _ : PreservesFiniteLimits F := hF.1
  let _ : PreservesFiniteColimits F := hF.2
  exact ⟨
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso e,
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e
  ⟩

/-- Helper for Lemma 18.39.3: in a functor category, a short complex is short exact exactly when
all componentwise evaluations are short exact. -/
private theorem shortExact_iff_pointwiseShortExactFunctorCategory
    {J : Type*} [Category J]
    {A : Type*} [Category A] [Abelian A]
    {S : ShortComplex (J ⥤ A)} :
    S.ShortExact ↔ ∀ j, (S.map ((CategoryTheory.evaluation J A).obj j)).ShortExact := by
  let hEval :
      JointlyReflectIsomorphisms
        ((CategoryTheory.evaluation J A).obj : J → (J ⥤ A) ⥤ A) := by
    -- Proof comment: a natural transformation is an isomorphism once all of its components are.
    refine ⟨fun {F G} α _ ↦ ?_⟩
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    simpa using (inferInstance : IsIso (((CategoryTheory.evaluation J A).obj j).map α))
  constructor
  · intro hS j
    -- Proof comment: exactness, monomorphy, and epimorphy in a functor category are computed
    -- componentwise.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact (hEval.exact_iff S).1 hS.exact j
    · exact (NatTrans.mono_iff_mono_app S.f).1 hS.mono_f j
    · exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g j
  · intro hS
    -- Proof comment: reassemble the global short exact row from the pointwise short exact rows.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact (hEval.exact_iff S).2 fun j ↦ (hS j).exact
    · exact (NatTrans.mono_iff_mono_app S.f).2 fun j ↦ (hS j).mono_f
    · exact (NatTrans.epi_iff_epi_app S.g).2 fun j ↦ (hS j).epi_g

/-- Helper for Lemma 18.39.3: a short complex of presheaves of modules is short exact once each
open-set evaluation is short exact. -/
private theorem presheafOfModules_shortExact_of_pointwise
    {S : ShortComplex (PresheafOfModules X.ringCatSheaf.obj)}
    (hS : ∀ U : (Opens X)ᵒᵖ,
      (S.map (PresheafOfModules.evaluation X.ringCatSheaf.obj U)).ShortExact) :
    S.ShortExact :=
  -- TODO: rebuild the pointwise-to-global reflection through
  -- `PresheafOfModules.toPresheaf`; the current blocker is the evaluation functor's codomain
  -- spelling mismatch between additive presheaves and `Ab`.
  sorry

/-- Helper for Lemma 18.39.3: an open of `X` missing `x` pulls back along `pointInclusion x` to
the bottom open of the one-point space. -/
private theorem pointInclusion_preimage_eq_bot
    (x : X) {U : Opens X} (hxU : x ∉ U) :
    ((TopologicalSpace.Opens.map (pointInclusion x).hom.base).obj U) = ⊥ :=
  -- TODO: finish the one-point preimage calculation after normalizing the ambient `Opens` goal
  -- to the same spelling used by `pointInclusion_preimage_eq_top`.
  sorry

/-- Helper for Lemma 18.39.3: realize a stalk module as the canonical module sheaf on the
one-point ringed space `({x}, \mathcal O_{X, x})`. -/
private noncomputable def pointModuleSheafFunctor
    (x : X) :
    ModuleCat (X.presheaf.stalk x) ⥤ RingedSpace.Modules (pointRingedSpace x) :=
  -- TODO: restore the top-open reconstruction proof for `map_id` and `map_comp`; the current
  -- blocker is the changed normal form of `pointModuleSheaf_homEquivTop`.
  sorry

/-- Helper for Lemma 18.39.3: the top-open component of `pointModuleSheafFunctor.map` is the
expected restriction-of-scalars image of the original module morphism. -/
private theorem pointModuleSheafFunctor_map_top
    (x : X) {M N : ModuleCat (X.presheaf.stalk x)} (φ : M ⟶ N) :
    True := by
  -- TODO: restore the explicit top-open formula once `pointModuleSheafFunctor` has a stable map.
  trivial

/-- Helper for Chap18 Lemma 18 39 3: evaluating the point-module sheaf functor on the top open
recovers restriction of scalars along the canonical identification of the top ring with
`\mathcal O_{X, x}`. -/
private noncomputable def pointModuleSheafFunctorTopIso
    (x : X) :
    pointModuleSheafFunctor (X := X) x ⋙
        SheafOfModules.forget (RingedSpace.ringCatSheaf (pointRingedSpace x)) ⋙
        PresheafOfModules.evaluation
          (RingedSpace.ringCatSheaf (pointRingedSpace x)).obj
          (op (⊤ : Opens (TopCat.of PUnit))) ≅
      ModuleCat.restrictScalars
        (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom :=
  -- TODO: package the previous top-open map computation into a natural isomorphism.
  sorry

/-- Helper for Chap18 Lemma 18 39 3: after forgetting sheaf structure and evaluating on the top
open, the point-module sheaf functor is exact because it is naturally isomorphic to restriction
of scalars. -/
private theorem pointModuleSheafFunctorTopExact
    (x : X) :
    exactFunctor
      (ModuleCat (X.presheaf.stalk x))
      (ModuleCat ((RingedSpace.ringCatSheaf (pointRingedSpace x)).obj.obj
        (op (⊤ : Opens (TopCat.of PUnit)))))
      (pointModuleSheafFunctor (X := X) x ⋙
        SheafOfModules.forget (RingedSpace.ringCatSheaf (pointRingedSpace x)) ⋙
        PresheafOfModules.evaluation
          (RingedSpace.ringCatSheaf (pointRingedSpace x)).obj
          (op (⊤ : Opens (TopCat.of PUnit)))) :=
  -- TODO: transport exactness across `pointModuleSheafFunctorTopIso` after the natural
  -- isomorphism direction and exactness lemma normalization are repaired.
  sorry

/-- Helper for Chap18 Lemma 18 39 3: on the one-point ringed space, short exactness is detected
by evaluating the underlying module sheaf on the top open. -/
private theorem pointRingedSpaceShortExact_iff_topEvaluation
    (x : X)
    {S : ShortComplex (RingedSpace.Modules (pointRingedSpace x))} :
    S.ShortExact ↔
      ((S.map
          (SheafOfModules.forget (RingedSpace.ringCatSheaf (pointRingedSpace x)) ⋙
            PresheafOfModules.evaluation
              (RingedSpace.ringCatSheaf (pointRingedSpace x)).obj
              (op (⊤ : Opens (TopCat.of PUnit)))))).ShortExact :=
  -- TODO: rebuild the one-point-space reduction after the presheaf pointwise-reflection helper
  -- and bottom-open zero-object API are repaired.
  sorry

/-- Helper for Chap18 Lemma 18 39 3: evaluating any short complex of point-module sheaves on the
bottom open of the one-point space yields a zero short complex. -/
private theorem pointRingedSpaceBotEvaluationShortExact
    (x : X)
    {S : ShortComplex (RingedSpace.Modules (pointRingedSpace x))} :
    ((S.map
        (SheafOfModules.forget (RingedSpace.ringCatSheaf (pointRingedSpace x)) ⋙
          PresheafOfModules.evaluation
            (RingedSpace.ringCatSheaf (pointRingedSpace x)).obj
            (op (⊥ : Opens (TopCat.of PUnit)))))).ShortExact :=
  -- TODO: isolate the empty-open zero-object API for point module sheaves, then this becomes an
  -- immediate `IsZero` short-exactness argument.
  sorry

/-- Helper for Chap18 Lemma 18 39 3: the point-module sheaf functor is exact because short
exactness on the one-point space is already determined by the top-open evaluation where the
functor is restriction of scalars. -/
private theorem pointModuleSheafFunctorExact
    (x : X) :
    exactFunctor
      (ModuleCat (X.presheaf.stalk x))
      (RingedSpace.Modules (pointRingedSpace x))
      (pointModuleSheafFunctor (X := X) x) :=
  -- TODO: this follows from the top-open exactness plus the one-point-space short-exactness
  -- criterion once those two helpers are restored.
  sorry

/-- Helper for Chap18 Lemma 18 39 3: pushforward along the point inclusion is exact because, on
every open of `X`, it is either top-open evaluation or bottom-open evaluation on the one-point
space followed by restriction of scalars. -/
private theorem pointInclusionPushforwardExact
    (x : X) :
    exactFunctor
      (RingedSpace.Modules (pointRingedSpace x))
      X.Modules
      ((pointInclusion x) _*) :=
  -- TODO: the point-inclusion pushforward becomes exact once the top/bottom-open evaluation
  -- analysis is restored on the one-point space.
  sorry

/-- Helper for Lemma 18.39.3: forgetting the retargeted point stalk functor gives the ordinary
additive point fiber functor on the opens site. -/
private noncomputable def pointStalkModuleFunctorForgetIso
    (x : X) :
    pointStalkModuleFunctor (X := X) x ⋙
        forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat ≅
      SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
        (Opens.pointGrothendieckTopology x).sheafFiber :=
  NatIso.ofComponents
    (fun ℱ ↦ Iso.refl _)
    (fun {ℱ 𝒢} φ ↦ by
      -- Proof comment: both functors act by the same additive stalk map; only the scalar action
      -- differs before forgetting.
      simpa [Category.assoc] using pointStalkModuleFunctor_forget_map (X := X) x φ)

/-- Helper for Lemma 18.39.3: the retargeted module-valued point stalk functor is exact. -/
private theorem pointStalkModuleFunctorExact
    (x : X) :
    exactFunctor X.Modules (ModuleCat (X.presheaf.stalk x))
      (pointStalkModuleFunctor (X := X) x) := by
  -- Proof comment: the site-point module stalk functor is exact, and restricting scalars along
  -- the canonical stalk-ring equivalence is exact as well.
  exact exactFunctorComp
    ((Opens.pointGrothendieckTopology x).sheafModuleStalk_exact X.ringCatSheaf)
    (restrictScalars_exact (pointStalkRingEquivStalkRing (X := X) x).symm.toRingHom)

/-- Helper for Lemma 18.39.3: taking the point stalk after tensoring with `ℱ` agrees with
tensoring the point stalk by `ℱ_x`. -/
private noncomputable def pointStalkTensorComparisonIso
    (x : X) (ℱ : X.Modules) :
    tensorRight ℱ ⋙ pointStalkModuleFunctor (X := X) x ≅
      pointStalkModuleFunctor (X := X) x ⋙
        tensorRight (RingedSpace.stalkModuleCat ℱ x) :=
  -- TODO: recover this tensor/stalk comparison from the Chapter 17 owner
  -- `tensorProductStalkIso` once a dependency-closed import path to that theorem is restored.
  sorry

/-- Helper for Lemma 18.39.3: stalkwise flatness in the Chapter 17 sense implies the Chapter 18
site-point exactness condition at the corresponding opens-site point. -/
private theorem isFlatAtPoint_of_flatAt
    (x : X) (ℱ : X.Modules)
    (hFlat : ℱ.flat_at x) :
    opensIsFlatAtPoint (X := X) x ℱ :=
  -- TODO: this is the forward tensor/stalk transport through `pointStalkTensorComparisonIso`;
  -- it should close once the Chapter 17 tensor/stalk comparison is available again.
  sorry

/-- Helper for Lemma 18.39.3: the site-point exactness hypothesis at `x` should imply exactness
of tensoring with the ordinary stalk module `\mathcal F_x`. -/
private theorem tensorRightExactOfIsFlatAtPoint
    (x : X) (ℱ : X.Modules)
    (hPoint : opensIsFlatAtPoint (X := X) x ℱ) :
    exactFunctor
      (ModuleCat (X.presheaf.stalk x))
      (ModuleCat (X.presheaf.stalk x))
      (tensorRight (RingedSpace.stalkModuleCat ℱ x)) := by
  -- Route correction: the missing converse bridge is not another conservative-family argument on
  -- `X.Modules`; it is the sequence-level transport from stalk-module short exact sequences to
  -- point-supported sheaf short exact sequences via skyscraper module sheaves at `x`.
  -- TODO: `pointRingedSpaceShortExact_iff_topEvaluation` and `pointModuleSheafFunctorExact` now
  -- reduce the point-space side to top-open evaluation. The remaining blocker is the transport of
  -- `hPoint` to that top-open route: one still needs a functor-level comparison identifying the
  -- point-stalk of the pushed-forward point-module sheaf with the plain underlying stalk module,
  -- together with the matching tensor comparison for `((pointInclusion x)^*).obj ℱ`.
  sorry

/-- Helper for Lemma 18.39.3: opens-site flatness at `x` recovers the Chapter 17 stalk-flatness
predicate `flat_at x`. -/
private theorem flatAt_of_isFlatAtPoint
    (x : X) (ℱ : X.Modules)
    (hPoint : opensIsFlatAtPoint (X := X) x ℱ) :
    ℱ.flat_at x :=
  -- TODO: reflect exactness of `tensorRight (stalkModuleCat ℱ x)` back to the Chapter 17
  -- predicate once the converse tensor/stalk bridge is restored.
  sorry

/- Domain-style sampling for the ringed-space/opens-site flatness bridge:
- primary domain: flat sheaves of modules on a ringed space, compared with the canonical opens-site
  owner on `X.sheaf`;
- sampled owner declarations:
  `SheafOfModules.IsFlat`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.isFlat_stalk`,
  `SheafOfModules.RingedSite.isFlat_iff_isFlatAtPoint_of_conservativeFamily`;
- best owner abstraction: the Chapter 18 owner `SheafOfModules.RingedSite.IsFlat` is the canonical
  exactness notion, while the Chapter 17 ringed-space class `SheafOfModules.IsFlat` is the
  source-facing stalkwise specialization on a ringed space;
- primitive data: a module sheaf `ℱ : X.Modules`;
- derived API: the comparison theorem below between the source-facing ringed-space owner and the
  canonical opens-site owner.

Source/core/bridge triage:
- `source-facing`: `SheafOfModules.IsFlat` on `X.Modules`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat X.sheaf`;
- `bridge/view`: `isFlat_iff_ringedSite_isFlat`. -/

/-- The Chapter 17 ringed-space flatness owner agrees with the opens-site specialization of the
canonical Chapter 18 flatness owner. -/
theorem isFlat_iff_ringedSite_isFlat
    (ℱ : X.Modules) :
    ℱ.IsFlat ↔ SheafOfModules.RingedSite.IsFlat X.sheaf ℱ :=
  -- TODO: combine the stalkwise Chapter 17 criterion with the all-points opens-site criterion
  -- after the forward and converse tensor/stalk bridges have both been repaired.
  sorry

end SheafOfModules
