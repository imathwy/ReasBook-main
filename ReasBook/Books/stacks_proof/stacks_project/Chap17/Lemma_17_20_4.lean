import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import stacks_proof.stacks_project.Chap18.Definition_18_28_1
import stacks_proof.stacks_project.Chap17.Definition_17_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.20.4:
- primary domain: exactness of pullback followed by tensoring with a sheaf that is flat over the
  target ringed space in the canonical relative-flatness sense;
- sampled owner declarations:
  `SheafOfModules.relativeModule`,
  `SheafOfModules.IsFlat`,
  `SheafOfModules.RingedSite.IsFlat`,
  `f^*`,
  `sheafModuleTensorRightFunctor`,
  `exactFunctor`;
- owner abstraction: the source-facing flatness hypothesis should reuse
  direct canonical flatness of the restricted `f^{-1}\mathcal O_Y`-module
  `(SheafOfModules.relativeModule ℱ f).IsFlat`, while the functor part should reuse the canonical
  pullback owner `f^*` and the existing tensor owner `sheafModuleTensorRightFunctor`;
- primitive data: a morphism `f : X ⟶ Y` and a sheaf `ℱ : (RingedSpace.Modules X)`;
- derived API: the exactness theorem for the canonical composite functor
  `f^* ⋙ sheafModuleTensorRightFunctor ℱ`.

Source/core/bridge triage:
- `source-facing`: exactness of `𝒢 ↦ f^*𝒢 ⊗ ℱ` under the hypothesis that `ℱ` is flat over `Y`;
- `core/canonical`: `SheafOfModules.relativeModule`, `SheafOfModules.IsFlat`, `f^*`,
  `sheafModuleTensorRightFunctor`, and `exactFunctor`;
- `bridge/view`: the composite pullback-then-tensor functor used directly in the theorem.
-/

variable {X Y : RingedSpace.{u}}
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable [(Opens.grothendieckTopology Y).HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [MonoidalCategory X.Modules]
variable [MonoidalCategory Y.Modules]

/-- The inverse-image commutative structure sheaf `f^{-1}\mathcal O_Y` on `X`. -/
private abbrev inverseImageStructureSheaf (f : X ⟶ Y) :
    TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf

/-- The underlying `RingCat`-valued inverse-image structure sheaf `f^{-1}\mathcal O_Y`. -/
private abbrev inverseImageRingSheaf (f : X ⟶ Y) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj
    (inverseImageStructureSheaf f)

/-- The ringed space on the carrier `X` with structure sheaf `f^{-1}\mathcal O_Y`. -/
private abbrev inverseImageRingedSpace (f : X ⟶ Y) : RingedSpace.{u} :=
  { carrier := X
    presheaf := (inverseImageStructureSheaf f).presheaf
    IsSheaf := (inverseImageStructureSheaf f).2 }

/-- The module category over the inverse-image structure sheaf `f^{-1}\mathcal O_Y`. -/
private abbrev inverseImageModules (f : X ⟶ Y) :=
  (inverseImageRingedSpace f).Modules

/-- The unit-style structure morphism whose pullback is the inverse-image functor on
`\mathcal O_Y`-modules before the final same-space base change to `\mathcal O_X`. -/
private noncomputable abbrev inverseImageRingUnit (f : X ⟶ Y) :
    Y.ringCatSheaf ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (inverseImageRingSheaf f) := by
  simpa [RingedSpace.ringCatSheaf, inverseImageStructureSheaf, inverseImageRingSheaf] using
    (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app Y.sheaf)

/-- The exact inverse-image functor `\mathcal G \mapsto f^{-1}\mathcal G` landing in modules over
`f^{-1}\mathcal O_Y`. -/
private noncomputable abbrev inverseImageModule (f : X ⟶ Y) :
    Y.Modules ⥤ inverseImageModules f :=
  SheafOfModules.pullback (inverseImageRingUnit f)

/-- The same-space change-of-rings morphism
`f^{-1}\mathcal O_Y \to \mathcal O_X`, viewed in the owner category for module pullback. -/
private noncomputable abbrev inverseImageStructureSheafHom (f : X ⟶ Y) :
    inverseImageRingSheaf f ⟶
      (Functor.sheafPushforwardContinuous (𝟭 (TopologicalSpace.Opens X)) RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).map
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f) ≫
    (Functor.sheafPushforwardContinuousId RingCat.{u} (Opens.grothendieckTopology X)).inv.app
      X.ringCatSheaf

open scoped SheafOfModules.RingedSite

variable (f : X ⟶ Y) (ℱ : X.Modules)

private abbrev relativeFlatness
    (f : X ⟶ Y) (ℱ : X.Modules) : Prop :=
  (SheafOfModules.relativeModule ℱ f).IsFlat

local notation "RelMod" => SheafOfModules.relativeModule ℱ f

/-- The tensor-right endofunctor on modules over `f^{-1}\mathcal O_Y` defined by the relative
module `\mathcal F`. -/
private abbrev relativeTensorFunctor (f : X ⟶ Y) (ℱ : X.Modules) :
    inverseImageModules f ⥤ inverseImageModules f :=
  -- TODO: replan around the canonical `restrictionAlong (f^♯)` owner so that
  -- `SheafOfModules.relativeModule ℱ f` and the inverse-image module category agree definitionally.
  sorry

/-- The same-site restriction-of-scalars functor from `\mathcal O_X`-modules to
`f^{-1}\mathcal O_Y`-modules. -/
private abbrev inverseImageRestrictionFunctor (f : X ⟶ Y) :
    X.Modules ⥤ inverseImageModules f :=
  SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).map
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f))

/-- The `RingCat`-valued view of a commutative ring sheaf on `X`. -/
private abbrev commRingSheafAsRingSheaf (𝒪 : TopCat.Sheaf CommRingCat.{u} X) :
    TopCat.Sheaf RingCat.{u} X :=
  SheafOfModules.RingedSite.ringSheaf (Opens.grothendieckTopology X) 𝒪

/-- Helper for Lemma 17.20.4: same-site restriction of scalars along
`f^{-1}\mathcal O_Y \to \mathcal O_X` does not change the underlying additive sheaf. -/
private theorem inverseImageRestrictionFunctor_toSheaf
    (f : X ⟶ Y) :
    inverseImageRestrictionFunctor f ⋙
        SheafOfModules.toSheaf (inverseImageRingSheaf f) =
      SheafOfModules.toSheaf X.ringCatSheaf := by
  -- TODO: the proof should use the canonical same-site `restrictionAlong` owner, where forgetting
  -- to additive sheaves is definitionally unchanged.
  sorry

/-- Helper for Lemma 17.20.4: forgetting scalars to sheaves of abelian groups reflects and
preserves short exactness for sheaves of modules on a fixed ringed space. -/
private theorem shortExact_toSheaf_iff
    {𝒪 : TopCat.Sheaf CommRingCat.{u} X}
    (S : ShortComplex (SheafOfModules (commRingSheafAsRingSheaf 𝒪))) :
    (S.map (SheafOfModules.toSheaf (commRingSheafAsRingSheaf 𝒪))).ShortExact ↔
      S.ShortExact := by
  -- TODO: rebuild this through the actual exactness API for `toSheaf` rather than the current
  -- brittle `exactFunctor_iff`/`map_of_exact` route, which is failing on additive side conditions.
  sorry

/-- Helper for Lemma 17.20.4: same-site restriction of scalars along
`f^{-1}\mathcal O_Y \to \mathcal O_X` preserves and reflects short exact sequences. -/
private theorem inverseImageRestrictionFunctor_shortExact_iff
    (f : X ⟶ Y) (S : ShortComplex X.Modules) :
    (S.map (inverseImageRestrictionFunctor f)).ShortExact ↔ S.ShortExact := by
  -- TODO: once `inverseImageRestrictionFunctor_toSheaf` is repaired in the canonical owner, this
  -- should reduce to the corresponding `toSheaf` short-exact reflection statement.
  sorry

/-- Helper for Lemma 17.20.4: forgetting the module structure identifies inverse image with the
usual pullback of sheaves of abelian groups along `f`. -/
private theorem inverseImageModule_toSheaf
    (f : X ⟶ Y) :
    inverseImageModule f ⋙ SheafOfModules.toSheaf (inverseImageRingSheaf f) =
      SheafOfModules.toSheaf Y.ringCatSheaf ⋙
        TopCat.Sheaf.pullback AddCommGrpCat.{u} f.hom.base := by
  -- TODO: prove this via the canonical inverse-image owner instead of the current hand-built
  -- `RingCat` pushforward spelling.
  sorry

/-- Helper for Lemma 17.20.4: inverse image to modules over `f^{-1}\mathcal O_Y` is exact. -/
private theorem inverseImageModule_exact
    (f : X ⟶ Y) :
    exactFunctor Y.Modules (inverseImageModules f) (inverseImageModule f) := by
  -- TODO: reprove this after normalizing to the canonical inverse-image module owner used by
  -- `relativeModule`; the current `toSheaf` detour is not type-stable.
  sorry

/-- Helper for Lemma 17.20.4: exactness is preserved under a natural isomorphism of functors. -/
private theorem exactFunctor_of_natIso
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) :
    exactFunctor C D F → exactFunctor C D G := by
  intro hF
  -- Transport finite-limit and finite-colimit preservation across the functor isomorphism.
  rw [CategoryTheory.exactFunctor_iff] at hF ⊢
  let _ : PreservesFiniteLimits F := hF.1
  let _ : PreservesFiniteColimits F := hF.2
  exact ⟨
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso e,
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e
  ⟩

/-- Helper for Lemma 17.20.4: relative flatness of `\mathcal F` over `Y` gives exactness of
tensoring by `\mathcal F` after viewing it as an `f^{-1}\mathcal O_Y`-module. -/
private theorem relative_flat_tensor_exact
    [relativeFlatness f ℱ] :
    exactFunctor _ _ (relativeTensorFunctor f ℱ) := by
  -- TODO: this should be a one-line wrapper around `IsFlat.exact_tensor` once
  -- `relativeTensorFunctor` is restated over the canonical `f⁻¹𝒪_Y` owner.
  sorry

/-- Helper for Lemma 17.20.4: the composite ring-sheaf map in the standard factorization of
`f^*` agrees with the usual structure-sheaf map of `f`. -/
private theorem
    inverseImageRingUnit_comp_inverseImageStructureSheafHom_eq_toRingCatSheafHom
    (f : X ⟶ Y) :
    inverseImageRingUnit f ≫
      ((Opens.map f.hom.base).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).map
        (inverseImageStructureSheafHom f) =
      RingedSpace.Hom.toRingCatSheafHom f := by
  -- TODO: repair this comparison by using the canonical `f^♯` API directly; the current proof is
  -- blocked on the hand-transport between the commutative and noncommutative sheaf owners.
  sorry

/-- Helper for Lemma 17.20.4: `f^*` factors as inverse image to `f^{-1}\mathcal O_Y`-modules
followed by the same-space base change along `f^\sharp : f^{-1}\mathcal O_Y \to \mathcal O_X`. -/
private noncomputable abbrev pullback_iso_inverse_image_base_change (f : X ⟶ Y) :
    f^* ≅
      inverseImageModule f ⋙
        SheafOfModules.pullback (inverseImageStructureSheafHom f) :=
  -- TODO: rebuild this factorization using the canonical `pullbackComp` route after the
  -- `f^♯`/owner normalization is in place.
  sorry

/-- Helper for Lemma 17.20.4: exact functors remain exact after composition. -/
private theorem exactFunctor_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ E}
    (hF : exactFunctor C D F) (hG : exactFunctor D E G) :
    exactFunctor C E (F ⋙ G) := by
  -- Exactness is the conjunction of preserving finite limits and finite colimits, both stable
  -- under composition.
  rw [CategoryTheory.exactFunctor_iff] at hF hG ⊢
  let _ : PreservesFiniteLimits F := hF.1
  let _ : PreservesFiniteColimits F := hF.2
  let _ : PreservesFiniteLimits G := hG.1
  let _ : PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 17.20.4: if a composite `F ⋙ G` is exact and `G` reflects finite limits and
finite colimits, then `F` is exact. -/
private theorem exactFunctor_of_exact_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ E}
    [ReflectsFiniteLimits G] [ReflectsFiniteColimits G]
    (hFG : exactFunctor C E (F ⋙ G)) :
    exactFunctor C D F := by
  -- Reflect finite limits and finite colimits separately from the exact composite.
  rw [CategoryTheory.exactFunctor_iff] at hFG ⊢
  let _ : PreservesFiniteLimits (F ⋙ G) := hFG.1
  let _ : PreservesFiniteColimits (F ⋙ G) := hFG.2
  exact ⟨
    preservesFiniteLimits_of_reflects_of_preserves F G,
    preservesFiniteColimits_of_reflects_of_preserves F G
  ⟩

/-- Helper for Lemma 17.20.4: a strong monoidal functor commutes with tensoring on the right by a
fixed object. -/
private noncomputable def tensorRightCommIso
    {A : Type*} [Category A] [MonoidalCategory A]
    {B : Type*} [Category B] [MonoidalCategory B]
    (F : A ⥤ B) [Functor.Monoidal F] (M : A) :
    F ⋙ CategoryTheory.MonoidalCategory.tensorRight (F.obj M) ≅
      CategoryTheory.MonoidalCategory.tensorRight M ⋙ F := by
  -- Proof comment: this is the canonical monoidal comparison `μ` specialized to tensoring on the
  -- right by a fixed object.
  refine NatIso.ofComponents (fun N ↦ Functor.Monoidal.μIso F N M) ?_
  intro N N' g
  simpa using Functor.Monoidal.μIso_hom_natural_right (F := F) N g

/-- Helper for Lemma 17.20.4: same-site restriction of scalars along
`f^{-1}\mathcal O_Y \to \mathcal O_X` commutes with tensoring on the right by `\mathcal F`. -/
private noncomputable abbrev sameSiteRestrictionTensorIso
    (f : X ⟶ Y) (ℱ : X.Modules) :
    ((show X.Modules ⥤ X.Modules from
        SheafOfModules.RingedSite.sheafModuleTensorRightFunctor ℱ) ⋙
      inverseImageRestrictionFunctor f) ≅
      inverseImageRestrictionFunctor f ⋙ relativeTensorFunctor f ℱ :=
  -- TODO: restate this over the actual monoidal `restrictionAlong (f^♯)` owner; the current
  -- `restrictScalars` spelling does not synthesize the needed monoidal functor instance.
  sorry

/-- Helper for Lemma 17.20.4: after restricting scalars from `\mathcal O_X` to
`f^{-1}\mathcal O_Y`, the textbook functor `\mathcal G \mapsto f^*\mathcal G \otimes \mathcal F`
identifies with inverse image followed by tensoring with the relative module
`SheafOfModules.relativeModule \mathcal F f`. -/
private noncomputable abbrev restrictedPullbackTensorIso
    (f : X ⟶ Y) (ℱ : X.Modules) :
    ((f^* ⋙
      (show X.Modules ⥤ X.Modules from
        SheafOfModules.RingedSite.sheafModuleTensorRightFunctor ℱ)) ⋙
      inverseImageRestrictionFunctor f) ≅
      inverseImageModule f ⋙ relativeTensorFunctor f ℱ :=
  -- TODO: after normalizing to `restrictionAlong (f^♯)`, prove the textbook bridge
  -- `((f^* G) ⊗ ℱ)|_{f^{-1}\mathcal O_Y} ≅ f^{-1} G ⊗ relativeModule ℱ f`
  -- as the single remaining functor-level comparison.
  sorry

/-- Helper for Lemma 17.20.4: after postcomposing with restriction of scalars along
`f^{-1}\mathcal O_Y \to \mathcal O_X`, exactness reflects back to the original
`\mathcal O_X`-module-valued functor. -/
private theorem
    restrictionAlong_reflects_exactFunctor_for_inverseImageStructureSheafHom
    {F : Y.Modules ⥤ X.Modules}
    (hF :
      exactFunctor _ _
        (F ⋙
          inverseImageRestrictionFunctor f)) :
    exactFunctor _ _ F := by
  -- TODO: once the short-exact reflection lemma for same-site restriction is repaired, this
  -- should be the final formal reflection step.
  sorry

-- Proof sketch: rewrite the textbook functor as
-- `𝒢 ↦ f^{-1}𝒢 ⊗_{f^{-1}\mathcal O_Y} ℱ`. The inverse-image functor on abelian sheaves is exact,
-- and the relative-flatness instance on `ℱ` is exactly the flatness needed for tensoring with
-- `ℱ` over `f^{-1}\mathcal O_Y` to preserve short exact sequences; combining these gives exactness of the
-- composite functor.
/-- Lemma 17.20.4: if `f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)` is a morphism of ringed
spaces and `\mathcal F` is an `\mathcal O_X`-module flat over `Y`, then the functor
`\mathcal G \mapsto f^* \mathcal G \otimes_{\mathcal O_X} \mathcal F` from
`Mod(\mathcal O_Y)` to `Mod(\mathcal O_X)` is exact. -/
@[stacks 0GMU]
theorem ringedSpaceModulePullbackTensor_exact_of_flatOverTarget
    (f : X ⟶ Y) (ℱ : X.Modules)
    [(SheafOfModules.relativeModule ℱ f).IsFlat] :
    exactFunctor Y.Modules X.Modules
      (f^* ⋙
        (show ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf ⥤
            ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf from
          SheafOfModules.RingedSite.sheafModuleTensorRightFunctor ℱ)) := by
  -- TODO: finish the proof by combining `inverseImageModule_exact`,
  -- `relative_flat_tensor_exact`, the bridge `restrictedPullbackTensorIso`, and the final
  -- reflection lemma for same-site restriction of scalars.
  sorry

end AlgebraicGeometry.RingedSpace
