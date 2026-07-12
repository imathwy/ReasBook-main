import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap07.Lemma_7_22_2
import StacksProject_2024.Chap18.Lemma_18_15_3
import StacksProject_2024.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/- Domain-style sampling for Lemma 18.19.3:
- primary domain: exactness of extension by zero and localized restriction for sheaves of modules
  on the localized ringed site `(C/U, J.over U, 𝒪.over U)`;
- sampled owner declarations:
  `ringedSiteLocalizedExtensionByZero`,
  `ringedSiteLocalizedRestriction`,
  `exactFunctor`;
- best owner abstraction: the source-facing chapter owners
  `ringedSiteLocalizedExtensionByZero J 𝒪 U` and
  `ringedSiteLocalizedRestriction J 𝒪 U`.
-/

omit [HasWeakSheafify J AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.19.3: after forgetting module structure, localized extension by zero is
definitionally the additive-sheaf pushforward along `Over.star U`. -/
private theorem localizedExtensionByZeroCompToSheaf :
    ringedSiteLocalizedExtensionByZero J 𝒪 U ⋙
        SheafOfModules.toSheaf (ringSheaf J 𝒪) =
      SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
        (Over.star U).sheafPushforwardContinuous AddCommGrpCat.{u} J (J.over U) := by
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.19.3: localized extension by zero preserves finite limits because it is
the right adjoint in the localized adjunction. -/
private theorem localizedExtensionByZeroPreservesFiniteLimitsAux :
    PreservesFiniteLimits (ringedSiteLocalizedExtensionByZero J 𝒪 U) := by
  -- Proof comment: the localized extension-by-zero functor is already registered as a right
  -- adjoint, so finite-limit preservation is an instance search step.
  infer_instance

/-- Helper for Lemma 18.19.3: the underlying additive-sheaf extension by zero is exact. -/
private theorem underlying_locally_surjective_of_additive_sheaf_map
    {E : Type u} [Category.{u} E] (L : GrothendieckTopology E)
    [L.HasSheafCompose (forget AddCommGrpCat.{u})]
    {F G : Sheaf L AddCommGrpCat.{u}} (π : F ⟶ G)
    (hπ : Sheaf.IsLocallySurjective π) :
    Sheaf.IsLocallySurjective ((sheafCompose L (forget AddCommGrpCat.{u})).map π) := by
  change Presheaf.IsLocallySurjective L
    (Functor.whiskerRight π.hom (forget AddCommGrpCat.{u}))
  change Presheaf.IsLocallySurjective L π.hom at hπ
  refine Presheaf.IsLocallySurjective.mk ?_
  intro V s
  simpa [Presheaf.imageSieve] using hπ.imageSieve_mem (U := V) s

private theorem sheafType_preservesEpimorphisms_of_preservesCoequalizers
    {E E' : Type u} [Category.{u} E] [Category.{u} E']
    {L : GrothendieckTopology E} {L' : GrothendieckTopology E'}
    {F : Sheaf L (Type u) ⥤ Sheaf L' (Type u)}
    [PreservesColimitsOfShape WalkingParallelPair F] :
    F.PreservesEpimorphisms := by
  constructor
  intro X Y φ hφ
  letI : Epi φ := hφ
  letI : IsRegularEpi φ := isRegularEpi_of_regularEpi <| regularEpiOfEpi φ
  have hcofork :
      IsColimit
        (Cofork.ofπ (F.map φ)
          (by
            simpa only [Functor.map_comp] using congrArg (fun k ↦ F.map k) (IsRegularEpi.w φ))) := by
    exact isColimitCoforkMapOfIsColimit F (IsRegularEpi.w φ) (IsRegularEpi.isColimit φ)
  exact Cofork.IsColimit.epi hcofork

private theorem localizedAdditiveExtensionByZeroExact :
    exactFunctor
      (Sheaf (J.over U) AddCommGrpCat.{u})
      (Sheaf J AddCommGrpCat.{u})
      ((Over.star U).sheafPushforwardContinuous AddCommGrpCat.{u} J (J.over U)) := by
  let G : Sheaf (J.over U) AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
    (Over.star U).sheafPushforwardContinuous AddCommGrpCat.{u} J (J.over U)
  let GType : Sheaf (J.over U) (Type u) ⥤ Sheaf J (Type u) :=
    (Over.star U).sheafPushforwardContinuous (Type u) J (J.over U)
  let GCocontType : Sheaf (J.over U) (Type u) ⥤ Sheaf J (Type u) :=
    (Over.forget U).sheafPushforwardCocontinuous (Type u) (J.over U) J
  let _ : HasWeakSheafify (J.over U) AddCommGrpCat.{u} := inferInstance
  let _ : HasSheafify (J.over U) AddCommGrpCat.{u} := inferInstance
  let _ : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let _ : (Over.star U).IsContinuous J (J.over U) := inferInstance
  let _ : (Over.forget U).IsCocontinuous (J.over U) J := inferInstance
  let _ : ∀ P : (Over U)ᵒᵖ ⥤ Type u, (Over.forget U).op.HasPointwiseRightKanExtension P :=
    fun _ ↦ inferInstance
  have eType : GType ≅ GCocontType :=
    continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
      (u := Over.forget U)
      (v := Over.star U)
      (A := Type u)
      (adj := Over.forgetAdjStar U)
  have hTypeCoeq : PreservesColimitsOfShape WalkingParallelPair GType := by
    let _ : PreservesColimits GCocontType := by
      infer_instance
    let _ : PreservesColimitsOfShape WalkingParallelPair GCocontType := by
      infer_instance
    exact preservesColimitsOfShape_of_natIso eType.symm
  let _ : GType.PreservesEpimorphisms :=
    sheafType_preservesEpimorphisms_of_preservesCoequalizers
  have hAddEpi : G.PreservesEpimorphisms := by
    constructor
    intro X Y φ hφ
    have hφForget : Epi ((sheafCompose (J.over U) (forget AddCommGrpCat.{u})).map φ) := by
      let hloc : Sheaf.IsLocallySurjective φ :=
        (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} φ).2 hφ
      exact (Sheaf.isLocallySurjective_iff_epi _).1
        (underlying_locally_surjective_of_additive_sheaf_map (J.over U) φ hloc)
    have hmapForget :
        Epi (GType.map ((sheafCompose (J.over U) (forget AddCommGrpCat.{u})).map φ)) := by
      infer_instance
    have hmapUnderlying :
        Epi ((sheafCompose J (forget AddCommGrpCat.{u})).map (G.map φ)) := by
      simpa [G, GType, sheaf_pushforward_forget] using hmapForget
    refine ⟨?_⟩
    intro Z g h hgh
    apply (sheafCompose J (forget AddCommGrpCat.{u})).map_injective
    apply (cancel_epi ((sheafCompose J (forget AddCommGrpCat.{u})).map (G.map φ))).1
    simpa using congrArg ((sheafCompose J (forget AddCommGrpCat.{u})).map) hgh
  let _ : G.IsRightAdjoint :=
    ((Over.star U).sheafAdjunctionContinuous AddCommGrpCat.{u} J (J.over U)).isRightAdjoint
  let _ : PreservesFiniteLimits G := inferInstance
  let _ : Abelian (Sheaf (J.over U) AddCommGrpCat.{u}) := by infer_instance
  let _ : Abelian (Sheaf J AddCommGrpCat.{u}) := by infer_instance
  have hLeft : leftExactFunctor _ _ G := by
    simpa [leftExactFunctor_iff] using (inferInstance : PreservesFiniteLimits G)
  let _ : G.Additive :=
    CategoryTheory.functor_additive_of_leftExact_or_rightExact (F := G) (.inl hLeft)
  let _ : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive G
  let _ : G.PreservesEpimorphisms := hAddEpi
  let _ : G.PreservesHomology :=
    CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels G
  let _ : PreservesFiniteColimits G :=
    CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology G
  exact (exactFunctor_iff G).2 ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 18.19.3: localized extension by zero preserves finite colimits after
forgetting to additive sheaves and reflecting finite colimits back through `toSheaf`. -/
private theorem localizedExtensionByZeroPreservesFiniteColimitsAux :
    PreservesFiniteColimits (ringedSiteLocalizedExtensionByZero J 𝒪 U) := by
  let F : ringedSiteModuleCategory (J.over U) (𝒪.over U) ⥤ ringedSiteModuleCategory J 𝒪 :=
    ringedSiteLocalizedExtensionByZero J 𝒪 U
  let G : Sheaf (J.over U) AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
    (Over.star U).sheafPushforwardContinuous AddCommGrpCat.{u} J (J.over U)
  let TOver : ringedSiteModuleCategory (J.over U) (𝒪.over U) ⥤
      Sheaf (J.over U) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))
  let TBase : ringedSiteModuleCategory J 𝒪 ⥤ Sheaf J AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf (ringSheaf J 𝒪)
  have hGExact :
      exactFunctor
        (Sheaf (J.over U) AddCommGrpCat.{u})
        (Sheaf J AddCommGrpCat.{u})
        G :=
    localizedAdditiveExtensionByZeroExact (C := C) (J := J) (U := U)
  let _ : PreservesFiniteColimits G :=
    ((exactFunctor_iff G).1 hGExact).2
  let _ : PreservesFiniteColimits TOver := by
    infer_instance
  have hComp : PreservesFiniteColimits (TOver ⋙ G) := by
    exact comp_preservesFiniteColimits TOver G
  -- Proof comment: compose the exact additive extension-by-zero with `toSheaf`, then reflect the
  -- resulting finite-colimit preservation back to module sheaves.
  let _ : PreservesFiniteColimits (F ⋙ TBase) := by
    rw [localizedExtensionByZeroCompToSheaf (C := C) (J := J) (𝒪 := 𝒪) (U := U)]
    exact hComp
  let _ : ReflectsFiniteColimits TBase := by
    infer_instance
  simpa [F] using
    (preservesFiniteColimits_of_reflects_of_preserves
      (ringedSiteLocalizedExtensionByZero J 𝒪 U) TBase :
        PreservesFiniteColimits (ringedSiteLocalizedExtensionByZero J 𝒪 U))

/-- Lemma 18.19.3: the localized extension-by-zero functor is exact. -/
@[stacks 03DJ]
theorem ringedSiteLocalizedExtensionByZero_exact :
    exactFunctor _ _ (ringedSiteLocalizedExtensionByZero J 𝒪 U) := by
  -- Proof comment: exactness follows from the exact-functor criterion once the localized direct
  -- image is known to preserve finite limits and finite colimits.
  exact (exactFunctor_iff (ringedSiteLocalizedExtensionByZero J 𝒪 U)).2
    ⟨localizedExtensionByZeroPreservesFiniteLimitsAux (C := C) (J := J) (𝒪 := 𝒪) (U := U),
      localizedExtensionByZeroPreservesFiniteColimitsAux (C := C) (J := J) (𝒪 := 𝒪) (U := U)⟩

instance ringedSiteLocalizedExtensionByZero_preservesFiniteLimits :
    PreservesFiniteLimits (ringedSiteLocalizedExtensionByZero J 𝒪 U) :=
  localizedExtensionByZeroPreservesFiniteLimitsAux (C := C) (J := J) (𝒪 := 𝒪) (U := U)

instance ringedSiteLocalizedExtensionByZero_preservesFiniteColimits :
    PreservesFiniteColimits (ringedSiteLocalizedExtensionByZero J 𝒪 U) :=
  localizedExtensionByZeroPreservesFiniteColimitsAux (C := C) (J := J) (𝒪 := 𝒪) (U := U)

instance ringedSiteLocalizedExtensionByZero_additive
    [Abelian (ringedSiteModuleCategory J 𝒪)]
    [Abelian (ringedSiteModuleCategory (J.over U) (𝒪.over U))] :
    (ringedSiteLocalizedExtensionByZero J 𝒪 U).Additive := by
  refine ⟨?_⟩
  intro M N f g
  ext V x
  rfl

section RestrictionExact

variable [HasSheafify (J.over U) AddCommGrpCat.{u}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasBinaryProducts C] in
/-- Lemma 18.19.3: the localized restriction functor is exact. -/
@[stacks 03DJ]
theorem ringedSiteLocalizedRestriction_exact :
    exactFunctor _ _ (ringedSiteLocalizedRestriction J 𝒪 U) := by
  -- Proof comment: `j_U^*` is the same module pushforward specialized to `Over.forget U`.
  let _ : (Over.forget U).IsAlmostCocontinuous (J.over U) J := by
    infer_instance
  simpa [ringedSiteLocalizedRestriction] using
    CategoryTheory.Functor.sheafOfModules_pushforward_exact_of_isAlmostCocontinuous
      (u := Over.forget U)
      (JC := J.over U)
      (JD := J)
      (𝒪C := ringSheaf (J.over U) (𝒪.over U))
      (𝒪D := ringSheaf J 𝒪)
      (φ := 𝟙 ((ringSheaf J 𝒪).over U))

instance ringedSiteLocalizedRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (ringedSiteLocalizedRestriction J 𝒪 U) :=
  (CategoryTheory.exactFunctor_iff
      (ringedSiteLocalizedRestriction J 𝒪 U)).mp
    (ringedSiteLocalizedRestriction_exact J 𝒪 U) |>.1

instance ringedSiteLocalizedRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (ringedSiteLocalizedRestriction J 𝒪 U) :=
  (CategoryTheory.exactFunctor_iff
      (ringedSiteLocalizedRestriction J 𝒪 U)).mp
    (ringedSiteLocalizedRestriction_exact J 𝒪 U) |>.2

instance ringedSiteLocalizedRestriction_additive
    [Abelian (ringedSiteModuleCategory J 𝒪)]
    [Abelian (ringedSiteModuleCategory (J.over U) (𝒪.over U))] :
    (ringedSiteLocalizedRestriction J 𝒪 U).Additive := by
  refine ⟨?_⟩
  intro M N f g
  ext V x
  rfl

end RestrictionExact

end
