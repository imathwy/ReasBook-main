import Mathlib
import StacksProject_2024.Chap06.Definition_6_27_1
import StacksProject_2024.Chap07.Example_7_33_5
import StacksProject_2024.Chap12.Lemma_12_7_2
import StacksProject_2024.Chap17.Definition_17_17_1
import StacksProject_2024.Chap17.Lemma_17_17_2
import StacksProject_2024.Chap18.Lemma_18_14_4
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Lemma_18_28_2
import StacksProject_2024.Chap18.Lemma_18_36_3
import StacksProject_2024.Chap18.Lemma_18_39_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite

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

-- Proof sketch: the forward implication is Lemma 18.39.2 applied pointwise. For the converse,
-- flatness means exactness of tensoring with `ℱ`, and exactness of the resulting short complexes
-- of abelian sheaves can be checked on the conservative family `p` by Lemma 18.14.4. The stalk
-- identification for tensor products from Lemma 18.26.2 matches those stalkwise exactness
-- conditions with `IsFlatAtPoint`.
/-- Lemma 18.39.3: a sheaf of `\mathcal O`-modules on a ringed site is flat if and only if it is
flat at every point of a conservative family, expressed here by exactness of tensoring with
`\mathcal F` followed by taking the fiber functor at each `p_i`; this is the site-theoretic form
of saying that each stalk `\mathcal F_{p_i}` is a flat `\mathcal O_{p_i}`-module. -/
theorem isFlat_iff_isFlatAtPoint_of_conservativeFamily
    (hp : (ofObj p).IsConservativeFamilyOfPoints) :
    IsFlat 𝒪 ℱ ↔
      ∀ i : I,
        exactFunctor
          (SheafOfModules (ringSheaf J 𝒪))
          AddCommGrpCat.{u}
          (tensorRight ℱ ⋙
            SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
              (p i).sheafFiber) := by
  constructor
  · intro hFlat i
    -- Proof comment: apply the pointwise flatness theorem from Lemma 18.39.2 to each member of
    -- the conservative family.
    letI : IsFlat 𝒪 ℱ := hFlat
    simpa [IsFlatAtPoint] using
      (isFlatAtPoint_of_isFlat (𝒪 := 𝒪) (p := p i) (ℱ := ℱ))
  · intro hPoint
    refine ⟨?_⟩
    -- Proof comment: use the Chapter 12 exact-functor criterion, then detect short exactness of
    -- the underlying additive sheaf row on the conservative family of points.
    refine
      (CategoryTheory.functor_exact_iff_maps_shortExact_to_exact_mono_epi
        (A := SheafOfModules (ringSheaf J 𝒪))
        (B := SheafOfModules (ringSheaf J 𝒪))
        (F := tensorRight ℱ)).2 ?_
    intro S hS
    let G : SheafOfModules (ringSheaf J 𝒪) ⥤ Sheaf J AddCommGrpCat.{u} :=
      SheafOfModules.toSheaf (ringSheaf J 𝒪)
    let T : ShortComplex (SheafOfModules (ringSheaf J 𝒪)) := S.map (tensorRight ℱ)
    have hPointShortExact :
        ∀ i : I, ((T.map G).map (p i).sheafFiber).ShortExact := by
      intro i
      -- Proof comment: the assumed pointwise exactness makes tensoring with `ℱ` preserve every
      -- short exact row after taking the fiber at `p i`.
      exact
        (((Functor.exact_tfae (tensorRight ℱ ⋙ G ⋙ (p i).sheafFiber)).out 3 0).1
          (by simpa [exactFunctor_iff] using hPoint i)) S hS
    have hUnderlyingExact : (T.map G).Exact := by
      -- Proof comment: exactness of additive sheaves is detected on the conservative family `p`.
      refine
        (CategoryTheory.GrothendieckTopology.abelianSheaf_exact_iff_stalkwise_exact_of_conservativeFamily
          p hp (T.map G)).2 ?_
      intro i
      simpa [T, G] using (hPointShortExact i).exact
    have hUnderlyingMono : Mono (T.map G).f := by
      -- Proof comment: monicity is likewise reflected by the conservative family of fiber
      -- functors.
      rw [(hp.jointlyReflectMonomorphisms AddCommGrpCat.{u}).mono_iff]
      intro Φ
      rcases Φ with ⟨q, hq⟩
      rcases (ofObj_iff p q).1 hq with ⟨i, hi⟩
      cases hi
      simpa [T, G] using (hPointShortExact i).mono_f
    have hUnderlyingEpi : Epi (T.map G).g := by
      -- Proof comment: the same conservative-family argument recovers epimorphy of the right
      -- map from the stalkwise short exact rows.
      rw [(hp.jointlyReflectEpimorphisms AddCommGrpCat.{u}).epi_iff]
      intro Φ
      rcases Φ with ⟨q, hq⟩
      rcases (ofObj_iff p q).1 hq with ⟨i, hi⟩
      cases hi
      simpa [T, G] using (hPointShortExact i).epi_g
    have hUnderlyingShortExact : (T.map G).ShortExact := by
      -- Proof comment: package exactness, monicity, and epimorphy into a short exact row in the
      -- additive sheaf category.
      exact ShortComplex.ShortExact.mk' hUnderlyingExact hUnderlyingMono hUnderlyingEpi
    have hMapped : T.ShortExact := by
      -- Proof comment: forgetting module structure is faithful, so short exactness reflects back
      -- from additive sheaves to sheaves of modules.
      exact ShortComplex.reflects_shortExact_of_faithful G hUnderlyingShortExact
    refine ⟨?_, ?_, ?_⟩
    · simpa [T] using (T.exact_iff_exact_toComposableArrows).1 hMapped.exact
    · simpa [T] using hMapped.mono_f
    · simpa [T] using hMapped.epi_g

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
private theorem ringedSiteIsFlat_iff_isFlatAtPoint_allPoints
    (ℱ : X.Modules) :
    SheafOfModules.RingedSite.IsFlat X.sheaf ℱ ↔
      ∀ x : X,
        IsFlatAtPoint X.sheaf (Opens.pointGrothendieckTopology x) ℱ := by
  -- Proof comment: the family of all opens-site points is conservative, so the general
  -- conservative-family criterion applies verbatim.
  simpa using
    (isFlat_iff_isFlatAtPoint_of_conservativeFamily
      (p := fun x : X ↦ Opens.pointGrothendieckTopology x)
      (𝒪 := X.sheaf)
      (ℱ := ℱ)
      (Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology X))

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
    S.ShortExact := by
  let F := PresheafOfModules.toPresheaf X.ringCatSheaf.obj
  have hUnderlying :
      (S.map F).ShortExact := by
    refine (shortExact_iff_pointwiseShortExactFunctorCategory
      (J := (Opens X)ᵒᵖ) (A := AddCommGrpCat.{u}) (S := S.map F)).2 ?_
    intro U
    let evalU := PresheafOfModules.evaluation X.ringCatSheaf.obj U
    let G : ModuleCat (X.ringCatSheaf.obj.obj U) ⥤ AddCommGrpCat.{u} := forget₂ _ _
    have hForgetU :
        (((S.map evalU).map G)).ShortExact := by
      let hExactG :
          exactFunctor
            (ModuleCat (X.ringCatSheaf.obj.obj U))
            AddCommGrpCat.{u}
            G := (ExactFunctor.of G).property
      exact
        (((Functor.exact_tfae G).out 3 0).1
          (by simpa [exactFunctor_iff] using hExactG))
          (S.map evalU) (hS U)
    -- Proof comment: after forgetting module structure at `U`, evaluation is exactly ordinary
    -- evaluation of the underlying additive presheaf.
    change
      ((S.map F).map ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U)).ShortExact
    simpa [F, evalU, PresheafOfModules.evaluation] using hForgetU
  -- Proof comment: the faithful forgetful functor to additive presheaves reflects short
  -- exactness.
  exact ShortComplex.reflects_shortExact_of_faithful F hUnderlying

/-- Helper for Lemma 18.39.3: an open of `X` missing `x` pulls back along `pointInclusion x` to
the bottom open of the one-point space. -/
private theorem pointInclusion_preimage_eq_bot
    (x : X) {U : Opens X} (hxU : x ∉ U) :
    ((TopologicalSpace.Opens.map (pointInclusion x).hom.base).obj U) = ⊥ := by
  -- Proof comment: the source of `pointInclusion x` has one point, and that point lands at `x`,
  -- so the preimage is empty exactly when `x` is not in `U`.
  ext y
  cases y
  simpa [pointInclusion_hom_base_apply, hxU]

/-- Helper for Lemma 18.39.3: realize a stalk module as the canonical module sheaf on the
one-point ringed space `({x}, \mathcal O_{X, x})`. -/
private noncomputable def pointModuleSheafFunctor
    (x : X) :
    ModuleCat (X.presheaf.stalk x) ⥤ RingedSpace.Modules (pointRingedSpace x) where
  obj M := pointModuleSheaf x M
  map {M N} φ :=
    (pointModuleSheaf_homEquivTop x (pointModuleSheaf x M) N).symm
      ((pointModuleSheaf_objTopIso x M).hom ≫
        (ModuleCat.restrictScalars
          (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).map φ ≫
        (pointModuleSheaf_objTopIso x N).inv)
  map_id M := by
    -- Proof comment: the point-module map is defined by its top-open component, so the identity
    -- law reduces to the identity component on `⊤`.
    apply (pointModuleSheaf_homEquivTop x (pointModuleSheaf x M) M).injective
    simp [pointModuleSheafFunctor, Category.assoc]
  map_comp {M N P} φ ψ := by
    -- Proof comment: composition is again determined by the top-open component, where the chosen
    -- defining formula is functorial by ordinary composition in `ModuleCat`.
    apply (pointModuleSheaf_homEquivTop x (pointModuleSheaf x M) P).injective
    simp [pointModuleSheafFunctor, Category.assoc]

/-- Helper for Lemma 18.39.3: the top-open component of `pointModuleSheafFunctor.map` is the
expected restriction-of-scalars image of the original module morphism. -/
private theorem pointModuleSheafFunctor_map_top
    (x : X) {M N : ModuleCat (X.presheaf.stalk x)} (φ : M ⟶ N) :
    (((pointModuleSheafFunctor (X := X) x).map φ).val.app
        (op (⊤ : Opens (TopCat.of PUnit)))) ≫
        (pointModuleSheaf_objTopIso x N).hom =
      (pointModuleSheaf_objTopIso x M).hom ≫
        (ModuleCat.restrictScalars
          (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).map φ := by
  -- Proof comment: by construction, the map of point module sheaves is the unique morphism whose
  -- top-open component is the displayed restriction-of-scalars map.
  have htop :=
    (pointModuleSheaf_homEquivTop x (pointModuleSheaf x M) N).apply_symm_apply
      ((pointModuleSheaf_objTopIso x M).hom ≫
        (ModuleCat.restrictScalars
          (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).map φ ≫
        (pointModuleSheaf_objTopIso x N).inv)
  simpa [pointModuleSheafFunctor, Category.assoc] using htop

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
  NatIso.ofComponents
    (fun 𝒢 ↦ RingedSpace.tensorProductStalkIso 𝒢 ℱ x)
    (fun {𝒢 𝒢'} φ ↦ by
      -- Proof comment: functoriality is exactly the imported tensor/stalk naturality square,
      -- specialized to the identity on `ℱ`.
      simpa [Category.assoc] using
        (RingedSpace.tensorProductStalkIso_naturality
          (f := φ) (g := 𝟙 ℱ) (x := x)).w)

/-- Helper for Lemma 18.39.3: stalkwise flatness in the Chapter 17 sense implies the Chapter 18
site-point exactness condition at the corresponding opens-site point. -/
private theorem isFlatAtPoint_of_flatAt
    (x : X) (ℱ : X.Modules)
    (hFlat : ℱ.flat_at x) :
    IsFlatAtPoint X.sheaf (Opens.pointGrothendieckTopology x) ℱ := by
  let M := RingedSpace.stalkModuleCat ℱ x
  letI : Module.Flat (X.presheaf.stalk x) ↑M := by
    simpa [SheafOfModules.flat_at] using hFlat
  have hTensor :
      exactFunctor
        (ModuleCat (X.presheaf.stalk x))
        (ModuleCat (X.presheaf.stalk x))
        (tensorRight M) := by
    -- Proof comment: a flat module is exactly what makes tensoring with it preserve finite
    -- limits, and `tensorRight` already preserves finite colimits in the module category.
    rw [CategoryTheory.exactFunctor_iff]
    exact ⟨
      (Module.Flat.iff_preservesFiniteLimits_tensorRight M).1 inferInstance,
      inferInstance
    ⟩
  have hPointTensor :
      exactFunctor
        X.Modules
        (ModuleCat (X.presheaf.stalk x))
        (tensorRight ℱ ⋙ pointStalkModuleFunctor (X := X) x) := by
    -- Proof comment: first tensor after taking the retargeted point stalk, then transport back
    -- across the canonical tensor/stalk comparison.
    exact exactFunctorOfNatIso
      (pointStalkTensorComparisonIso (X := X) x ℱ).symm
      (exactFunctorComp (pointStalkModuleFunctorExact (X := X) x) hTensor)
  have hForget :
      exactFunctor
        (ModuleCat (X.presheaf.stalk x))
        AddCommGrpCat
        (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat) :=
    (ExactFunctor.of (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat)).property
  have hUnderlying :
      exactFunctor
        X.Modules
        AddCommGrpCat
        (tensorRight ℱ ⋙ pointStalkModuleFunctor (X := X) x ⋙
          forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat) := by
    -- Proof comment: exactness survives after forgetting the module structure on the stalk.
    exact exactFunctorComp hPointTensor hForget
  have hPoint :
      exactFunctor
        X.Modules
        AddCommGrpCat
        (tensorRight ℱ ⋙
          SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
          (Opens.pointGrothendieckTopology x).sheafFiber) := by
    -- Proof comment: replace the forgotten module-valued stalk by the ordinary additive point
    -- fiber functor using the canonical comparison isomorphism.
    exact exactFunctorOfNatIso
      (Functor.isoWhiskerLeft (tensorRight ℱ)
        (pointStalkModuleFunctorForgetIso (X := X) x))
      hUnderlying
  simpa [IsFlatAtPoint] using hPoint

/-- Helper for Lemma 18.39.3: the site-point exactness hypothesis at `x` should imply exactness
of tensoring with the ordinary stalk module `\mathcal F_x`. -/
private theorem tensorRightExactOfIsFlatAtPoint
    (x : X) (ℱ : X.Modules)
    (hPoint : IsFlatAtPoint X.sheaf (Opens.pointGrothendieckTopology x) ℱ) :
    exactFunctor
      (ModuleCat (X.presheaf.stalk x))
      (ModuleCat (X.presheaf.stalk x))
      (tensorRight (RingedSpace.stalkModuleCat ℱ x)) := by
  -- Route correction: the missing converse bridge is not another conservative-family argument on
  -- `X.Modules`; it is the sequence-level transport from stalk-module short exact sequences to
  -- point-supported sheaf short exact sequences via skyscraper module sheaves at `x`.
  -- TODO: `pointModuleSheafFunctor` and `pointModuleSheafFunctor_map_top` now isolate the map
  -- normalization on the one-point ringed space. The remaining blocker is a natural comparison
  -- identifying the forgotten point stalk of
  -- `pointModuleSheafFunctor x ⋙ RingedSpace.Hom.pushforward (pointInclusion x)` with the plain
  -- forgetful functor on `ModuleCat (X.presheaf.stalk x)`, so that `hPoint` can be reflected back
  -- to exactness of `tensorRight (RingedSpace.stalkModuleCat ℱ x)`.
  sorry

/-- Helper for Lemma 18.39.3: opens-site flatness at `x` recovers the Chapter 17 stalk-flatness
predicate `flat_at x`. -/
private theorem flatAt_of_isFlatAtPoint
    (x : X) (ℱ : X.Modules)
    (hPoint : IsFlatAtPoint X.sheaf (Opens.pointGrothendieckTopology x) ℱ) :
    ℱ.flat_at x := by
  let M := RingedSpace.stalkModuleCat ℱ x
  have hExact :
      exactFunctor
        (ModuleCat (X.presheaf.stalk x))
        (ModuleCat (X.presheaf.stalk x))
        (tensorRight M) :=
    tensorRightExactOfIsFlatAtPoint (X := X) x ℱ hPoint
  -- Proof comment: once tensoring with the stalk module is exact, the Chapter 17 flatness
  -- predicate is exactly the standard flat-module exactness criterion on `ModuleCat`.
  simpa [SheafOfModules.flat_at] using
    (Module.Flat.iff_preservesFiniteLimits_tensorRight M).2
      ((CategoryTheory.exactFunctor_iff (tensorRight M)).1 hExact).1

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
    ℱ.IsFlat ↔ SheafOfModules.RingedSite.IsFlat X.sheaf ℱ := by
  -- Route correction: the remaining bridge is not the conservative-family criterion itself, which
  -- is now available above, but the opens-site identification between the pointwise exact-functor
  -- condition at `Opens.pointGrothendieckTopology x` and the Chapter 17 stalk-flatness predicate
  -- `ℱ.flat_at x`.
  rw [SheafOfModules.isFlat_iff_stalkwise,
    ringedSiteIsFlat_iff_isFlatAtPoint_allPoints (X := X) ℱ]
  intro x
  -- Proof comment: after specializing to a single opens-site point, the remaining task is to
  -- identify the exact-functor definition `IsFlatAtPoint` with the Chapter 17 stalk-flatness
  -- predicate `flat_at`.
  constructor
  · intro hFlat
    -- Proof comment: the easy direction only needs the exact tensor functor on the stalk module,
    -- transported back through the canonical point-stalk comparison.
    exact isFlatAtPoint_of_flatAt (X := X) x ℱ hFlat
  · intro hPoint
    -- Proof comment: the converse now factors through the isolated exactness bridge for tensoring
    -- with the stalk module.
    exact flatAt_of_isFlatAtPoint (X := X) x ℱ hPoint

end SheafOfModules
