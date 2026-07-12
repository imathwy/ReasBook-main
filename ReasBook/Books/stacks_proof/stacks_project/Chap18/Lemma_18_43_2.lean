import Mathlib
import StacksProject_2024.Chap18.Definition_18_43_1
import StacksProject_2024.Chap07.Definition_7_15_1_Topoi
import StacksProject_2024.Chap07.Lemma_7_29_3
import StacksProject_2024.Chap07.Remark_7_29_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ w

namespace CategoryTheory

/- Domain-style sampling for Lemma 18.43.2:
- primary domain: inverse image for morphisms of topoi and locally constant sheaves.
- sampled owner/bridge declarations:
  `Sheaf.IsLocallyConstant`,
  the inverse-image notation `f⁻¹`,
  `sheaf_pullback_forget`,
  `Sheaf.isLocallyConstant_of_iso`.
- best owner abstraction: the source-facing theorem should be stated directly for the canonical
  inverse-image functor `f⁻¹` of a morphism of topoi; forget-compatibility for algebraic-valued
  sheaves is derived bridge data.
- primitive data: a morphism of topoi `f`, a sheaf `𝒢`, and local constancy of `𝒢`.
- derived API: the set-valued inverse image `f⁻¹ 𝒢` is locally constant.
- source/core/bridge triage:
  `source-facing`: `inverseImage_isLocallyConstant`;
  `core/canonical`: `Sheaf.IsLocallyConstant` and the inverse-image owner `f⁻¹`;
  `bridge/view`: the forget-compatibility comparison, canonically owned upstream by
  `sheaf_pullback_forget`; this file only needs the direct set-valued source-facing theorem. -/

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [HasWeakSheafify JC (Type w)] [HasWeakSheafify JD (Type w)]
variable [∀ X : C, HasWeakSheafify (JC.over X) (Type w)]
variable [∀ Y : D, HasWeakSheafify (JD.over Y) (Type w)]

/-- Helper for Lemma 18.43.2: restricting a constant sheaf to a slice site again gives a
constant sheaf. -/
lemma isConstant_over_of_isConstant
    [JC.WEqualsLocallyBijective (Type w)]
    [∀ X : C, (JC.over X).WEqualsLocallyBijective (Type w)]
    {H : Sheaf JC (Type w)} (U : C) [Sheaf.IsConstant JC H] :
    Sheaf.IsConstant (JC.over U) (H.over U) := by
  -- We first choose a global constant model for `H`.
  obtain ⟨E, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant (J := JC) H
  -- Restrict that model to the slice site and compare it with the canonical slice constant sheaf.
  obtain ⟨econst⟩ := Sheaf.constant_sheaf_over_nonempty_iso (J := JC) (D := Type w) U E
  exact Sheaf.isConstant_of_iso (J := JC.over U)
    ((JC.overPullback (Type w) U).mapIso e.symm ≪≫ econst)

/-- Helper for Lemma 18.43.2: the constant singleton sheaf identifies with the terminal sheaf on
any site of set-valued sheaves. -/
private noncomputable def constantSheafPUnitIsoTerminalSheaf
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)] :
    (constantSheaf J (Type w)).obj PUnit.{w + 1} ≅
      Sheaf.terminal J Types.isTerminalPUnit :=
  by
    -- The terminal sheaf is the sheafification of the constant singleton presheaf.
    simpa [constantSheaf, Sheaf.terminal] using
      (sheafificationIso (Sheaf.terminal J Types.isTerminalPUnit)).symm

/-- Helper for Lemma 18.43.2: global sections are morphisms out of the terminal sheaf. -/
private noncomputable def globalSectionsEquivTerminalSheafHom
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)]
    (ℱ : Sheaf J (Type w)) :
    (Sheaf.Γ J (Type w)).obj ℱ ≃ (Sheaf.terminal J Types.isTerminalPUnit ⟶ ℱ) :=
  -- We transport the canonical `Γ ⊣ constantSheaf` equivalence from the constant singleton sheaf
  -- to the chosen terminal sheaf.
  (Sheaf.ΓObjEquivHom J ℱ PUnit.{w + 1}).trans
    ((constantSheafPUnitIsoTerminalSheaf (J := J)).homCongr (Iso.refl ℱ))

/-- Helper for Lemma 18.43.2: the terminal-sheaf description of global sections is natural in the
sheaf argument. -/
private theorem globalSectionsEquivTerminalSheafHom_naturality
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)]
    {F G : Sheaf J (Type w)} (η : F ⟶ G)
    (x : (Sheaf.Γ J (Type w)).obj F) :
    globalSectionsEquivTerminalSheafHom (J := J) G ((Sheaf.Γ J (Type w)).map η x) =
      globalSectionsEquivTerminalSheafHom (J := J) F x ≫ η := by
  -- We first use the owner naturality for `ΓObjEquivHom` and then transport from the constant
  -- singleton sheaf to the chosen terminal sheaf.
  rw [globalSectionsEquivTerminalSheafHom, Equiv.trans_apply]
  rw [Sheaf.ΓObjEquivHom_naturality (J := J) PUnit.{w + 1} η x]
  calc
    ((constantSheafPUnitIsoTerminalSheaf (J := J)).homCongr (Iso.refl G))
        ((Sheaf.ΓObjEquivHom J F PUnit.{w + 1}) x ≫ η) =
      ((constantSheafPUnitIsoTerminalSheaf (J := J)).homCongr (Iso.refl F))
          ((Sheaf.ΓObjEquivHom J F PUnit.{w + 1}) x) ≫ η := by
            simpa using
              (Iso.homCongr_comp (constantSheafPUnitIsoTerminalSheaf (J := J))
                (Iso.refl F) (Iso.refl G)
                ((Sheaf.ΓObjEquivHom J F PUnit.{w + 1}) x) η)
    _ = globalSectionsEquivTerminalSheafHom (J := J) F x ≫ η := by
      rfl

/-- Helper for Lemma 18.43.2: the inverse terminal-sheaf description of global sections is also
natural in the sheaf argument. -/
private theorem globalSectionsEquivTerminalSheafHom_naturality_symm
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)]
    {F G : Sheaf J (Type w)} (η : F ⟶ G)
    (τ : Sheaf.terminal J Types.isTerminalPUnit ⟶ F) :
    (globalSectionsEquivTerminalSheafHom (J := J) G).symm (τ ≫ η) =
      (Sheaf.Γ J (Type w)).map η
        ((globalSectionsEquivTerminalSheafHom (J := J) F).symm τ) := by
  -- Applying the forward equivalence reduces this to the already proved naturality statement.
  apply (globalSectionsEquivTerminalSheafHom (J := J) G).injective
  simpa using
    (globalSectionsEquivTerminalSheafHom_naturality (J := J) η
      ((globalSectionsEquivTerminalSheafHom (J := J) F).symm τ)).symm

/-- Helper for Lemma 18.43.2: the inverse image of the terminal sheaf is again terminal. -/
private noncomputable def inverseImageTerminal_isTerminal
    (f : MorphismOfTopoiIn JD JC) :
    IsTerminal ((f⁻¹).obj (Sheaf.terminal JD Types.isTerminalPUnit)) :=
  by
  -- The inverse image functor preserves the empty-diagram limit because it preserves finite
  -- limits.
  let F : Sheaf JD (Type w) ⥤ Sheaf JC (Type w) := f
  letI : PreservesLimit (Functor.empty.{0} (Sheaf JD (Type w))) F := inferInstance
  simpa [F] using
    (CategoryTheory.Limits.IsTerminal.isTerminalObj
      (C := Sheaf JD (Type w))
      (D := Sheaf JC (Type w))
      (G := F)
      (X := Sheaf.terminal JD Types.isTerminalPUnit)
      (Sheaf.isTerminalTerminal JD Types.isTerminalPUnit))

/-- Helper for Lemma 18.43.2: inverse image preserves the terminal sheaf of a topos. -/
private noncomputable def inverseImageTerminalIso
    (f : MorphismOfTopoiIn JD JC) :
    (f⁻¹).obj (Sheaf.terminal JD Types.isTerminalPUnit) ≅
      Sheaf.terminal JC Types.isTerminalPUnit :=
  -- Route correction: the universe-sensitive `PreservesTerminal.iso` specialization is replaced by
  -- the stable proposition-level terminality route.
  IsTerminal.uniqueUpToIso (inverseImageTerminal_isTerminal f)
    (Sheaf.isTerminalTerminal JC Types.isTerminalPUnit)

/-- Helper for Lemma 18.43.2: global sections commute with pushforward along a morphism of
topoi. -/
private noncomputable def global_sections_pushforward_iso
    (f : MorphismOfTopoiIn JD JC)
    [HasGlobalSectionsFunctor JD (Type w)] [HasGlobalSectionsFunctor JC (Type w)] :
    (f _*) ⋙ Sheaf.Γ JD (Type w) ≅ Sheaf.Γ JC (Type w) := by
  let componentEquiv :
      ∀ F : Sheaf JC (Type w),
        ((Sheaf.Γ JD (Type w)).obj ((f _*).obj F)) ≃
          (Sheaf.Γ JC (Type w)).obj F :=
    fun F ↦
      -- We compare global sections with terminal-object morphisms, move across the adjunction,
      -- and then replace the pulled-back terminal sheaf by the terminal sheaf on the source.
      (globalSectionsEquivTerminalSheafHom (J := JD) ((f _*).obj F)).trans <|
        (f.adjunction.homEquiv (Sheaf.terminal JD Types.isTerminalPUnit) F).symm.trans <|
          (((inverseImageTerminalIso f).homCongr (Iso.refl F)).trans
            (globalSectionsEquivTerminalSheafHom (J := JC) F).symm)
  refine NatIso.ofComponents (fun F ↦ Equiv.toIso (componentEquiv F)) ?_
  intro F G η
  ext x
  -- Route correction: the source proof first isolates the right-adjoint comparison; the only
  -- remaining work here is to prove naturality by combining
  -- `Sheaf.ΓObjEquivHom_naturality`, `Adjunction.homEquiv_naturality_right`, and the fixed
  -- transport through `inverseImageTerminalIso`.
  dsimp [componentEquiv]
  calc
    (globalSectionsEquivTerminalSheafHom (J := JC) G).symm
        (((inverseImageTerminalIso f).homCongr (Iso.refl G))
          ((f.adjunction.homEquiv (Sheaf.terminal JD Types.isTerminalPUnit) G).symm
            (globalSectionsEquivTerminalSheafHom (J := JD) ((f _*).obj G)
              (((Sheaf.Γ JD (Type w)).map ((f _*).map η)) x)))) =
      (globalSectionsEquivTerminalSheafHom (J := JC) G).symm
        (((inverseImageTerminalIso f).homCongr (Iso.refl G))
          ((f.adjunction.homEquiv (Sheaf.terminal JD Types.isTerminalPUnit) G).symm
            (globalSectionsEquivTerminalSheafHom (J := JD) ((f _*).obj F) x ≫
              (f _*).map η))) := by
          rw [globalSectionsEquivTerminalSheafHom_naturality (J := JD) ((f _*).map η) x]
    _ = (globalSectionsEquivTerminalSheafHom (J := JC) G).symm
        (((inverseImageTerminalIso f).homCongr (Iso.refl G))
            (((f.adjunction.homEquiv (Sheaf.terminal JD Types.isTerminalPUnit) F).symm
              (globalSectionsEquivTerminalSheafHom (J := JD) ((f _*).obj F) x)) ≫ η)) := by
          congr 1
          exact congrArg (((inverseImageTerminalIso f).homCongr (Iso.refl G)))
            (f.adjunction.homEquiv_naturality_right_symm
              (globalSectionsEquivTerminalSheafHom (J := JD) ((f _*).obj F) x) η)
    _ = (globalSectionsEquivTerminalSheafHom (J := JC) G).symm
        ((((inverseImageTerminalIso f).homCongr (Iso.refl F))
            ((f.adjunction.homEquiv (Sheaf.terminal JD Types.isTerminalPUnit) F).symm
              (globalSectionsEquivTerminalSheafHom (J := JD) ((f _*).obj F) x))) ≫ η) := by
          exact congrArg ((globalSectionsEquivTerminalSheafHom (J := JC) G).symm) <|
            by
              simpa using
                (Iso.homCongr_comp (inverseImageTerminalIso f) (Iso.refl F) (Iso.refl G)
                  ((f.adjunction.homEquiv (Sheaf.terminal JD Types.isTerminalPUnit) F).symm
                    (globalSectionsEquivTerminalSheafHom (J := JD) ((f _*).obj F) x)) η)
    _ = (Sheaf.Γ JC (Type w)).map η
        ((globalSectionsEquivTerminalSheafHom (J := JC) F).symm
          (((inverseImageTerminalIso f).homCongr (Iso.refl F))
            ((f.adjunction.homEquiv (Sheaf.terminal JD Types.isTerminalPUnit) F).symm
              (globalSectionsEquivTerminalSheafHom (J := JD) ((f _*).obj F) x)))) := by
          rw [globalSectionsEquivTerminalSheafHom_naturality_symm (J := JC) η]
    _ = (Sheaf.Γ JC (Type w)).map η ((Equiv.trans
        (Equiv.symm (f.adjunction.homEquiv (Sheaf.terminal JD Types.isTerminalPUnit) F))
        (((inverseImageTerminalIso f).homCongr (Iso.refl F)).trans
          (globalSectionsEquivTerminalSheafHom (J := JC) F).symm))
        (globalSectionsEquivTerminalSheafHom (J := JD) ((f _*).obj F) x)) := by
          rfl

/-- Helper for Lemma 18.43.2: inverse image preserves constant sheaves of sets. -/
private noncomputable def inverse_image_constant_sheaf_iso
    (f : MorphismOfTopoiIn JD JC)
    [HasGlobalSectionsFunctor JD (Type w)] [HasGlobalSectionsFunctor JC (Type w)] :
    (constantSheaf JD (Type w)) ⋙ f⁻¹ ≅ constantSheaf JC (Type w) := by
  -- Once the right adjoints are identified, the constant sheaf functors are the corresponding
  -- unique left adjoints.
  let pulledAdj :
      (constantSheaf JD (Type w) ⋙ f⁻¹) ⊣ Sheaf.Γ JC (Type w) :=
    (((constantSheafΓAdj JD (Type w)).comp f.adjunction).ofNatIsoRight
      (global_sections_pushforward_iso (JC := JC) (JD := JD) f))
  exact Adjunction.leftAdjointUniq pulledAdj (constantSheafΓAdj JC (Type w))

/-- Helper for Lemma 18.43.2: once the constant-sheaf comparison is available, inverse image
sends constant sheaves of sets to constant sheaves of sets. -/
private theorem inverseImage_isConstant_of_isConstant
    (f : MorphismOfTopoiIn JD JC)
    [HasGlobalSectionsFunctor JD (Type w)] [HasGlobalSectionsFunctor JC (Type w)]
    {𝒢 : Sheaf JD (Type w)} [Sheaf.IsConstant JD 𝒢] :
    Sheaf.IsConstant JC ((f⁻¹).obj 𝒢) := by
  -- We first choose a global constant model for `𝒢`.
  obtain ⟨E, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant (J := JD) 𝒢
  -- Then we transport that model through inverse image and the fixed constant-sheaf comparison.
  exact Sheaf.isConstant_of_iso (J := JC)
    (((f⁻¹).mapIso e).symm ≪≫ (inverse_image_constant_sheaf_iso (JC := JC) (JD := JD) f).app E)

/-- Helper for Lemma 18.43.2: after the global constant comparison, every slice restriction of the
inverse image is again constant. -/
private theorem inverseImage_over_isConstant_of_isConstant
    [JC.WEqualsLocallyBijective (Type w)]
    [∀ X : C, (JC.over X).WEqualsLocallyBijective (Type w)]
    (f : MorphismOfTopoiIn JD JC)
    [HasGlobalSectionsFunctor JD (Type w)] [HasGlobalSectionsFunctor JC (Type w)]
    {𝒢 : Sheaf JD (Type w)} [Sheaf.IsConstant JD 𝒢]
    (U : C) :
    Sheaf.IsConstant (JC.over U) (((f⁻¹).obj 𝒢).over U) := by
  -- The source-proof route first proves global constancy after inverse image, then restricts to
  -- the slice site where the chart argument lives.
  letI : Sheaf.IsConstant JC ((f⁻¹).obj 𝒢) :=
    inverseImage_isConstant_of_isConstant (JC := JC) (JD := JD) f
  exact isConstant_over_of_isConstant (JC := JC) (U := U)

/-- Helper for Lemma 18.43.2: on a slice site, the universe-raising `ulift` comparison reflects
constancy. -/
private theorem isConstant_of_slice_ulift_transport
    {U : C} {F : Sheaf (JC.over U) (Type w)}
    [HasWeakSheafify (JC.over U) (Type (max w u₄))]
    [(JC.over U).PreservesSheafification uliftFunctor.{u₄, w}]
    [(constantSheaf (JC.over U) (Type w)).Faithful]
    [(constantSheaf (JC.over U) (Type w)).Full]
    [(constantSheaf (JC.over U) (Type (max w u₄))).Faithful]
    [(constantSheaf (JC.over U) (Type (max w u₄))).Full]
    [(sheafCompose (JC.over U) uliftFunctor.{u₄, w}).ReflectsIsomorphisms]
    [Sheaf.IsConstant (JC.over U)
      ((sheafCompose (JC.over U) uliftFunctor.{u₄, w}).obj F)] :
    Sheaf.IsConstant (JC.over U) F := by
  -- We evaluate the forget-comparison at the terminal object `Over.mk (𝟙 U)` of the slice site.
  let TU : Over U := Over.mk (𝟙 U)
  let hTU : IsTerminal TU := Over.mkIdTerminal
  exact
    (Sheaf.isConstant_iff_forget
      (J := JC.over U) (U := uliftFunctor.{u₄, w}) (F := F) hTU).mpr inferInstance

/-- Helper for Lemma 18.43.2: on a slice site, the dense-subsite equivalence part of the canonical
transport already reflects constancy. -/
private theorem isConstant_inverse_of_slice_denseSubsiteTypeTransport
    {C' : Type u₃} [Category.{v₃} C']
    {J' : GrothendieckTopology C'}
    [HasWeakSheafify J' (Type (max w u₁ u₃ v₁ v₃))]
    [∀ X : C', HasWeakSheafify (J'.over X) (Type (max w u₁ u₃ v₁ v₃))]
    (v : C ⥤ C')
    (U : C) {F : Sheaf (JC.over U) (Type w)}
    [(Over.post v).IsDenseSubsite (JC.over U) (J'.over (v.obj U))]
    [Sheaf.IsConstant (J'.over (v.obj U))
      (((Over.post v).denseSubsiteTypeTransport (JC.over U) (J'.over (v.obj U))).obj F)] :
    Sheaf.IsConstant (JC.over U)
      ((Functor.IsDenseSubsite.sheafEquiv
          (JC.over U) (J'.over (v.obj U)) (Over.post v) (Type (max w u₁ u₃ v₁ v₃))).inverse.obj
        (((Over.post v).denseSubsiteTypeTransport (JC.over U) (J'.over (v.obj U))).obj F)) := by
  let E :=
    Functor.IsDenseSubsite.sheafEquiv
      (JC.over U) (J'.over (v.obj U)) (Over.post v) (Type (max w u₁ u₃ v₁ v₃))
  -- We first reflect constancy across the slice dense-subsite equivalence.
  let TU : Over U := Over.mk (𝟙 U)
  let hTU : IsTerminal TU := Over.mkIdTerminal
  let hTV : IsTerminal ((Over.post v).obj TU) := by
    simpa [TU] using (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (v.obj U))))
  exact
    (Sheaf.isConstant_iff_of_equivalence
      (J := JC.over U) (K := J'.over (v.obj U)) (G := Over.post v)
      (D := Type (max w u₁ u₃ v₁ v₃))
      (hT := hTU) (hT' := hTV)
      (((Over.post v).denseSubsiteTypeTransport (JC.over U) (J'.over (v.obj U))).obj F)).mpr
      inferInstance

/-- Helper for Lemma 18.43.2: constancy on the dense-subsite slice transport already reflects all
the way back to the original slice sheaf. -/
private theorem isConstant_of_sourceSliceDenseSubsiteTypeTransport
    {C' : Type u₃} [Category.{v₃} C']
    {J' : GrothendieckTopology C'}
    [HasWeakSheafify J' (Type (max w u₁ u₃ v₁ v₃))]
    [∀ X : C', HasWeakSheafify (J'.over X) (Type (max w u₁ u₃ v₁ v₃))]
    (v : C ⥤ C')
    (U : C) {F : Sheaf (JC.over U) (Type w)}
    [HasWeakSheafify (JC.over U) (Type (max w u₁ u₃ v₁ v₃))]
    [(JC.over U).PreservesSheafification uliftFunctor.{max w u₁ u₃ v₁ v₃, w}]
    [(constantSheaf (JC.over U) (Type w)).Faithful]
    [(constantSheaf (JC.over U) (Type w)).Full]
    [(constantSheaf (JC.over U) (Type (max w u₁ u₃ v₁ v₃))).Faithful]
    [(constantSheaf (JC.over U) (Type (max w u₁ u₃ v₁ v₃))).Full]
    [(sheafCompose (JC.over U) uliftFunctor.{max w u₁ u₃ v₁ v₃, w}).ReflectsIsomorphisms]
    [(Over.post v).IsDenseSubsite (JC.over U) (J'.over (v.obj U))]
    [Sheaf.IsConstant (J'.over (v.obj U))
      (((Over.post v).denseSubsiteTypeTransport (JC.over U) (J'.over (v.obj U))).obj F)] :
    Sheaf.IsConstant (JC.over U) F := by
  let E :=
    Functor.IsDenseSubsite.sheafEquiv
      (JC.over U) (J'.over (v.obj U)) (Over.post v) (Type (max w u₁ u₃ v₁ v₃))
  let H := (sheafCompose (JC.over U) uliftFunctor.{max w u₁ u₃ v₁ v₃, w}).obj F
  -- We first remove the dense-subsite equivalence part of the transport.
  have hInv :
      Sheaf.IsConstant (JC.over U)
        (E.inverse.obj
          (((Over.post v).denseSubsiteTypeTransport (JC.over U) (J'.over (v.obj U))).obj F)) :=
    isConstant_inverse_of_slice_denseSubsiteTypeTransport
      (JC := JC) (J' := J') (v := v) (U := U) (F := F)
  have hUnit :
      H ≅
        E.inverse.obj
          (((Over.post v).denseSubsiteTypeTransport (JC.over U) (J'.over (v.obj U))).obj F) := by
    -- The canonical transport is `sheafCompose` followed by the dense-subsite equivalence.
    simpa [E, H, Functor.denseSubsiteTypeTransport] using E.unitIso.app H
  have hUlift :
      Sheaf.IsConstant (JC.over U)
        ((sheafCompose (JC.over U) uliftFunctor.{max w u₁ u₃ v₁ v₃, w}).obj F) := by
    letI :
        Sheaf.IsConstant (JC.over U)
          (E.inverse.obj
            (((Over.post v).denseSubsiteTypeTransport (JC.over U) (J'.over (v.obj U))).obj F)) :=
      hInv
    exact Sheaf.isConstant_congr (J := JC.over U) hUnit.symm
  -- Then we reflect constancy across the remaining universe-raising comparison.
  letI :
      Sheaf.IsConstant (JC.over U)
        ((sheafCompose (JC.over U) uliftFunctor.{max w u₁ u₃ v₁ v₃, w}).obj F) := hUlift
  exact isConstant_of_slice_ulift_transport (JC := JC) (U := U) (F := F)

/-- Helper for Lemma 18.43.2: the sieve on `U` generated by a slice-site family is exactly the
ambient sieve generated by the underlying arrows of that family. -/
private theorem overSieveOfObjectsEqOfArrows
    {U : C} {ι : Type u₆} (X : ι → Over U) :
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects X (Over.mk (𝟙 U))) =
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) := by
  -- A factorization in the slice category forgets to the same factorization in the ambient site.
  ext W g
  constructor
  · intro hg
    rw [Sieve.overEquiv_iff] at hg
    rw [Sieve.mem_ofObjects_iff] at hg
    rcases hg with ⟨i, ⟨a⟩⟩
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨i, a.left, by simpa using a.w.symm⟩
  · intro hg
    -- Conversely, any ambient factorization lifts uniquely to the corresponding slice factorization.
    rw [Sieve.overEquiv_iff]
    rw [Sieve.mem_ofArrows_iff] at hg
    rcases hg with ⟨i, a, ha⟩
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨Over.homMk a (by simpa using ha.symm)⟩⟩

/-- Helper for Lemma 18.43.2: a slice-site `CoversTop` hypothesis is equivalent to the ambient
covering sieve generated by the underlying arrows. -/
private theorem coveringSieve_of_coversTopOver
    {U : C} {ι : Type u₆} (X : ι → Over U)
    (hcover : (JC.over U).CoversTop X) :
    Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈ JC U := by
  -- We rewrite the slice cover of the terminal object into the corresponding ambient covering sieve.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    (J := JC.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal)] at hcover
  rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows (X := X)] at hcover
  exact hcover

/-- Helper for Lemma 18.43.2: an ambient covering sieve generated by arrows over `U` converts back
into the corresponding slice-site `CoversTop` statement. -/
private theorem coversTopOver_of_coveringSieve
    {U : C} {ι : Type u₆} (X : ι → Over U)
    (hcover : Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈ JC U) :
    (JC.over U).CoversTop X := by
  -- We package the ambient covering sieve back as a slice cover of the terminal object.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    (J := JC.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows (X := X)]
  exact hcover

/-- Helper for Lemma 18.43.2: pulling back a covering family in a slice site along a morphism
produces another `CoversTop` family. -/
private theorem coversTopOver_pullbackFamily
    [HasPullbacks C]
    {U V : C} (f : U ⟶ V) {ι : Type u₆} (X : ι → Over V)
    (hcover : (JC.over V).CoversTop X) :
    (JC.over U).CoversTop
      (fun i ↦ Over.mk (pullback.fst (f := f) (g := (X i).hom))) := by
  -- We pass to the ambient covering sieve, apply pullback stability, and then recognize the
  -- resulting generators as the chosen pullback family.
  apply coversTopOver_of_coveringSieve (JC := JC)
  have hS :
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈ JC V := by
    exact coveringSieve_of_coversTopOver (JC := JC) (X := X) hcover
  refine JC.superset_covering ?_ (JC.pullback_stable f hS)
  intro Z g hg
  rw [Sieve.pullback_apply, Sieve.mem_ofArrows_iff] at hg
  rw [Sieve.mem_ofArrows_iff]
  rcases hg with ⟨i, a, ha⟩
  refine ⟨i, pullback.lift g a ?_, ?_⟩
  · simpa [Category.assoc] using ha
  · simpa using (pullback.lift_fst (f := f) (g := (X i).hom) g a ha).symm

/-- Helper for Lemma 18.43.2: composing a slice-site cover of `U` with slice-site covers of each
member yields a sigma-indexed slice-site cover of `U`. -/
private theorem coversTopSigmaComp
    {U : C} {ι : Type u₆} {X : ι → Over U}
    (hX : (JC.over U).CoversTop X)
    {κ : ι → Type u₆} {Y : ∀ i : ι, κ i → Over (X i).left}
    (hY : ∀ i : ι, (JC.over (X i).left).CoversTop (Y i)) :
    (JC.over U).CoversTop
      (fun a : Sigma κ ↦ Over.mk ((Y a.1 a.2).hom ≫ (X a.1).hom)) := by
  -- We convert both slice covers to ambient covering sieves and compose them with `bindOfArrows`.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    (J := JC.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows]
  have hX' :
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈ JC U := by
    have hXCover :=
      GrothendieckTopology.coversTop_iff_of_isTerminal
        (J := JC.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal) X
    have hXTerminal :
        Sieve.ofObjects X (Over.mk (𝟙 U)) ∈ (JC.over U) (Over.mk (𝟙 U)) :=
      hXCover.mp hX
    rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows] at hXTerminal
    exact hXTerminal
  have hY' :
      ∀ i : ι,
        Sieve.ofArrows (fun a : κ i ↦ (Y i a).left) (fun a ↦ (Y i a).hom) ∈ JC (X i).left := by
    intro i
    have hYCover :=
      GrothendieckTopology.coversTop_iff_of_isTerminal
        (J := JC.over (X i).left) (X := Over.mk (𝟙 (X i).left))
        (hX := Over.mkIdTerminal) (Y i)
    have hYTerminal :
        Sieve.ofObjects (Y i) (Over.mk (𝟙 (X i).left)) ∈
          (JC.over (X i).left) (Over.mk (𝟙 (X i).left)) :=
      hYCover.mp (hY i)
    rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows] at hYTerminal
    exact hYTerminal
  simpa [Presieve.bindOfArrows_ofArrows] using
    JC.bindOfArrows
      (h := hX')
      (R := fun i ↦ Presieve.ofArrows (fun a : κ i ↦ (Y i a).left) (fun a ↦ (Y i a).hom))
      (fun i ↦ by simpa using hY' i)

/-- Helper for Lemma 18.43.2: constancy on a target slice site survives the canonical
dense-subsite transport to a reduced target slice. -/
private theorem isConstant_targetSliceDenseSubsiteTransport_of_isConstant
    {D' : Type u₃} [Category.{v₃} D']
    {K' : GrothendieckTopology D'}
    (v : D ⥤ D')
    (V : D) {F : Sheaf (JD.over V) (Type w)}
    [HasWeakSheafify (K'.over (v.obj V)) (Type (max w u₂ u₃ v₂ v₃))]
    [HasWeakSheafify (JD.over V) (Type (max w u₂ u₃ v₂ v₃))]
    [(JD.over V).PreservesSheafification uliftFunctor.{max w u₂ u₃ v₂ v₃, w}]
    [(constantSheaf (JD.over V) (Type w)).Faithful]
    [(constantSheaf (JD.over V) (Type w)).Full]
    [(constantSheaf (JD.over V) (Type (max w u₂ u₃ v₂ v₃))).Faithful]
    [(constantSheaf (JD.over V) (Type (max w u₂ u₃ v₂ v₃))).Full]
    [(sheafCompose (JD.over V) uliftFunctor.{max w u₂ u₃ v₂ v₃, w}).ReflectsIsomorphisms]
    [(Over.post v).IsDenseSubsite (JD.over V) (K'.over (v.obj V))]
    [Sheaf.IsConstant (JD.over V) F] :
    Sheaf.IsConstant (K'.over (v.obj V))
      (((Over.post v).denseSubsiteTypeTransport (JD.over V) (K'.over (v.obj V))).obj F) := by
  let E :=
    Functor.IsDenseSubsite.sheafEquiv
      (JD.over V) (K'.over (v.obj V)) (Over.post v) (Type (max w u₂ u₃ v₂ v₃))
  let H := (sheafCompose (JD.over V) uliftFunctor.{max w u₂ u₃ v₂ v₃, w}).obj F
  let TV : Over V := Over.mk (𝟙 V)
  let hTV : IsTerminal TV := Over.mkIdTerminal
  -- We first transport constancy across the universe-raising forgetful comparison on the slice.
  have hUlift :
      Sheaf.IsConstant (JD.over V)
        ((sheafCompose (JD.over V) uliftFunctor.{max w u₂ u₃ v₂ v₃, w}).obj F) := by
    exact
      (Sheaf.isConstant_iff_forget
        (J := JD.over V) (U := uliftFunctor.{max w u₂ u₃ v₂ v₃, w})
        (F := F) hTV).mp inferInstance
  let hTV' : IsTerminal ((Over.post v).obj TV) := by
    simpa [TV] using (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (v.obj V))))
  have hUnit :
      H ≅
        E.inverse.obj
          (((Over.post v).denseSubsiteTypeTransport (JD.over V) (K'.over (v.obj V))).obj F) := by
    -- The dense-subsite transport is the forward equivalence applied to the `ulift` comparison.
    simpa [E, H, Functor.denseSubsiteTypeTransport] using E.unitIso.app H
  have hInv :
      Sheaf.IsConstant (JD.over V)
        (E.inverse.obj
          (((Over.post v).denseSubsiteTypeTransport (JD.over V) (K'.over (v.obj V))).obj F)) := by
    letI :
        Sheaf.IsConstant (JD.over V)
          ((sheafCompose (JD.over V) uliftFunctor.{max w u₂ u₃ v₂ v₃, w}).obj F) := hUlift
    exact Sheaf.isConstant_congr (J := JD.over V) hUnit
  -- Then we pass to the reduced target slice via the dense-subsite equivalence.
  letI :
      Sheaf.IsConstant (JD.over V)
        (E.inverse.obj
          (((Over.post v).denseSubsiteTypeTransport (JD.over V) (K'.over (v.obj V))).obj F)) :=
    hInv
  exact
    (Sheaf.isConstant_iff_of_equivalence
      (J := JD.over V) (K := K'.over (v.obj V)) (G := Over.post v)
      (D := Type (max w u₂ u₃ v₂ v₃))
      (hT := hTV) (hT' := hTV')
      (((Over.post v).denseSubsiteTypeTransport (JD.over V) (K'.over (v.obj V))).obj F)).mp
      inferInstance

/-- Helper for Lemma 18.43.2: package the canonical Chapter 7 reduction with empty auxiliary
families so the main proof can name the replacement sites without universe holes. -/
private theorem inverseImageLocallyConstantReductionData
    (f : MorphismOfTopoiIn JD JC) :
    ∃ (C' : Type (max w u₁ u₂ v₁ v₂)) (_ : Category.{max w u₁ u₂ v₁ v₂} C')
      (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite JC J'),
      ∃ (D' : Type (max w u₁ u₂ v₁ v₂)) (_ : Category.{max w u₁ u₂ v₁ v₂} D')
        (K' : GrothendieckTopology D')
        (_ : K'.Subcanonical) (_ : HasFiniteLimits D')
        (targetFunctor : D ⥤ D') (_ : targetFunctor.IsDenseSubsite JD K'),
        ∃ (u : D' ⥤ C') (_ : IsMorphismOfSites K' J' u)
          (_ : PreservesLimitsOfShape WalkingCospan u)
          (_ : IsTerminal (u.obj (⊤_ D')))
          (g : MorphismOfTopoiIn K' J')
          (sq : CatCommSq
            (targetFunctor.sheafPushforwardContinuous
              (Type (max w u₁ u₂ v₁ v₂)) JD K')
            (g⁻¹)
            (f⁻¹)
            (sourceFunctor.sheafPushforwardContinuous
              (Type (max w u₁ u₂ v₁ v₂)) JC J')),
          True := by
  let emptySource : Empty → Sheaf JC (Type w) := Empty.elim
  let emptyTarget : Empty → Sheaf JD (Type w) := Empty.elim
  -- Proof comment: the empty-family specialization removes the auxiliary representability payload
  -- while keeping the canonical replacement-site data at the ambient universe where
  -- `exists_topos_morphism_reduction` already lives.
  obtain ⟨C', instC', J', hJ', hfinC', sourceFunctor, hsource,
      D', instD', K', hK', hfinD', targetFunctor, htarget,
      u, hu, huPullbacks, huTerminal, g, sq, _, _⟩ :=
    exists_topos_morphism_reduction
      (f := f) (ℱ := emptySource) (𝒢 := emptyTarget)
  -- Proof comment: for the empty families, the representability payload is vacuous.
  exact ⟨C', instC', J', hJ', hfinC', sourceFunctor, hsource,
    D', instD', K', hK', hfinD', targetFunctor, htarget,
    u, hu, huPullbacks, huTerminal, g, sq, trivial⟩

/-- Helper for Lemma 18.43.2: on the reduced target site, the terminal object is covered by charts
coming directly from objects of `D`. -/
private theorem targetDenseSubsiteTopImageCover
    {D' : Type u₃} [Category.{v₃} D']
    {K' : GrothendieckTopology D'}
    [HasFiniteLimits D']
    (targetFunctor : D ⥤ D')
    [targetFunctor.IsDenseSubsite JD K']
    :
    (K'.over (⊤_ D')).CoversTop
      (fun V : ULift.{max u₃ v₃} D ↦ Over.mk (terminal.from (targetFunctor.obj V.down))) := by
  -- We start from the dense-subsite cover of the reduced target terminal object by image charts.
  letI : targetFunctor.IsCoverDense K' :=
    Functor.IsDenseSubsite.isCoverDense JD K' targetFunctor
  have hImageCover :
      Sieve.ofArrows
          (fun V : ULift.{max u₃ v₃} D ↦ targetFunctor.obj V.down)
          (fun V ↦ terminal.from (targetFunctor.obj V.down)) ∈ K' (⊤_ D') := by
    have hDenseCover :
        Sieve.coverByImage targetFunctor (⊤_ D') ∈ K' (⊤_ D') :=
      Functor.is_cover_of_isCoverDense targetFunctor K' (⊤_ D')
    refine K'.superset_covering ?_ hDenseCover
    intro Z g hg
    rw [Sieve.mem_ofArrows_iff]
    change Nonempty (Presieve.CoverByImageStructure targetFunctor g) at hg
    rcases hg with ⟨s⟩
    refine ⟨ULift.up s.obj, s.lift, ?_⟩
    simpa using (terminal.hom_ext g (s.lift ≫ terminal.from (targetFunctor.obj s.obj)))
  -- We package the ambient covering sieve as a cover of the terminal object in the slice site.
  exact coversTopOver_of_coveringSieve
    (JC := K')
    (X := fun V : ULift.{max u₃ v₃} D ↦ Over.mk (terminal.from (targetFunctor.obj V.down)))
    hImageCover

/-- Helper for Chap18 Lemma 18 43 2: on any slice site, an image-covering sieve on the terminal
object is exactly a `CoversTop` family for the corresponding slice objects. -/
private theorem sliceImageCoverCoversTop
    {A : Type u₅} [Category.{v₃} A]
    {J : GrothendieckTopology A}
    {U : A} {ι : Type u₆} (X : ι → Over U)
    (hImageCover :
      Sieve.ofArrows
          (fun i : ι ↦ X i)
          (fun i ↦ terminal.from (X i)) ∈
        (J.over U) (⊤_ Over U)) :
    (J.over U).CoversTop X := by
  -- Proof comment: reinterpret the covering sieve on the slice terminal object as the ambient
  -- sieve generated by the underlying arrows of the family.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff]
  have hOver :
      (Sieve.overEquiv (Over.mk (𝟙 U)))
          (Sieve.ofObjects X (Over.mk (𝟙 U))) =
        Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) := by
    -- Proof comment: a factorization in the slice category is equivalent to a factorization of
    -- the underlying arrows in the ambient category.
    ext W g
    constructor
    · intro hg
      rw [Sieve.overEquiv_iff] at hg
      rw [Sieve.mem_ofObjects_iff] at hg
      rcases hg with ⟨i, ⟨a⟩⟩
      rw [Sieve.mem_ofArrows_iff]
      exact ⟨i, a.left, by simpa using a.w.symm⟩
    · intro hg
      rw [Sieve.overEquiv_iff]
      rw [Sieve.mem_ofArrows_iff] at hg
      rcases hg with ⟨i, a, ha⟩
      rw [Sieve.mem_ofObjects_iff]
      exact ⟨i, ⟨Over.homMk a (by simpa using ha.symm)⟩⟩
  rw [hOver]
  simpa using hImageCover

/-- Helper for Chap18 Lemma 18 43 2: on the reduced target slice above `targetFunctor.obj V`,
the terminal object is covered by image charts coming from objects of `Over V`. -/
private theorem targetSliceDenseSubsiteTopImageCover
    {D' : Type u₃} [Category.{v₃} D']
    {K' : GrothendieckTopology D'}
    [HasFiniteLimits D']
    (targetFunctor : D ⥤ D')
    [targetFunctor.IsDenseSubsite JD K']
    (V : D) :
    (K'.over (targetFunctor.obj V)).CoversTop
      (fun X : ULift.{max u₃ v₃} (Over V) ↦ (Over.post targetFunctor).obj X.down) := by
  -- Proof comment: the slice dense-subsite theorem for `Over.post targetFunctor` gives the
  -- same terminal-image cover after localizing above `targetFunctor.obj V`.
  letI : (Over.post targetFunctor).IsDenseSubsite (JD.over V) (K'.over (targetFunctor.obj V)) :=
    CategoryTheory.overPost_isDenseSubsite
      (J := JD) (K := K') targetFunctor V
  letI : (Over.post targetFunctor).IsCoverDense (K'.over (targetFunctor.obj V)) :=
    Functor.IsDenseSubsite.isCoverDense (JD.over V) (K'.over (targetFunctor.obj V))
      (Over.post targetFunctor)
  have hImageCover :
      Sieve.ofArrows
          (fun X : ULift.{max u₃ v₃} (Over V) ↦ (Over.post targetFunctor).obj X.down)
          (fun X ↦ terminal.from ((Over.post targetFunctor).obj X.down)) ∈
        (K'.over (targetFunctor.obj V)) (⊤_ Over (targetFunctor.obj V)) := by
    have hDenseCover :
        Sieve.coverByImage (Over.post targetFunctor) (⊤_ Over (targetFunctor.obj V)) ∈
          (K'.over (targetFunctor.obj V)) (⊤_ Over (targetFunctor.obj V)) :=
      Functor.is_cover_of_isCoverDense (Over.post targetFunctor)
        (K'.over (targetFunctor.obj V)) (⊤_ Over (targetFunctor.obj V))
    refine (K'.over (targetFunctor.obj V)).superset_covering ?_ hDenseCover
    intro Z g hg
    rw [Sieve.mem_ofArrows_iff]
    change Nonempty (Presieve.CoverByImageStructure (Over.post targetFunctor) g) at hg
    rcases hg with ⟨s⟩
    refine ⟨ULift.up s.obj, s.lift, ?_⟩
    simpa using
      (terminal.hom_ext g (s.lift ≫ terminal.from ((Over.post targetFunctor).obj s.obj)))
  -- Proof comment: the generic slice-image bridge packages that sieve as a `CoversTop` family.
  exact sliceImageCoverCoversTop
    (J := K') (X := fun X : ULift.{max u₃ v₃} (Over V) ↦ (Over.post targetFunctor).obj X.down)
    hImageCover

/-- Helper for Chap18 Lemma 18 43 2: composing the reduced target top cover by image objects with
the slice covers above each image object yields a single sigma-indexed cover of the reduced target
terminal object. -/
private theorem reducedTargetTopSigmaImageCover
    {D' : Type u₃} [Category.{v₃} D']
    {K' : GrothendieckTopology D'}
    [HasFiniteLimits D']
    [HasTerminal D']
    (targetFunctor : D ⥤ D')
    [targetFunctor.IsDenseSubsite JD K'] :
    (K'.over (⊤_ D')).CoversTop
      (fun a : Sigma (fun V : ULift.{max u₃ v₃} D ↦ ULift.{max u₃ v₃} (Over V.down)) ↦
        Over.mk
          (((Over.post targetFunctor).obj a.2.down).hom ≫
            terminal.from (targetFunctor.obj a.1.down))) := by
  -- Proof comment: the ambient dense-subsite cover by objects of `D` is refined chartwise by the
  -- corresponding dense-subsite covers on each localized target slice.
  exact coversTopSigmaComp
    (JC := K')
    (U := ⊤_ D')
    (X := fun V : ULift.{max u₃ v₃} D ↦ Over.mk (terminal.from (targetFunctor.obj V.down)))
    (targetDenseSubsiteTopImageCover (JD := JD) (D' := D') (K' := K') targetFunctor)
    (Y := fun V : ULift.{max u₃ v₃} D ↦
      fun X : ULift.{max u₃ v₃} (Over V.down) ↦
        (show Over (targetFunctor.obj V.down) from (Over.post targetFunctor).obj X.down))
    (fun V ↦ by
      simpa using
        targetSliceDenseSubsiteTopImageCover
          (JD := JD) (D' := D') (K' := K') targetFunctor V.down)

/-- Helper for Lemma 18.43.2: every reduced source object has the canonical morphism to the image
under `u` of the reduced target terminal object. -/
private noncomputable def sourceToReducedTargetTerminalMap
    {C' : Type u₃} [Category.{v₃} C']
    {D' : Type u₃} [Category.{v₃} D'] [HasTerminal D']
    (sourceFunctor : C ⥤ C')
    (u : D' ⥤ C')
    (huTerminal : IsTerminal (u.obj (⊤_ D')))
    (U : C) :
    sourceFunctor.obj U ⟶ u.obj (⊤_ D') :=
  huTerminal.from (sourceFunctor.obj U)

/-- Helper for Lemma 18.43.2: the canonical map from a reduced source object to the reduced target
terminal object is uniquely determined by terminality. -/
private theorem sourceToReducedTargetTerminalMap_eq
    {C' : Type u₃} [Category.{v₃} C']
    {D' : Type u₃} [Category.{v₃} D'] [HasTerminal D']
    (sourceFunctor : C ⥤ C')
    (u : D' ⥤ C')
    (huTerminal : IsTerminal (u.obj (⊤_ D')))
    (U : C)
    (g : sourceFunctor.obj U ⟶ u.obj (⊤_ D')) :
    g = sourceToReducedTargetTerminalMap
      (sourceFunctor := sourceFunctor) (u := u) huTerminal U := by
  -- Proof comment: maps into a terminal object are unique.
  apply huTerminal.hom_ext

/-- Helper for Chap18 Lemma 18 43 2: on the reduced source slice, the terminal object is covered
by the image charts coming from objects of `Over U`. -/
private theorem sourceSliceDenseSubsiteTopImageCover
    {C' : Type u₃} [Category.{v₃} C']
    {J' : GrothendieckTopology C'}
    [HasFiniteLimits C']
    (sourceFunctor : C ⥤ C')
    [sourceFunctor.IsDenseSubsite JC J']
    (U : C) :
    (J'.over (sourceFunctor.obj U)).CoversTop
      (fun X : ULift.{max u₃ v₃} (Over U) ↦ (Over.post sourceFunctor).obj X.down) := by
  -- Proof comment: the slice dense-subsite theorem from Chapter 7 lets us reuse the terminal-image
  -- cover construction directly on the localized site.
  letI : (Over.post sourceFunctor).IsDenseSubsite (JC.over U) (J'.over (sourceFunctor.obj U)) :=
    CategoryTheory.overPost_isDenseSubsite
      (J := JC) (K := J') sourceFunctor U
  letI : (Over.post sourceFunctor).IsCoverDense (J'.over (sourceFunctor.obj U)) :=
    Functor.IsDenseSubsite.isCoverDense (JC.over U) (J'.over (sourceFunctor.obj U))
      (Over.post sourceFunctor)
  have hImageCover :
      Sieve.ofArrows
          (fun X : ULift.{max u₃ v₃} (Over U) ↦ (Over.post sourceFunctor).obj X.down)
          (fun X ↦ terminal.from ((Over.post sourceFunctor).obj X.down)) ∈
        (J'.over (sourceFunctor.obj U)) (⊤_ Over (sourceFunctor.obj U)) := by
    have hDenseCover :
        Sieve.coverByImage (Over.post sourceFunctor) (⊤_ Over (sourceFunctor.obj U)) ∈
          (J'.over (sourceFunctor.obj U)) (⊤_ Over (sourceFunctor.obj U)) :=
      Functor.is_cover_of_isCoverDense (Over.post sourceFunctor)
        (J'.over (sourceFunctor.obj U)) (⊤_ Over (sourceFunctor.obj U))
    refine (J'.over (sourceFunctor.obj U)).superset_covering ?_ hDenseCover
    intro Z g hg
    rw [Sieve.mem_ofArrows_iff]
    change Nonempty (Presieve.CoverByImageStructure (Over.post sourceFunctor) g) at hg
    rcases hg with ⟨s⟩
    refine ⟨ULift.up s.obj, s.lift, ?_⟩
    simpa using
      (terminal.hom_ext g (s.lift ≫ terminal.from ((Over.post sourceFunctor).obj s.obj)))
  -- Proof comment: the generic slice-image bridge packages that sieve as a `CoversTop` family.
  exact sliceImageCoverCoversTop
    (J := J') (X := fun X : ULift.{max u₃ v₃} (Over U) ↦ (Over.post sourceFunctor).obj X.down)
    hImageCover

/- Proof sketch: pull back a local constant trivialization of `𝒢`; inverse image carries constant
sheaves of sets to constant sheaves of sets, so the pulled-back cover still witnesses local
constancy. -/
/-- Lemma 18.43.2: if `f : \mathit{Sh}(\mathcal C) \to \mathit{Sh}(\mathcal D)` is a morphism of
topoi and `\mathcal G` is a locally constant sheaf of sets on `\mathcal D`, then its inverse
image `f^{-1}\mathcal G` is a locally constant sheaf of sets on `\mathcal C`. -/
@[stacks 093R]
theorem inverseImage_isLocallyConstant
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [HasWeakSheafify JC (Type w)] [HasWeakSheafify JD (Type w)]
    [∀ X : C, HasWeakSheafify (JC.over X) (Type w)]
    [∀ Y : D, HasWeakSheafify (JD.over Y) (Type w)]
    (f : MorphismOfTopoiIn JD JC)
    (𝒢 : Sheaf JD (Type w))
    [Sheaf.IsLocallyConstant 𝒢] :
    Sheaf.IsLocallyConstant ((f⁻¹).obj 𝒢) := by
  classical
  -- Route correction: the old abstract slice-topos cover-extraction route stalled on producing
  -- representable source charts. The source-faithful next step is the Chapter 7 canonical
  -- reduction to a site morphism, where the transported charts are representable by construction.
  refine Sheaf.isLocallyConstant_of_explicit_constant_models (J := JC) ?_
  intro U
  -- Proof comment: the proved helpers reduce the theorem to a Chapter 7 replacement-site
  -- argument. The reduced target-side sigma cover is now packaged by
  -- `reducedTargetTopSigmaImageCover`; the remaining blocker is the chartwise comparison that
  -- transports that cover through `u` and identifies the pulled-back reduced-source charts with
  -- the original slice restrictions via `sq.iso` and the site-pullback comparison.
  let emptySource : Empty → Sheaf JC (Type w) := Empty.elim
  let emptyTarget : Empty → Sheaf JD (Type w) := Empty.elim
  -- Proof comment: the empty-family specialization removes the auxiliary representability payload
  -- while keeping the canonical replacement-site data for the current morphism of topoi.
  obtain ⟨C', instC', J', hJ', hfinC', sourceFunctor, hsource,
      D', instD', K', hK', hfinD', targetFunctor, htarget,
      u, hu, huPullbacks, huTerminal, g, sq, _, _⟩ :=
    exists_topos_morphism_reduction
      (f := f) (ℱ := emptySource) (𝒢 := emptyTarget)
  let γ :=
    sourceToReducedTargetTerminalMap
      (sourceFunctor := sourceFunctor) (u := u) huTerminal U
  have hTargetCover :
      (K'.over (⊤_ D')).CoversTop
        (fun a : Sigma (fun V : ULift.{max (max w u₁ u₂ v₁ v₂) (max w u₁ u₂ v₁ v₂)} D ↦
            ULift.{max (max w u₁ u₂ v₁ v₂) (max w u₁ u₂ v₁ v₂)} (Over V.down)) ↦
          Over.mk
            (((Over.post targetFunctor).obj a.2.down).hom ≫
              terminal.from (targetFunctor.obj a.1.down))) :=
    reducedTargetTopSigmaImageCover (JD := JD) targetFunctor
  -- TODO: push `hTargetCover` through the site morphism `u`, pull it back along `γ`, and prove
  -- that each resulting source chart restriction is the pullback of a constant target chart by a
  -- stable comparison lemma combining `sq.iso` with `Functor.sheafPullbackIso`.
  sorry

end CategoryTheory
