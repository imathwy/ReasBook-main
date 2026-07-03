import Mathlib
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_29_1 (from Chap07) -/
open CategoryTheory Opposite

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- A functor is source-locally faithful for a topology on the source if equal arrows become equal
after restricting along a covering sieve in the source site. -/
class IsSourceLocallyFaithful (u : C ⥤ D) (J : GrothendieckTopology C) : Prop where
  equalizer_mem {U' U : C} (a b : U' ⟶ U) (h : u.map a = u.map b) :
    Sieve.equalizer a b ∈ J U'

/-- A functor is source-locally full for a topology on the source if every arrow between objects in
the image locally comes from an arrow in the source site. -/
class IsSourceLocallyFull (u : C ⥤ D) (J : GrothendieckTopology C) : Prop where
  imageSieve_mem {U' U : C} (c : u.obj U' ⟶ u.obj U) : u.imageSieve c ∈ J U'

end CategoryTheory.Functor

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace Functor

/-- Helper for Lemma 7.29.1: over an object of the form `u(U)`, the counit of the
right-Kan-extension adjunction is an isomorphism because source-local fullness supplies local
lifts and source-local faithfulness supplies the overlap equalities needed for sheaf glueing. -/
private theorem source_local_isIso_ranCounit_app
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [IsSourceLocallyFaithful u J] [IsSourceLocallyFull u J] [u.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P]
    (Y : Sheaf J (Type w)) (U : C) (X : Type w) :
    IsIso ((yoneda.map ((u.op.ranCounit.app Y.obj).app (op U))).app (op X)) := by
  set_option backward.isDefEq.respectTransparency false in
    -- Route correction: this is the dense-subsite counit proof with the image/equalizer covers
    -- supplied directly by the source-local hypotheses rather than by an `IsDenseSubsite` owner.
    rw [isIso_iff_bijective]
    constructor
    · intro f₁ f₂ e
      -- Two candidate sections agree once they agree after every source-local lift of `g`.
      apply (isPointwiseRightKanExtensionRanCounit u.op Y.1 (.op (u.obj U))).hom_ext
      rintro ⟨⟨⟨⟩⟩, ⟨W⟩, g⟩
      obtain ⟨g, rfl⟩ : ∃ g' : u.obj W ⟶ u.obj U, g = g'.op := ⟨g.unop, rfl⟩
      apply (Y.2 X _ (IsSourceLocallyFull.imageSieve_mem (u := u) (J := J) g)).isSeparatedFor.ext
      dsimp
      rintro V iVW ⟨iVU, e'⟩
      have := congr($e ≫ Y.1.map iVU.op)
      simp only [comp_obj, yoneda_map_app, Category.assoc, comp_map,
        ← NatTrans.naturality, op_obj, op_map, Quiver.Hom.unop_op, ← map_comp_assoc,
        ← op_comp, ← e'] at this ⊢
      simpa [← NatTrans.naturality] using this
    · intro f
      -- We glue the source-local lifts of `f` to build the universal cone element.
      have (X Y Z) (f : X ⟶ Y) (g : u.obj Y ⟶ u.obj Z) (hf : u.imageSieve g f) : Exists _ := hf
      choose l hl using this
      let c : Limits.Cone (StructuredArrow.proj (op (u.obj U)) u.op ⋙ Y.obj) := by
        refine ⟨X, ⟨fun g ↦ ?_, ?_⟩⟩
        · refine Y.2.amalgamate ⟨_, IsSourceLocallyFull.imageSieve_mem (u := u) (J := J) g.hom.unop⟩
            (fun I ↦ f ≫ Y.1.map (l _ _ _ _ _ I.hf).op) fun I₁ I₂ r ↦ ?_
          apply (Y.2 X _ (IsSourceLocallyFaithful.equalizer_mem (u := u) (J := J)
            (r.g₁ ≫ l _ _ _ _ _ I₁.hf) (r.g₂ ≫ l _ _ _ _ _ I₂.hf) ?_)).isSeparatedFor.ext
              fun V iUV (hiUV : _ = _) ↦ ?_
          · simp only [const_obj_obj, op_obj, map_comp, hl]
            simp only [← map_comp_assoc, r.w]
          · simp [← map_comp, ← op_comp, hiUV]
        · dsimp
          rintro ⟨⟨⟨⟩⟩, ⟨W₁⟩, g₁⟩ ⟨⟨⟨⟩⟩, ⟨W₂⟩, g₂⟩ ⟨⟨⟨⟨⟩⟩⟩, i, hi⟩
          dsimp at g₁ g₂ i hi
          have h : g₂ = g₁ ≫ (u.map i.unop).op := by simpa only [Category.id_comp] using hi
          rcases h with ⟨rfl⟩
          have h : ∃ g' : u.obj W₁ ⟶ u.obj U, g₁ = g'.op := ⟨g₁.unop, rfl⟩
          rcases h with ⟨g, rfl⟩
          have h : ∃ i' : W₂ ⟶ W₁, i = i'.op := ⟨i.unop, rfl⟩
          rcases h with ⟨i, rfl⟩
          simp only [unop_comp, Quiver.Hom.unop_op, Category.id_comp]
          apply Y.2.hom_ext ⟨_, IsSourceLocallyFull.imageSieve_mem (u := u) (J := J) (u.map i ≫ g)⟩
          intro I
          simp only [Presheaf.IsSheaf.amalgamate_map, Category.assoc, ← Functor.map_comp, ← op_comp]
          let I' :
              GrothendieckTopology.Cover.Arrow
                ⟨_, IsSourceLocallyFull.imageSieve_mem (u := u) (J := J) g⟩ :=
            ⟨_, I.f ≫ i, ⟨l _ _ _ _ _ I.hf, by simp [hl]⟩⟩
          refine Eq.trans ?_ (Y.2.amalgamate_map _ _ _ I').symm
          apply (Y.2 X _ (IsSourceLocallyFaithful.equalizer_mem (u := u) (J := J)
            (l _ _ _ _ _ I.hf) (l _ _ _ _ _ I'.hf) (by simp [I', hl]))).isSeparatedFor.ext
              fun V iUV (hiUV : _ = _) ↦ ?_
          simp [I', ← Functor.map_comp, ← op_comp, hiUV]
      refine ⟨(isPointwiseRightKanExtensionRanCounit u.op Y.1 (.op (u.obj U))).lift c, ?_⟩
      -- The glued cone is forced to recover the original section at the identity object.
      have := (isPointwiseRightKanExtensionRanCounit u.op Y.1 (.op (u.obj U))).fac c (.mk (𝟙 _))
      simp only [id_obj, comp_obj, StructuredArrow.proj_obj, StructuredArrow.mk_right,
        RightExtension.coneAt_pt, RightExtension.mk_left, RightExtension.coneAt_π_app,
        const_obj_obj, op_obj, StructuredArrow.mk_hom_eq_self, map_id, whiskeringLeft_obj_obj,
        RightExtension.mk_hom, Category.id_comp] at this
      simp only [c, id_obj, yoneda_map_app, this]
      apply Y.2.hom_ext ⟨_, IsSourceLocallyFull.imageSieve_mem (u := u) (J := J) (𝟙 (u.obj U))⟩
      intro I
      apply (Y.2 X _ (IsSourceLocallyFaithful.equalizer_mem (u := u) (J := J)
        (l _ _ _ _ _ I.hf) I.f (by simp [hl]))).isSeparatedFor.ext fun V iUV (hiUV : _ = _) ↦ ?_
      simp [← Functor.map_comp, ← op_comp, hiUV]

/-- Helper for Lemma 7.29.1: the source-local computation on `u(U)` upgrades to the counit
isomorphism for the sheaf adjunction itself by reflecting through `sheafToPresheaf` and `yoneda`. -/
private instance source_local_counit_isIso
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [IsSourceLocallyFaithful u J] [IsSourceLocallyFull u J] [u.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P]
    (Y : Sheaf J (Type w)) :
    IsIso ((u.sheafAdjunctionCocontinuous (Type w) J K).counit.app Y) := by
  -- Reflect the objectwise counit through the faithful forgetful functors to presheaves.
  apply +allowSynthFailures Functor.ReflectsIsomorphisms.reflects (sheafToPresheaf J (Type w))
  rw [NatTrans.isIso_iff_isIso_app]
  intro ⟨U⟩
  apply +allowSynthFailures Functor.ReflectsIsomorphisms.reflects yoneda
  rw [NatTrans.isIso_iff_isIso_app]
  intro ⟨X⟩
  simpa [Functor.sheafAdjunctionCocontinuous_counit_app_hom]
    using source_local_isIso_ranCounit_app (J := J) (K := K) u Y U X

/-- Helper for Lemma 7.29.1: after the source-local counit computation, the unit evaluated on an
object of the form `u(U)` is bijective because the right adjoint is fully faithful. -/
private theorem source_local_unit_bijective_on_image
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [IsSourceLocallyFaithful u J] [IsSourceLocallyFull u J] [u.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P]
    (F : Sheaf K (Type w)) (U : C) :
    Function.Bijective (((u.sheafAdjunctionCocontinuous (Type w) J K).unit.app F).hom.app
      (op (u.obj U))) := by
  let adj := u.sheafAdjunctionCocontinuous (Type w) J K
  letI : IsIso adj.counit := by
    exact NatIso.isIso_of_isIso_app _
  -- Since the counit is invertible, the right adjoint is fully faithful, hence the unit becomes
  -- invertible after applying the left adjoint.
  let ff : (u.sheafPushforwardCocontinuous (Type w) J K).FullyFaithful :=
    CategoryTheory.Adjunction.fullyFaithfulROfIsIsoCounit (h := adj)
  letI : (u.sheafPushforwardCocontinuous (Type w) J K).Full := ff.full
  letI : (u.sheafPushforwardCocontinuous (Type w) J K).Faithful := ff.faithful
  haveI : IsIso ((u.sheafPushforwardContinuous (Type w) J K).map (adj.unit.app F)) := by
    infer_instance
  let e := (asIso ((sheafToPresheaf J (Type w)).map
    ((u.sheafPushforwardContinuous (Type w) J K).map (adj.unit.app F)))).app (op U)
  have he : e.hom = ((adj.unit.app F).hom.app (op (u.obj U))) := rfl
  rw [← he]
  exact (isIso_iff_bijective _).mp inferInstance

/-- Helper for Lemma 7.29.1: the unit is an isomorphism because sections of the target sheaf are
locally determined on image covers, and the local inverse on those image objects glues uniquely. -/
private instance source_local_unit_isIso
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [IsSourceLocallyFaithful u J] [IsSourceLocallyFull u J] [u.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P]
    (F : Sheaf K (Type w)) :
    IsIso ((u.sheafAdjunctionCocontinuous (Type w) J K).unit.app F) := by
  let adj := u.sheafAdjunctionCocontinuous (Type w) J K
  let F' :=
    (u.sheafPushforwardCocontinuous (Type w) J K).obj
      ((u.sheafPushforwardContinuous (Type w) J K).obj F)
  let η := ((adj.unit.app F).hom : F.obj ⟶ F'.obj)
  apply +allowSynthFailures Functor.ReflectsIsomorphisms.reflects (sheafToPresheaf K (Type w))
  rw [NatTrans.isIso_iff_isIso_app]
  intro ⟨V⟩
  rw [isIso_iff_bijective]
  constructor
  · intro s t hst
    -- Injectivity is checked on the cover by image objects, where the unit is already bijective.
    apply Functor.IsCoverDense.ext u F V
    intro U f
    apply (source_local_unit_bijective_on_image (J := J) (K := K) u F U).1
    have hs : η.app (op (u.obj U)) (F.obj.map f.op s) = F'.obj.map f.op (η.app (op V) s) :=
      congrFun (η.naturality f.op) s
    have hmid : F'.obj.map f.op (η.app (op V) s) = F'.obj.map f.op (η.app (op V) t) :=
      congrArg (F'.obj.map f.op) hst
    have ht : F'.obj.map f.op (η.app (op V) t) = η.app (op (u.obj U)) (F.obj.map f.op t) := by
      simpa using (congrFun (η.naturality f.op) t).symm
    exact hs.trans (hmid.trans ht)
  · intro y
    -- We first choose inverse images on every image object and then assemble them by sheaf glueing.
    let imagePreimage : ∀ U : C, F'.obj.obj (op (u.obj U)) → F.obj.obj (op (u.obj U)) :=
      fun U z ↦ ((source_local_unit_bijective_on_image (J := J) (K := K) u F U).2 z).choose
    have imagePreimage_spec :
        ∀ U : C, ∀ z : F'.obj.obj (op (u.obj U)),
          η.app (op (u.obj U)) (imagePreimage U z) = z := by
      intro U z
      exact ((source_local_unit_bijective_on_image (J := J) (K := K) u F U).2 z).choose_spec
    let localFamily :
        CategoryTheory.Presieve.FamilyOfElements F.obj (CategoryTheory.Presieve.coverByImage u V) :=
      fun Y g hg ↦
        let l := Nonempty.some hg
        F.obj.map l.lift.op (imagePreimage l.obj (F'.obj.map l.map.op y))
    have localFamily_spec :
        ∀ {Y : D} (g : Y ⟶ V) (hg : Presieve.coverByImage u V g),
          η.app (op Y) (localFamily g hg) = F'.obj.map g.op y := by
      intro Y g hg
      let l := Nonempty.some hg
      calc
        η.app (op Y) (F.obj.map l.lift.op (imagePreimage l.obj (F'.obj.map l.map.op y)))
            = F'.obj.map l.lift.op
                (η.app (op (u.obj l.obj)) (imagePreimage l.obj (F'.obj.map l.map.op y))) := by
                  exact congrFun (η.naturality l.lift.op) _
        _ = F'.obj.map l.lift.op (F'.obj.map l.map.op y) := by
          rw [imagePreimage_spec]
        _ = F'.obj.map g.op y := by
          rw [← FunctorToTypes.map_comp_apply]
          simp [← op_comp, l.fac]
    have localFamily_compatible : localFamily.Compatible := by
      intro Y₁ Y₂ Z iZY₁ iZY₂ g₁ g₂ hg₁ hg₂ e
      -- Compatibility is reduced to image objects, where injectivity is already available.
      apply Functor.IsCoverDense.ext u F Z
      intro W k
      apply (source_local_unit_bijective_on_image (J := J) (K := K) u F W).1
      have h₁ :
          η.app (op (u.obj W)) (F.obj.map ((k ≫ iZY₁).op) (localFamily g₁ hg₁)) =
            F'.obj.map (k ≫ iZY₁).op (F'.obj.map g₁.op y) := by
        calc
          η.app (op (u.obj W)) (F.obj.map ((k ≫ iZY₁).op) (localFamily g₁ hg₁))
              = F'.obj.map (k ≫ iZY₁).op (η.app (op Y₁) (localFamily g₁ hg₁)) := by
                  exact congrFun (η.naturality ((k ≫ iZY₁).op)) (localFamily g₁ hg₁)
          _ = F'.obj.map (k ≫ iZY₁).op (F'.obj.map g₁.op y) := by rw [localFamily_spec]
      have h₂ :
          η.app (op (u.obj W)) (F.obj.map ((k ≫ iZY₂).op) (localFamily g₂ hg₂)) =
            F'.obj.map (k ≫ iZY₂).op (F'.obj.map g₂.op y) := by
        calc
          η.app (op (u.obj W)) (F.obj.map ((k ≫ iZY₂).op) (localFamily g₂ hg₂))
              = F'.obj.map (k ≫ iZY₂).op (η.app (op Y₂) (localFamily g₂ hg₂)) := by
                  exact congrFun (η.naturality ((k ≫ iZY₂).op)) (localFamily g₂ hg₂)
          _ = F'.obj.map (k ≫ iZY₂).op (F'.obj.map g₂.op y) := by rw [localFamily_spec]
      have hk₁' :
          F.obj.map k.op (F.obj.map iZY₁.op (localFamily g₁ hg₁)) =
            F.obj.map ((k ≫ iZY₁).op) (localFamily g₁ hg₁) := by
        rw [← FunctorToTypes.map_comp_apply]
        simp [← op_comp]
      have hk₁ :
          η.app (op (u.obj W)) (F.obj.map k.op (F.obj.map iZY₁.op (localFamily g₁ hg₁))) =
            η.app (op (u.obj W)) (F.obj.map ((k ≫ iZY₁).op) (localFamily g₁ hg₁)) :=
        congrArg (η.app (op (u.obj W))) hk₁'
      have hk₂' :
          F.obj.map ((k ≫ iZY₂).op) (localFamily g₂ hg₂) =
            F.obj.map k.op (F.obj.map iZY₂.op (localFamily g₂ hg₂)) := by
        symm
        rw [← FunctorToTypes.map_comp_apply]
        simp [← op_comp]
      have hk₂ :
          η.app (op (u.obj W)) (F.obj.map ((k ≫ iZY₂).op) (localFamily g₂ hg₂)) =
            η.app (op (u.obj W)) (F.obj.map k.op (F.obj.map iZY₂.op (localFamily g₂ hg₂))) :=
        congrArg (η.app (op (u.obj W))) hk₂'
      have hm :
          F'.obj.map (k ≫ iZY₁).op (F'.obj.map g₁.op y) =
            F'.obj.map (k ≫ iZY₂).op (F'.obj.map g₂.op y) := by
        rw [← FunctorToTypes.map_comp_apply]
        rw [← FunctorToTypes.map_comp_apply]
        simpa [Category.assoc, ← op_comp] using congrArg (fun h => F'.obj.map (k ≫ h).op y) e
      exact hk₁.trans (h₁.trans (hm.trans (h₂.symm.trans hk₂)))
    let hFsheaf := ((isSheaf_iff_isSheaf_of_type K F.obj).mp F.property) _
      (u.is_cover_of_isCoverDense K V)
    let x := hFsheaf.amalgamate localFamily localFamily_compatible
    refine ⟨x, ?_⟩
    -- The glued section recovers the prescribed target section because this can be checked on the
    -- same image cover, where the local inverse was chosen by construction.
    apply Functor.IsCoverDense.ext u F' V
    intro U f
    have hx : F.obj.map f.op x = localFamily f (CategoryTheory.Presieve.in_coverByImage u f) :=
      hFsheaf.valid_glue localFamily_compatible f (CategoryTheory.Presieve.in_coverByImage u f)
    have hη :
        F'.obj.map f.op (η.app (op V) x) = η.app (op (u.obj U)) (F.obj.map f.op x) := by
      simpa using (congrFun (η.naturality f.op) x).symm
    have hglue :
        η.app (op (u.obj U)) (F.obj.map f.op x) =
          η.app (op (u.obj U)) (localFamily f (CategoryTheory.Presieve.in_coverByImage u f)) := by
      rw [hx]
    exact hη.trans (hglue.trans (localFamily_spec f (CategoryTheory.Presieve.in_coverByImage u f)))

/-- Helper for Lemma 7.29.1: once the counit is invertible, the adjunction shows that the
continuous pushforward is an equivalence. -/
private theorem sheafPushforwardContinuous_isEquivalence_of_source_local
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [IsSourceLocallyFaithful u J] [IsSourceLocallyFull u J] [u.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P] :
    (u.sheafPushforwardContinuous (Type w) J K).IsEquivalence := by
  let adj := u.sheafAdjunctionCocontinuous (Type w) J K
  -- Both the counit and the unit are now known objectwise, so the adjunction upgrades to an
  -- equivalence of categories.
  letI : IsIso adj.counit := by
    exact NatIso.isIso_of_isIso_app _
  letI : IsIso adj.unit := by
    exact NatIso.isIso_of_isIso_app _
  exact adj.toEquivalence.isEquivalence_functor

end Functor

-- Proof sketch: the source-local hypotheses upgrade to mathlib's canonical dense-subsite owner,
-- whose comparison-lemma API gives the continuous pushforward equivalence after the required
-- right-Kan-extension bridge is supplied. Applying the adjunction between continuous inverse image
-- and cocontinuous direct image then shows that the right adjoint is also an equivalence.
/-- Lemma 7.29.1: if `u : C ⥤ D` is continuous, cocontinuous, source-locally faithful,
source-locally full, and cover-dense, then the direct-image functor on sheaves of sets attached to
`u` is an equivalence of categories; equivalently, the morphism of topoi associated to `u` is an
equivalence. -/
lemma comparison_directImage_isEquivalence
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [Functor.IsSourceLocallyFaithful u J] [Functor.IsSourceLocallyFull u J] [u.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P] :
    (u.sheafPushforwardCocontinuous (Type w) J K).IsEquivalence := by
  letI : (u.sheafPushforwardContinuous (Type w) J K).IsEquivalence :=
    Functor.sheafPushforwardContinuous_isEquivalence_of_source_local u
  exact (u.sheafAdjunctionCocontinuous (Type w) J K).isEquivalence_right_of_isEquivalence_left

end

end CategoryTheory

/-! ### Definition_7_29_2 (from Chap07) -/
universe u₁ u₂ v₁ v₂ w

/- Domain-style sampling for Definition 7.29.2:
- primary domain: dense-subsite comparison for sheaf topoi and cocontinuous direct images;
- sampled owner API:
  `CategoryTheory.Functor.IsDenseSubsite`,
  `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`,
  `CategoryTheory.sourceLocal_isDenseSubsite`,
  `CategoryTheory.Functor.sheafPushforwardCocontinuous`,
  `CategoryTheory.Adjunction.isEquivalence_right_of_isEquivalence_left`;
- source/core/bridge triage:
  `source-facing`: the Stacks notion of a special cocontinuous functor;
  `core/canonical`: the dense-subsite owner `Functor.IsDenseSubsite`;
  `bridge/view`: the pointwise right Kan extension data needed to realize the cocontinuous direct
  image on sheaves of sets, and the resulting equivalence instance.

Primitive data are only the dense-subsite owner data expressing the comparison-lemma hypotheses.
The set-valued pointwise right Kan extension hypotheses are bridge data needed to realize the
cocontinuous direct image on sheaves of sets, and the resulting equivalence is derived API from
that owner plus those extra hypotheses.
-/

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Definition 7.29.2: the Stacks notion of a special cocontinuous functor is owned canonically by
`G.IsDenseSubsite J K`; this file keeps only the cocontinuous direct-image bridge under the extra
pointwise right Kan extension hypotheses. -/
recall Functor.IsDenseSubsite

namespace IsDenseSubsite

/-- A dense-subsite functor has cocontinuous direct image on `Type w`-valued sheaves an
equivalence whenever the corresponding pointwise right Kan extensions exist. -/
theorem sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension
    (G : C ⥤ D) [G.IsDenseSubsite J K]
    [∀ P : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension P] :
    (G.sheafPushforwardCocontinuous (Type w) J K).IsEquivalence := by
  letI : IsSourceLocallyFaithful G J := ⟨fun a b h ↦ equalizer_mem J K G a b h⟩
  letI : IsSourceLocallyFull G J := ⟨fun c ↦ imageSieve_mem J K G c⟩
  letI : G.IsCoverDense K := isCoverDense J K G
  exact comparison_directImage_isEquivalence G

/-- A dense-subsite functor has cocontinuous direct image on sheaves of sets an
equivalence whenever the corresponding pointwise right Kan extensions exist. -/
instance sheafPushforwardCocontinuous_isEquivalence
    (G : C ⥤ D) [G.IsDenseSubsite J K]
    [∀ P : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), G.op.HasPointwiseRightKanExtension P] :
    (G.sheafPushforwardCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).IsEquivalence :=
  sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension G

end IsDenseSubsite

end Functor
end CategoryTheory

/-! ### Lemma_7_29_3 (from Chap07) -/
universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Lemma 7.29.3:
- primary domain: comparison-lemma style sheaf equivalences for dense subsites and their slice-site
  localizations;
- sampled owner API:
  `Functor.IsDenseSubsite`,
  `Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension`,
  `Over.post`;
- source/core/bridge triage:
  `source-facing`: the localized dense-subsite instance for `Over.post u`;
  `core/canonical`: the dense-subsite direct-image equivalence instance for
  `G.sheafPushforwardCocontinuous`;
  `bridge/view`: the slice-site specialization obtained by instantiating that canonical instance at
  `G := Over.post u`.

Primitive data here are only the functor `u`, the object `U`, and the owner instance
`u.IsDenseSubsite J K`. The sheaf-equivalence statement is derived API from that
owner together with separate pointwise right Kan extension hypotheses on `Over.post u`, so this
file should keep only the localized owner instance and recall the bridge theorem directly rather
than introducing a parallel theorem wrapper.
-/

/-- Helper for Lemma 7.29.3: after transporting a slice sieve back to the base category, pushing
it forward along `Over.post u` is the same as pushing the transported sieve forward along `u`. -/
private theorem overEquiv_functorPushforward_post
    (u : C ⥤ D) {U : C} {Y : Over U} (S : Sieve Y) :
    Sieve.overEquiv ((Over.post u).obj Y) (S.functorPushforward (Over.post u)) =
      (Sieve.overEquiv Y S).functorPushforward u := by
  -- Both sides are the pushforward of `S` along the same composite
  -- `Over.forget U ⋙ u = Over.post u ⋙ Over.forget (u.obj U)`.
  change Sieve.functorPushforward (Over.forget (u.obj U)) (S.functorPushforward (Over.post u)) =
    Sieve.functorPushforward u (Sieve.functorPushforward (Over.forget U) S)
  rw [← Sieve.functorPushforward_comp, ← Sieve.functorPushforward_comp]
  rfl

/-- Helper for Lemma 7.29.3: equalizer sieves in the slice category transport to equalizer sieves
of the underlying arrows in the base category. -/
private theorem overEquiv_equalizer
    {U : C} {X Y : Over U} (f g : X ⟶ Y) :
    Sieve.overEquiv X (Sieve.equalizer f g) = Sieve.equalizer f.left g.left := by
  ext Z k
  rw [Sieve.overEquiv_iff]
  constructor
  · -- Equality of slice morphisms is detected on their underlying arrows.
    intro hk
    change (Over.homMk k : Over.mk (k ≫ X.hom) ⟶ X) ≫ f =
        (Over.homMk k : Over.mk (k ≫ X.hom) ⟶ X) ≫ g at hk
    simpa using congrArg CommaMorphism.left hk
  · -- Conversely, equal underlying arrows give equal morphisms in the slice.
    intro hk
    change (Over.homMk k : Over.mk (k ≫ X.hom) ⟶ X) ≫ f =
        (Over.homMk k : Over.mk (k ≫ X.hom) ⟶ X) ≫ g
    apply Over.OverMorphism.ext
    simpa using hk

/-- Helper for Lemma 7.29.3: the pushforward-covering criterion for `Over.post u` is exactly the
base dense-subsite criterion for `u` transported along the slice forgetful functors. -/
private theorem overPost_functorPushforward_mem_iff
    (u : C ⥤ D) [u.IsDenseSubsite J K] {U : C} {X : Over U} {S : Sieve X} :
    S.functorPushforward (Over.post u) ∈ K.over (u.obj U) ((Over.post u).obj X) ↔ S ∈ J.over U X := by
  -- After moving both slice sieves to the base categories, this is exactly the defining dense
  -- subsite equivalence for `u`.
  rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
    overEquiv_functorPushforward_post]
  exact Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J) (K := K) (G := u)

/-- Helper for Lemma 7.29.3: local faithfulness of `u` on the base site upgrades directly to local
faithfulness of `Over.post u` on the slice site. -/
private theorem overPost_equalizer_mem
    (u : C ⥤ D) [u.IsDenseSubsite J K] {U : C} {X Y : Over U}
    (a b : X ⟶ Y) (h : (Over.post u).map a = (Over.post u).map b) :
    Sieve.equalizer a b ∈ J.over U X := by
  -- Transport the slice equalizer sieve to the base, then apply local faithfulness for `u`.
  rw [GrothendieckTopology.mem_over_iff, overEquiv_equalizer]
  have hleft : u.map a.left = u.map b.left := by
    simpa using congrArg CommaMorphism.left h
  exact Functor.IsDenseSubsite.equalizer_mem J K u a.left b.left hleft

/-- Helper for Lemma 7.29.3: local fullness on the slice follows by first lifting the underlying
arrow in the base, then refining by a covering equalizer so the lift becomes a morphism over
`U`. -/
private theorem overPost_imageSieve_mem
    (u : C ⥤ D) [u.IsDenseSubsite J K] {U : C} {X Y : Over U}
    (c : (Over.post u).obj X ⟶ (Over.post u).obj Y) :
    (Over.post u).imageSieve c ∈ J.over U X := by
  rw [GrothendieckTopology.mem_over_iff]
  let R : Sieve X.left := Sieve.overEquiv X ((Over.post u).imageSieve c)
  have hT : u.imageSieve c.left ∈ J X.left := Functor.IsDenseSubsite.imageSieve_mem J K u c.left
  -- Start from the base image-sieve cover and refine it by equalizers forcing the lifted arrow to
  -- commute with the structure map to `U`.
  refine J.transitive hT R ?_
  intro Z g hg
  rcases hg with ⟨l, hl⟩
  have hEq : Sieve.equalizer (l ≫ Y.hom) (g ≫ X.hom) ∈ J Z := by
    apply Functor.IsDenseSubsite.equalizer_mem J K u (l ≫ Y.hom) (g ≫ X.hom)
    rw [Functor.map_comp, Functor.map_comp]
    calc
      u.map l ≫ u.map Y.hom = (u.map g ≫ c.left) ≫ u.map Y.hom := by
        simpa [Category.assoc] using congrArg (fun t ↦ t ≫ u.map Y.hom) hl
      _ = u.map g ≫ u.map X.hom := by
        simpa [Category.assoc] using congrArg (fun t ↦ u.map g ≫ t) (Over.w c)
  refine J.superset_covering ?_ hEq
  intro V p hp
  rw [Sieve.pullback_apply]
  rw [Sieve.overEquiv_iff]
  refine ⟨Over.homMk (p ≫ l) ?_, ?_⟩
  · simpa [Category.assoc] using hp
  · -- After restricting by the equalizer cover, the lifted arrow is genuinely a morphism over
    -- `U`, hence it lies in the slice image sieve.
    apply Over.OverMorphism.ext
    simpa [Category.assoc] using congrArg (fun t ↦ u.map p ≫ t) hl

/-- Helper for Lemma 7.29.3: the slice cover-by-image sieve is covering because every base
factorization through `u.obj W` can be refined by a cover on `W` whose lifted arrows land over
`U`. -/
private theorem coverByImage_mem_over_post
    (u : C ⥤ D) [u.IsDenseSubsite J K] {U : C}
    (Y : Over (u.obj U)) :
    Sieve.coverByImage (Over.post u) Y ∈ K.over (u.obj U) Y := by
  letI : u.IsCoverDense K := Functor.IsDenseSubsite.isCoverDense J K u
  rw [GrothendieckTopology.mem_over_iff]
  let R : Sieve Y.left := Sieve.overEquiv Y (Sieve.coverByImage (Over.post u) Y)
  have hT : Sieve.coverByImage u Y.left ∈ K Y.left := u.is_cover_of_isCoverDense K Y.left
  -- First cover `Y.left` by objects in the image of `u`, then use local fullness of `u` on the
  -- structure morphism to refine each such factorization into an actual slice factorization.
  refine K.transitive hT R ?_
  intro Z g hg
  rcases hg with ⟨⟨W, lift, map, fac⟩⟩
  let S : Sieve W := u.imageSieve (map ≫ Y.hom)
  have hS : S ∈ J W := Functor.IsDenseSubsite.imageSieve_mem J K u (map ≫ Y.hom)
  have hSu : S.functorPushforward u ∈ K (u.obj W) := by
    exact (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J) (K := K) (G := u)
      (X := W) (S := S)).2 hS
  have hPull : (S.functorPushforward u).pullback lift ∈ K Z := K.pullback_stable lift hSu
  refine K.superset_covering ?_ hPull
  intro V p hp
  rw [Sieve.pullback_apply] at hp
  rw [Sieve.pullback_apply]
  rw [Sieve.overEquiv_iff]
  rcases hp with ⟨W', a, b, ha, hfac⟩
  rcases ha with ⟨q, hq⟩
  refine ⟨⟨Over.mk q, Over.homMk b ?_, Over.homMk (u.map a ≫ map) ?_, ?_⟩⟩
  · change b ≫ u.map q = (p ≫ g) ≫ Y.hom
    calc
      b ≫ u.map q = (b ≫ u.map a) ≫ map ≫ Y.hom := by
        simpa [Category.assoc] using congrArg (fun t ↦ b ≫ t) hq
      _ = (p ≫ lift) ≫ map ≫ Y.hom := by rw [hfac]
      _ = (p ≫ g) ≫ Y.hom := by
        simpa [Category.assoc] using congrArg (fun t ↦ p ≫ t ≫ Y.hom) fac
  · change (u.map a ≫ map) ≫ Y.hom = u.map q
    simpa [Category.assoc] using hq.symm
  · -- The refined factorization is now represented by an honest object of `Over U`.
    apply Over.OverMorphism.ext
    change b ≫ (u.map a ≫ map) = p ≫ g
    calc
      b ≫ (u.map a ≫ map) = (b ≫ u.map a) ≫ map := by simp [Category.assoc]
      _ = (p ≫ lift) ≫ map := by rw [hfac]
      _ = p ≫ g := by simpa [Category.assoc] using congrArg (fun t ↦ p ≫ t) fac

/-- Lemma 7.29.3, source-facing owner layer: a dense-subsite functor remains a dense subsite
after passage to any slice site. -/
instance overPost_isDenseSubsite
    (u : C ⥤ D) (U : C) [u.IsDenseSubsite J K] :
    (Over.post u).IsDenseSubsite (J.over U) (K.over (u.obj U)) := by
  -- Route correction: the planned `sourceLocal_isDenseSubsite` bridge is not available, so we
  -- construct the dense-subsite owner directly from the slice versions of properties (3)–(5).
  refine
    { isCoverDense' := ?_
      isLocallyFull' := ?_
      isLocallyFaithful' := ?_
      functorPushforward_mem_iff := ?_ }
  · -- Property (5): the slice cover-by-image sieve is covering.
    exact ⟨fun Y ↦ coverByImage_mem_over_post (J := J) (K := K) u Y⟩
  · -- Property (4): source-local fullness upgrades to target-local fullness via the
    -- pushforward-covering criterion.
    exact
      ⟨fun c ↦ (overPost_functorPushforward_mem_iff (J := J) (K := K) u).2
        (overPost_imageSieve_mem (J := J) (K := K) u c)⟩
  · -- Property (3): source-local faithfulness upgrades in the same way.
    exact
      ⟨fun a b h ↦ (overPost_functorPushforward_mem_iff (J := J) (K := K) u).2
        (overPost_equalizer_mem (J := J) (K := K) u a b h)⟩
  · -- Property (2): coverings on the slice are exactly the coverings whose pushforward is a
    -- covering on the target slice.
    intro X S
    exact overPost_functorPushforward_mem_iff (J := J) (K := K) u

/- Lemma 7.29.3, bridge/view recall: once `overPost_isDenseSubsite` upgrades `Over.post u`
to the canonical dense-subsite owner on slice sites, the induced cocontinuous direct image
on sheaves of sets is an equivalence after supplying the needed pointwise right Kan extensions. -/
variable (u : C ⥤ D) (U : C) [u.IsDenseSubsite J K]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂),
  (Over.post u).op.HasPointwiseRightKanExtension P]

#synth
  ((Over.post u).sheafPushforwardCocontinuous (Type (max u₁ u₂ v₁ v₂)) (J.over U)
    (K.over (u.obj U))).IsEquivalence

end CategoryTheory
