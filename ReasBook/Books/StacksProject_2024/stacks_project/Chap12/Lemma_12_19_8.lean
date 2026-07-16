import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Category.ULift
import StacksProject_2024.stacks_project.Chap12.Lemma_12_19_7

open CategoryTheory
open CategoryTheory.Limits
open ModuleCat

attribute [local instance] uliftCategory

universe v u v₁ u₁

noncomputable section

namespace CategoryTheory
namespace FilteredObject.Hom

/-
Source/core/bridge triage for Lemma 12.19.8:
- source-facing: closure and non-closure properties of strict filtered morphisms under composition
- core/canonical owner: `FilteredObject.Hom.Strict`
- bridge/view: the mono/epi characterizations from Lemma `12.19.7`
-/

variable {C : Type u} [Category.{v} C] [HasImages C] [HasPullbacks C]
variable [HasEqualizers C]

private theorem imageSubobject_comp_eq_map_of_mono [Balanced C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    imageSubobject (f ≫ g) = (Subobject.map g).obj (imageSubobject f) := by
  calc
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
      rw [CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction f g]
    _ = Subobject.mk ((imageSubobject f).arrow ≫ g) := by
      simpa using (Limits.imageSubobject_mono ((imageSubobject f).arrow ≫ g))
    _ = (Subobject.map g).obj (Subobject.mk (imageSubobject f).arrow) := by
      rw [Subobject.map_mk]
    _ = (Subobject.map g).obj (imageSubobject f) := by
      rw [Subobject.mk_arrow]

private theorem imageSubobject_comp_eq_of_epi [Balanced C] {X Y Z : C}
    (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) = imageSubobject g := by
  calc
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
      rw [CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction f g]
    _ = imageSubobject (((⊤ : Subobject Y)).arrow ≫ g) := by
      simpa using congrArg (fun S : Subobject Y ↦ imageSubobject (S.arrow ≫ g))
        (Limits.imageSubobject_eq_top_of_epi f)
    _ = imageSubobject g := by
      simpa using
        (CategoryTheory.Limits.imageSubobject_iso_comp ((⊤ : Subobject Y).arrow) g)

/-- Helper for Lemma 12.19.8: the one-dimensional rational vector space used for the source and
target of the counterexample. -/
private abbrev counterexampleLineObject : ModuleCat ℚ :=
  ModuleCat.of ℚ ℚ

/-- Helper for Lemma 12.19.8: the two-dimensional rational vector space used for the middle term
of the counterexample. -/
private abbrev counterexamplePlaneObject : ModuleCat ℚ :=
  ModuleCat.of ℚ (ℚ × ℚ)

/-- Helper for Lemma 12.19.8: convert a submodule of the rational line into the corresponding
subobject. -/
private noncomputable abbrev lineSubobject (S : Submodule ℚ ℚ) :
    Subobject counterexampleLineObject :=
  (ModuleCat.subobjectModule counterexampleLineObject).symm S

/-- Helper for Lemma 12.19.8: convert a submodule of the rational plane into the corresponding
subobject. -/
private noncomputable abbrev planeSubobject (S : Submodule ℚ (ℚ × ℚ)) :
    Subobject counterexamplePlaneObject :=
  (ModuleCat.subobjectModule counterexamplePlaneObject).symm S

/-- Helper for Lemma 12.19.8: order comparison for subobjects of the rational line is inherited
from the corresponding submodule inclusion. -/
private theorem lineSubobject_mono {S T : Submodule ℚ ℚ} (hST : S ≤ T) :
    lineSubobject S ≤ lineSubobject T :=
  (ModuleCat.subobjectModule counterexampleLineObject).symm.monotone hST

/-- Helper for Lemma 12.19.8: order comparison for subobjects of the rational plane is inherited
from the corresponding submodule inclusion. -/
private theorem planeSubobject_mono {S T : Submodule ℚ (ℚ × ℚ)} (hST : S ≤ T) :
    planeSubobject S ≤ planeSubobject T :=
  (ModuleCat.subobjectModule counterexamplePlaneObject).symm.monotone hST

/-- Helper for Lemma 12.19.8: a top/bottom-valued submodule family attached to an antitone
predicate is itself antitone. -/
private theorem top_bot_submodule_filtration_antitone {M : Type _} [AddCommGroup M] [Module ℚ M]
    {P : ℤ → Prop} [DecidablePred P] (hP : Antitone P) :
    Antitone (fun i : ℤ ↦ if P i then (⊤ : Submodule ℚ M) else ⊥) := by
  -- A later index stays inside the same branch or drops from `⊤` to `⊥`.
  intro i j hij
  by_cases hj : P j
  · simp [hj, hP hij hj]
  · simp [hj]

/-- Helper for Lemma 12.19.8: the first-axis submodule `ℚ × 0 ⊆ ℚ²`. -/
private abbrev first_axis_submodule : Submodule ℚ (ℚ × ℚ) :=
  LinearMap.ker (LinearMap.snd ℚ ℚ ℚ)

/-- Helper for Lemma 12.19.8: the first-axis subobject of the rational plane. -/
private noncomputable abbrev first_axis_subobject :
    Subobject counterexamplePlaneObject :=
  planeSubobject first_axis_submodule

/-- Helper for Lemma 12.19.8: the middle filtration stage family on `ℚ²`, equal to `⊤` for
negative indices, the first axis in degree `0`, and `⊥` for positive indices. -/
private def plane_counterexample_stage (i : ℤ) : Submodule ℚ (ℚ × ℚ) :=
  if i < 0 then ⊤ else if i = 0 then first_axis_submodule else ⊥

/-- Helper for Lemma 12.19.8: the middle filtration family on `ℚ²` is decreasing. -/
private theorem plane_counterexample_filtration_antitone :
    Antitone plane_counterexample_stage := by
  -- The only nontrivial transition is from the negative stage `⊤` down to the degree-zero first
  -- axis; after degree zero the family is already `⊥`.
  intro i j hij
  by_cases hjneg : j < 0
  · have hineg : i < 0 := lt_of_le_of_lt hij hjneg
    simp [plane_counterexample_stage, hjneg, hineg]
  · by_cases hj0 : j = 0
    · by_cases hineg : i < 0
      · simp [plane_counterexample_stage, hj0, hineg]
      · have hi0 : i = 0 := by
          exact le_antisymm (hj0 ▸ hij) (le_of_not_gt hineg)
        simp [plane_counterexample_stage, hj0, hi0]
    · have hjpos : 0 < j := lt_of_le_of_ne (le_of_not_gt hjneg) (Ne.symm hj0)
      simp [plane_counterexample_stage, hjneg, hj0]

/-- Helper for Lemma 12.19.8: the diagonal linear map `x ↦ (x,x)`. -/
private def counterexample_diagonal_linear : ℚ →ₗ[ℚ] (ℚ × ℚ) :=
  LinearMap.prod (LinearMap.id) (LinearMap.id)

/-- Helper for Lemma 12.19.8: the first projection `(x,y) ↦ x`. -/
private def counterexample_fst_linear : (ℚ × ℚ) →ₗ[ℚ] ℚ :=
  LinearMap.fst ℚ ℚ ℚ

/-- Helper for Lemma 12.19.8: the strict source filtration on the rational line, equal to `⊤`
in negative degrees and `⊥` from degree `0` onward. -/
private theorem counterexample_source_filtration_mono :
    Monotone
      (fun p : OrderDual ℤ ↦
        lineSubobject
          (if OrderDual.ofDual p < 0 then (⊤ : Submodule ℚ ℚ) else ⊥)) := by
  -- Reindex the antitone family on `ℤ` as a monotone family on `OrderDual ℤ`.
  intro p q hpq
  exact lineSubobject_mono <|
    top_bot_submodule_filtration_antitone (M := ℚ) (fun _ _ hij ↦ lt_of_le_of_lt hij) hpq

/-- Helper for Lemma 12.19.8: the source filtered object `A` in the counterexample. -/
private def counterexampleSource : FilteredObject (ModuleCat ℚ) :=
  { obj := counterexampleLineObject
    filtration :=
      { toFun := fun p ↦
          lineSubobject
            (if OrderDual.ofDual p < 0 then (⊤ : Submodule ℚ ℚ) else ⊥)
        monotone' := counterexample_source_filtration_mono } }

/-- Helper for Lemma 12.19.8: the middle filtration on `ℚ²`, equal to `⊤` in negative degrees,
the first axis in degree `0`, and `⊥` in positive degrees. -/
private theorem counterexample_middle_filtration_mono :
    Monotone (fun p : OrderDual ℤ ↦ planeSubobject (plane_counterexample_stage (OrderDual.ofDual p))) := by
  -- This is the `OrderDual` repackaging of the stagewise antitone family above.
  intro p q hpq
  exact planeSubobject_mono <| plane_counterexample_filtration_antitone hpq

/-- Helper for Lemma 12.19.8: the middle filtered object `B` in the counterexample. -/
private def counterexampleMiddle : FilteredObject (ModuleCat ℚ) :=
  { obj := counterexamplePlaneObject
    filtration :=
      { toFun := fun p ↦ planeSubobject (plane_counterexample_stage (OrderDual.ofDual p))
        monotone' := counterexample_middle_filtration_mono } }

/-- Helper for Lemma 12.19.8: the looser target filtration on the rational line, equal to `⊤`
through degree `0` and `⊥` afterwards. -/
private theorem counterexample_target_filtration_mono :
    Monotone
      (fun p : OrderDual ℤ ↦
        lineSubobject
          (if OrderDual.ofDual p ≤ 0 then (⊤ : Submodule ℚ ℚ) else ⊥)) := by
  -- Reindex the nonpositive top/bottom family as a decreasing filtration.
  intro p q hpq
  exact lineSubobject_mono <|
    top_bot_submodule_filtration_antitone (M := ℚ) (fun _ _ hij ↦ le_trans hij) hpq

/-- Helper for Lemma 12.19.8: the target filtered object `C` in the counterexample. -/
private def counterexampleTarget : FilteredObject (ModuleCat ℚ) :=
  { obj := counterexampleLineObject
    filtration :=
      { toFun := fun p ↦
          lineSubobject
            (if OrderDual.ofDual p ≤ 0 then (⊤ : Submodule ℚ ℚ) else ⊥)
        monotone' := counterexample_target_filtration_mono } }

/-- Helper for Lemma 12.19.8: the source filtration is zero in degree `0`. -/
private theorem counterexampleSource_filtration_zero :
    counterexampleSource.filtration 0 = (⊥ : Subobject counterexampleLineObject) := by
  -- Degree `0` is the cutoff where the source filtration drops to zero.
  change lineSubobject (if (0 : ℤ) < 0 then (⊤ : Submodule ℚ ℚ) else ⊥) = ⊥
  simp [lineSubobject]

/-- Helper for Lemma 12.19.8: the middle filtration is the first axis in degree `0`. -/
private theorem counterexampleMiddle_filtration_zero :
    counterexampleMiddle.filtration 0 = first_axis_subobject := by
  -- Degree `0` is the unique nontrivial intermediate stage.
  change planeSubobject (plane_counterexample_stage 0) = first_axis_subobject
  simp [plane_counterexample_stage, first_axis_subobject]

/-- Helper for Lemma 12.19.8: the target filtration is the whole line in degree `0`. -/
private theorem counterexampleTarget_filtration_zero :
    counterexampleTarget.filtration 0 = (⊤ : Subobject counterexampleLineObject) := by
  -- The target keeps the whole line at degree `0`.
  change lineSubobject (if (0 : ℤ) ≤ 0 then (⊤ : Submodule ℚ ℚ) else ⊥) = ⊤
  simp [lineSubobject]

/-- Helper for Lemma 12.19.8: the diagonal meets the first axis only at the origin, so the
pullback of the first-axis stage along the diagonal is zero. -/
private theorem diagonal_comap_first_axis_eq_bot :
    Submodule.comap counterexample_diagonal_linear first_axis_submodule = ⊥ := by
  -- Membership in the pullback means `(x,x)` lies on the first axis, hence `x = 0`.
  ext x
  constructor
  · intro hx
    have hx0 : x = 0 := by
      simpa [Submodule.mem_comap, first_axis_submodule, counterexample_diagonal_linear] using hx
    simpa [hx0]
  · intro hx
    simpa [Submodule.mem_comap, first_axis_submodule, counterexample_diagonal_linear] using hx

/-- Helper for Lemma 12.19.8: the first projection maps the first axis onto the whole line. -/
private theorem fst_map_first_axis_eq_top :
    Submodule.map counterexample_fst_linear first_axis_submodule = ⊤ := by
  -- Every line element is the first coordinate of a point on the first axis.
  ext x
  constructor
  · intro hx
    simp at hx
    simp
  · intro _
    refine Submodule.mem_map.2 ?_
    refine ⟨(x, 0), ?_, by simp [counterexample_fst_linear]⟩
    simp [first_axis_submodule]

/-- Helper for Lemma 12.19.8: in `ModuleCat`, the categorical image subobject of a morphism is
the linear-algebraic range of its underlying map. -/
private theorem subobjectModule_imageSubobject
    {X Y : ModuleCat ℚ} (f : X ⟶ Y) :
    ModuleCat.subobjectModule Y (imageSubobject f) = LinearMap.range f.hom := by
  -- Compare the categorical image factorization with the explicit range factorization for
  -- modules, then transport the result through `ModuleCat.subobjectModule`.
  have himage :
      imageSubobject f = Subobject.mk (ModuleCat.ofHom (LinearMap.range f.hom).subtype) := by
    exact CategoryTheory.Subobject.eq_mk_of_comm
      (ModuleCat.ofHom (LinearMap.range f.hom).subtype)
      ((imageSubobjectIso f).trans (ModuleCat.imageIsoRange f))
      (by simp [Category.assoc])
  rw [himage]
  exact (ModuleCat.subobjectModule Y).right_inv (LinearMap.range f.hom)

/-- Helper for Lemma 12.19.8: the diagonal linear map is injective. -/
private theorem counterexample_diagonal_injective :
    Function.Injective counterexample_diagonal_linear := by
  -- Equality of diagonal images is equality of their first coordinates.
  intro x y hxy
  have hfst := congrArg (fun z : ℚ × ℚ ↦ z.1) hxy
  simpa [counterexample_diagonal_linear] using hfst

/-- Helper for Lemma 12.19.8: the first projection is surjective. -/
private theorem counterexample_fst_surjective :
    Function.Surjective counterexample_fst_linear := by
  -- Every rational number is the first coordinate of `(x,0)`.
  intro x
  refine ⟨(x, 0), by simp [counterexample_fst_linear]⟩

/-- Helper for Lemma 12.19.8: the diagonal map preserves the chosen filtrations. -/
private theorem counterexampleDiagonal_preserves (i : ℤ) :
    (counterexampleMiddle.filtration i).Factors
      ((counterexampleSource.filtration i).arrow ≫ ModuleCat.ofHom counterexample_diagonal_linear) :=
by
  by_cases hi : i < 0
  · -- In negative degrees the middle stage is `⊤`, so every morphism factors through it.
    have hmiddle :
        counterexampleMiddle.filtration i = (⊤ : Subobject counterexamplePlaneObject) := by
      change planeSubobject (plane_counterexample_stage i) = ⊤
      simp [plane_counterexample_stage, hi, planeSubobject]
    simpa [hmiddle] using
      (Subobject.top_factors
        ((counterexampleSource.filtration i).arrow ≫ ModuleCat.ofHom counterexample_diagonal_linear))
  · -- From degree `0` onward the source stage is `⊥`, so the stage map is zero.
    have hsource :
        counterexampleSource.filtration i = (⊥ : Subobject counterexampleLineObject) := by
      change lineSubobject (if i < 0 then (⊤ : Submodule ℚ ℚ) else ⊥) = ⊥
      simp [hi, lineSubobject]
    rw [hsource]
    have hcomp :
        (((⊥ : Subobject counterexampleLineObject).arrow :
            ((⊥ : Subobject counterexampleLineObject) : ModuleCat ℚ) ⟶ counterexampleLineObject) ≫
          ModuleCat.ofHom counterexample_diagonal_linear) = 0 := by
      simp
    exact hcomp.symm ▸
      (Subobject.factors_zero :
        (counterexampleMiddle.filtration i).Factors
          (0 : ((⊥ : Subobject counterexampleLineObject) : ModuleCat ℚ) ⟶
            counterexamplePlaneObject))

/-- Helper for Lemma 12.19.8: the diagonal filtered morphism `A ⟶ B`. -/
private def counterexampleDiagonal : counterexampleSource ⟶ counterexampleMiddle where
  hom := ModuleCat.ofHom counterexample_diagonal_linear
  preserves := counterexampleDiagonal_preserves

/-- Helper for Lemma 12.19.8: the diagonal filtered morphism has mono underlying map. -/
private instance : Mono counterexampleDiagonal.hom :=
  (ModuleCat.mono_iff_injective _).2 counterexample_diagonal_injective

/-- Helper for Lemma 12.19.8: at degree `0`, pulling back the first-axis stage along the diagonal
recovers the zero subobject of the source line. -/
private theorem diagonal_pullback_first_axis_eq_bot :
    (Subobject.pullback counterexampleDiagonal.hom).obj first_axis_subobject =
      (⊥ : Subobject counterexampleLineObject) := by
  -- Route correction: compute the concrete pullback object for this witness instead of adding a
  -- generic `ModuleCat.subobjectModule` bridge.
  rw [Subobject.pullback_obj]
  apply (Subobject.mk_eq_bot_iff_zero).2
  refine ModuleCat.hom_ext ?_
  ext z
  -- The pullback condition says the diagonal image equals a point on the first axis, so its
  -- second coordinate vanishes.
  have hcond :
      first_axis_subobject.arrow.hom ((pullback.fst first_axis_subobject.arrow counterexampleDiagonal.hom).hom z) =
        counterexampleDiagonal.hom.hom
          ((pullback.snd first_axis_subobject.arrow counterexampleDiagonal.hom).hom z) := by
    exact LinearMap.congr_fun
      (ModuleCat.hom_ext_iff.mp
        (show pullback.fst first_axis_subobject.arrow counterexampleDiagonal.hom ≫
            first_axis_subobject.arrow =
            pullback.snd first_axis_subobject.arrow counterexampleDiagonal.hom ≫
              counterexampleDiagonal.hom from pullback.condition)) z
  have hz0 :
      ((pullback.snd first_axis_subobject.arrow counterexampleDiagonal.hom).hom z : ℚ) = 0 := by
    have hz := congrArg (fun w : ℚ × ℚ ↦ w.2) hcond
    have hdiag :
        ((pullback.snd first_axis_subobject.arrow counterexampleDiagonal.hom).hom z : ℚ) =
          (first_axis_subobject.arrow.hom
              ((pullback.fst first_axis_subobject.arrow counterexampleDiagonal.hom).hom z)).2 := by
      simpa [counterexampleDiagonal, counterexample_diagonal_linear] using hz.symm
    have hrange :
        LinearMap.range first_axis_subobject.arrow.hom = first_axis_submodule := by
      calc
        LinearMap.range first_axis_subobject.arrow.hom =
            ModuleCat.subobjectModule counterexamplePlaneObject
              (imageSubobject first_axis_subobject.arrow) := by
                symm
                exact subobjectModule_imageSubobject (f := first_axis_subobject.arrow)
        _ = ModuleCat.subobjectModule counterexamplePlaneObject first_axis_subobject := by
              rw [Limits.imageSubobject_mono first_axis_subobject.arrow]
              rw [Subobject.mk_arrow]
        _ = first_axis_submodule := by
              simp [first_axis_subobject, planeSubobject]
    have haxis :
        (first_axis_subobject.arrow.hom
            ((pullback.fst first_axis_subobject.arrow counterexampleDiagonal.hom).hom z)).2 = 0 := by
      have hmem :
          first_axis_subobject.arrow.hom
              ((pullback.fst first_axis_subobject.arrow counterexampleDiagonal.hom).hom z) ∈
            first_axis_submodule := by
        rw [← hrange]
        exact LinearMap.mem_range_self _ _
      simpa [first_axis_submodule] using hmem
    calc
      ((pullback.snd first_axis_subobject.arrow counterexampleDiagonal.hom).hom z : ℚ) =
          (first_axis_subobject.arrow.hom
              ((pullback.fst first_axis_subobject.arrow counterexampleDiagonal.hom).hom z)).2 := hdiag
      _ = 0 := haxis
  simpa [hz0]

/-- Helper for Lemma 12.19.8: the first projection preserves the chosen filtrations. -/
private theorem counterexampleFst_preserves (i : ℤ) :
    (counterexampleTarget.filtration i).Factors
      ((counterexampleMiddle.filtration i).arrow ≫ ModuleCat.ofHom counterexample_fst_linear) :=
by
  by_cases hi : i ≤ 0
  · -- Up through degree `0`, the target stage is `⊤`, so the stage map factors tautologically.
    have htarget :
        counterexampleTarget.filtration i = (⊤ : Subobject counterexampleLineObject) := by
      change lineSubobject (if i ≤ 0 then (⊤ : Submodule ℚ ℚ) else ⊥) = ⊤
      simp [hi, lineSubobject]
    simpa [htarget] using
      (Subobject.top_factors
        ((counterexampleMiddle.filtration i).arrow ≫ ModuleCat.ofHom counterexample_fst_linear))
  · -- In positive degrees the middle stage is `⊥`, so the induced stage map is zero.
    have hpos : 0 < i := lt_of_not_ge hi
    have hmiddle :
        counterexampleMiddle.filtration i = (⊥ : Subobject counterexamplePlaneObject) := by
      change planeSubobject (plane_counterexample_stage i) = ⊥
      simp [plane_counterexample_stage, not_lt.mpr (le_of_lt hpos), ne_of_gt hpos, planeSubobject]
    rw [hmiddle]
    have hcomp :
        (((⊥ : Subobject counterexamplePlaneObject).arrow :
            ((⊥ : Subobject counterexamplePlaneObject) : ModuleCat ℚ) ⟶ counterexamplePlaneObject) ≫
          ModuleCat.ofHom counterexample_fst_linear) = 0 := by
      simp
    exact hcomp.symm ▸
      (Subobject.factors_zero :
        (counterexampleTarget.filtration i).Factors
          (0 : ((⊥ : Subobject counterexamplePlaneObject) : ModuleCat ℚ) ⟶
            counterexampleLineObject))

/-- Helper for Lemma 12.19.8: the projection filtered morphism `B ⟶ C`. -/
private def counterexampleFst : counterexampleMiddle ⟶ counterexampleTarget where
  hom := ModuleCat.ofHom counterexample_fst_linear
  preserves := counterexampleFst_preserves

/-- Helper for Lemma 12.19.8: the projection filtered morphism has epi underlying map. -/
private instance : Epi counterexampleFst.hom :=
  (ModuleCat.epi_iff_surjective _).2 counterexample_fst_surjective

/-- Helper for Lemma 12.19.8: at degree `0`, the image of the first-axis stage under the first
projection is the whole target line. -/
private theorem first_axis_image_under_fst_eq_top :
    imageSubobject (first_axis_subobject.arrow ≫ counterexampleFst.hom) =
      (⊤ : Subobject counterexampleLineObject) := by
  -- Transport the categorical image to a range computation and then reuse the linear-algebra
  -- surjectivity calculation on the first axis.
  apply (ModuleCat.subobjectModule counterexampleLineObject).injective
  have htop :
      ModuleCat.subobjectModule counterexampleLineObject
          (⊤ : Subobject counterexampleLineObject) =
        (⊤ : Submodule ℚ ℚ) := by
    simpa [lineSubobject] using
      ((ModuleCat.subobjectModule counterexampleLineObject).left_inv (⊤ : Submodule ℚ ℚ))
  rw [htop]
  change ModuleCat.subobjectModule counterexampleLineObject
      (imageSubobject (first_axis_subobject.arrow ≫ counterexampleFst.hom)) =
    (⊤ : Submodule ℚ ℚ)
  rw [subobjectModule_imageSubobject]
  change LinearMap.range (counterexample_fst_linear.comp first_axis_subobject.arrow.hom) = ⊤
  rw [LinearMap.range_comp]
  have hrange :
      LinearMap.range first_axis_subobject.arrow.hom = first_axis_submodule := by
    calc
      LinearMap.range first_axis_subobject.arrow.hom =
          ModuleCat.subobjectModule counterexamplePlaneObject
            (imageSubobject first_axis_subobject.arrow) := by
              symm
              exact subobjectModule_imageSubobject (f := first_axis_subobject.arrow)
      _ = ModuleCat.subobjectModule counterexamplePlaneObject first_axis_subobject := by
            rw [Limits.imageSubobject_mono first_axis_subobject.arrow]
            rw [Subobject.mk_arrow]
      _ = first_axis_submodule := by
            simp [first_axis_subobject, planeSubobject]
  rw [hrange]
  simpa [first_axis_subobject, planeSubobject, counterexampleFst] using fst_map_first_axis_eq_top

/-- Helper for Lemma 12.19.8: the diagonal filtered morphism is strict. -/
private theorem strict_counterexampleDiagonal :
    Strict counterexampleDiagonal :=
by
  -- The source proof uses the induced-filtration characterization for a mono and then checks the
  -- three stage shapes: `⊤`, the degree-zero pullback, and `⊥`.
  refine (strict_iff_induced_filtration_of_mono counterexampleDiagonal).2 ?_
  refine OrderHom.ext _ _ ?_
  funext p
  change
    lineSubobject
        (if OrderDual.ofDual p < 0 then (⊤ : Submodule ℚ ℚ) else ⊥) =
      (Subobject.pullback counterexampleDiagonal.hom).obj
        (planeSubobject (plane_counterexample_stage (OrderDual.ofDual p)))
  by_cases hi_neg : OrderDual.ofDual p < 0
  · -- In negative degrees both filtrations are the whole line.
    rw [show
        lineSubobject
            (if OrderDual.ofDual p < 0 then (⊤ : Submodule ℚ ℚ) else ⊥) =
          (⊤ : Subobject counterexampleLineObject) by
            simp [hi_neg, lineSubobject]]
    rw [show
        planeSubobject (plane_counterexample_stage (OrderDual.ofDual p)) =
          (⊤ : Subobject counterexamplePlaneObject) by
            simp [plane_counterexample_stage, hi_neg, planeSubobject]]
    simpa using (Subobject.pullback_top counterexampleDiagonal.hom).symm
  · by_cases hi_zero : OrderDual.ofDual p = 0
    · -- Degree `0` is the single nontrivial stage, computed by the concrete pullback lemma above.
      rw [show
          lineSubobject
              (if OrderDual.ofDual p < 0 then (⊤ : Submodule ℚ ℚ) else ⊥) =
            (⊥ : Subobject counterexampleLineObject) by
              simp [hi_neg, lineSubobject]]
      rw [show
          planeSubobject (plane_counterexample_stage (OrderDual.ofDual p)) =
            first_axis_subobject by
              simp [plane_counterexample_stage, hi_neg, hi_zero, first_axis_subobject,
                planeSubobject]]
      simpa using diagonal_pullback_first_axis_eq_bot.symm
    · -- In positive degrees the middle stage is `⊥`, and pulling it back stays `⊥`.
      have hpullback_bot :
          (Subobject.pullback counterexampleDiagonal.hom).obj
              (⊥ : Subobject counterexamplePlaneObject) =
            (⊥ : Subobject counterexampleLineObject) := by
        rw [Subobject.pullback_obj]
        apply (Subobject.mk_eq_bot_iff_zero).2
        refine ModuleCat.hom_ext ?_
        ext z
        have hcond :
            ((⊥ : Subobject counterexamplePlaneObject).arrow.hom)
                ((pullback.fst ((⊥ : Subobject counterexamplePlaneObject).arrow)
                    counterexampleDiagonal.hom).hom z) =
              counterexampleDiagonal.hom.hom
                ((pullback.snd ((⊥ : Subobject counterexamplePlaneObject).arrow)
                    counterexampleDiagonal.hom).hom z) := by
          exact LinearMap.congr_fun
            (ModuleCat.hom_ext_iff.mp
              (show pullback.fst ((⊥ : Subobject counterexamplePlaneObject).arrow)
                    counterexampleDiagonal.hom ≫
                  (⊥ : Subobject counterexamplePlaneObject).arrow =
                  pullback.snd ((⊥ : Subobject counterexamplePlaneObject).arrow)
                    counterexampleDiagonal.hom ≫ counterexampleDiagonal.hom from pullback.condition)) z
        have hz := congrArg (fun w : ℚ × ℚ ↦ w.1) hcond
        simpa [counterexampleDiagonal, counterexample_diagonal_linear] using hz.symm
      rw [show
          lineSubobject
              (if OrderDual.ofDual p < 0 then (⊤ : Submodule ℚ ℚ) else ⊥) =
            (⊥ : Subobject counterexampleLineObject) by
              simp [hi_neg, lineSubobject]]
      rw [show
          planeSubobject (plane_counterexample_stage (OrderDual.ofDual p)) =
            (⊥ : Subobject counterexamplePlaneObject) by
              simp [plane_counterexample_stage, hi_neg, hi_zero, planeSubobject]]
      simpa using hpullback_bot.symm

/-- Helper for Lemma 12.19.8: the first projection filtered morphism is strict. -/
private theorem strict_counterexampleFst :
    Strict counterexampleFst :=
by
  -- The source proof uses the quotient-filtration characterization for an epi and again splits
  -- into the negative, zero, and positive stage shapes.
  refine (strict_iff_quotient_filtration_of_epi counterexampleFst).2 ?_
  refine OrderHom.ext _ _ ?_
  funext p
  by_cases hi_neg : OrderDual.ofDual p < 0
  · -- In negative degrees the source stage is `⊤`, so the quotient stage is the full image.
    have himage_top :
        imageSubobject (((⊤ : Subobject counterexamplePlaneObject).arrow) ≫ counterexampleFst.hom) =
          (⊤ : Subobject counterexampleLineObject) := by
      rw [imageSubobject_comp_eq_of_epi ((⊤ : Subobject counterexamplePlaneObject).arrow) counterexampleFst.hom]
      simpa using (Limits.imageSubobject_eq_top_of_epi counterexampleFst.hom)
    rw [show
          counterexampleTarget.filtration p =
            (⊤ : Subobject counterexampleLineObject) by
            change lineSubobject
                (if OrderDual.ofDual p ≤ 0 then (⊤ : Submodule ℚ ℚ) else ⊥) =
              (⊤ : Subobject counterexampleLineObject)
            simp [le_of_lt hi_neg, lineSubobject]]
    rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    rw [show
          counterexampleMiddle.filtration p =
            (⊤ : Subobject counterexamplePlaneObject) by
            change planeSubobject (plane_counterexample_stage (OrderDual.ofDual p)) =
              (⊤ : Subobject counterexamplePlaneObject)
            simp [plane_counterexample_stage, hi_neg, planeSubobject]]
    simpa using himage_top.symm
  · by_cases hi_zero : OrderDual.ofDual p = 0
    · -- Degree `0` is exactly the first-axis image computation.
      rw [show
            counterexampleTarget.filtration p =
              (⊤ : Subobject counterexampleLineObject) by
              change lineSubobject
                  (if OrderDual.ofDual p ≤ 0 then (⊤ : Submodule ℚ ℚ) else ⊥) =
                (⊤ : Subobject counterexampleLineObject)
              simp [hi_zero, lineSubobject]]
      rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
      rw [show
            counterexampleMiddle.filtration p = first_axis_subobject by
              change planeSubobject (plane_counterexample_stage (OrderDual.ofDual p)) =
                first_axis_subobject
              simp [plane_counterexample_stage, hi_neg, hi_zero, first_axis_subobject,
                planeSubobject]]
      simpa using first_axis_image_under_fst_eq_top.symm
    · -- In positive degrees the source stage is `⊥`, hence its image quotient stage is also `⊥`.
      have hpos : 0 < OrderDual.ofDual p := lt_of_le_of_ne (le_of_not_gt hi_neg) (Ne.symm hi_zero)
      have hcomp :
          (((⊥ : Subobject counterexamplePlaneObject).arrow :
              ((⊥ : Subobject counterexamplePlaneObject) : ModuleCat ℚ) ⟶ counterexamplePlaneObject) ≫
            counterexampleFst.hom) = 0 := by
        simp
      have himage_bot :
          imageSubobject
              ((((⊥ : Subobject counterexamplePlaneObject).arrow :
                  ((⊥ : Subobject counterexamplePlaneObject) : ModuleCat ℚ) ⟶
                    counterexamplePlaneObject) ≫ counterexampleFst.hom)) =
            (⊥ : Subobject counterexampleLineObject) := by
        rw [hcomp]
        exact (Limits.imageSubobject_zero :
          imageSubobject
              (0 : ((⊥ : Subobject counterexamplePlaneObject) : ModuleCat ℚ) ⟶
                counterexampleLineObject) =
            (⊥ : Subobject counterexampleLineObject))
      rw [show
            counterexampleTarget.filtration p =
              (⊥ : Subobject counterexampleLineObject) by
              change lineSubobject
                  (if OrderDual.ofDual p ≤ 0 then (⊤ : Submodule ℚ ℚ) else ⊥) =
                (⊥ : Subobject counterexampleLineObject)
              simp [not_le.mpr hpos, lineSubobject]]
      rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
      rw [show
            counterexampleMiddle.filtration p =
              (⊥ : Subobject counterexamplePlaneObject) by
              change planeSubobject (plane_counterexample_stage (OrderDual.ofDual p)) =
                (⊥ : Subobject counterexamplePlaneObject)
              simp [plane_counterexample_stage, hi_neg, hi_zero, planeSubobject]]
      exact himage_bot.symm

/-- Helper for Lemma 12.19.8: on the underlying rational line, the composite of the diagonal and
the first projection is the identity. -/
private theorem counterexample_comp_hom :
    counterexampleDiagonal.hom ≫ counterexampleFst.hom = 𝟙 counterexampleLineObject :=
by
  -- Evaluate the composite on an arbitrary rational number; it returns the first coordinate of
  -- `(x,x)`, hence `x`.
  rfl

/-- Helper for Lemma 12.19.8: the universe-adjusted coefficient field used for the corrected
counterexample packaging. -/
private abbrev counterexampleField : Type :=
  ℚ

/-- Helper for Lemma 12.19.8: the small source category for the corrected universe-exact route is
the finitely generated module representation model over `ℚ`. -/
private abbrev counterexampleSmallSource : Type :=
  FGModuleRepr counterexampleField

/-- Helper for Lemma 12.19.8: the final ambient category first lifts objects and then lifts the
hom-universe, so its universes match the target theorem exactly. -/
private abbrev counterexampleAmbient : Type u₁ :=
  ULiftHom.{v₁} (ULift.{u₁} counterexampleSmallSource)

/-- Helper for Lemma 12.19.8: the small source category really is a small category, so the
combined object/hom lift has morphisms in universe `v₁`. -/
private instance counterexampleSmallSource_smallCategory :
    SmallCategory counterexampleSmallSource :=
  inferInstance

/-- Helper for Lemma 12.19.8: the small finitely generated-module model inherits its additive
structure from `FGModuleCat`. -/
private noncomputable instance counterexampleSmallSource_preadditive :
    Preadditive counterexampleSmallSource :=
  CategoryTheory.Preadditive.ofFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful (FGModuleRepr.embed.{0, 0} counterexampleField))

/-- Helper for Lemma 12.19.8: the small source category carries zero morphisms, as required by the
exact-universe transport functor. -/
private noncomputable instance counterexampleSmallSource_hasZeroMorphisms :
    HasZeroMorphisms counterexampleSmallSource :=
  inferInstance

/-- Helper for Lemma 12.19.8: pin the ambient category to hom-universe `v₁` after the combined
object and hom lift. -/
private instance counterexampleAmbient_category :
    Category.{v₁} counterexampleAmbient :=
  inferInstance

/-- Helper for Lemma 12.19.8: after the final `ULiftHom` hom-universe adjustment, the ambient
category is still preadditive. -/
private noncomputable instance counterexampleAmbient_preadditive :
    Preadditive counterexampleAmbient :=
  sorry

/-- Helper for Lemma 12.19.8: the exact-universe ambient category carries zero morphisms. -/
private noncomputable instance counterexampleAmbient_hasZeroMorphisms :
    HasZeroMorphisms counterexampleAmbient :=
  inferInstance

/-- Helper for Lemma 12.19.8: the explicit small finitely generated-module model is equivalent to
the usual finitely generated module category. -/
private noncomputable def fgReprEquiv :
    counterexampleSmallSource ≌ FGModuleCat.{0} counterexampleField :=
  (FGModuleRepr.embed.{0, 0} counterexampleField).asEquivalence

/-- Helper for Lemma 12.19.8: the exact-universe ambient category is equivalent to the small
source category via the combined object and hom lift. -/
private noncomputable def ambientEquiv :
    counterexampleSmallSource ≌ counterexampleAmbient :=
  ULiftHomULiftCategory.equiv.{v₁, u₁, 0, 0} counterexampleSmallSource

/-- Helper for Lemma 12.19.8: the universe-corrected ambient functor sends the small witness into
the final category used in the negated-universal theorem. -/
private noncomputable def counterexampleAmbientUp :
    counterexampleSmallSource ⥤ counterexampleAmbient :=
  -- TODO: replan route should pin down the exact `ULiftHom (ULift _)` equivalence functor with
  -- universe parameters that elaborate without metas in downstream ambient morphisms.
  sorry

/-- Helper for Lemma 12.19.8: the exact-universe ambient functor preserves zero morphisms, which
is the transport fact needed for the ambient split-identity rewrites. -/
private noncomputable instance counterexampleAmbientUp_preservesZeroMorphisms :
    counterexampleAmbientUp.PreservesZeroMorphisms :=
  -- TODO: after the ambient functor is stabilized, this should follow by a direct `map_zero`
  -- calculation for the `ULift`/`ULiftHom` transport.
  sorry

/-- Helper for Lemma 12.19.8: the small finitely generated-module model has the finite limits
needed to talk about strict morphisms. -/
private noncomputable instance counterexampleSmallSource_hasFiniteLimits :
    HasFiniteLimits counterexampleSmallSource where
  out := fun J _ _ ↦ by
    -- Transfer each finite diagram limit across the explicit equivalence with `FGModuleCat`.
    exact Adjunction.hasLimitsOfShape_of_equivalence fgReprEquiv.functor

/-- Helper for Lemma 12.19.8: the small finitely generated-module model is abelian. -/
private noncomputable instance counterexampleSmallSource_abelian :
    Abelian counterexampleSmallSource :=
  abelianOfEquivalence fgReprEquiv.functor

/-- Helper for Lemma 12.19.8: the final ambient category keeps the finite limits required by the
strictness API. -/
private noncomputable instance counterexampleAmbient_hasFiniteLimits :
    HasFiniteLimits counterexampleAmbient where
  out := fun J _ _ ↦ by
    -- Transfer finite limits from the small source back along the equivalence inverse.
    exact Adjunction.hasLimitsOfShape_of_equivalence ambientEquiv.inverse

/-- Helper for Lemma 12.19.8: the final universe-exact ambient category is abelian. -/
private noncomputable instance counterexampleAmbient_abelian :
    Abelian counterexampleAmbient :=
  abelianOfEquivalence ambientEquiv.inverse

/-- Helper for Lemma 12.19.8: the small line object in the finitely generated-module
representation model. -/
private abbrev small_counterexample_line_object : counterexampleSmallSource :=
  FGModuleRepr.ofFinite counterexampleField ℚ

/-- Helper for Lemma 12.19.8: the small plane object in the finitely generated-module
representation model. -/
private abbrev small_counterexample_plane_object : counterexampleSmallSource :=
  FGModuleRepr.ofFinite counterexampleField (ℚ × ℚ)

/-- Helper for Lemma 12.19.8: the small line representation identifies with the literal line over
`counterexampleField`. -/
private noncomputable abbrev small_counterexample_line_equiv :
    small_counterexample_line_object ≃ₗ[counterexampleField] ℚ :=
  FGModuleRepr.ofFiniteEquiv counterexampleField ℚ

/-- Helper for Lemma 12.19.8: the small plane representation identifies with the literal plane
over `counterexampleField`. -/
private noncomputable abbrev small_counterexample_plane_equiv :
    small_counterexample_plane_object ≃ₗ[counterexampleField]
      (ℚ × ℚ) :=
  FGModuleRepr.ofFiniteEquiv counterexampleField (ℚ × ℚ)

/-- Helper for Lemma 12.19.8: the diagonal map on the small witness is the conjugate of
`x ↦ (x,x)` under the chosen representation equivalences. -/
private def small_counterexample_diagonal_linear :
    small_counterexample_line_object →ₗ[counterexampleField]
      small_counterexample_plane_object :=
  small_counterexample_plane_equiv.symm.toLinearMap.comp
    (((LinearMap.prod
        (LinearMap.id : counterexampleField →ₗ[counterexampleField] counterexampleField)
        (LinearMap.id : counterexampleField →ₗ[counterexampleField] counterexampleField)) :
      counterexampleField →ₗ[counterexampleField]
        (counterexampleField × counterexampleField)).comp
      small_counterexample_line_equiv.toLinearMap)

/-- Helper for Lemma 12.19.8: the first-axis inclusion on the small witness is the conjugate of
`x ↦ (x,0)` under the chosen representation equivalences. -/
private def small_counterexample_first_axis_linear :
    small_counterexample_line_object →ₗ[counterexampleField]
      small_counterexample_plane_object :=
  small_counterexample_plane_equiv.symm.toLinearMap.comp
    (((LinearMap.prod
        (LinearMap.id : counterexampleField →ₗ[counterexampleField] counterexampleField)
        (0 : counterexampleField →ₗ[counterexampleField] counterexampleField)) :
      counterexampleField →ₗ[counterexampleField]
        (counterexampleField × counterexampleField)).comp
      small_counterexample_line_equiv.toLinearMap)

/-- Helper for Lemma 12.19.8: the first projection on the small witness is the conjugate of
`(x,y) ↦ x` under the chosen representation equivalences. -/
private def small_counterexample_fst_linear :
    small_counterexample_plane_object →ₗ[counterexampleField]
      small_counterexample_line_object :=
  small_counterexample_line_equiv.symm.toLinearMap.comp
    (((LinearMap.fst counterexampleField counterexampleField counterexampleField) :
      (counterexampleField × counterexampleField) →ₗ[counterexampleField]
        counterexampleField).comp
      small_counterexample_plane_equiv.toLinearMap)

/-- Helper for Lemma 12.19.8: on the small witness, projecting the first-axis inclusion recovers
the identity on the line. -/
private theorem small_counterexample_fst_linear_comp_first_axis_linear :
    small_counterexample_fst_linear.comp small_counterexample_first_axis_linear = LinearMap.id := by
  -- Evaluate the conjugated composite on an arbitrary element and cancel the chosen equivalences.
  ext x
  simp [small_counterexample_fst_linear, small_counterexample_first_axis_linear]

/-- Helper for Lemma 12.19.8: on the small witness, projecting the diagonal also recovers the
identity on the line. -/
private theorem small_counterexample_fst_linear_comp_diagonal_linear :
    small_counterexample_fst_linear.comp small_counterexample_diagonal_linear = LinearMap.id := by
  -- The source proof's composite `A → B → C` is still the identity after conjugating into the
  -- small representation model.
  ext x
  simp [small_counterexample_fst_linear, small_counterexample_diagonal_linear]

/-- Helper for Lemma 12.19.8: the small diagonal map is injective. -/
private theorem small_counterexample_diagonal_linear_injective :
    Function.Injective small_counterexample_diagonal_linear := by
  -- Read the first coordinate after transporting to the literal plane to recover the source
  -- line element.
  intro x y hxy
  apply small_counterexample_line_equiv.injective
  have hfst := congrArg (fun z : counterexampleField × counterexampleField ↦ z.1)
    (congrArg small_counterexample_plane_equiv hxy)
  simpa [small_counterexample_diagonal_linear] using hfst

/-- Helper for Lemma 12.19.8: the small first projection is surjective. -/
private theorem small_counterexample_fst_linear_surjective :
    Function.Surjective small_counterexample_fst_linear := by
  -- Every line element is already the projection of its first-axis lift.
  intro x
  refine ⟨small_counterexample_first_axis_linear x, ?_⟩
  change (small_counterexample_fst_linear.comp small_counterexample_first_axis_linear) x = x
  simp [small_counterexample_fst_linear_comp_first_axis_linear]

/-- Helper for Lemma 12.19.8: the diagonal morphism inside the small representation category. -/
private abbrev small_counterexample_diagonal_hom :
    small_counterexample_line_object ⟶ small_counterexample_plane_object :=
  (FGModuleRepr.embed.{0, 0} counterexampleField).preimage
    ((FGModuleCat.ulift.{0, 0} counterexampleField).map
      (FGModuleCat.ofHom small_counterexample_diagonal_linear))

/-- Helper for Lemma 12.19.8: the first-axis inclusion morphism inside the small representation
category. -/
private abbrev small_counterexample_first_axis_hom :
    small_counterexample_line_object ⟶ small_counterexample_plane_object :=
  (FGModuleRepr.embed.{0, 0} counterexampleField).preimage
    ((FGModuleCat.ulift.{0, 0} counterexampleField).map
      (FGModuleCat.ofHom small_counterexample_first_axis_linear))

/-- Helper for Lemma 12.19.8: the first projection morphism inside the small representation
category. -/
private abbrev small_counterexample_fst_hom :
    small_counterexample_plane_object ⟶ small_counterexample_line_object :=
  (FGModuleRepr.embed.{0, 0} counterexampleField).preimage
    ((FGModuleCat.ulift.{0, 0} counterexampleField).map
      (FGModuleCat.ofHom small_counterexample_fst_linear))

/-- Helper for Lemma 12.19.8: the ambient line object is the exact-universe image of the small
line witness. -/
private abbrev ambient_counterexample_line_object : counterexampleAmbient :=
  counterexampleAmbientUp.obj small_counterexample_line_object

/-- Helper for Lemma 12.19.8: the ambient plane object is the exact-universe image of the small
plane witness. -/
private abbrev ambient_counterexample_plane_object : counterexampleAmbient :=
  counterexampleAmbientUp.obj small_counterexample_plane_object

/-- Helper for Lemma 12.19.8: the ambient diagonal morphism is obtained by applying the exact
universe functor to the small diagonal. -/
private abbrev ambient_counterexample_diagonal_hom :
    ambient_counterexample_line_object ⟶ ambient_counterexample_plane_object :=
  counterexampleAmbientUp.map small_counterexample_diagonal_hom

/-- Helper for Lemma 12.19.8: the ambient first-axis inclusion is obtained by applying the exact
universe functor to the small first-axis map. -/
private abbrev ambient_counterexample_first_axis_hom :
    ambient_counterexample_line_object ⟶ ambient_counterexample_plane_object :=
  counterexampleAmbientUp.map small_counterexample_first_axis_hom

/-- Helper for Lemma 12.19.8: the ambient first projection is obtained by applying the exact
universe functor to the small projection. -/
private abbrev ambient_counterexample_fst_hom :
    ambient_counterexample_plane_object ⟶ ambient_counterexample_line_object :=
  counterexampleAmbientUp.map small_counterexample_fst_hom

/-- Helper for Lemma 12.19.8: the second projection on the small witness is the conjugate of
`(x,y) ↦ y` under the chosen representation equivalences. -/
private def small_counterexample_snd_linear :
    small_counterexample_plane_object →ₗ[counterexampleField]
      small_counterexample_line_object :=
  small_counterexample_line_equiv.symm.toLinearMap.comp
    (((LinearMap.snd counterexampleField counterexampleField counterexampleField) :
      (counterexampleField × counterexampleField) →ₗ[counterexampleField]
        counterexampleField).comp
      small_counterexample_plane_equiv.toLinearMap)

/-- Helper for Lemma 12.19.8: the second projection annihilates the first-axis inclusion on the
small witness. -/
private theorem small_counterexample_snd_linear_comp_first_axis_linear :
    small_counterexample_snd_linear.comp small_counterexample_first_axis_linear = 0 := by
  -- Evaluate the conjugated composite on an arbitrary element and use the coordinate formula.
  ext x
  simp [small_counterexample_snd_linear, small_counterexample_first_axis_linear]

/-- Helper for Lemma 12.19.8: the second projection composed with the diagonal is the identity on
the small witness line. -/
private theorem small_counterexample_snd_linear_comp_diagonal_linear :
    small_counterexample_snd_linear.comp small_counterexample_diagonal_linear = LinearMap.id := by
  -- The diagonal has equal coordinates, so the second projection recovers the input.
  ext x
  simp [small_counterexample_snd_linear, small_counterexample_diagonal_linear]

/-- Helper for Lemma 12.19.8: the second projection morphism inside the small representation
category. -/
private abbrev small_counterexample_snd_hom :
    small_counterexample_plane_object ⟶ small_counterexample_line_object :=
  (FGModuleRepr.embed.{0, 0} counterexampleField).preimage
    ((FGModuleCat.ulift.{0, 0} counterexampleField).map
      (FGModuleCat.ofHom small_counterexample_snd_linear))

/-- Helper for Lemma 12.19.8: on the small witness, the first-axis inclusion followed by the
first projection is the identity. -/
private theorem small_counterexample_first_axis_hom_comp_fst_hom :
    small_counterexample_first_axis_hom ≫ small_counterexample_fst_hom =
      𝟙 small_counterexample_line_object := by
  -- TODO: replan route should use `Functor.preimage_comp`/`Functor.preimage_id` for
  -- `FGModuleRepr.embed` and normalize the embedded composite inside `FGModuleCat`.
  sorry

/-- Helper for Lemma 12.19.8: on the small witness, the diagonal followed by the first projection
is the identity. -/
private theorem small_counterexample_diagonal_hom_comp_fst_hom :
    small_counterexample_diagonal_hom ≫ small_counterexample_fst_hom =
      𝟙 small_counterexample_line_object := by
  -- TODO: replan route should mirror the previous split identity with the diagonal linear map.
  sorry

/-- Helper for Lemma 12.19.8: on the small witness, the first-axis inclusion followed by the
second projection is zero. -/
private theorem small_counterexample_first_axis_hom_comp_snd_hom :
    small_counterexample_first_axis_hom ≫ small_counterexample_snd_hom = 0 := by
  -- TODO: replan route should prove the embedded composite is zero and reflect it by faithfulness.
  sorry

/-- Helper for Lemma 12.19.8: on the small witness, the diagonal followed by the second
projection is the identity. -/
private theorem small_counterexample_diagonal_hom_comp_snd_hom :
    small_counterexample_diagonal_hom ≫ small_counterexample_snd_hom =
      𝟙 small_counterexample_line_object := by
  -- TODO: replan route should finish the final small split identity by the same `preimage` API.
  sorry

/-- Helper for Lemma 12.19.8: the ambient second projection is obtained by lifting the small
second projection through the exact-universe functor. -/
private abbrev ambient_counterexample_snd_hom :
    ambient_counterexample_plane_object ⟶ ambient_counterexample_line_object :=
  counterexampleAmbientUp.map small_counterexample_snd_hom

/-- Helper for Lemma 12.19.8: in the ambient category, the first-axis inclusion followed by the
first projection is the identity. -/
private theorem ambient_counterexample_first_axis_hom_comp_fst_hom :
    ambient_counterexample_first_axis_hom ≫ ambient_counterexample_fst_hom =
      𝟙 ambient_counterexample_line_object := by
  -- Apply the exact-universe functor to the small split identity.
  rw [ambient_counterexample_first_axis_hom, ambient_counterexample_fst_hom, ← Functor.map_comp,
    small_counterexample_first_axis_hom_comp_fst_hom, Functor.map_id]

/-- Helper for Lemma 12.19.8: in the ambient category, the diagonal followed by the first
projection is the identity. -/
private theorem ambient_counterexample_diagonal_hom_comp_fst_hom :
    ambient_counterexample_diagonal_hom ≫ ambient_counterexample_fst_hom =
      𝟙 ambient_counterexample_line_object := by
  -- The ambient split identity is again the image of the small one.
  rw [ambient_counterexample_diagonal_hom, ambient_counterexample_fst_hom, ← Functor.map_comp,
    small_counterexample_diagonal_hom_comp_fst_hom, Functor.map_id]

/-- Helper for Lemma 12.19.8: in the ambient category, the first-axis inclusion followed by the
second projection is zero. -/
private theorem ambient_counterexample_first_axis_hom_comp_snd_hom :
    ambient_counterexample_first_axis_hom ≫ ambient_counterexample_snd_hom = 0 := by
  -- The second coordinate still kills the lifted first axis after the universe adjustment.
  rw [ambient_counterexample_first_axis_hom, ambient_counterexample_snd_hom, ← Functor.map_comp,
    small_counterexample_first_axis_hom_comp_snd_hom, Functor.map_zero]

/-- Helper for Lemma 12.19.8: in the ambient category, the diagonal followed by the second
projection is the identity. -/
private theorem ambient_counterexample_diagonal_hom_comp_snd_hom :
    ambient_counterexample_diagonal_hom ≫ ambient_counterexample_snd_hom =
      𝟙 ambient_counterexample_line_object := by
  -- The lifted diagonal is still split by the lifted second projection.
  rw [ambient_counterexample_diagonal_hom, ambient_counterexample_snd_hom, ← Functor.map_comp,
    small_counterexample_diagonal_hom_comp_snd_hom, Functor.map_id]

/-- Helper for Lemma 12.19.8: the ambient first-axis inclusion is a monomorphism because it
splits by the ambient first projection. -/
private instance ambient_counterexample_first_axis_hom_mono :
    Mono ambient_counterexample_first_axis_hom := by
  -- The ambient first-axis inclusion has an explicit retraction.
  exact mono_of_mono_fac ambient_counterexample_first_axis_hom_comp_fst_hom

/-- Helper for Lemma 12.19.8: the ambient diagonal is a monomorphism because it splits by the
ambient first projection. -/
private instance ambient_counterexample_diagonal_hom_mono :
    Mono ambient_counterexample_diagonal_hom := by
  -- The ambient diagonal also has an explicit retraction.
  exact mono_of_mono_fac ambient_counterexample_diagonal_hom_comp_fst_hom

/-- Helper for Lemma 12.19.8: the ambient first projection is an epimorphism because the ambient
first-axis inclusion is a section. -/
private instance ambient_counterexample_fst_hom_epi :
    Epi ambient_counterexample_fst_hom := by
  -- The ambient first projection has an explicit section.
  exact epi_of_epi_fac ambient_counterexample_first_axis_hom_comp_fst_hom

/-- Helper for Lemma 12.19.8: the degree-zero middle stage in the ambient witness is the
subobject cut out by the first-axis inclusion. -/
private abbrev ambient_counterexample_first_axis_subobject :
    Subobject ambient_counterexample_plane_object :=
  Subobject.mk ambient_counterexample_first_axis_hom

/-- Helper for Lemma 12.19.8: the arrow of the ambient first-axis subobject is annihilated by the
ambient second projection. -/
private theorem ambient_counterexample_first_axis_arrow_comp_snd :
    ambient_counterexample_first_axis_subobject.arrow ≫ ambient_counterexample_snd_hom = 0 := by
  -- TODO: once the ambient split identity is stabilized, rewrite the subobject arrow to the
  -- chosen inclusion and close by the mapped zero composite.
  sorry

/-- Helper for Lemma 12.19.8: the ambient source stage is `⊤` in negative degrees and `⊥`
otherwise. -/
private def ambient_counterexample_source_stage (i : ℤ) :
    Subobject ambient_counterexample_line_object :=
  if i < 0 then ⊤ else ⊥

/-- Helper for Lemma 12.19.8: the ambient middle stage is `⊤` in negative degrees, the first axis
in degree `0`, and `⊥` in positive degrees. -/
private def ambient_counterexample_middle_stage (i : ℤ) :
    Subobject ambient_counterexample_plane_object :=
  if i < 0 then ⊤ else if i = 0 then ambient_counterexample_first_axis_subobject else ⊥

/-- Helper for Lemma 12.19.8: the ambient target stage is `⊤` through degree `0` and `⊥`
afterwards. -/
private def ambient_counterexample_target_stage (i : ℤ) :
    Subobject ambient_counterexample_line_object :=
  if i ≤ 0 then ⊤ else ⊥

/-- Helper for Lemma 12.19.8: the ambient source stage family is antitone. -/
private theorem ambient_counterexample_source_stage_antitone :
    Antitone ambient_counterexample_source_stage := by
  -- Once the stage drops to `⊥`, it never rises again.
  intro i j hij
  by_cases hj : j < 0
  · have hi : i < 0 := lt_of_le_of_lt hij hj
    simp [ambient_counterexample_source_stage, hi, hj]
  · simp [ambient_counterexample_source_stage, hj]

/-- Helper for Lemma 12.19.8: the ambient middle stage family is antitone. -/
private theorem ambient_counterexample_middle_stage_antitone :
    Antitone ambient_counterexample_middle_stage := by
  -- The only nontrivial drop is from `⊤` to the first axis at degree `0`.
  intro i j hij
  by_cases hjneg : j < 0
  · have hineg : i < 0 := lt_of_le_of_lt hij hjneg
    simp [ambient_counterexample_middle_stage, hjneg, hineg]
  · by_cases hj0 : j = 0
    · by_cases hineg : i < 0
      · simp [ambient_counterexample_middle_stage, hj0, hineg]
      · have hi0 : i = 0 := le_antisymm (hj0 ▸ hij) (le_of_not_gt hineg)
        simp [ambient_counterexample_middle_stage, hj0, hi0]
    · simp [ambient_counterexample_middle_stage, hjneg, hj0]

/-- Helper for Lemma 12.19.8: the ambient target stage family is antitone. -/
private theorem ambient_counterexample_target_stage_antitone :
    Antitone ambient_counterexample_target_stage := by
  -- The target keeps `⊤` exactly through degree `0`.
  intro i j hij
  by_cases hj : j ≤ 0
  · have hi : i ≤ 0 := le_trans hij hj
    simp [ambient_counterexample_target_stage, hi, hj]
  · simp [ambient_counterexample_target_stage, hj]

/-- Helper for Lemma 12.19.8: reindexing the ambient source stages along `OrderDual` yields a
monotone filtration. -/
private theorem ambient_counterexample_source_filtration_mono :
    Monotone
      (fun p : OrderDual ℤ ↦ ambient_counterexample_source_stage (OrderDual.ofDual p)) := by
  -- Monotonicity on `OrderDual` is just antitonicity on `ℤ`.
  intro p q hpq
  exact ambient_counterexample_source_stage_antitone hpq

/-- Helper for Lemma 12.19.8: reindexing the ambient middle stages along `OrderDual` yields a
monotone filtration. -/
private theorem ambient_counterexample_middle_filtration_mono :
    Monotone
      (fun p : OrderDual ℤ ↦ ambient_counterexample_middle_stage (OrderDual.ofDual p)) := by
  -- This is the same stagewise antitonicity expressed in the filtered-object indexing.
  intro p q hpq
  exact ambient_counterexample_middle_stage_antitone hpq

/-- Helper for Lemma 12.19.8: reindexing the ambient target stages along `OrderDual` yields a
monotone filtration. -/
private theorem ambient_counterexample_target_filtration_mono :
    Monotone
      (fun p : OrderDual ℤ ↦ ambient_counterexample_target_stage (OrderDual.ofDual p)) := by
  -- The nonpositive cutoff is antitone on `ℤ`, hence monotone on `OrderDual ℤ`.
  intro p q hpq
  exact ambient_counterexample_target_stage_antitone hpq

/-- Helper for Lemma 12.19.8: the ambient source filtered object. -/
private def ambientCounterexampleSource : FilteredObject counterexampleAmbient :=
  { obj := ambient_counterexample_line_object
    filtration :=
      { toFun := fun p ↦ ambient_counterexample_source_stage (OrderDual.ofDual p)
        monotone' := ambient_counterexample_source_filtration_mono } }

/-- Helper for Lemma 12.19.8: the ambient middle filtered object. -/
private def ambientCounterexampleMiddle : FilteredObject counterexampleAmbient :=
  { obj := ambient_counterexample_plane_object
    filtration :=
      { toFun := fun p ↦ ambient_counterexample_middle_stage (OrderDual.ofDual p)
        monotone' := ambient_counterexample_middle_filtration_mono } }

/-- Helper for Lemma 12.19.8: the ambient target filtered object. -/
private def ambientCounterexampleTarget : FilteredObject counterexampleAmbient :=
  { obj := ambient_counterexample_line_object
    filtration :=
      { toFun := fun p ↦ ambient_counterexample_target_stage (OrderDual.ofDual p)
        monotone' := ambient_counterexample_target_filtration_mono } }

/-- Helper for Lemma 12.19.8: the ambient diagonal preserves the chosen filtrations. -/
private theorem ambient_counterexample_diagonal_preserves (i : ℤ) :
    (ambientCounterexampleMiddle.filtration i).Factors
      ((ambientCounterexampleSource.filtration i).arrow ≫ ambient_counterexample_diagonal_hom) := by
  by_cases hi : i < 0
  · -- In negative degrees the middle stage is `⊤`, so the stage map factors automatically.
    have hmiddle :
        ambientCounterexampleMiddle.filtration i =
          (⊤ : Subobject ambient_counterexample_plane_object) := by
      change ambient_counterexample_middle_stage i =
        (⊤ : Subobject ambient_counterexample_plane_object)
      simp [ambient_counterexample_middle_stage, hi]
    rw [hmiddle]
    simpa using
      (Subobject.top_factors
        ((ambientCounterexampleSource.filtration i).arrow ≫ ambient_counterexample_diagonal_hom))
  · -- From degree `0` onward the source stage is `⊥`, so the induced stage map is zero.
    have hsource :
        ambientCounterexampleSource.filtration i =
          (⊥ : Subobject ambient_counterexample_line_object) := by
      change ambient_counterexample_source_stage i =
        (⊥ : Subobject ambient_counterexample_line_object)
      simp [ambient_counterexample_source_stage, hi]
    rw [hsource]
    have hcomp :
        (((⊥ : Subobject ambient_counterexample_line_object).arrow :
            ((⊥ : Subobject ambient_counterexample_line_object) : counterexampleAmbient) ⟶
              ambient_counterexample_line_object) ≫
          ambient_counterexample_diagonal_hom) = 0 := by
      simp
    exact hcomp.symm ▸
      (Subobject.factors_zero :
        (ambientCounterexampleMiddle.filtration i).Factors
          (0 :
            ((⊥ : Subobject ambient_counterexample_line_object) : counterexampleAmbient) ⟶
              ambient_counterexample_plane_object))

/-- Helper for Lemma 12.19.8: the ambient diagonal filtered morphism. -/
private def ambientCounterexampleDiagonal :
    ambientCounterexampleSource ⟶ ambientCounterexampleMiddle where
  hom := ambient_counterexample_diagonal_hom
  preserves := ambient_counterexample_diagonal_preserves

/-- Helper for Lemma 12.19.8: the ambient diagonal filtered morphism has mono underlying map. -/
private instance : Mono ambientCounterexampleDiagonal.hom := by
  change Mono ambient_counterexample_diagonal_hom
  infer_instance

/-- Helper for Lemma 12.19.8: at degree `0`, pulling back the ambient first-axis stage along the
ambient diagonal gives the zero subobject. -/
private theorem ambient_counterexample_diagonal_pullback_first_axis_eq_bot :
    (Subobject.pullback ambient_counterexample_diagonal_hom).obj
        ambient_counterexample_first_axis_subobject =
      (⊥ : Subobject ambient_counterexample_line_object) := by
  -- Compose the pullback leg with the ambient second projection: the first-axis side gives zero,
  -- while the diagonal side collapses to the identity.
  rw [Subobject.pullback_obj]
  apply (Subobject.mk_eq_bot_iff_zero).2
  calc
    pullback.snd ambient_counterexample_first_axis_subobject.arrow
        ambient_counterexample_diagonal_hom =
        pullback.snd ambient_counterexample_first_axis_subobject.arrow
            ambient_counterexample_diagonal_hom ≫
          (ambient_counterexample_diagonal_hom ≫ ambient_counterexample_snd_hom) := by
            simp [ambient_counterexample_diagonal_hom_comp_snd_hom]
    _ = (pullback.snd ambient_counterexample_first_axis_subobject.arrow
            ambient_counterexample_diagonal_hom ≫ ambient_counterexample_diagonal_hom) ≫
          ambient_counterexample_snd_hom := by
            simp [Category.assoc]
    _ = (pullback.fst ambient_counterexample_first_axis_subobject.arrow
            ambient_counterexample_diagonal_hom ≫
          ambient_counterexample_first_axis_subobject.arrow) ≫
          ambient_counterexample_snd_hom := by
            rw [(pullback.condition
              (f := ambient_counterexample_first_axis_subobject.arrow)
              (g := ambient_counterexample_diagonal_hom)).symm]
    _ = pullback.fst ambient_counterexample_first_axis_subobject.arrow
            ambient_counterexample_diagonal_hom ≫
          (ambient_counterexample_first_axis_subobject.arrow ≫
            ambient_counterexample_snd_hom) := by
            simp [Category.assoc]
    _ = 0 := by
          simp [ambient_counterexample_first_axis_arrow_comp_snd]

/-- Helper for Lemma 12.19.8: pulling back the zero stage along the ambient diagonal still gives
the zero subobject. -/
private theorem ambient_counterexample_diagonal_pullback_bot_eq_bot :
    (Subobject.pullback ambient_counterexample_diagonal_hom).obj
        (⊥ : Subobject ambient_counterexample_plane_object) =
      (⊥ : Subobject ambient_counterexample_line_object) := by
  -- The pullback condition makes the pullback leg land in the zero subobject, and the diagonal
  -- split by the first projection then forces that leg itself to be zero.
  rw [Subobject.pullback_obj]
  apply (Subobject.mk_eq_bot_iff_zero).2
  have hdiag_zero :
      pullback.snd ((⊥ : Subobject ambient_counterexample_plane_object).arrow)
          ambient_counterexample_diagonal_hom ≫
        ambient_counterexample_diagonal_hom = 0 := by
    simpa using
      (show
          pullback.snd ((⊥ : Subobject ambient_counterexample_plane_object).arrow)
              ambient_counterexample_diagonal_hom ≫ ambient_counterexample_diagonal_hom =
            pullback.fst ((⊥ : Subobject ambient_counterexample_plane_object).arrow)
              ambient_counterexample_diagonal_hom ≫
              (⊥ : Subobject ambient_counterexample_plane_object).arrow by
        simpa [Category.assoc] using
          (pullback.condition
            (f := (⊥ : Subobject ambient_counterexample_plane_object).arrow)
            (g := ambient_counterexample_diagonal_hom)).symm)
  calc
    pullback.snd ((⊥ : Subobject ambient_counterexample_plane_object).arrow)
        ambient_counterexample_diagonal_hom =
        pullback.snd ((⊥ : Subobject ambient_counterexample_plane_object).arrow)
            ambient_counterexample_diagonal_hom ≫
          (ambient_counterexample_diagonal_hom ≫ ambient_counterexample_fst_hom) := by
            simp [ambient_counterexample_diagonal_hom_comp_fst_hom]
    _ = (pullback.snd ((⊥ : Subobject ambient_counterexample_plane_object).arrow)
            ambient_counterexample_diagonal_hom ≫ ambient_counterexample_diagonal_hom) ≫
          ambient_counterexample_fst_hom := by
            simp [Category.assoc]
    _ = 0 := by
          rw [hdiag_zero]
          simp

/-- Helper for Lemma 12.19.8: the ambient first projection preserves the chosen filtrations. -/
private theorem ambient_counterexample_fst_preserves (i : ℤ) :
    (ambientCounterexampleTarget.filtration i).Factors
      ((ambientCounterexampleMiddle.filtration i).arrow ≫ ambient_counterexample_fst_hom) := by
  by_cases hi : i ≤ 0
  · -- Up through degree `0`, the target stage is `⊤`, so the stage map factors tautologically.
    have htarget :
        ambientCounterexampleTarget.filtration i =
          (⊤ : Subobject ambient_counterexample_line_object) := by
      change ambient_counterexample_target_stage i =
        (⊤ : Subobject ambient_counterexample_line_object)
      simp [ambient_counterexample_target_stage, hi]
    rw [htarget]
    simpa using
      (Subobject.top_factors
        ((ambientCounterexampleMiddle.filtration i).arrow ≫ ambient_counterexample_fst_hom))
  · -- In positive degrees the middle stage is `⊥`, so the induced stage map is zero.
    have hmiddle :
        ambientCounterexampleMiddle.filtration i =
          (⊥ : Subobject ambient_counterexample_plane_object) := by
      change ambient_counterexample_middle_stage i =
        (⊥ : Subobject ambient_counterexample_plane_object)
      have hpos : 0 < i := lt_of_not_ge hi
      simp [ambient_counterexample_middle_stage, not_lt.mpr (le_of_lt hpos), ne_of_gt hpos]
    rw [hmiddle]
    have hcomp :
        (((⊥ : Subobject ambient_counterexample_plane_object).arrow :
            ((⊥ : Subobject ambient_counterexample_plane_object) : counterexampleAmbient) ⟶
              ambient_counterexample_plane_object) ≫
          ambient_counterexample_fst_hom) = 0 := by
      simp
    exact hcomp.symm ▸
      (Subobject.factors_zero :
        (ambientCounterexampleTarget.filtration i).Factors
          (0 :
            ((⊥ : Subobject ambient_counterexample_plane_object) : counterexampleAmbient) ⟶
              ambient_counterexample_line_object))

/-- Helper for Lemma 12.19.8: the ambient first projection filtered morphism. -/
private def ambientCounterexampleFst :
    ambientCounterexampleMiddle ⟶ ambientCounterexampleTarget where
  hom := ambient_counterexample_fst_hom
  preserves := ambient_counterexample_fst_preserves

/-- Helper for Lemma 12.19.8: the ambient first projection filtered morphism has epi underlying
map. -/
private instance : Epi ambientCounterexampleFst.hom := by
  change Epi ambient_counterexample_fst_hom
  infer_instance

/-- Helper for Lemma 12.19.8: the ambient degree-zero stage maps onto the full target line under
the ambient first projection. -/
private theorem ambient_counterexample_first_axis_image_under_fst_eq_top :
    imageSubobject
        (ambient_counterexample_first_axis_subobject.arrow ≫ ambient_counterexample_fst_hom) =
      (⊤ : Subobject ambient_counterexample_line_object) := by
  -- TODO: after the ambient subobject arrow is identified with the lifted first-axis inclusion,
  -- rewrite the composite to the identity and conclude by `imageSubobject_eq_top_of_epi`.
  sorry

/-- Helper for Lemma 12.19.8: the ambient source filtration vanishes in degree `0`. -/
private theorem ambientCounterexampleSource_filtration_zero :
    ambientCounterexampleSource.filtration 0 =
      (⊥ : Subobject ambient_counterexample_line_object) := by
  -- Degree `0` is exactly where the source drops from `⊤` to `⊥`.
  change ambient_counterexample_source_stage 0 =
    (⊥ : Subobject ambient_counterexample_line_object)
  simp [ambient_counterexample_source_stage]

/-- Helper for Lemma 12.19.8: the ambient middle filtration is the first-axis subobject in degree
`0`. -/
private theorem ambientCounterexampleMiddle_filtration_zero :
    ambientCounterexampleMiddle.filtration 0 =
      ambient_counterexample_first_axis_subobject := by
  -- Degree `0` is the unique nontrivial intermediate stage.
  change ambient_counterexample_middle_stage 0 = ambient_counterexample_first_axis_subobject
  simp [ambient_counterexample_middle_stage]

/-- Helper for Lemma 12.19.8: the ambient target filtration is the whole line in degree `0`. -/
private theorem ambientCounterexampleTarget_filtration_zero :
    ambientCounterexampleTarget.filtration 0 =
      (⊤ : Subobject ambient_counterexample_line_object) := by
  -- The target retains the full line through degree `0`.
  change ambient_counterexample_target_stage 0 =
    (⊤ : Subobject ambient_counterexample_line_object)
  simp [ambient_counterexample_target_stage]

/-- Helper for Lemma 12.19.8: the ambient diagonal filtered morphism is strict. -/
private theorem ambient_counterexample_diagonal_strict :
    Strict ambientCounterexampleDiagonal := by
  -- Apply the mono characterization and evaluate the three possible stage shapes separately.
  refine (strict_iff_induced_filtration_of_mono ambientCounterexampleDiagonal).2 ?_
  refine OrderHom.ext _ _ ?_
  funext p
  change ambient_counterexample_source_stage (OrderDual.ofDual p) =
    (Subobject.pullback ambientCounterexampleDiagonal.hom).obj
      (ambient_counterexample_middle_stage (OrderDual.ofDual p))
  by_cases hi_neg : OrderDual.ofDual p < 0
  · -- Negative stages are `⊤` on both sides.
    rw [show ambient_counterexample_source_stage (OrderDual.ofDual p) =
        (⊤ : Subobject ambient_counterexample_line_object) by
          simp [ambient_counterexample_source_stage, hi_neg]]
    rw [show ambient_counterexample_middle_stage (OrderDual.ofDual p) =
        (⊤ : Subobject ambient_counterexample_plane_object) by
          simp [ambient_counterexample_middle_stage, hi_neg]]
    simpa using (Subobject.pullback_top ambientCounterexampleDiagonal.hom).symm
  · by_cases hi_zero : OrderDual.ofDual p = 0
    · -- Degree `0` is the concrete pullback computation against the first-axis stage.
      rw [show ambient_counterexample_source_stage (OrderDual.ofDual p) =
          (⊥ : Subobject ambient_counterexample_line_object) by
            simp [ambient_counterexample_source_stage, hi_neg]]
      rw [show ambient_counterexample_middle_stage (OrderDual.ofDual p) =
          ambient_counterexample_first_axis_subobject by
            simp [ambient_counterexample_middle_stage, hi_neg, hi_zero]]
      simpa [ambientCounterexampleDiagonal] using
        ambient_counterexample_diagonal_pullback_first_axis_eq_bot.symm
    · -- Positive stages are `⊥`, and pulling back `⊥` along the diagonal stays `⊥`.
      rw [show ambient_counterexample_source_stage (OrderDual.ofDual p) =
          (⊥ : Subobject ambient_counterexample_line_object) by
            simp [ambient_counterexample_source_stage, hi_neg]]
      rw [show ambient_counterexample_middle_stage (OrderDual.ofDual p) =
          (⊥ : Subobject ambient_counterexample_plane_object) by
            simp [ambient_counterexample_middle_stage, hi_neg, hi_zero]]
      simpa [ambientCounterexampleDiagonal] using
        ambient_counterexample_diagonal_pullback_bot_eq_bot.symm

/-- Helper for Lemma 12.19.8: the ambient first projection filtered morphism is strict. -/
private theorem ambient_counterexample_fst_strict :
    Strict ambientCounterexampleFst := sorry

/-- Helper for Lemma 12.19.8: the ambient composite underlying morphism is the identity on the
ambient line. -/
private theorem ambient_counterexample_comp_hom :
    ambientCounterexampleDiagonal.hom ≫ ambientCounterexampleFst.hom =
      𝟙 ambient_counterexample_line_object := by
  -- The composite is the lifted diagonal-then-first-projection identity.
  simpa [ambientCounterexampleDiagonal, ambientCounterexampleFst] using
    ambient_counterexample_diagonal_hom_comp_fst_hom

/-- Helper for Lemma 12.19.8: the small witness line is nonzero, so its identity morphism does not
vanish. -/
private theorem small_counterexample_line_id_ne_zero :
    (𝟙 small_counterexample_line_object : small_counterexample_line_object ⟶
      small_counterexample_line_object) ≠ 0 := sorry

/-- Helper for Lemma 12.19.8: the ambient witness line is nonzero because it is the image of the
nonzero small witness line under a faithful equivalence functor. -/
private theorem ambient_counterexample_line_id_ne_zero :
    (𝟙 ambient_counterexample_line_object : ambient_counterexample_line_object ⟶
      ambient_counterexample_line_object) ≠ 0 := sorry

/-- Helper for Lemma 12.19.8: the composite of the two ambient strict maps is not strict. -/
private theorem ambient_counterexample_comp_not_strict :
    ¬ Strict (ambientCounterexampleDiagonal ≫ ambientCounterexampleFst) := sorry

-- Proof sketch: use the explicit two-step filtration on a two-dimensional vector space, together
-- with the induced filtration on a line and the quotient filtration on the quotient by a basis
-- vector, to obtain strict maps whose nonzero composite fails the strictness equality.
/-- Lemma 12.19.8 (1): in general, the composite of strict morphisms of filtered objects need not
be strict. -/
theorem strict_comp_not_in_general :
    ¬ ∀ {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] {A B C : FilteredObject 𝒜}
        (f : A ⟶ B) (g : B ⟶ C), Strict f → Strict g → Strict (f ≫ g) :=
by
  -- Route correction: instead of trying to reflect strictness back through `ULiftHom.down`, build
  -- the lifted counterexample directly in `counterexampleAmbient` and use the split identities
  -- there to replay the source proof stage-by-stage.
  intro hstrict_comp
  exact ambient_counterexample_comp_not_strict <|
    hstrict_comp ambientCounterexampleDiagonal ambientCounterexampleFst
      ambient_counterexample_diagonal_strict ambient_counterexample_fst_strict

variable {A B D : FilteredObject C}

private theorem map_inf_eq_of_strict_mono (g : B ⟶ D) [Mono g.hom] (hg : Strict g)
    (x : Subobject B.obj) (i : ℤ) :
    (Subobject.map g.hom).obj (x ⊓ B.filtration i) =
      (Subobject.map g.hom).obj x ⊓ D.filtration i := by
  have hgi : B.filtration i = (Subobject.pullback g.hom).obj (D.filtration i) := by
    exact congrArg (fun F ↦ F i) ((strict_iff_induced_filtration_of_mono g).1 hg)
  rw [hgi, Subobject.inf_map]
  rw [show (Subobject.map g.hom).obj ((Subobject.pullback g.hom).obj (D.filtration i)) =
      Subobject.mk g.hom ⊓ D.filtration i by
        simpa [Subobject.inf_def] using
          (Subobject.inf_eq_map_pullback' (MonoOver.mk g.hom) (D.filtration i)).symm]
  have hx : (Subobject.map g.hom).obj x ≤ Subobject.mk g.hom := by
    induction x using Subobject.ind
    rename_i X m hm
    simpa [Subobject.map_mk] using
      (Subobject.mk_le_mk_of_comm m (by simp) :
        Subobject.mk (m ≫ g.hom) ≤ Subobject.mk g.hom)
  calc
    (Subobject.map g.hom).obj x ⊓ (Subobject.mk g.hom ⊓ D.filtration i)
        = ((Subobject.map g.hom).obj x ⊓ Subobject.mk g.hom) ⊓ D.filtration i := by
            simp [inf_assoc]
    _ = (Subobject.map g.hom).obj x ⊓ D.filtration i := by
            simp [inf_eq_left.mpr hx]

private theorem quotient_comp_eq_quotient_of_quotient [Balanced C] (f : A ⟶ B) (g : B ⟶ D)
    (i : ℤ) : A.filtration.quotient (f.hom ≫ g.hom) i =
      (A.filtration.quotient f.hom).quotient g.hom i := by
  rw [DecreasingFiltration.quotient_eq_imageSubobject_comp,
    DecreasingFiltration.quotient_eq_imageSubobject_comp]
  rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
  simpa [Category.assoc] using
    (CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction
      ((A.filtration i).arrow ≫ f.hom) g.hom)

-- Proof sketch: strictness of `f` identifies `g (f(F^p A))` with
-- `g (f(A) ∩ F^p B)`; injectivity of `g.hom` turns this into the intersection of the image of the
-- composite with `g(F^p B)`, and strictness of `g` rewrites `g(F^p B)` as `F^p C ∩ image g`.
/-- Lemma 12.19.8 (2): if `g` is injective, then the composite `g ∘ f` of strict morphisms of
filtered objects is strict. -/
theorem strict_comp_of_mono [Balanced C] (f : A ⟶ B) (g : B ⟶ D) [Mono g.hom]
    (hf : Strict f) (hg : Strict g) :
    Strict (f ≫ g) := by
  refine (strict_iff_quotient_eq_inf (f ≫ g)).2 ?_
  intro i
  calc
    A.filtration.quotient (f.hom ≫ g.hom) i
        = imageSubobject ((A.filtration i).arrow ≫ f.hom ≫ g.hom) := by
            rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    _ = (Subobject.map g.hom).obj (imageSubobject ((A.filtration i).arrow ≫ f.hom)) := by
            simpa [Category.assoc] using
              (imageSubobject_comp_eq_map_of_mono ((A.filtration i).arrow ≫ f.hom) g.hom)
    _ = (Subobject.map g.hom).obj (A.filtration.quotient f.hom i) := by
            rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    _ = (Subobject.map g.hom).obj (imageSubobject f.hom ⊓ B.filtration i) := by
            rw [(strict_iff_quotient_eq_inf f).1 hf i]
    _ = (Subobject.map g.hom).obj (imageSubobject f.hom) ⊓ D.filtration i := by
            simpa using map_inf_eq_of_strict_mono g hg (imageSubobject f.hom) i
    _ = imageSubobject (f.hom ≫ g.hom) ⊓ D.filtration i := by
            rw [← imageSubobject_comp_eq_map_of_mono f.hom g.hom]

-- Proof sketch: rewrite the preimage of `F^p C` under `g ∘ f` as the preimage under `f` of
-- `F^p B + ker g` using strictness of `g`; surjectivity of `f.hom` lets the pullback of this sum
-- split as the sum of the pullbacks, and strictness of `f` identifies the pullback of `F^p B`
-- with `F^p A + ker f`, which collapses to `F^p A + ker (g ≫ f)`.
/-- Lemma 12.19.8 (3): if `f` is surjective, then the composite `g ∘ f` of strict morphisms of
filtered objects is strict. -/
theorem strict_comp_of_epi [Balanced C] (f : A ⟶ B) (g : B ⟶ D) [Epi f.hom]
    (hf : Strict f) (hg : Strict g) :
    Strict (f ≫ g) := by
  refine (strict_iff_quotient_eq_inf (f ≫ g)).2 ?_
  intro i
  calc
    A.filtration.quotient (f.hom ≫ g.hom) i
        = (A.filtration.quotient f.hom).quotient g.hom i :=
            quotient_comp_eq_quotient_of_quotient f g i
    _ = B.filtration.quotient g.hom i := by
          have hfi : A.filtration.quotient f.hom = B.filtration := by
            simpa using ((strict_iff_quotient_filtration_of_epi f).1 hf).symm
          rw [hfi]
    _ = imageSubobject g.hom ⊓ D.filtration i := by
          exact (strict_iff_quotient_eq_inf g).1 hg i
    _ = imageSubobject (f.hom ≫ g.hom) ⊓ D.filtration i := by
          rw [imageSubobject_comp_eq_of_epi f.hom g.hom]

end FilteredObject.Hom
end CategoryTheory
