import StacksProject_2024.Chap08.Lemma_8_12_6.IsoCommaModel
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open Bicategory
open scoped Bicategory

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

namespace Functor

open scoped Functor

variable (u : C ⥤ D) (p : S ⥤ C)

variable [p.IsFibered]
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.6: a hom-lift for the raw iso-comma projection fixes the left comma
component to be the chosen base map. -/
theorem pushforwardProjectionIsoCommaProjection_homLift_left
    {Y Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
    (θ : Z ⟶ Y)
    (hθ : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift (g ≫ f) θ) :
    θ.hom.left = g ≫ f := by
  let _ : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift (g ≫ f) θ := hθ
  -- The raw projection forgets everything except the left comma component.
  simpa [pushforwardProjectionIsoCommaProjection] using
    (IsHomLift.fac' (pushforwardProjectionIsoCommaProjection (u := u) (p := p)) (g ≫ f) θ)

/-- Helper for Lemma 8.12.6: once the source-faithful descent supplies the right component of the
universal factor, the existence half of the raw iso-comma universal property is just bookkeeping
with the packaged factor constructor. -/
theorem pushforwardProjectionIsoComma_factor_exists_of_right_component
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
    (θ : Z ⟶ Y)
    (χr : Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
      (u := u) (p := p) Y f).obj.right)
    (hχr :
      g ≫ (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom =
        Z.obj.hom ≫ (u.pushforwardProjection p).map χr)
    (hfacr :
      χr ≫ (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f).hom.right =
        θ.hom.right) :
    ∃ χ : Z ⟶ pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f,
      (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift g χ ∧
        χ ≫ pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f = θ := by
  -- Package the descended right component together with the fixed left base map `g`.
  let χ :=
    pushforwardProjectionIsoComma_factorHom (u := u) (p := p) f χr hχr
  refine ⟨χ, ?_, ?_⟩
  · -- The packaged factor is automatically a raw hom-lift because its left component is `g`.
    exact
      pushforwardProjectionIsoComma_factorHom_isHomLift
        (u := u) (p := p) f χr hχr
  · -- The right-component factorization already forces the full composite equality.
    exact
      pushforwardProjectionIsoComma_factorHom_comp
        (u := u) (p := p) f χr hχr hfacr

/-- Helper for Lemma 8.12.6: a fixed right-fraction representative of the transported right
component satisfies the expected same-denominator numerator identity in the localization. -/
theorem pushforwardProjectionIsoComma_fraction_denominator_comp_eq_numerator
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
    (θ : Z ⟶ Y)
    (ρ : (u.pushforwardFractions p).RightFraction
      (((u.pushforwardFractions p).Q).objPreimage Z.obj.right)
      (((u.pushforwardFractions p).Q).objPreimage Y.obj.right))
    (hρ :
      (((u.pushforwardFractions p).Q.objObjPreimageIso Z.obj.right).hom ≫
          θ.hom.right ≫
            ((u.pushforwardFractions p).Q.objObjPreimageIso Y.obj.right).inv) =
        ρ.map ((u.pushforwardFractions p).Q)
          (Localization.inverts ((u.pushforwardFractions p).Q)
            (u.pushforwardFractions p))) :
    ((u.pushforwardFractions p).Q.map ρ.s) ≫
        (((u.pushforwardFractions p).Q.objObjPreimageIso Z.obj.right).hom ≫
          θ.hom.right ≫
            ((u.pushforwardFractions p).Q.objObjPreimageIso Y.obj.right).inv) =
      ((u.pushforwardFractions p).Q.map ρ.f) := by
  -- Replace the transported right component by the chosen fraction and then clear the common
  -- denominator with the standard right-fraction identity.
  calc
    ((u.pushforwardFractions p).Q.map ρ.s) ≫
        (((u.pushforwardFractions p).Q.objObjPreimageIso Z.obj.right).hom ≫
          θ.hom.right ≫
            ((u.pushforwardFractions p).Q.objObjPreimageIso Y.obj.right).inv) =
      ((u.pushforwardFractions p).Q.map ρ.s) ≫
        ρ.map ((u.pushforwardFractions p).Q)
          (Localization.inverts ((u.pushforwardFractions p).Q)
            (u.pushforwardFractions p)) := by
          rw [hρ]
    _ = ((u.pushforwardFractions p).Q.map ρ.f) := by
      simpa using
        MorphismProperty.RightFraction.map_s_comp_map
          ρ ((u.pushforwardFractions p).Q)
          (Localization.inverts ((u.pushforwardFractions p).Q)
            (u.pushforwardFractions p))

/-- Helper for Lemma 8.12.6: once the numerator `ρ.f` is rewritten as a literal source-side
map over `gρ ≫ sourceBase`, the source strongly-cartesian precomposition lift factors it
uniquely. -/
theorem pushforwardProjectionIsoComma_fraction_source_factor
    {Y₀ : u ₚₚ p} {V : D}
    (sourceBase : V ⟶ Y₀.fst.left)
    {Z₀ : u ₚₚ p}
    (ρ : (u.pushforwardFractions p).RightFraction Z₀ Y₀)
    (gρ : ρ.X'.fst.left ⟶ V)
    (hbase : (pushforwardSourceProjection u p).map ρ.f = gρ ≫ sourceBase) :
    ∃! χ₀ : ρ.X' ⟶ pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase,
      (pushforwardSourceProjection u p).IsHomLift gρ χ₀ ∧
        χ₀ ≫ pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase = ρ.f := by
  let α := pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase
  letI : (pushforwardSourceProjection u p).IsStronglyCartesian sourceBase α :=
    pushforwardSource_precompose_isStronglyCartesian (u := u) (p := p) Y₀ sourceBase
  have hρlift :
      (pushforwardSourceProjection u p).IsHomLift (gρ ≫ sourceBase) ρ.f := by
    -- The rewritten numerator equation is exactly the source-level hom-lift condition.
    refine IsHomLift.of_fac' (pushforwardSourceProjection u p) (gρ ≫ sourceBase) ρ.f rfl rfl ?_
    simpa using hbase
  -- Apply the source universal property before any localization packaging is reintroduced.
  simpa [α] using
    @Functor.IsStronglyCartesian.universal_property' _ _ _ _
      (pushforwardSourceProjection u p) _ _ _ _ sourceBase α inferInstance
      _ gρ ρ.f hρlift

/-- Helper for Lemma 8.12.6: the explicit source chart on `Q.obj (Q.objPreimage X)` is exactly
the strict-model image of the canonical preimage comparison isomorphism. -/
theorem pushforwardProjectionIsoComma_preimage_chart_eq_whiskered
    (X : u ₚ p) :
    let Q := (u.pushforwardFractions p).Q
    let chartX :
        pushforwardProjectionStrictObj (u := u) (p := p)
            (Q.obj (Q.objPreimage X)) ⟶
          (pushforwardSourceProjection u p).obj (Q.objPreimage X) :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p)
          (Q.obj (Q.objPreimage X))).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
          (Q.objPreimage X)).hom
    (pushforwardProjectionStrictObjIso (u := u) (p := p)
        (Q.obj (Q.objPreimage X))).hom ≫ chartX =
      (pushforwardProjectionStrictObjIso (u := u) (p := p)
        (Q.obj (Q.objPreimage X))).hom ≫
          (pushforwardProjectionStrict u p).map ((Q.objObjPreimageIso X).hom) := by
  dsimp
  let Q := (u.pushforwardFractions p).Q
  let chartX :
      pushforwardProjectionStrictObj (u := u) (p := p)
          (Q.obj (Q.objPreimage X)) ⟶
        (pushforwardSourceProjection u p).obj (Q.objPreimage X) :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p)
        (Q.obj (Q.objPreimage X))).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
        (Q.objPreimage X)).hom
  let eX :
      (u.pushforwardProjection p).obj X ≅
        (u.pushforwardProjection p).obj (Q.obj (Q.objPreimage X)) :=
    (u.pushforwardProjection p).mapIso ((Q.objObjPreimageIso X).symm)
  have htarget :
      (u.pushforwardProjection p).map ((Q.objObjPreimageIso X).hom) ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) X).hom =
        (pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
          (Q.objPreimage X)).hom := by
    -- Expand only the comparison isomorphism on `X` and cancel the `mapIso` for the preimage
    -- chart before touching the source-side localization comparison.
    change
      (u.pushforwardProjection p).map ((Q.objObjPreimageIso X).hom) ≫
          (eX.hom ≫
            (pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
              (Q.objPreimage X)).hom) =
        (pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
          (Q.objPreimage X)).hom
    simpa [eX, Category.assoc] using
      Iso.inv_hom_id_assoc eX
        ((pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
          (Q.objPreimage X)).hom)
  have hchart :
      (pushforwardProjectionStrictObjIso (u := u) (p := p)
          (Q.obj (Q.objPreimage X))).hom ≫ chartX =
        (pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
          (Q.objPreimage X)).hom := by
    -- The explicit source chart is designed so that precomposing by the strict chart cancels.
    simpa [chartX] using
      pushforwardProjectionStrict_obj_Q_obj_chart_cancel
        (u := u) (p := p) (Q.objPreimage X)
  have hmap :
      (pushforwardProjectionStrictObjIso (u := u) (p := p)
          (Q.obj (Q.objPreimage X))).hom ≫
          (pushforwardProjectionStrict u p).map ((Q.objObjPreimageIso X).hom) =
        (pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
          (Q.objPreimage X)).hom := by
    -- Naturality moves the strict-model map back to the canonical localized projection.
    exact
      (pushforwardProjectionStrictIso_naturality
        (u := u) (p := p) ((Q.objObjPreimageIso X).hom)).symm.trans htarget
  -- Both whiskered composites identify with the same fixed source chart.
  exact hchart.trans hmap.symm

/-- Helper for Lemma 8.12.6: the explicit source chart on `Q.obj (Q.objPreimage X)` is exactly
the strict-model image of the canonical preimage comparison isomorphism. -/
theorem pushforwardProjectionIsoComma_preimage_chart_eq
    (X : u ₚ p) :
    let Q := (u.pushforwardFractions p).Q
    let chartX :
        pushforwardProjectionStrictObj (u := u) (p := p)
            (Q.obj (Q.objPreimage X)) ⟶
          (pushforwardSourceProjection u p).obj (Q.objPreimage X) :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p)
          (Q.obj (Q.objPreimage X))).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
          (Q.objPreimage X)).hom
    chartX =
      (pushforwardProjectionStrict u p).map ((Q.objObjPreimageIso X).hom) := by
  dsimp
  let Q := (u.pushforwardFractions p).Q
  let chartX :
      pushforwardProjectionStrictObj (u := u) (p := p)
          (Q.obj (Q.objPreimage X)) ⟶
        (pushforwardSourceProjection u p).obj (Q.objPreimage X) :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p)
        (Q.obj (Q.objPreimage X))).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
        (Q.objPreimage X)).hom
  -- Route correction: cancel the source strict chart after proving the whiskered identity, rather
  -- than trying to normalize the unwhiskered equality directly.
  apply (cancel_epi
    ((pushforwardProjectionStrictObjIso (u := u) (p := p)
      (Q.obj (Q.objPreimage X))).hom)).1
  -- The whiskered theorem already rewrites both composites to the same source-side chart.
  simpa [Q, chartX, Category.assoc] using
    pushforwardProjectionIsoComma_preimage_chart_eq_whiskered
      (u := u) (p := p) X

/-- Helper for Lemma 8.12.6: postcomposing the inverse strict image of the chosen preimage
comparison with the explicit source chart cancels back to the identity on the strict model of
`X`. -/
theorem pushforwardProjectionIsoComma_preimage_chart_inv_comp
    (X : u ₚ p) :
    let Q := (u.pushforwardFractions p).Q
    let chartX :
        pushforwardProjectionStrictObj (u := u) (p := p)
            (Q.obj (Q.objPreimage X)) ⟶
          (pushforwardSourceProjection u p).obj (Q.objPreimage X) :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p)
          (Q.obj (Q.objPreimage X))).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
          (Q.objPreimage X)).hom
    (pushforwardProjectionStrict u p).map ((Q.objObjPreimageIso X).inv) ≫ chartX =
      𝟙 (pushforwardProjectionStrictObj (u := u) (p := p) X) := by
  dsimp
  let Q := (u.pushforwardFractions p).Q
  let chartX :
      pushforwardProjectionStrictObj (u := u) (p := p)
          (Q.obj (Q.objPreimage X)) ⟶
        (pushforwardSourceProjection u p).obj (Q.objPreimage X) :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p)
        (Q.obj (Q.objPreimage X))).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
        (Q.objPreimage X)).hom
  let eX : Q.obj (Q.objPreimage X) ≅ X := Q.objObjPreimageIso X
  have hchartX :
      chartX = (pushforwardProjectionStrict u p).map eX.hom := by
    -- The explicit chart is the strict-model image of the canonical preimage comparison.
    simpa [Q, chartX, eX] using
      pushforwardProjectionIsoComma_preimage_chart_eq
        (u := u) (p := p) X
  calc
    (pushforwardProjectionStrict u p).map eX.inv ≫ chartX
        = (pushforwardProjectionStrict u p).map eX.inv ≫
            (pushforwardProjectionStrict u p).map eX.hom := by
              simpa [hchartX]
    _ = (pushforwardProjectionStrict u p).map (eX.inv ≫ eX.hom) := by
          rw [← Functor.map_comp]
    _ = 𝟙 (pushforwardProjectionStrictObj (u := u) (p := p) X) := by
          simpa using
            pushforwardProjectionStrict_map_id (u := u) (p := p) X

/-- Helper for Lemma 8.12.6: the comma square of `θ` becomes a literal equality in the strict
source charts after canceling the stored comparison isomorphism on `Z`. -/
theorem pushforwardProjectionIsoComma_right_component_strict_eq
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    [IsIso Z.obj.hom]
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
    (θ : Z ⟶ Y)
    (hθ : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift (g ≫ f) θ) :
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    (pushforwardProjectionStrict u p).map θ.hom.right =
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
        (asIso Z.obj.hom).inv ≫ g ≫ sourceBase := by
  let sourceBase :=
    pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
  let eZ := pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right
  let eY := pushforwardProjectionStrictObjIso (u := u) (p := p) Y.obj.right
  have hleft :
      θ.hom.left = g ≫ f :=
    pushforwardProjectionIsoCommaProjection_homLift_left
      (u := u) (p := p) f g θ hθ
  have hcomma :
      Z.obj.hom ≫ (u.pushforwardProjection p).map θ.hom.right =
        g ≫ f ≫ Y.obj.hom := by
    -- The raw comma square becomes literal after replacing the left component by `g ≫ f`.
    exact θ.hom.w.symm.trans <| by
      simpa [hleft, Category.assoc]
  have hwhisker :
      Z.obj.hom ≫ (u.pushforwardProjection p).map θ.hom.right ≫ eY.hom =
        g ≫ sourceBase := by
    -- Whisker the literal comma equality by the fixed target chart on `Y`.
    calc
      Z.obj.hom ≫ (u.pushforwardProjection p).map θ.hom.right ≫ eY.hom =
          (g ≫ f ≫ Y.obj.hom) ≫ eY.hom := by
            simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eY.hom) hcomma
      _ = g ≫ sourceBase := by
            let targetBase :=
              (u.pushforwardProjection p).map
                (((u.pushforwardFractions p).Q.objObjPreimageIso Y.obj.right).inv)
            have htarget :
                (g ≫ f ≫ Y.obj.hom) ≫ eY.hom =
                  g ≫ f ≫ Y.obj.hom ≫ targetBase := by
              dsimp [targetBase, eY, pushforwardProjectionStrictObjIso]
              simpa only [Category.assoc] using
                Category.comp_id (g ≫ f ≫ Y.obj.hom ≫ targetBase)
            have hsource :
                g ≫ sourceBase = g ≫ f ≫ Y.obj.hom ≫ targetBase := by
              dsimp [sourceBase, pushforwardProjection_precompose_sourceBase]
              change g ≫ ((f ≫ Y.obj.hom) ≫ targetBase) =
                g ≫ f ≫ Y.obj.hom ≫ targetBase
              simp only [Category.assoc]
            exact htarget.trans hsource.symm
  have hnat :
      Z.obj.hom ≫ (u.pushforwardProjection p).map θ.hom.right ≫ eY.hom =
        Z.obj.hom ≫ eZ.hom ≫ (pushforwardProjectionStrict u p).map θ.hom.right := by
    -- Naturality of the strict chart converts the localized right component to the strict model.
    simpa [eZ, eY, Category.assoc] using
      congrArg (fun k ↦ Z.obj.hom ≫ k)
        (pushforwardProjectionStrictIso_naturality
          (u := u) (p := p) θ.hom.right)
  have hstrict :
      Z.obj.hom ≫ eZ.hom ≫ (pushforwardProjectionStrict u p).map θ.hom.right =
        g ≫ sourceBase := by
    -- The whiskered comma square now has the source-proof shape needed for cancellation.
    exact hnat.symm.trans hwhisker
  -- Cancel the stored comparison isomorphisms on `Z` to isolate the strict right component.
  change (pushforwardProjectionStrict u p).map θ.hom.right =
    eZ.inv ≫ (asIso Z.obj.hom).inv ≫ g ≫ sourceBase
  simpa [Category.assoc] using
    congrArg (fun k ↦ eZ.inv ≫ (asIso Z.obj.hom).inv ≫ k) hstrict

/-- Helper for Lemma 8.12.6: after whiskering the transported right component by the target
source chart, the endpoint preimage charts collapse to the literal source chart on `Z`. -/
theorem pushforwardProjectionIsoComma_preimage_chart_comp_right_component
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    (θ : Z ⟶ Y) :
    let Q := (u.pushforwardFractions p).Q
    let chartZ :
        pushforwardProjectionStrictObj (u := u) (p := p)
            (Q.obj (Q.objPreimage Z.obj.right)) ⟶
          (pushforwardSourceProjection u p).obj (Q.objPreimage Z.obj.right) :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p)
          (Q.obj (Q.objPreimage Z.obj.right))).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
          (Q.objPreimage Z.obj.right)).hom
    let chartY :
        pushforwardProjectionStrictObj (u := u) (p := p)
            (Q.obj (Q.objPreimage Y.obj.right)) ⟶
          (pushforwardSourceProjection u p).obj (Q.objPreimage Y.obj.right) :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p)
          (Q.obj (Q.objPreimage Y.obj.right))).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
          (Q.objPreimage Y.obj.right)).hom
    (pushforwardProjectionStrict u p).map
        ((Q.objObjPreimageIso Z.obj.right).hom ≫
          θ.hom.right ≫
            (Q.objObjPreimageIso Y.obj.right).inv) ≫
      chartY =
        chartZ ≫ (pushforwardProjectionStrict u p).map θ.hom.right := by
  dsimp
  let Q := (u.pushforwardFractions p).Q
  let chartZ :
      pushforwardProjectionStrictObj (u := u) (p := p)
          (Q.obj (Q.objPreimage Z.obj.right)) ⟶
        (pushforwardSourceProjection u p).obj (Q.objPreimage Z.obj.right) :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p)
        (Q.obj (Q.objPreimage Z.obj.right))).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
        (Q.objPreimage Z.obj.right)).hom
  let chartY :
      pushforwardProjectionStrictObj (u := u) (p := p)
          (Q.obj (Q.objPreimage Y.obj.right)) ⟶
        (pushforwardSourceProjection u p).obj (Q.objPreimage Y.obj.right) :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p)
        (Q.obj (Q.objPreimage Y.obj.right))).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
        (Q.objPreimage Y.obj.right)).hom
  let a := (Q.objObjPreimageIso Z.obj.right).hom
  let b := θ.hom.right
  let c := (Q.objObjPreimageIso Y.obj.right).inv
  let F := pushforwardProjectionStrict u p
  have hcompabc : F.map (a ≫ b ≫ c) = F.map (a ≫ b) ≫ F.map c := by
    -- Reassociate the strictified composite through the functor law before touching charts.
    simpa using F.map_comp (a ≫ b) c
  have hcompab : F.map (a ≫ b) = F.map a ≫ F.map b := by
    -- The middle factor is then exposed by one more functoriality rewrite.
    simpa using F.map_comp a b
  have hchartY :
      F.map c ≫ chartY =
        𝟙 (pushforwardProjectionStrictObj (u := u) (p := p) Y.obj.right) := by
    -- Cancel the trailing preimage comparison on `Y` against the explicit source chart.
    simpa [F, Q, c, chartY] using
      pushforwardProjectionIsoComma_preimage_chart_inv_comp
        (u := u) (p := p) Y.obj.right
  have hchartZ :
      chartZ = F.map a := by
    -- The leading source chart on `Z` is exactly the strict image of the chosen preimage map.
    simpa [F, Q, a, chartZ] using
      pushforwardProjectionIsoComma_preimage_chart_eq
        (u := u) (p := p) Z.obj.right
  calc
    F.map (a ≫ b ≫ c) ≫
      chartY =
        (F.map (a ≫ b) ≫ F.map c) ≫ chartY := by
          rw [hcompabc]
    _ =
        F.map a ≫ F.map b ≫ F.map c ≫ chartY := by
          rw [hcompab]
          simp only [Category.assoc]
    _ =
        F.map a ≫ F.map b ≫ 𝟙 (pushforwardProjectionStrictObj (u := u) (p := p) Y.obj.right) := by
          simpa [Category.assoc] using congrArg (fun k ↦ F.map a ≫ F.map b ≫ k) hchartY
    _ = F.map a ≫ F.map b := by
          simpa [F, pushforwardProjectionStrict, pushforwardProjectionStrictMap, Category.assoc]
    _ = chartZ ≫ F.map b := by
          simpa [Category.assoc] using congrArg (fun k ↦ k ≫ F.map b) hchartZ.symm

/-- Helper for Lemma 8.12.6: once the literal source charts on `Q.obj A` and `Q.obj B` are
named, the strict image of `Q.map k` matches the source projection on the nose. -/
theorem pushforwardProjectionIsoComma_fraction_source_chart_endpoints_exact
    {A B : u ₚₚ p} (k : A ⟶ B) :
    let Q := (u.pushforwardFractions p).Q
    let chartA :
        pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj A) ⟶
          (pushforwardSourceProjection u p).obj A :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj A)).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).hom
    let chartB :
        pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj B) ⟶
          (pushforwardSourceProjection u p).obj B :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj B)).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).hom
    (pushforwardProjectionStrict u p).map (Q.map k) ≫ chartB =
      chartA ≫ (pushforwardSourceProjection u p).map k := by
  dsimp
  -- Route correction: record the endpoint chart rewrite in the exact assoc-normalized form
  -- consumed by the fixed-denominator chart calculation, instead of asking `simpa` to bridge
  -- local chart abbreviations later.
  simpa using pushforwardProjectionStrict_map_Q_map (u := u) (p := p) k

/-- Helper for Lemma 8.12.6: after applying the strict source chart to the fixed-denominator
numerator equality, both sides acquire the same leading source-chart factor on `ρ.X'`. -/
theorem pushforwardProjectionIsoComma_fraction_source_chart_middle_eq
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    [IsIso Z.obj.hom]
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
    (θ : Z ⟶ Y)
    (hθ : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift (g ≫ f) θ)
    (ρ : (u.pushforwardFractions p).RightFraction
      (((u.pushforwardFractions p).Q).objPreimage Z.obj.right)
      (((u.pushforwardFractions p).Q).objPreimage Y.obj.right)) :
    let Q := (u.pushforwardFractions p).Q
    let chartZ :
        pushforwardProjectionStrictObj (u := u) (p := p)
            (Q.obj (Q.objPreimage Z.obj.right)) ⟶
          (pushforwardSourceProjection u p).obj (Q.objPreimage Z.obj.right) :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p)
          (Q.obj (Q.objPreimage Z.obj.right))).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
          (Q.objPreimage Z.obj.right)).hom
    let chartY :
        pushforwardProjectionStrictObj (u := u) (p := p)
            (Q.obj (Q.objPreimage Y.obj.right)) ⟶
          (pushforwardSourceProjection u p).obj (Q.objPreimage Y.obj.right) :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p)
          (Q.obj (Q.objPreimage Y.obj.right))).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
          (Q.objPreimage Y.obj.right)).hom
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    (pushforwardProjectionStrict u p).map
        ((Q.objObjPreimageIso Z.obj.right).hom ≫
          θ.hom.right ≫
            (Q.objObjPreimageIso Y.obj.right).inv) ≫
      chartY =
        chartZ ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
            (asIso Z.obj.hom).inv ≫ g ≫ sourceBase := by
  dsimp
  let Q := (u.pushforwardFractions p).Q
  let chartZ :
      pushforwardProjectionStrictObj (u := u) (p := p)
          (Q.obj (Q.objPreimage Z.obj.right)) ⟶
        (pushforwardSourceProjection u p).obj (Q.objPreimage Z.obj.right) :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p)
        (Q.obj (Q.objPreimage Z.obj.right))).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
        (Q.objPreimage Z.obj.right)).hom
  let chartY :
      pushforwardProjectionStrictObj (u := u) (p := p)
          (Q.obj (Q.objPreimage Y.obj.right)) ⟶
        (pushforwardSourceProjection u p).obj (Q.objPreimage Y.obj.right) :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p)
        (Q.obj (Q.objPreimage Y.obj.right))).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
        (Q.objPreimage Y.obj.right)).hom
  let sourceBase :=
    pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
  have hadapter :
      (pushforwardProjectionStrict u p).map
          ((Q.objObjPreimageIso Z.obj.right).hom ≫
            θ.hom.right ≫
              (Q.objObjPreimageIso Y.obj.right).inv) ≫
        chartY =
          chartZ ≫ (pushforwardProjectionStrict u p).map θ.hom.right := by
    -- Package the endpoint chart rewrites before replacing the strict middle factor.
    simpa [Q, chartZ, chartY] using
      pushforwardProjectionIsoComma_preimage_chart_comp_right_component
        (u := u) (p := p) Y θ
  have hstrict :
      (pushforwardProjectionStrict u p).map θ.hom.right =
        (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
          (asIso Z.obj.hom).inv ≫ g ≫ sourceBase := by
    -- The remaining middle term is exactly the strictified comma-square identity.
    let h :=
      pushforwardProjectionIsoComma_right_component_strict_eq
        (u := u) (p := p) Y f g θ hθ
    exact h
  calc
    (pushforwardProjectionStrict u p).map
        ((Q.objObjPreimageIso Z.obj.right).hom ≫
          θ.hom.right ≫
            (Q.objObjPreimageIso Y.obj.right).inv) ≫
      chartY =
        chartZ ≫ (pushforwardProjectionStrict u p).map θ.hom.right := hadapter
    _ =
        chartZ ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
            (asIso Z.obj.hom).inv ≫ g ≫ sourceBase := by
          simpa [Category.assoc] using congrArg (fun k ↦ chartZ ≫ k) hstrict

/-- Helper for Lemma 8.12.6: after applying the strict source chart to the fixed-denominator
numerator equality, both sides acquire the same leading source-chart factor on `ρ.X'`. -/
theorem pushforwardProjectionIsoComma_fraction_source_chart_eq
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    [IsIso Z.obj.hom]
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
    (θ : Z ⟶ Y)
    (hθ : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift (g ≫ f) θ)
    (ρ : (u.pushforwardFractions p).RightFraction
      (((u.pushforwardFractions p).Q).objPreimage Z.obj.right)
      (((u.pushforwardFractions p).Q).objPreimage Y.obj.right))
    (hρnum :
      ((u.pushforwardFractions p).Q.map ρ.s) ≫
          (((u.pushforwardFractions p).Q.objObjPreimageIso Z.obj.right).hom ≫
            θ.hom.right ≫
              ((u.pushforwardFractions p).Q.objObjPreimageIso Y.obj.right).inv) =
        ((u.pushforwardFractions p).Q.map ρ.f)) :
    let Q := (u.pushforwardFractions p).Q
    let chart :
        pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj ρ.X') ⟶
          (pushforwardSourceProjection u p).obj ρ.X' :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj ρ.X')).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p) ρ.X').hom
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    let gρ : ρ.X'.fst.left ⟶ V :=
      ρ.s.fst.left ≫
        (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
          (asIso Z.obj.hom).inv ≫ g
    chart ≫ (pushforwardSourceProjection u p).map ρ.f =
      chart ≫ gρ ≫ sourceBase := by
  dsimp
  let Q := (u.pushforwardFractions p).Q
  let chart :
      pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj ρ.X') ⟶
        (pushforwardSourceProjection u p).obj ρ.X' :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj ρ.X')).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p) ρ.X').hom
  let chartZ :
      pushforwardProjectionStrictObj (u := u) (p := p)
          (Q.obj (Q.objPreimage Z.obj.right)) ⟶
        (pushforwardSourceProjection u p).obj (Q.objPreimage Z.obj.right) :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p)
        (Q.obj (Q.objPreimage Z.obj.right))).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
        (Q.objPreimage Z.obj.right)).hom
  let chartY :
      pushforwardProjectionStrictObj (u := u) (p := p)
          (Q.obj (Q.objPreimage Y.obj.right)) ⟶
        (pushforwardSourceProjection u p).obj (Q.objPreimage Y.obj.right) :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p)
        (Q.obj (Q.objPreimage Y.obj.right))).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
        (Q.objPreimage Y.obj.right)).hom
  let sourceBase :=
    pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
  let middle :=
    (Q.objObjPreimageIso Z.obj.right).hom ≫
      θ.hom.right ≫
        (Q.objObjPreimageIso Y.obj.right).inv
  let F := pushforwardProjectionStrict u p
  have hs :
      F.map (Q.map ρ.s) ≫ chartZ =
        chart ≫ (pushforwardSourceProjection u p).map ρ.s := by
    -- Rewrite the denominator endpoint in the literal source-chart form needed below.
    simpa [Q, chart, chartZ, F] using
      pushforwardProjectionIsoComma_fraction_source_chart_endpoints_exact
        (u := u) (p := p) (k := ρ.s)
  have hf :
      F.map (Q.map ρ.f) ≫ chartY =
        chart ≫ (pushforwardSourceProjection u p).map ρ.f := by
    -- Rewrite the numerator endpoint against the same source chart on `ρ.X'`.
    simpa [Q, chart, chartY, F] using
      pushforwardProjectionIsoComma_fraction_source_chart_endpoints_exact
        (u := u) (p := p) (k := ρ.f)
  have hmiddle :
      F.map middle ≫ chartY =
        chartZ ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
            (asIso Z.obj.hom).inv ≫ g ≫ sourceBase := by
    -- Replace the transported right component by the strict source-side comma-square identity.
    let h :=
      pushforwardProjectionIsoComma_fraction_source_chart_middle_eq
        (u := u) (p := p) Y f g θ hθ ρ
    simpa [Q, chartZ, chartY, middle, F] using h
  -- Route correction: this `calc` uses only the exact endpoint and middle chart lemmas, so no
  -- `simpa` has to bridge mismatched local chart abbreviations anymore.
  calc
    chart ≫ (pushforwardSourceProjection u p).map ρ.f =
        F.map (Q.map ρ.f) ≫ chartY := by
          simpa using hf.symm
    _ = F.map ((Q.map ρ.s) ≫ middle) ≫ chartY := by
          rw [hρnum]
    _ = (F.map (Q.map ρ.s) ≫ F.map middle) ≫ chartY := by
          rw [Functor.map_comp]
    _ = F.map (Q.map ρ.s) ≫ (F.map middle ≫ chartY) := by
          simp [Category.assoc]
    _ =
        F.map (Q.map ρ.s) ≫
          (chartZ ≫
            (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
              (asIso Z.obj.hom).inv ≫ g ≫ sourceBase) := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ F.map (Q.map ρ.s) ≫ k) hmiddle
    _ =
        (F.map (Q.map ρ.s) ≫ chartZ) ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
            (asIso Z.obj.hom).inv ≫ g ≫ sourceBase := by
          simp [Category.assoc]
    _ =
        (chart ≫ (pushforwardSourceProjection u p).map ρ.s) ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
            (asIso Z.obj.hom).inv ≫ g ≫ sourceBase := by
          rw [hs]
    _ =
        chart ≫
          (ρ.s.fst.left ≫
            (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
              (asIso Z.obj.hom).inv ≫ g) ≫
            sourceBase := by
          simp [pushforwardSourceProjection, Category.assoc]

/-- Helper for Lemma 8.12.6: canceling the common source chart from
`pushforwardProjectionIsoComma_fraction_source_chart_eq` produces the literal source-base
equation needed by the strongly-cartesian source lift. -/
theorem pushforwardProjectionIsoComma_fraction_source_chart_base_eq
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    [IsIso Z.obj.hom]
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
    (θ : Z ⟶ Y)
    (hθ : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift (g ≫ f) θ)
    (ρ : (u.pushforwardFractions p).RightFraction
      (((u.pushforwardFractions p).Q).objPreimage Z.obj.right)
      (((u.pushforwardFractions p).Q).objPreimage Y.obj.right))
    (hρnum :
      ((u.pushforwardFractions p).Q.map ρ.s) ≫
          (((u.pushforwardFractions p).Q.objObjPreimageIso Z.obj.right).hom ≫
            θ.hom.right ≫
              ((u.pushforwardFractions p).Q.objObjPreimageIso Y.obj.right).inv) =
        ((u.pushforwardFractions p).Q.map ρ.f)) :
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    let gρ : ρ.X'.fst.left ⟶ V :=
      ρ.s.fst.left ≫
        (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
          (asIso Z.obj.hom).inv ≫ g
    (pushforwardSourceProjection u p).map ρ.f = gρ ≫ sourceBase := by
  dsimp
  let Q := (u.pushforwardFractions p).Q
  let chart :
      pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj ρ.X') ⟶
        (pushforwardSourceProjection u p).obj ρ.X' :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj ρ.X')).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p) ρ.X').hom
  let sourceBase :=
    pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
  let gρ : ρ.X'.fst.left ⟶ V :=
    ρ.s.fst.left ≫
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
        (asIso Z.obj.hom).inv ≫ g
  have hchart :
      chart ≫ (pushforwardSourceProjection u p).map ρ.f =
        chart ≫ gρ ≫ sourceBase := by
    -- Reuse the exact charted numerator equality before canceling the common source chart.
    let h :=
      pushforwardProjectionIsoComma_fraction_source_chart_eq
        (u := u) (p := p) Y f g θ hθ ρ hρnum
    simpa [Q, chart, gρ] using h
  -- The chart on `ρ.X'` is the hom of an isomorphism, so right-cancellation recovers the
  -- literal source-base equation.
  exact (cancel_epi chart).1 <| by
    simpa [gρ, sourceBase, pushforwardProjection_precompose_sourceBase,
      Category.assoc, Category.comp_id] using hchart

end Functor

end

end CategoryTheory
