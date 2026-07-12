import StacksProject_2024.Chap08.Lemma_8_12_6.FractionSourceCharts
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

/-- Helper for Lemma 8.12.6: the chosen base comparison isomorphism on the localized
precomposition object is definitionally the source-side localization comparison on the literal
source precomposition object `T₀`. -/
theorem pushforwardProjection_precompose_modelBaseIso_eq_source_baseIso_hom
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y) :
    let Q := (u.pushforwardFractions p).Q
    let Y₀ := Q.objPreimage Y.obj.right
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
    (pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)).hom =
      (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) T₀).hom := by
  -- Route correction: the model-base comparison is now defined to be the canonical source chart
  -- on the literal source precomposition object `T₀`, so the equality is definitional.
  dsimp [pushforwardProjection_precompose_modelBaseIso, pushforwardProjection_precompose_sourceBase,
    pushforwardProjection_obj_Q_obj_base]

/-- Helper for Lemma 8.12.6: the inverse chosen base comparison on the localized precomposition
object is definitionally the inverse source-side localization comparison on `T₀`. -/
theorem pushforwardProjection_precompose_modelBaseIso_eq_source_baseIso_inv
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y) :
    let Q := (u.pushforwardFractions p).Q
    let Y₀ := Q.objPreimage Y.obj.right
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
    (pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)).inv =
      (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) T₀).inv := by
  -- The inverse comparison is equally definitional after the canonical source-chart rewrite.
  dsimp [pushforwardProjection_precompose_modelBaseIso, pushforwardProjection_precompose_sourceBase,
    pushforwardProjection_obj_Q_obj_base]

/-- Helper for Lemma 8.12.6: composing the descended fixed-fraction candidate with the chosen
denominator `ρ.s` cancels the endpoint preimage chart and recovers the numerator `χ₀`. -/
theorem pushforwardProjectionIsoComma_fixed_fraction_descended_numerator
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    (ρ : (u.pushforwardFractions p).RightFraction
      (((u.pushforwardFractions p).Q).objPreimage Z.obj.right)
      (((u.pushforwardFractions p).Q).objPreimage Y.obj.right))
    {χ₀ : ρ.X' ⟶
      pushforwardSourcePrecomposeObj (u := u) (p := p)
        (((u.pushforwardFractions p).Q).objPreimage Y.obj.right)
        (pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom))} :
    ((u.pushforwardFractions p).Q.map ρ.s) ≫
        ((((u.pushforwardFractions p).Q.objObjPreimageIso Z.obj.right).hom) ≫
          ((((u.pushforwardFractions p).Q.objObjPreimageIso Z.obj.right).inv) ≫
            (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
              ((u.pushforwardFractions p).Q)
              (Localization.inverts ((u.pushforwardFractions p).Q)
                (u.pushforwardFractions p)))) =
      ((u.pushforwardFractions p).Q.map χ₀) := by
  -- Expand the descended candidate once, so the preimage chart cancels before clearing the
  -- common denominator `ρ.s`.
  calc
    ((u.pushforwardFractions p).Q.map ρ.s) ≫
        ((((u.pushforwardFractions p).Q.objObjPreimageIso Z.obj.right).hom) ≫
          ((((u.pushforwardFractions p).Q.objObjPreimageIso Z.obj.right).inv) ≫
            (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
              ((u.pushforwardFractions p).Q)
              (Localization.inverts ((u.pushforwardFractions p).Q)
                (u.pushforwardFractions p)))) =
      ((u.pushforwardFractions p).Q.map ρ.s) ≫
        (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
          ((u.pushforwardFractions p).Q)
          (Localization.inverts ((u.pushforwardFractions p).Q)
            (u.pushforwardFractions p)) := by
            simp [Category.assoc]
    _ = ((u.pushforwardFractions p).Q.map χ₀) := by
          simpa using
            MorphismProperty.RightFraction.map_s_comp_map
              (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀)
              ((u.pushforwardFractions p).Q)
              (Localization.inverts ((u.pushforwardFractions p).Q)
                (u.pushforwardFractions p))

/-- Helper for Lemma 8.12.6: the remaining raw universal-property step is the source-chart
descent of the right component through a fixed right-fraction representative. -/
theorem pushforwardProjectionIsoComma_fixed_fraction_candidate_denominator_eq
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    (ρ : (u.pushforwardFractions p).RightFraction
      (((u.pushforwardFractions p).Q).objPreimage Z.obj.right)
      (((u.pushforwardFractions p).Q).objPreimage Y.obj.right)) :
    let Q := (u.pushforwardFractions p).Q
    let Y₀ := Q.objPreimage Y.obj.right
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
    ∀ {χ₀ : ρ.X' ⟶ T₀},
      let χr :
          Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
            (u := u) (p := p) Y f).obj.right :=
        (Q.objObjPreimageIso Z.obj.right).inv ≫
          (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
            Q (Localization.inverts Q (u.pushforwardFractions p))
      (Q.map ρ.s) ≫ ((Q.objObjPreimageIso Z.obj.right).hom ≫ χr) = Q.map χ₀ := by
  -- Normalize the `let`-bound descended candidate once, then reuse the previously proved
  -- numerator identity for the fixed denominator `ρ.s`.
  dsimp
  intro chi0
  simpa using
    pushforwardProjectionIsoComma_fixed_fraction_descended_numerator
      (u := u) (p := p) Y f ρ (χ₀ := chi0)

/-- Helper for Lemma 8.12.6: the remaining raw universal-property step is the source-chart
descent of the right component through a fixed right-fraction representative. -/
theorem pushforwardProjectionIsoComma_fixed_fraction_candidate_chart_whisker
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    (ρ : (u.pushforwardFractions p).RightFraction
      (((u.pushforwardFractions p).Q).objPreimage Z.obj.right)
      (((u.pushforwardFractions p).Q).objPreimage Y.obj.right)) :
    let Q := (u.pushforwardFractions p).Q
    let Y₀ := Q.objPreimage Y.obj.right
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
    let chartρ :
        pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj ρ.X') ⟶
          (pushforwardSourceProjection u p).obj ρ.X' :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj ρ.X')).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p) ρ.X').hom
    let chartZ :
        pushforwardProjectionStrictObj (u := u) (p := p)
            (Q.obj (Q.objPreimage Z.obj.right)) ⟶
          (pushforwardProjectionStrict u p).obj Z.obj.right :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p)
          (Q.obj (Q.objPreimage Z.obj.right))).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
          (Q.objPreimage Z.obj.right)).hom
    let chartT :
        pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj T₀) ⟶
          (pushforwardSourceProjection u p).obj T₀ :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj T₀)).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p) T₀).hom
    ∀ {χ₀ : ρ.X' ⟶ T₀},
      let χr :
          Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
            (u := u) (p := p) Y f).obj.right :=
        (Q.objObjPreimageIso Z.obj.right).inv ≫
          (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
            Q (Localization.inverts Q (u.pushforwardFractions p))
      (pushforwardProjectionStrict u p).map (Q.map ρ.s) ≫ chartZ ≫
          (pushforwardProjectionStrict u p).map χr ≫ chartT =
        chartρ ≫ (pushforwardSourceProjection u p).map χ₀ := by
  -- Route correction: rewrite the endpoint chart on `Z` to the literal preimage comparison,
  -- then turn the cleared-denominator equality into a strict/source-chart identity.
  dsimp
  intro chi0
  let Q := (u.pushforwardFractions p).Q
  let Y₀ := Q.objPreimage Y.obj.right
  let sourceBase :=
    pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
  let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
  let chartρ :
      pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj ρ.X') ⟶
        (pushforwardSourceProjection u p).obj ρ.X' :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj ρ.X')).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p) ρ.X').hom
  let chartZ :
      pushforwardProjectionStrictObj (u := u) (p := p)
          (Q.obj (Q.objPreimage Z.obj.right)) ⟶
        (pushforwardProjectionStrict u p).obj Z.obj.right :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p)
        (Q.obj (Q.objPreimage Z.obj.right))).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
        (Q.objPreimage Z.obj.right)).hom
  let chartT :
      pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj T₀) ⟶
        (pushforwardSourceProjection u p).obj T₀ :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj T₀)).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p) T₀).hom
  let χr :
      Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
        (u := u) (p := p) Y f).obj.right :=
    (Q.objObjPreimageIso Z.obj.right).inv ≫
      (MorphismProperty.RightFraction.mk ρ.s ρ.hs chi0).map
        Q (Localization.inverts Q (u.pushforwardFractions p))
  let F := pushforwardProjectionStrict u p
  have hdenom :
      (Q.map ρ.s) ≫ ((Q.objObjPreimageIso Z.obj.right).hom ≫ χr) = Q.map chi0 := by
    -- Clear the fixed denominator `ρ.s` before rewriting either endpoint chart.
    simpa [Q, Y₀, sourceBase, T₀, χr] using
      pushforwardProjectionIsoComma_fixed_fraction_candidate_denominator_eq
        (u := u) (p := p) Y f ρ (χ₀ := chi0)
  have hchartZ :
      chartZ = F.map ((Q.objObjPreimageIso Z.obj.right).hom) := by
    -- The explicit source chart on the chosen preimage of `Z.obj.right` is literal.
    simpa [Q, chartZ, F] using
      pushforwardProjectionIsoComma_preimage_chart_eq
        (u := u) (p := p) Z.obj.right
  have hχ₀ :
      F.map (Q.map chi0) ≫ chartT =
        chartρ ≫ (pushforwardSourceProjection u p).map chi0 := by
    -- The source chart on `ρ.X'` and `T₀` is exactly the endpoint rewrite for `χ₀`.
    simpa [Q, chartρ, chartT, F] using
      pushforwardProjectionIsoComma_fraction_source_chart_endpoints_exact
        (u := u) (p := p) (k := chi0)
  have hdenom_map' :
      F.map ((Q.map ρ.s) ≫ ((Q.objObjPreimageIso Z.obj.right).hom ≫ χr)) ≫ chartT =
        F.map (Q.map chi0) ≫ chartT := by
    exact congrArg (fun k ↦ F.map k ≫ chartT) hdenom
  have hdenom_map :
      F.map (Q.map ρ.s) ≫ F.map ((Q.objObjPreimageIso Z.obj.right).hom) ≫ F.map χr ≫ chartT =
        F.map (Q.map chi0) ≫ chartT := by
    -- Expand the functorial composite on the left before applying the cleared-denominator rewrite.
    calc
      F.map (Q.map ρ.s) ≫ F.map ((Q.objObjPreimageIso Z.obj.right).hom) ≫ F.map χr ≫ chartT =
          F.map ((Q.map ρ.s) ≫ ((Q.objObjPreimageIso Z.obj.right).hom ≫ χr)) ≫ chartT := by
            simp [Functor.map_comp, Category.assoc]
      _ = F.map (Q.map chi0) ≫ chartT := hdenom_map'
  calc
    F.map (Q.map ρ.s) ≫ chartZ ≫ F.map χr ≫ chartT =
        F.map (Q.map ρ.s) ≫ F.map ((Q.objObjPreimageIso Z.obj.right).hom) ≫
          F.map χr ≫ chartT := by
          simpa [hchartZ, Category.assoc]
    _ = F.map (Q.map chi0) ≫ chartT := hdenom_map
    _ = chartρ ≫ (pushforwardSourceProjection u p).map chi0 := hχ₀

/-- Helper for Lemma 8.12.6: the remaining raw universal-property step is the source-chart
descent of the right component through a fixed right-fraction representative. -/
theorem pushforwardProjectionIsoComma_fixed_fraction_candidate_base_whiskered
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    [IsIso Z.obj.hom]
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
    (ρ : (u.pushforwardFractions p).RightFraction
      (((u.pushforwardFractions p).Q).objPreimage Z.obj.right)
      (((u.pushforwardFractions p).Q).objPreimage Y.obj.right)) :
    let Q := (u.pushforwardFractions p).Q
    let Y₀ := Q.objPreimage Y.obj.right
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
    let gρ : ρ.X'.fst.left ⟶ V :=
      ρ.s.fst.left ≫
        (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
          (asIso Z.obj.hom).inv ≫ g
    let chartT :
        pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj T₀) ⟶
          (pushforwardSourceProjection u p).obj T₀ :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj T₀)).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p) T₀).hom
    ∀ {χ₀ : ρ.X' ⟶ T₀},
      (pushforwardSourceProjection u p).IsHomLift gρ χ₀ →
      let χr :
          Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
            (u := u) (p := p) Y f).obj.right :=
        (Q.objObjPreimageIso Z.obj.right).inv ≫
          (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
            Q (Localization.inverts Q (u.pushforwardFractions p))
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
          (asIso Z.obj.hom).inv ≫ g =
        (pushforwardProjectionStrict u p).map χr ≫ chartT := by
  dsimp
  intro χ₀ hχ₀
  let Q := (u.pushforwardFractions p).Q
  let Y₀ := Q.objPreimage Y.obj.right
  let sourceBase :=
    pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
  let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
  let gρ : ρ.X'.fst.left ⟶ V :=
    ρ.s.fst.left ≫
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
        (asIso Z.obj.hom).inv ≫ g
  let chartρ :
      pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj ρ.X') ⟶
        (pushforwardSourceProjection u p).obj ρ.X' :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj ρ.X')).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p) ρ.X').hom
  let chartZ :
      pushforwardProjectionStrictObj (u := u) (p := p)
          (Q.obj (Q.objPreimage Z.obj.right)) ⟶
        (pushforwardProjectionStrict u p).obj Z.obj.right :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p)
        (Q.obj (Q.objPreimage Z.obj.right))).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
        (Q.objPreimage Z.obj.right)).hom
  let chartT :
      pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj T₀) ⟶
        (pushforwardSourceProjection u p).obj T₀ :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj T₀)).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p) T₀).hom
  let χr :
      Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
        (u := u) (p := p) Y f).obj.right :=
    (Q.objObjPreimageIso Z.obj.right).inv ≫
      (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
        Q (Localization.inverts Q (u.pushforwardFractions p))
  let F := pushforwardProjectionStrict u p
  have hchart :
      F.map (Q.map ρ.s) ≫ chartZ ≫ F.map χr ≫ chartT =
        chartρ ≫ (pushforwardSourceProjection u p).map χ₀ := by
    -- The fixed-denominator chart comparison is already recorded in source-chart form.
    simpa [Q, Y₀, sourceBase, T₀, chartρ, chartZ, chartT, χr, F] using
      pushforwardProjectionIsoComma_fixed_fraction_candidate_chart_whisker
        (u := u) (p := p) Y f ρ (χ₀ := χ₀)
  have hsource_s :
      F.map (Q.map ρ.s) ≫ chartZ =
        chartρ ≫ (pushforwardSourceProjection u p).map ρ.s := by
    -- Rewrite the denominator endpoint against the same source chart on `ρ.X'`.
    simpa [Q, chartρ, chartZ, F] using
      pushforwardProjectionIsoComma_fraction_source_chart_endpoints_exact
        (u := u) (p := p) (k := ρ.s)
  have hχ₀ :
      (pushforwardSourceProjection u p).map χ₀ = gρ := by
    -- The chosen source factor `χ₀` is literally a lift over `gρ`.
    let _ : (pushforwardSourceProjection u p).IsHomLift gρ χ₀ := hχ₀
    simpa [gρ] using
      (IsHomLift.fac' (pushforwardSourceProjection u p) gρ χ₀)
  have hχ₀_chart :
      chartρ ≫ (pushforwardSourceProjection u p).map χ₀ =
        chartρ ≫ (pushforwardSourceProjection u p).map ρ.s ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
            (asIso Z.obj.hom).inv ≫ g := by
    -- Rewrite the source lift equation through the explicit denominator chart.
    simpa [gρ, pushforwardSourceProjection, Category.assoc] using
      congrArg (fun k ↦ chartρ ≫ k) hχ₀
  have hchart_cancel :
      chartρ ≫ (pushforwardSourceProjection u p).map ρ.s ≫ F.map χr ≫ chartT =
        chartρ ≫ (pushforwardSourceProjection u p).map ρ.s ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
            (asIso Z.obj.hom).inv ≫ g := by
    -- Route correction: first align both sides along the common source chart on `ρ.X'`.
    have hleft :
        chartρ ≫ (pushforwardSourceProjection u p).map ρ.s ≫ F.map χr ≫ chartT =
          chartρ ≫ (pushforwardSourceProjection u p).map χ₀ := by
      calc
        chartρ ≫ (pushforwardSourceProjection u p).map ρ.s ≫ F.map χr ≫ chartT =
            F.map (Q.map ρ.s) ≫ chartZ ≫ F.map χr ≫ chartT := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ F.map χr ≫ chartT) hsource_s.symm
        _ = chartρ ≫ (pushforwardSourceProjection u p).map χ₀ := hchart
    exact hleft.trans hχ₀_chart
  have hafter_chart :
      (pushforwardSourceProjection u p).map ρ.s ≫ F.map χr ≫ chartT =
        (pushforwardSourceProjection u p).map ρ.s ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
            (asIso Z.obj.hom).inv ≫ g := by
    -- Cancel the common source chart on `ρ.X'`.
    exact (cancel_epi chartρ).1 <| by
      simpa [Category.assoc] using hchart_cancel
  have hρiso :
      IsIso ((pushforwardSourceProjection u p).map ρ.s) := by
    -- The source projection inverts all allowed denominators.
    simpa [pushforwardSourceProjection] using
      (pushforwardSourceProjection_invertsFractions (u := u) (p := p) ρ.s ρ.hs)
  letI : IsIso ((pushforwardSourceProjection u p).map ρ.s) := hρiso
  have hfinal :
      F.map χr ≫ chartT =
        (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
          (asIso Z.obj.hom).inv ≫ g := by
    -- Cancel the inverted denominator image to recover the unwhiskered strict equality.
    exact (cancel_epi ((pushforwardSourceProjection u p).map ρ.s)).1 <| by
      simpa [Category.assoc] using hafter_chart
  exact hfinal.symm

/-- Helper for Lemma 8.12.6: the target chart on the fixed precomposition object cancels the
strictification isomorphism and leaves the literal source-base comparison. -/
theorem pushforwardProjectionIsoComma_precompose_target_chart_cancel
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y) :
    let Q := (u.pushforwardFractions p).Q
    let Y₀ := Q.objPreimage Y.obj.right
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
    let chartT :
        pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj T₀) ⟶
          (pushforwardSourceProjection u p).obj T₀ :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj T₀)).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p) T₀).hom
    (pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj T₀)).hom ≫ chartT =
      (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) T₀).hom := by
  dsimp
  -- The target chart is exactly the standard strict/source cancellation on `Q.obj T₀`.
  simpa using
    pushforwardProjectionStrict_obj_Q_obj_chart_cancel (u := u) (p := p)
      (pushforwardSourcePrecomposeObj (u := u) (p := p)
        (((u.pushforwardFractions p).Q).objPreimage Y.obj.right)
        (pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom)))

/-- Helper for Lemma 8.12.6: whiskered strict-chart naturality for the fixed target chart moves
the descended right component from the strict model back to the literal localized projection. -/
theorem pushforwardProjectionIsoComma_precompose_target_naturality_whiskered
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    (χr : Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
      (u := u) (p := p) Y f).obj.right) :
    let Q := (u.pushforwardFractions p).Q
    let Y₀ := Q.objPreimage Y.obj.right
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
    let chartT :
        pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj T₀) ⟶
          (pushforwardSourceProjection u p).obj T₀ :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj T₀)).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p) T₀).hom
    ((pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).hom ≫
        (pushforwardProjectionStrict u p).map χr) ≫ chartT =
      (u.pushforwardProjection p).map χr ≫
        (((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj T₀)).hom) ≫ chartT) := by
  dsimp
  let Q := (u.pushforwardFractions p).Q
  let Y₀ := Q.objPreimage Y.obj.right
  let sourceBase :=
    pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
  let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
  let chartT :
      pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj T₀) ⟶
        (pushforwardSourceProjection u p).obj T₀ :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj T₀)).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p) T₀).hom
  -- The whiskered target-side naturality square is the strict chart naturality for `χr`.
  simpa [Q, Y₀, sourceBase, T₀, chartT, Category.assoc] using
    congrArg (fun k ↦ k ≫ chartT)
      (pushforwardProjectionStrictIso_naturality
        (u := u) (p := p) χr).symm

/-- Helper for Lemma 8.12.6: the remaining raw universal-property step is the source-chart
descent of the right component through a fixed right-fraction representative. -/
theorem pushforwardProjectionIsoComma_precompose_target_transport
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    (χr : Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
      (u := u) (p := p) Y f).obj.right) :
    let Q := (u.pushforwardFractions p).Q
    let Y₀ := Q.objPreimage Y.obj.right
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
    let chartT :
        pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj T₀) ⟶
          (pushforwardSourceProjection u p).obj T₀ :=
      ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj T₀)).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p) T₀).hom
    (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).hom ≫
        (pushforwardProjectionStrict u p).map χr ≫ chartT =
      (u.pushforwardProjection p).map χr ≫
        (pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom)).hom := by
  dsimp
  let Q := (u.pushforwardFractions p).Q
  let Y₀ := Q.objPreimage Y.obj.right
  let sourceBase :=
    pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
  let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
  let chartT :
      pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj T₀) ⟶
        (pushforwardSourceProjection u p).obj T₀ :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj T₀)).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p) T₀).hom
  have hnat :
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).hom ≫
          (pushforwardProjectionStrict u p).map χr ≫ chartT =
        (u.pushforwardProjection p).map χr ≫
          (((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj T₀)).hom) ≫ chartT) := by
    -- First isolate the whiskered naturality square for the strict chart on `χr`.
    simpa [Q, Y₀, sourceBase, T₀, chartT, Category.assoc] using
      pushforwardProjectionIsoComma_precompose_target_naturality_whiskered
        (u := u) (p := p) Y f (Z := Z) χr
  have hcancel :
      ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj T₀)).hom) ≫ chartT =
        (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) T₀).hom := by
    -- Then cancel the explicit target chart on the precomposition object.
    simpa [Q, Y₀, sourceBase, T₀, chartT] using
      pushforwardProjectionIsoComma_precompose_target_chart_cancel
        (u := u) (p := p) Y f
  calc
    (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).hom ≫
        (pushforwardProjectionStrict u p).map χr ≫ chartT =
      (u.pushforwardProjection p).map χr ≫
        (((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj T₀)).hom) ≫ chartT) := hnat
    _ =
      (u.pushforwardProjection p).map χr ≫
        (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) T₀).hom := by
          rw [hcancel]
    _ =
      (u.pushforwardProjection p).map χr ≫
        (pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom)).hom := by
          rw [← pushforwardProjection_precompose_modelBaseIso_eq_source_baseIso_hom
            (u := u) (p := p) Y f]
          rfl

/-- Helper for Lemma 8.12.6: the remaining raw universal-property step is the source-chart
descent of the right component through a fixed right-fraction representative. -/
theorem pushforwardProjectionIsoComma_whiskered_source_chart_cancel
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    [IsIso Z.obj.hom]
    {V : D}
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V) :
    let eZ := pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right
    (Z.obj.hom ≫ eZ.hom) ≫ (eZ.inv ≫ (asIso Z.obj.hom).inv ≫ g) = g := by
  -- The whiskered source chart is already in the exact cancellation order:
  -- first remove the strict chart `eZ`, then clear the stored iso-comma chart `Z.obj.hom`.
  let eZ := pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right
  change (Z.obj.hom ≫ eZ.hom) ≫ (eZ.inv ≫ (asIso Z.obj.hom).inv ≫ g) = g
  simp [Category.assoc]

/-- Helper for Lemma 8.12.6: the remaining raw universal-property step is the source-chart
descent of the right component through a fixed right-fraction representative. -/
theorem pushforwardProjectionIsoComma_precomposeObj_hom_comp_target_baseIso_hom
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y) :
    let eT := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
    (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom ≫ eT.hom = 𝟙 V := by
  -- The stored base map on the precomposition object is definitionally the inverse target chart.
  dsimp [pushforwardProjectionIsoComma_precomposeObj]
  simpa [pushforwardProjection_precompose_modelBaseIso] using
    (pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)).inv_hom_id

/-- Helper for Lemma 8.12.6: canceling the bundled target comparison isomorphism `eT` rewrites
the transported target equation into the literal iso-comma base equation. -/

theorem pushforwardProjectionIsoComma_precomposeHom_right_comp_preimage_inv
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y) :
    let Q := (u.pushforwardFractions p).Q
    let Y₀ := Q.objPreimage Y.obj.right
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    ((pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f).hom.right) ≫
        (Q.objObjPreimageIso Y.obj.right).inv =
      Q.map (pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase) := by
  -- Unfold the chosen right component once, then cancel the target preimage comparison.
  dsimp [pushforwardProjectionIsoComma_precomposeHom, pushforwardProjection_precompose_modelHom,
    pushforwardProjection_precompose_sourceBase]
  simp [Category.assoc]

/-- Helper for Lemma 8.12.6: after clearing the fixed denominator `ρ.s`, the descended candidate
and the source factor `χ₀` have the same numerator in the localization. -/
theorem pushforwardProjectionIsoComma_fixed_fraction_candidate_right_denominator_eq
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    (ρ : (u.pushforwardFractions p).RightFraction
      (((u.pushforwardFractions p).Q).objPreimage Z.obj.right)
      (((u.pushforwardFractions p).Q).objPreimage Y.obj.right)) :
    let Q := (u.pushforwardFractions p).Q
    let Y₀ := Q.objPreimage Y.obj.right
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
    ∀ {χ₀ : ρ.X' ⟶ T₀},
      χ₀ ≫ pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase = ρ.f →
      let χr :
          Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
            (u := u) (p := p) Y f).obj.right :=
        (Q.objObjPreimageIso Z.obj.right).inv ≫
          (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
            Q (Localization.inverts Q (u.pushforwardFractions p))
      (Q.map ρ.s) ≫
          (((Q.objObjPreimageIso Z.obj.right).hom ≫ χr ≫
              (pushforwardProjectionIsoComma_precomposeHom
                (u := u) (p := p) Y f).hom.right) ≫
            (Q.objObjPreimageIso Y.obj.right).inv) =
        Q.map ρ.f := by
  dsimp
  intro χ₀ hχ₀
  let Q := (u.pushforwardFractions p).Q
  let Y₀ := Q.objPreimage Y.obj.right
  let sourceBase :=
    pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
  let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
  let χr :
      Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
        (u := u) (p := p) Y f).obj.right :=
    (Q.objObjPreimageIso Z.obj.right).inv ≫
      (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
        Q (Localization.inverts Q (u.pushforwardFractions p))
  have hdenom :
      (Q.map ρ.s) ≫ ((Q.objObjPreimageIso Z.obj.right).hom ≫ χr) = Q.map χ₀ := by
    -- Clear the fixed denominator before inserting the precomposition morphism.
    simpa [Q, Y₀, sourceBase, T₀, χr] using
      pushforwardProjectionIsoComma_fixed_fraction_candidate_denominator_eq
        (u := u) (p := p) Y f ρ (χ₀ := χ₀)
  have hprecomp :
      (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f).hom.right ≫
          (Q.objObjPreimageIso Y.obj.right).inv =
        Q.map (pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase) := by
    -- The stored right component of the precomposition object is exactly the localized source
    -- precomposition morphism once the endpoint chart is canceled.
    simpa [Q, Y₀, sourceBase] using
      pushforwardProjectionIsoComma_precomposeHom_right_comp_preimage_inv
        (u := u) (p := p) Y f
  calc
    (Q.map ρ.s) ≫
        (((Q.objObjPreimageIso Z.obj.right).hom ≫ χr ≫
            (pushforwardProjectionIsoComma_precomposeHom
              (u := u) (p := p) Y f).hom.right) ≫
          (Q.objObjPreimageIso Y.obj.right).inv) =
      ((Q.map ρ.s) ≫ ((Q.objObjPreimageIso Z.obj.right).hom ≫ χr)) ≫
          (pushforwardProjectionIsoComma_precomposeHom
            (u := u) (p := p) Y f).hom.right ≫
            (Q.objObjPreimageIso Y.obj.right).inv := by
            simp [Category.assoc]
    _ =
      Q.map χ₀ ≫
          (pushforwardProjectionIsoComma_precomposeHom
            (u := u) (p := p) Y f).hom.right ≫
            (Q.objObjPreimageIso Y.obj.right).inv := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ k ≫
                  (pushforwardProjectionIsoComma_precomposeHom
                    (u := u) (p := p) Y f).hom.right ≫
                    (Q.objObjPreimageIso Y.obj.right).inv)
                hdenom
    _ =
      Q.map χ₀ ≫ Q.map (pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase) := by
            simpa [Category.assoc] using congrArg (fun k ↦ Q.map χ₀ ≫ k) hprecomp
    _ = Q.map (χ₀ ≫ pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase) := by
          rw [← Functor.map_comp]
    _ = Q.map ρ.f := by
          simpa using congrArg (Q.map) hχ₀

/-- Helper for Lemma 8.12.6: the fixed right-fraction candidate built from the source lift `χ₀`
already satisfies the right-component equation in the iso-comma universal property. -/
theorem pushforwardProjectionIsoComma_fixed_fraction_candidate_right_cancel
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    (ρ : (u.pushforwardFractions p).RightFraction
      (((u.pushforwardFractions p).Q).objPreimage Z.obj.right)
      (((u.pushforwardFractions p).Q).objPreimage Y.obj.right))
    (χr : Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
      (u := u) (p := p) Y f).obj.right)
    (θ : Z ⟶ Y)
    (hχr :
      (((u.pushforwardFractions p).Q).map ρ.s) ≫
          ((((u.pushforwardFractions p).Q).objObjPreimageIso Z.obj.right).hom ≫
              χr ≫
                (pushforwardProjectionIsoComma_precomposeHom
                  (u := u) (p := p) Y f).hom.right) ≫
            (((u.pushforwardFractions p).Q).objObjPreimageIso Y.obj.right).inv =
        ((u.pushforwardFractions p).Q).map ρ.f)
    (hθ :
      (((u.pushforwardFractions p).Q).map ρ.s) ≫
          ((((u.pushforwardFractions p).Q).objObjPreimageIso Z.obj.right).hom ≫
              θ.hom.right) ≫
            (((u.pushforwardFractions p).Q).objObjPreimageIso Y.obj.right).inv =
        ((u.pushforwardFractions p).Q).map ρ.f) :
    χr ≫ (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f).hom.right =
      θ.hom.right := by
  dsimp
  let Q := (u.pushforwardFractions p).Q
  have hmiddle :
      (((Q.objObjPreimageIso Z.obj.right).hom ≫
            χr ≫
              (pushforwardProjectionIsoComma_precomposeHom
                (u := u) (p := p) Y f).hom.right) ≫
          (Q.objObjPreimageIso Y.obj.right).inv) =
        (((Q.objObjPreimageIso Z.obj.right).hom ≫ θ.hom.right) ≫
          (Q.objObjPreimageIso Y.obj.right).inv) := by
    have hρiso : IsIso (Q.map ρ.s) := by
      simpa [Q] using Localization.inverts Q (u.pushforwardFractions p) ρ.s ρ.hs
    letI : IsIso (Q.map ρ.s) := hρiso
    -- First clear the common denominator `ρ.s`.
    exact (cancel_epi (Q.map ρ.s)).1 <| by
      simpa [Category.assoc] using hχr.trans hθ.symm
  have hleft :
      (Q.objObjPreimageIso Z.obj.right).hom ≫
          χr ≫
            (pushforwardProjectionIsoComma_precomposeHom
              (u := u) (p := p) Y f).hom.right =
        (Q.objObjPreimageIso Z.obj.right).hom ≫ θ.hom.right := by
    -- Then cancel the target endpoint preimage isomorphism.
    exact (cancel_mono ((Q.objObjPreimageIso Y.obj.right).inv)).1 <| by
      simpa [Category.assoc] using hmiddle
  -- Finally cancel the source endpoint preimage isomorphism.
  exact (cancel_epi ((Q.objObjPreimageIso Z.obj.right).hom)).1 <| by
    simpa [Category.assoc] using hleft

/-- Helper for Lemma 8.12.6: the fixed right-fraction candidate built from the source lift `χ₀`
has the same right component as the original iso-comma morphism. -/
theorem pushforwardProjectionIsoComma_fixed_fraction_candidate_right
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
    let Q := (u.pushforwardFractions p).Q
    let Y₀ := Q.objPreimage Y.obj.right
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
    ∀ {χ₀ : ρ.X' ⟶ T₀},
      χ₀ ≫ pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase = ρ.f →
      let χr :
          Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
            (u := u) (p := p) Y f).obj.right :=
        (Q.objObjPreimageIso Z.obj.right).inv ≫
          (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
            Q (Localization.inverts Q (u.pushforwardFractions p))
      χr ≫ (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f).hom.right =
        θ.hom.right := by
  -- Normalize the fixed denominator on both the candidate and target side, then cancel it.
  dsimp
  intro χ₀ hχ₀
  let Q := (u.pushforwardFractions p).Q
  let Y₀ := Q.objPreimage Y.obj.right
  let sourceBase :=
    pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
  let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
  let χr :
      Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
        (u := u) (p := p) Y f).obj.right :=
    (Q.objObjPreimageIso Z.obj.right).inv ≫
      (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
        Q (Localization.inverts Q (u.pushforwardFractions p))
  have hχr :
      (Q.map ρ.s) ≫
          ((((Q.objObjPreimageIso Z.obj.right).hom ≫ χr ≫
                (pushforwardProjectionIsoComma_precomposeHom
                  (u := u) (p := p) Y f).hom.right) ≫
              (Q.objObjPreimageIso Y.obj.right).inv)) =
        Q.map ρ.f := by
    -- The candidate numerator identity is already proved with the fixed denominator `ρ.s`.
    simpa [Q, Y₀, sourceBase, T₀, χr] using
      pushforwardProjectionIsoComma_fixed_fraction_candidate_right_denominator_eq
        (u := u) (p := p) Y f ρ (χ₀ := χ₀) hχ₀
  have hθ' :
      (Q.map ρ.s) ≫
          ((((Q.objObjPreimageIso Z.obj.right).hom ≫ θ.hom.right) ≫
              (Q.objObjPreimageIso Y.obj.right).inv)) =
        Q.map ρ.f := by
    -- Reuse the fixed-denominator numerator identity already proved for the chosen
    -- representative `ρ` of `θ.hom.right`.
    simpa [Q, Category.assoc] using
      pushforwardProjectionIsoComma_fraction_denominator_comp_eq_numerator
        (u := u) (p := p) Y f g θ ρ hρ
  exact
    pushforwardProjectionIsoComma_fixed_fraction_candidate_right_cancel
      (u := u) (p := p) Y f ρ χr θ hχr hθ'

/-- Helper for Lemma 8.12.6: any competing right component can be represented by a source
right fraction into the fixed source chart `T₀`, and its postcomposition with the source
precomposition map is already fraction-equivalent to the chosen fixed representative `ρ`. -/
theorem pushforwardProjectionIsoComma_competing_right_component_fraction_relation
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
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
            (u.pushforwardFractions p)))
    (χr' : Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
      (u := u) (p := p) Y f).obj.right)
    (hχr' :
      χr' ≫ (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f).hom.right =
        θ.hom.right) :
    let Q := (u.pushforwardFractions p).Q
    let Y₀ := Q.objPreimage Y.obj.right
    let sourceBase :=
      pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
    let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
    let α := pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase
    ∃ σ : (u.pushforwardFractions p).RightFraction (Q.objPreimage Z.obj.right) T₀,
      ((Q.objObjPreimageIso Z.obj.right).hom ≫ χr') =
        σ.map Q (Localization.inverts Q (u.pushforwardFractions p)) ∧
      MorphismProperty.RightFractionRel
        (MorphismProperty.RightFraction.mk σ.s σ.hs (σ.f ≫ α))
        (MorphismProperty.RightFraction.mk ρ.s ρ.hs ρ.f) := by
  classical
  dsimp
  let Q := (u.pushforwardFractions p).Q
  let Y₀ := Q.objPreimage Y.obj.right
  let sourceBase :=
    pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
  let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
  let α := pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase
  obtain ⟨σ, hσ⟩ :=
    Localization.exists_rightFraction Q (u.pushforwardFractions p)
      ((Q.objObjPreimageIso Z.obj.right).hom ≫ χr')
  refine ⟨σ, hσ, ?_⟩
  -- Compare the represented composite with the fixed representative `ρ` after postcomposing
  -- by the source precomposition map `α`.
  apply
    (MorphismProperty.RightFraction.map_eq_iff
      (W := u.pushforwardFractions p)
      (L := Q)
      (MorphismProperty.RightFraction.mk σ.s σ.hs (σ.f ≫ α))
      (MorphismProperty.RightFraction.mk ρ.s ρ.hs ρ.f)).mp
  have hprecomp :
      (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f).hom.right ≫
          (Q.objObjPreimageIso Y.obj.right).inv =
        Q.map α := by
    -- This identifies the stored right component of the precomposition object with the source
    -- precomposition map in the fixed source chart.
    simpa [Q, Y₀, sourceBase, α] using
      pushforwardProjectionIsoComma_precomposeHom_right_comp_preimage_inv
        (u := u) (p := p) Y f
  have hσcomp :
      σ.map Q (Localization.inverts Q (u.pushforwardFractions p)) ≫ Q.map α =
        (((Q.objObjPreimageIso Z.obj.right).hom ≫ χr') ≫
            (pushforwardProjectionIsoComma_precomposeHom
              (u := u) (p := p) Y f).hom.right) ≫
          (Q.objObjPreimageIso Y.obj.right).inv := by
    calc
      σ.map Q (Localization.inverts Q (u.pushforwardFractions p)) ≫ Q.map α =
        (((Q.objObjPreimageIso Z.obj.right).hom ≫ χr')) ≫ Q.map α := by
          rw [hσ]
      _ =
        (((Q.objObjPreimageIso Z.obj.right).hom ≫ χr') ≫
            (pushforwardProjectionIsoComma_precomposeHom
              (u := u) (p := p) Y f).hom.right) ≫
          (Q.objObjPreimageIso Y.obj.right).inv := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ ((Q.objObjPreimageIso Z.obj.right).hom ≫ χr') ≫ k)
                hprecomp.symm
  calc
    (MorphismProperty.RightFraction.mk σ.s σ.hs (σ.f ≫ α)).map
        Q (Localization.inverts Q (u.pushforwardFractions p)) =
      σ.map Q (Localization.inverts Q (u.pushforwardFractions p)) ≫ Q.map α := by
        simp [MorphismProperty.RightFraction.map, Functor.map_comp, Category.assoc]
    _ =
      (((Q.objObjPreimageIso Z.obj.right).hom ≫ χr') ≫
          (pushforwardProjectionIsoComma_precomposeHom
            (u := u) (p := p) Y f).hom.right) ≫
        (Q.objObjPreimageIso Y.obj.right).inv := by
          exact hσcomp
    _ =
      (((Q.objObjPreimageIso Z.obj.right).hom ≫ θ.hom.right) ≫
        (Q.objObjPreimageIso Y.obj.right).inv) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ ((Q.objObjPreimageIso Z.obj.right).hom ≫ k) ≫
                (Q.objObjPreimageIso Y.obj.right).inv)
              hχr'
    _ =
      ρ.map Q (Localization.inverts Q (u.pushforwardFractions p)) := by
          simpa [Category.assoc] using hρ
    _ =
      (MorphismProperty.RightFraction.mk ρ.s ρ.hs ρ.f).map
        Q (Localization.inverts Q (u.pushforwardFractions p)) := by
          rfl

/-- Helper for Lemma 8.12.6: unpacking the right-fraction relation between the competitor roof
and the fixed roof yields the textbook common refinement data directly. -/
theorem pushforwardProjectionIsoComma_competing_right_component_common_refinement
    {X₀ T₀ Y₀ : u ₚₚ p}
    (ρ : (u.pushforwardFractions p).RightFraction X₀ Y₀)
    (σ : (u.pushforwardFractions p).RightFraction X₀ T₀)
    (α : T₀ ⟶ Y₀)
    (hσρ :
      MorphismProperty.RightFractionRel
        (MorphismProperty.RightFraction.mk σ.s σ.hs (σ.f ≫ α))
        (MorphismProperty.RightFraction.mk ρ.s ρ.hs ρ.f)) :
    ∃ (A : u ₚₚ p) (aσ : A ⟶ σ.X') (aρ : A ⟶ ρ.X'),
      aσ ≫ σ.s = aρ ≫ ρ.s ∧
        aσ ≫ σ.f ≫ α = aρ ≫ ρ.f ∧
        (u.pushforwardFractions p) (aσ ≫ σ.s) := by
  -- `RightFractionRel` is already the common-refinement datum required by the source proof.
  rcases hσρ with ⟨A, aσ, aρ, hdenom, hnum, hmem⟩
  refine ⟨A, aσ, aρ, hdenom, ?_, hmem⟩
  -- Reassociate the numerator comparison into the source-proof order.
  simpa [Category.assoc] using hnum

end Functor

end

end CategoryTheory
