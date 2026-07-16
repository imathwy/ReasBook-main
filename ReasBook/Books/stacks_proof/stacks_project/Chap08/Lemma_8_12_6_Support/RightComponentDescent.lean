import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_27_14
import stacks_proof.stacks_project.Chap08.Lemma_8_12_5
import stacks_proof.stacks_project.Chap08.Lemma_8_12_6.Index

open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

namespace Functor

open scoped Functor

variable (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.6 Support: canceling the bundled target comparison isomorphism `eT` rewrites the transported target equation into the literal iso-comma base equation. -/
theorem pushforwardProjectionIsoComma_target_base_transport_cancel_bundled
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
    (χr : Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
      (u := u) (p := p) Y f).obj.right) :
    let eT := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
    g = Z.obj.hom ≫ (u.pushforwardProjection p).map χr ≫ eT.hom ↔
      g ≫ (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom =
        Z.obj.hom ≫ (u.pushforwardProjection p).map χr := by
  dsimp
  let eT := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
    (f ≫ Y.obj.hom)
  have hT_hom :
      (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom =
        eT.inv := by
    rfl
  have hT_inv_hom :
      (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom ≫
        eT.hom = 𝟙 V := by
    simpa [eT] using
      (pushforwardProjectionIsoComma_precomposeObj_hom_comp_target_baseIso_hom
        (u := u) (p := p) Y f)
  have hT_hom_inv :
      eT.hom ≫ (pushforwardProjectionIsoComma_precomposeObj
        (u := u) (p := p) Y f).obj.hom = 𝟙 _ := by
    simpa [eT, hT_hom] using eT.hom_inv_id
  constructor
  · intro h
    -- Postcompose by the stored inverse chart; the two sides then cancel to the literal base map.
    calc
      g ≫ (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom
          = (Z.obj.hom ≫ (u.pushforwardProjection p).map χr ≫ eT.hom) ≫
              (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom := by
            simpa [eT] using
              congrArg
                (fun k ↦ k ≫
                  (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom)
                h
      _ = Z.obj.hom ≫ (u.pushforwardProjection p).map χr := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ (Z.obj.hom ≫ (u.pushforwardProjection p).map χr) ≫ k)
                hT_hom_inv
  · intro h
    -- Reinsert the target chart and use the literal base equation.
    calc
      g = g ≫ ((pushforwardProjectionIsoComma_precomposeObj
            (u := u) (p := p) Y f).obj.hom ≫ eT.hom) := by
          simpa using
            (congrArg (fun k ↦ g ≫ k) hT_inv_hom).symm
      _ = (g ≫ (pushforwardProjectionIsoComma_precomposeObj
            (u := u) (p := p) Y f).obj.hom) ≫ eT.hom := by
          simp [Category.assoc]
      _ = Z.obj.hom ≫ (u.pushforwardProjection p).map χr ≫ eT.hom := by
          simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eT.hom) h
/-- Helper for Lemma 8.12.6 Support: the remaining raw universal-property step is the source-chart descent of the right component through a fixed right-fraction representative. -/
theorem pushforwardProjectionIsoComma_fixed_fraction_candidate_base_transport_cancel
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    [IsIso Z.obj.hom]
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
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
    (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
        (asIso Z.obj.hom).inv ≫ g =
      (pushforwardProjectionStrict u p).map χr ≫ chartT ↔
    g ≫ (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom =
      Z.obj.hom ≫ (u.pushforwardProjection p).map χr := by
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
  let eZ := pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right
  let eT := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
    (f ≫ Y.obj.hom)
  have hleft_cancel :
      (Z.obj.hom ≫ eZ.hom) ≫ (eZ.inv ≫ (asIso Z.obj.hom).inv ≫ g) = g := by
    simpa [eZ] using
      pushforwardProjectionIsoComma_whiskered_source_chart_cancel
        (u := u) (p := p) (Z := Z) g
  have hright_transport :
      eZ.hom ≫ (pushforwardProjectionStrict u p).map χr ≫ chartT =
        (u.pushforwardProjection p).map χr ≫ eT.hom := by
    simpa [Q, Y₀, sourceBase, T₀, chartT, eZ, eT, Category.assoc] using
      pushforwardProjectionIsoComma_precompose_target_transport
        (u := u) (p := p) Y f (Z := Z) χr
  have hright_with_source :
      (Z.obj.hom ≫ eZ.hom) ≫ (pushforwardProjectionStrict u p).map χr ≫ chartT =
        Z.obj.hom ≫ (u.pushforwardProjection p).map χr ≫ eT.hom := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ Z.obj.hom ≫ k) hright_transport
  have hstrict_iff :
      eZ.inv ≫ (asIso Z.obj.hom).inv ≫ g =
          (pushforwardProjectionStrict u p).map χr ≫ chartT ↔
        g = Z.obj.hom ≫ (u.pushforwardProjection p).map χr ≫ eT.hom := by
    constructor
    · intro h
      -- Precompose the strict equation with the source chart; both charts then cancel.
      have hpre :
          (Z.obj.hom ≫ eZ.hom) ≫ (eZ.inv ≫ (asIso Z.obj.hom).inv ≫ g) =
            (Z.obj.hom ≫ eZ.hom) ≫ (pushforwardProjectionStrict u p).map χr ≫ chartT := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ (Z.obj.hom ≫ eZ.hom) ≫ k) h
      exact hleft_cancel.symm.trans (hpre.trans hright_with_source)
    · intro h
      -- Conversely, source-chart cancellation reduces the strict equation to the transported one.
      apply (cancel_epi (Z.obj.hom ≫ eZ.hom)).1
      exact hleft_cancel.trans (h.trans hright_with_source.symm)
  have htarget :=
    pushforwardProjectionIsoComma_target_base_transport_cancel_bundled
      (u := u) (p := p) Y f g χr
  exact (Iff.trans hstrict_iff htarget)
/-- Helper for Lemma 8.12.6 Support: the remaining raw universal-property step is the source-chart descent of the right component through a fixed right-fraction representative. -/
theorem pushforwardProjectionIsoComma_fixed_fraction_candidate_base
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
    ∀ {χ₀ : ρ.X' ⟶ T₀},
      (pushforwardSourceProjection u p).IsHomLift gρ χ₀ →
      let χr :
          Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
            (u := u) (p := p) Y f).obj.right :=
        (Q.objObjPreimageIso Z.obj.right).inv ≫
          (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
            Q (Localization.inverts Q (u.pushforwardFractions p))
      g ≫ (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom =
        Z.obj.hom ≫ (u.pushforwardProjection p).map χr := by
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
  let χr :
      Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
        (u := u) (p := p) Y f).obj.right :=
    (Q.objObjPreimageIso Z.obj.right).inv ≫
      (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
        Q (Localization.inverts Q (u.pushforwardFractions p))
  exact
    (pushforwardProjectionIsoComma_fixed_fraction_candidate_base_transport_cancel
      (u := u) (p := p) Y f g χr).mp <|
      (pushforwardProjectionIsoComma_fixed_fraction_candidate_base_whiskered
        (u := u) (p := p) Y f g ρ (χ₀ := χ₀) hχ₀)
/-- Helper for Lemma 8.12.6 Support: the fixed right-fraction candidate built from the source lift `χ₀` already satisfies the right-component equation in the iso-comma universal property. -/
theorem pushforwardProjectionIsoComma_competing_fraction_source_lift
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    [IsIso Z.obj.hom]
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
    (χr' : Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
      (u := u) (p := p) Y f).obj.right)
    (hbase :
      g ≫ (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom =
        Z.obj.hom ≫ (u.pushforwardProjection p).map χr')
    (σ : (u.pushforwardFractions p).RightFraction
      (((u.pushforwardFractions p).Q).objPreimage Z.obj.right)
      (pushforwardSourcePrecomposeObj (u := u) (p := p)
        (((u.pushforwardFractions p).Q).objPreimage Y.obj.right)
        (pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom))))
    (hσ :
      (((u.pushforwardFractions p).Q.objObjPreimageIso Z.obj.right).hom ≫ χr') =
        σ.map ((u.pushforwardFractions p).Q)
          (Localization.inverts ((u.pushforwardFractions p).Q)
            (u.pushforwardFractions p))) :
    let gσ : σ.X'.fst.left ⟶ V :=
      σ.s.fst.left ≫
        (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
          (asIso Z.obj.hom).inv ≫ g
    (pushforwardSourceProjection u p).IsHomLift gσ σ.f := by
  dsimp
  let Q := (u.pushforwardFractions p).Q
  let Y₀ := Q.objPreimage Y.obj.right
  let sourceBase :=
    pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
  let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
  let gσ : σ.X'.fst.left ⟶ V :=
    σ.s.fst.left ≫
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
        (asIso Z.obj.hom).inv ≫ g
  let chartσ :
      pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj σ.X') ⟶
        (pushforwardSourceProjection u p).obj σ.X' :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj σ.X')).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p) σ.X').hom
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
  let F := pushforwardProjectionStrict u p
  have hstrict' :
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
          (asIso Z.obj.hom).inv ≫ g =
        (pushforwardProjectionStrict u p).map χr' ≫ chartT := by
    exact
      (pushforwardProjectionIsoComma_fixed_fraction_candidate_base_transport_cancel
        (u := u) (p := p) Y f g χr').mpr hbase
  have hstrict :
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
          (asIso Z.obj.hom).inv ≫ g =
        F.map χr' ≫ chartT := by
    simpa [F] using hstrict'
  have hchartZ :
      chartZ = F.map ((Q.objObjPreimageIso Z.obj.right).hom) := by
    -- The chart on the selected preimage of `Z` is the strict projection image of that chart.
    simpa [Q, chartZ, F] using
      pushforwardProjectionIsoComma_preimage_chart_eq
        (u := u) (p := p) Z.obj.right
  have hdenom :
      Q.map σ.s ≫ ((Q.objObjPreimageIso Z.obj.right).hom ≫ χr') = Q.map σ.f := by
    calc
      Q.map σ.s ≫ ((Q.objObjPreimageIso Z.obj.right).hom ≫ χr') =
          Q.map σ.s ≫
            σ.map Q (Localization.inverts Q (u.pushforwardFractions p)) := by
            rw [hσ]
      _ = Q.map σ.f := by
            simpa using
              MorphismProperty.RightFraction.map_s_comp_map σ Q
                (Localization.inverts Q (u.pushforwardFractions p))
  have hdenom_map :
      F.map (Q.map σ.s) ≫ F.map ((Q.objObjPreimageIso Z.obj.right).hom) ≫
          F.map χr' ≫ chartT =
        F.map (Q.map σ.f) ≫ chartT := by
    calc
      F.map (Q.map σ.s) ≫ F.map ((Q.objObjPreimageIso Z.obj.right).hom) ≫
          F.map χr' ≫ chartT =
        F.map (Q.map σ.s ≫ ((Q.objObjPreimageIso Z.obj.right).hom ≫ χr')) ≫
          chartT := by
          simp [Functor.map_comp, Category.assoc]
      _ = F.map (Q.map σ.f) ≫ chartT := by
          rw [hdenom]
  have htarget_chart :
      F.map (Q.map σ.f) ≫ chartT =
        chartσ ≫ (pushforwardSourceProjection u p).map σ.f := by
    -- The numerator endpoint is read in the same source chart on `σ.X'` and `T₀`.
    simpa [Q, chartσ, chartT, F] using
      pushforwardProjectionIsoComma_fraction_source_chart_endpoints_exact
        (u := u) (p := p) (k := σ.f)
  have hchart :
      F.map (Q.map σ.s) ≫ chartZ ≫ F.map χr' ≫ chartT =
        chartσ ≫ (pushforwardSourceProjection u p).map σ.f := by
    calc
      F.map (Q.map σ.s) ≫ chartZ ≫ F.map χr' ≫ chartT =
          F.map (Q.map σ.s) ≫ F.map ((Q.objObjPreimageIso Z.obj.right).hom) ≫
            F.map χr' ≫ chartT := by
            simpa [hchartZ, Category.assoc]
      _ = F.map (Q.map σ.f) ≫ chartT := hdenom_map
      _ = chartσ ≫ (pushforwardSourceProjection u p).map σ.f := htarget_chart
  have hsource_s :
      F.map (Q.map σ.s) ≫ chartZ =
        chartσ ≫ (pushforwardSourceProjection u p).map σ.s := by
    simpa [Q, chartσ, chartZ, F] using
      pushforwardProjectionIsoComma_fraction_source_chart_endpoints_exact
        (u := u) (p := p) (k := σ.s)
  have hchartEq :
      chartσ ≫ (pushforwardSourceProjection u p).map σ.f =
        chartσ ≫ (pushforwardSourceProjection u p).map σ.s ≫
          ((pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
            (asIso Z.obj.hom).inv ≫ g) := by
    calc
      chartσ ≫ (pushforwardSourceProjection u p).map σ.f =
          F.map (Q.map σ.s) ≫ chartZ ≫ F.map χr' ≫ chartT := hchart.symm
      _ =
          F.map (Q.map σ.s) ≫ chartZ ≫
            ((pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
              (asIso Z.obj.hom).inv ≫ g) := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ F.map (Q.map σ.s) ≫ chartZ ≫ k) hstrict.symm
      _ =
          chartσ ≫ (pushforwardSourceProjection u p).map σ.s ≫
            ((pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
              (asIso Z.obj.hom).inv ≫ g) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ k ≫
                  ((pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
                    (asIso Z.obj.hom).inv ≫ g))
                hsource_s
  have hmap : (pushforwardSourceProjection u p).map σ.f = gσ := by
    have hcancel := (cancel_epi chartσ).1 hchartEq
    simpa [gσ, pushforwardSourceProjection, Category.assoc] using hcancel
  exact
    IsHomLift.of_fac' (pushforwardSourceProjection u p) gσ σ.f rfl rfl <|
      by simpa using hmap

section

omit [p.IsFibered] [HasPullbacks C] [HasEqualizers C]
  [PreservesLimitsOfShape WalkingCospan u]
  [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.6 Support: after passing to the common refinement, the competitor numerator and the fixed numerator lie over the same base map. -/
theorem pushforwardProjectionIsoComma_common_refinement_lifts_have_same_base
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    [IsIso Z.obj.hom]
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
    (ρ : (u.pushforwardFractions p).RightFraction
      (((u.pushforwardFractions p).Q).objPreimage Z.obj.right)
      (((u.pushforwardFractions p).Q).objPreimage Y.obj.right))
    (σ : (u.pushforwardFractions p).RightFraction
      (((u.pushforwardFractions p).Q).objPreimage Z.obj.right)
      (pushforwardSourcePrecomposeObj (u := u) (p := p)
        (((u.pushforwardFractions p).Q).objPreimage Y.obj.right)
        (pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom))))
    {χ₀ :
      ρ.X' ⟶ pushforwardSourcePrecomposeObj (u := u) (p := p)
        (((u.pushforwardFractions p).Q).objPreimage Y.obj.right)
        (pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom))}
    (hσlift :
      let gσ : σ.X'.fst.left ⟶ V :=
        σ.s.fst.left ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
            (asIso Z.obj.hom).inv ≫ g
      (pushforwardSourceProjection u p).IsHomLift gσ σ.f)
    (hχ₀ :
      let gρ : ρ.X'.fst.left ⟶ V :=
        ρ.s.fst.left ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
            (asIso Z.obj.hom).inv ≫ g
      (pushforwardSourceProjection u p).IsHomLift gρ χ₀)
    (A : u ₚₚ p) (aσ : A ⟶ σ.X') (aρ : A ⟶ ρ.X')
    (hdenom : aσ ≫ σ.s = aρ ≫ ρ.s) :
    let gA : A.fst.left ⟶ V :=
      (aρ ≫ ρ.s).fst.left ≫
        (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
          (asIso Z.obj.hom).inv ≫ g
    (pushforwardSourceProjection u p).IsHomLift gA (aσ ≫ σ.f) ∧
      (pushforwardSourceProjection u p).IsHomLift gA (aρ ≫ χ₀) := by
  dsimp
  let P := pushforwardSourceProjection u p
  let gσ : σ.X'.fst.left ⟶ V :=
    σ.s.fst.left ≫
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
        (asIso Z.obj.hom).inv ≫ g
  let gρ : ρ.X'.fst.left ⟶ V :=
    ρ.s.fst.left ≫
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
        (asIso Z.obj.hom).inv ≫ g
  let gA : A.fst.left ⟶ V :=
    (aρ ≫ ρ.s).fst.left ≫
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
        (asIso Z.obj.hom).inv ≫ g
  have hdenom_left :
      aσ.fst.left ≫ σ.s.fst.left = (aρ ≫ ρ.s).fst.left := by
    simpa [Category.assoc] using congrArg (fun k ↦ k.fst.left) hdenom
  have hbaseσ : P.map aσ ≫ gσ = gA := by
    -- The common-refinement equality identifies the two denominator base maps.
    simpa [P, gσ, gA, pushforwardSourceProjection, Category.assoc] using
      congrArg
        (fun k ↦ k ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
            (asIso Z.obj.hom).inv ≫ g)
        hdenom_left
  have hbaseρ : P.map aρ ≫ gρ = gA := by
    simp [P, gρ, gA, pushforwardSourceProjection, Category.assoc]
  constructor
  · -- The competitor numerator remains a lift after precomposition by `aσ`.
    change P.IsHomLift gA (aσ ≫ σ.f)
    rw [← hbaseσ]
    letI : P.IsHomLift (P.map aσ) aσ := inferInstance
    letI : P.IsHomLift gσ σ.f := by
      simpa [P, gσ] using hσlift
    exact
      @CategoryTheory.IsHomLift.comp _ _ _ _ P _ _ _ _ _ _ (P.map aσ) gσ aσ σ.f
        inferInstance (by simpa [P, gσ] using hσlift)
  · -- The fixed numerator has the same base after precomposition by `aρ`.
    change P.IsHomLift gA (aρ ≫ χ₀)
    rw [← hbaseρ]
    letI : P.IsHomLift (P.map aρ) aρ := inferInstance
    letI : P.IsHomLift gρ χ₀ := by
      simpa [P, gρ] using hχ₀
    exact
      @CategoryTheory.IsHomLift.comp _ _ _ _ P _ _ _ _ _ _ (P.map aρ) gρ aρ χ₀
        inferInstance (by simpa [P, gρ] using hχ₀)

end

/-- Helper for Lemma 8.12.6 Support: uniqueness for the descended right component reduces to the source-faithful common-refinement comparison of the competitor roof with the fixed denominator `ρ`. -/
theorem pushforwardProjectionIsoComma_descended_right_component_unique_of_fixed_fraction
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    [IsIso Z.obj.hom]
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
    let gρ : ρ.X'.fst.left ⟶ V :=
      ρ.s.fst.left ≫
        (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
          (asIso Z.obj.hom).inv ≫ g
    ∀ {χ₀ : ρ.X' ⟶ T₀},
      (pushforwardSourceProjection u p).IsHomLift gρ χ₀ →
      χ₀ ≫ pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase = ρ.f →
      let χr :
          Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
            (u := u) (p := p) Y f).obj.right :=
        (Q.objObjPreimageIso Z.obj.right).inv ≫
          (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
            Q (Localization.inverts Q (u.pushforwardFractions p))
      ∀ {χr' : Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
          (u := u) (p := p) Y f).obj.right},
        g ≫ (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom =
          Z.obj.hom ≫ (u.pushforwardProjection p).map χr' →
        χr' ≫ (pushforwardProjectionIsoComma_precomposeHom
          (u := u) (p := p) Y f).hom.right =
          θ.hom.right →
        χr' = χr := by
  dsimp
  intro χ₀ hχ₀ hχ₀comp χr' hbase hright
  let Q := (u.pushforwardFractions p).Q
  let Y₀ := Q.objPreimage Y.obj.right
  let sourceBase :=
    pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
  let T₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
  let α := pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase
  let gρ : ρ.X'.fst.left ⟶ V :=
    ρ.s.fst.left ≫
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
        (asIso Z.obj.hom).inv ≫ g
  let χr :
      Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
        (u := u) (p := p) Y f).obj.right :=
    (Q.objObjPreimageIso Z.obj.right).inv ≫
      (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
        Q (Localization.inverts Q (u.pushforwardFractions p))
  obtain ⟨σ, hσ, hσρ⟩ :=
    pushforwardProjectionIsoComma_competing_right_component_fraction_relation
      (u := u) (p := p) Y f θ ρ hρ χr' hright
  have hσlift :
      (pushforwardSourceProjection u p).IsHomLift
        (σ.s.fst.left ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
            (asIso Z.obj.hom).inv ≫ g)
        σ.f := by
    simpa [Q, Y₀, sourceBase, T₀] using
      pushforwardProjectionIsoComma_competing_fraction_source_lift
        (u := u) (p := p) Y f g χr' hbase σ hσ
  obtain ⟨A, aσ, aρ, hdenom, hnum, hmem⟩ :=
    pushforwardProjectionIsoComma_competing_right_component_common_refinement
      (u := u) (p := p) ρ σ α hσρ
  have hlifts :=
    pushforwardProjectionIsoComma_common_refinement_lifts_have_same_base
      (u := u) (p := p) Y f g ρ σ (χ₀ := χ₀) hσlift hχ₀ A aσ aρ hdenom
  let P := pushforwardSourceProjection u p
  let gA : A.fst.left ⟶ V :=
    (aρ ≫ ρ.s).fst.left ≫
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Z.obj.right).inv ≫
        (asIso Z.obj.hom).inv ≫ g
  have hαcart : P.IsStronglyCartesian sourceBase α := by
    simpa [P, Y₀, sourceBase, α] using
      pushforwardSource_precompose_isStronglyCartesian (u := u) (p := p) Y₀ sourceBase
  letI : P.IsStronglyCartesian sourceBase α := hαcart
  have hθlift : P.IsHomLift (gA ≫ sourceBase) (aσ ≫ σ.f ≫ α) := by
    letI : P.IsHomLift gA (aσ ≫ σ.f) := hlifts.1
    letI : P.IsHomLift sourceBase α := hαcart.toIsHomLift
    simpa [Category.assoc] using
      @CategoryTheory.IsHomLift.comp _ _ _ _ P _ _ _ _ _ _ gA sourceBase
        (aσ ≫ σ.f) α inferInstance inferInstance
  have hex :
      ∃! x : A ⟶ T₀, P.IsHomLift gA x ∧ x ≫ α = aσ ≫ σ.f ≫ α := by
    exact
      @Functor.IsStronglyCartesian.universal_property' _ _ _ _ P
        _ _ _ _ sourceBase α hαcart A gA (aσ ≫ σ.f ≫ α) hθlift
  have hnum_eq : aσ ≫ σ.f = aρ ≫ χ₀ := by
    obtain ⟨x, _hx, huniq⟩ := hex
    have hleft : aσ ≫ σ.f = x := by
      apply huniq
      refine ⟨hlifts.1, ?_⟩
      exact Category.assoc aσ σ.f α
    have hright' : aρ ≫ χ₀ = x := by
      apply huniq
      refine ⟨hlifts.2, ?_⟩
      have hρcomp : (aρ ≫ χ₀) ≫ α = aρ ≫ ρ.f := by
        exact (Category.assoc aρ χ₀ α).trans (congrArg (fun k ↦ aρ ≫ k) hχ₀comp)
      exact hρcomp.trans hnum.symm
    exact hleft.trans hright'.symm
  have hrel' :
      MorphismProperty.RightFractionRel σ
        (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀) := by
    exact ⟨A, aσ, aρ, hdenom, hnum_eq, hmem⟩
  have hmaps :
      σ.map Q (Localization.inverts Q (u.pushforwardFractions p)) =
        (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map Q
          (Localization.inverts Q (u.pushforwardFractions p)) := by
    exact
      (MorphismProperty.RightFraction.map_eq_iff
        (W := u.pushforwardFractions p) (L := Q) σ
        (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀)).mpr hrel'
  apply (cancel_epi ((Q.objObjPreimageIso Z.obj.right).hom)).1
  have hleftmap :
      (Q.objObjPreimageIso Z.obj.right).hom ≫ χr' =
        σ.map Q (Localization.inverts Q (u.pushforwardFractions p)) := by
    simpa [Q] using hσ
  have hrightmap :
      (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map Q
          (Localization.inverts Q (u.pushforwardFractions p)) =
        (Q.objObjPreimageIso Z.obj.right).hom ≫ χr := by
    simp [χr]
  exact hleftmap.trans (hmaps.trans hrightmap)
/-- Helper for Lemma 8.12.6 Support: the remaining raw universal-property step is the source-chart descent of the right component through a fixed right-fraction representative. -/
theorem pushforwardProjectionIsoComma_descend_right_component_of_fraction
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
    (θ : Z ⟶ Y)
    (hθ : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift (g ≫ f) θ)
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
    ∃! χr : Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
        (u := u) (p := p) Y f).obj.right,
      g ≫ (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom =
        Z.obj.hom ≫ (u.pushforwardProjection p).map χr ∧
      χr ≫ (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f).hom.right =
        θ.hom.right := by
  letI : IsIso Z.obj.hom := Z.property
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
  have hρnum :
      (Q.map ρ.s) ≫
          (((Q.objObjPreimageIso Z.obj.right).hom ≫
              θ.hom.right ≫
                (Q.objObjPreimageIso Y.obj.right).inv)) =
        Q.map ρ.f := by
    exact
      pushforwardProjectionIsoComma_fraction_denominator_comp_eq_numerator
        (u := u) (p := p) Y f g θ ρ hρ
  have hbase :
      (pushforwardSourceProjection u p).map ρ.f = gρ ≫ sourceBase := by
    exact
      pushforwardProjectionIsoComma_fraction_source_chart_base_eq
        (u := u) (p := p) Y f g θ hθ ρ hρnum
  obtain ⟨χ₀, hχ₀, hχ₀uniq⟩ :=
    pushforwardProjectionIsoComma_fraction_source_factor
      (u := u) (p := p) (sourceBase := sourceBase) (ρ := ρ) gρ hbase
  let χr :
      Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
        (u := u) (p := p) Y f).obj.right :=
    (Q.objObjPreimageIso Z.obj.right).inv ≫
      (MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀).map
        Q (Localization.inverts Q (u.pushforwardFractions p))
  refine ⟨χr, ?_, ?_⟩
  · -- Existence follows by descending the source factor through the fixed denominator `ρ.s`.
    constructor
    · simpa [Q, Y₀, sourceBase, T₀, gρ, χr] using
        pushforwardProjectionIsoComma_fixed_fraction_candidate_base
          (u := u) (p := p) Y f g ρ (χ₀ := χ₀) hχ₀.1
    · simpa [Q, Y₀, sourceBase, T₀, χr] using
        pushforwardProjectionIsoComma_fixed_fraction_candidate_right
          (u := u) (p := p) Y f (Z := Z) g θ ρ hρ (χ₀ := χ₀) hχ₀.2
  · intro χr' hχr'
    exact
      pushforwardProjectionIsoComma_descended_right_component_unique_of_fixed_fraction
        (u := u) (p := p) Y f g θ ρ hρ hχ₀.1 hχ₀.2 hχr'.1 hχr'.2
/-- Helper for Lemma 8.12.6 Support: the remaining raw universal-property step is the source-chart descent of the right component through a fixed right-fraction representative. -/
theorem pushforwardProjectionIsoComma_descend_right_component_fixed_fraction
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
    (θ : Z ⟶ Y)
    (hθ : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift (g ≫ f) θ) :
    ∃! χr : Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
        (u := u) (p := p) Y f).obj.right,
      g ≫ (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom =
        Z.obj.hom ≫ (u.pushforwardProjection p).map χr ∧
      χr ≫ (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f).hom.right =
        θ.hom.right := by
  obtain ⟨ρ, hρ⟩ :=
    pushforwardProjection_preimage_exists_rightFraction
      (u := u) (p := p) θ.hom.right
  exact
    pushforwardProjectionIsoComma_descend_right_component_of_fraction
      (u := u) (p := p) Y f g θ hθ ρ hρ
/-- Helper for Lemma 8.12.6 Support: the remaining raw universal-property step is the source-chart descent of the right component through a fixed right-fraction representative. -/
theorem pushforwardProjectionIsoComma_descended_factor
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    (g : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V)
    (θ : Z ⟶ Y)
    (hθ : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift (g ≫ f) θ) :
    ∃! χ : Z ⟶ pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f,
      (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift g χ ∧
        χ ≫ pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f = θ := by
  obtain ⟨χr, hχr, hχruniq⟩ :=
    pushforwardProjectionIsoComma_descend_right_component_fixed_fraction
      (u := u) (p := p) Y f g θ hθ
  let χ :=
    pushforwardProjectionIsoComma_factorHom (u := u) (p := p) f χr hχr.1
  refine ⟨χ, ?_, ?_⟩
  · -- Package the descended right component with the fixed left map `g`.
    refine ⟨?_, ?_⟩
    · simpa [χ] using
        pushforwardProjectionIsoComma_factorHom_isHomLift
          (u := u) (p := p) (f := f) (h := g) χr hχr.1
    · simpa [χ] using
        pushforwardProjectionIsoComma_factorHom_comp
          (u := u) (p := p) (f := f) (h := g) (θ := θ) χr hχr.1 hχr.2
  · intro χ' hχ'
    apply pushforwardProjectionIsoComma_hom_ext_right (u := u) (p := p)
    apply hχruniq χ'.hom.right
    constructor
    · have hχ'left :
        χ'.hom.left = g := by
          let _ :
              (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift g χ' := hχ'.1
          simpa [pushforwardProjectionIsoCommaProjection] using
            (IsHomLift.fac' (pushforwardProjectionIsoCommaProjection (u := u) (p := p)) g χ')
      simpa [hχ'left, Category.assoc] using χ'.hom.w
    · have hcomp := congrArg (fun ψ ↦ ψ.hom.right) hχ'.2
      simpa [pushforwardProjectionIsoComma_precomposeHom, Category.assoc] using hcomp
/-- Helper for Lemma 8.12.6 Support: for the literal projection from the iso-comma model to `D`, the chosen precomposition morphism is the source-faithful strongly cartesian lift. -/
theorem pushforwardProjectionIsoCommaProjection_precompose_isStronglyCartesian
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y) :
    (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsStronglyCartesian f
      (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f) := by
  refine
    { toIsHomLift := ?_
      universal_property' := ?_ }
  · -- The chosen precomposition morphism is already a literal lift over `f`.
    exact
      pushforwardProjectionIsoComma_precomposeHom_isHomLift
        (u := u) (p := p) Y f
  · intro Z g θ hθ
    simpa using
      pushforwardProjectionIsoComma_descended_factor
        (u := u) (p := p) Y f g θ hθ
/-- Helper for Lemma 8.12.6 Support: once the literal iso-comma projection has strongly cartesian precomposition lifts, it is a fibred category over `D`. -/
theorem pushforwardProjectionIsoCommaProjection_isFibered :
    (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsFibered := by
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro Y V f
  refine ⟨pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f, ?_, ?_⟩
  · exact pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f
  · exact
      pushforwardProjectionIsoCommaProjection_precompose_isStronglyCartesian
        (u := u) (p := p) Y f

end Functor

end

end CategoryTheory
