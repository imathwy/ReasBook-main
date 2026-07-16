import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_27_14
import stacks_proof.stacks_project.Chap08.Lemma_8_12_5
import stacks_proof.stacks_project.Chap08.Lemma_8_12_6.Index
import stacks_proof.stacks_project.Chap08.Lemma_8_12_6_Support.RawSectionTransport

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

section

omit [p.IsFibered] [HasPullbacks C] [HasEqualizers C]
  [PreservesLimitsOfShape WalkingCospan u]
  [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.6 Support: the raw base map used at the normalized frontier is an
isomorphism, because it is the stored iso-comma chart preceded by an equality transport. -/
theorem pushforwardProjectionIsoComma_normalized_frontier_raw_base_isIso
    {V : D}
    (Xraw : pushforwardProjectionIsoComma (u := u) (p := p))
    (hRaw : Xraw.obj.left = V) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let gRaw : V ⟶ q.obj Xraw := eqToHom hRaw.symm ≫ Xraw.obj.hom
    IsIso gRaw := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let gRaw : V ⟶ q.obj Xraw := eqToHom hRaw.symm ≫ Xraw.obj.hom
  -- The equality transport and the iso-comma chart are both isomorphisms, so their composite is.
  change IsIso (eqToHom hRaw.symm ≫ Xraw.obj.hom)
  exact
    IsIso.comp_isIso'
      (show IsIso (eqToHom hRaw.symm : V ⟶ Xraw.obj.left) from inferInstance)
      Xraw.property

end

section

omit [p.IsFibered] [HasPullbacks C] [HasEqualizers C]
  [PreservesLimitsOfShape WalkingCospan u]
  [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.6 Support: the transported frontier base
`eX.hom ≫ gRaw` is an isomorphism. -/
theorem pushforwardProjectionIsoComma_normalized_frontier_transported_base_isIso
    {V : D}
    (Xraw : pushforwardProjectionIsoComma (u := u) (p := p))
    (hRaw : Xraw.obj.left = V) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let gRaw : V ⟶ q.obj Xraw := eqToHom hRaw.symm ≫ Xraw.obj.hom
    letI : IsIso Xraw.obj.hom := Xraw.property
    let fRaw : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Xraw :=
      gRaw ≫ (asIso Xraw.obj.hom).inv
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Xraw.obj.right
      (fRaw ≫ Xraw.obj.hom)
    IsIso (eX.hom ≫ gRaw) := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let gRaw : V ⟶ q.obj Xraw := eqToHom hRaw.symm ≫ Xraw.obj.hom
  letI : IsIso Xraw.obj.hom := Xraw.property
  let fRaw : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Xraw :=
    gRaw ≫ (asIso Xraw.obj.hom).inv
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Xraw.obj.right
    (fRaw ≫ Xraw.obj.hom)
  have hgRaw_iso : IsIso gRaw := by
    -- Reuse the raw-base lemma so this side condition is not reproved at each frontier use.
    simpa [q, gRaw] using
      pushforwardProjectionIsoComma_normalized_frontier_raw_base_isIso
        (u := u) (p := p) Xraw hRaw
  exact
    IsIso.comp_isIso'
      (show IsIso eX.hom from inferInstance)
      hgRaw_iso

end

/-- Helper for Lemma 8.12.6 Support: the normalized source chart always has a strongly cartesian lift
over the transported base map; the remaining frontier is only the strict removal of the leading
source comparison isomorphism. -/
theorem pushforwardProjectionIsoComma_normalized_frontier_transported_lift
    {V : D}
    (Xraw : pushforwardProjectionIsoComma (u := u) (p := p))
    (hRaw : Xraw.obj.left = V) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let gRaw : V ⟶ q.obj Xraw := eqToHom hRaw.symm ≫ Xraw.obj.hom
    letI : IsIso Xraw.obj.hom := Xraw.property
    let fRaw : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Xraw :=
      gRaw ≫ (asIso Xraw.obj.hom).inv
    let X := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Xraw fRaw
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Xraw.obj.right
      (fRaw ≫ Xraw.obj.hom)
    let δ :=
      ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X) ≫
        pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Xraw fRaw
    q.IsStronglyCartesian (eX.hom ≫ gRaw) δ := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let gRaw : V ⟶ q.obj Xraw := eqToHom hRaw.symm ≫ Xraw.obj.hom
  letI : IsIso Xraw.obj.hom := Xraw.property
  let fRaw : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Xraw :=
    gRaw ≫ (asIso Xraw.obj.hom).inv
  let X := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Xraw fRaw
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Xraw.obj.right
    (fRaw ≫ Xraw.obj.hom)
  let δ :=
    ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X) ≫
      pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Xraw fRaw
  have hδ :
      q.IsHomLift (eX.hom ≫ gRaw) δ := by
    -- The existing precomposition adapter gives the exact transported hom-lift.
    simpa [q, gRaw, fRaw, X, eX, δ, Category.assoc] using
      pushforwardProjectionIsoComma_precompose_over_composite_isHomLift
        (u := u) (p := p) Xraw gRaw
  have hfRaw_iso : IsIso fRaw := by
    -- The normalized raw base is a composite of the stored chart and its inverse.
    have hgRaw_iso : IsIso gRaw := by
      simpa [q, gRaw] using
        pushforwardProjectionIsoComma_normalized_frontier_raw_base_isIso
          (u := u) (p := p) Xraw hRaw
    letI : IsIso gRaw := hgRaw_iso
    dsimp [fRaw]
    change IsIso (gRaw ≫ (asIso Xraw.obj.hom).inv)
    exact
      IsIso.comp_isIso' hgRaw_iso
        (show IsIso (asIso Xraw.obj.hom).inv from inferInstance)
  have hpre_cart :
      (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsStronglyCartesian fRaw
        (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Xraw fRaw) := by
    -- The literal iso-comma projection has strongly cartesian precomposition lifts.
    exact
      pushforwardProjectionIsoCommaProjection_precompose_isStronglyCartesian
        (u := u) (p := p) Xraw fRaw
  have hpre_iso :
      IsIso (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Xraw fRaw) := by
    letI :
        (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsStronglyCartesian fRaw
          (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Xraw fRaw) :=
      hpre_cart
    letI : IsIso fRaw := hfRaw_iso
    exact
      Functor.IsStronglyCartesian.isIso_of_base_isIso
        (pushforwardProjectionIsoCommaProjection (u := u) (p := p)) fRaw
        (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Xraw fRaw)
  letI :
      IsIso (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Xraw fRaw) :=
    hpre_iso
  have hunit_iso :
      IsIso ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X) := by
    infer_instance
  letI : IsIso ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X) :=
    hunit_iso
  have hδ_iso : IsIso δ := by
    -- The transported frontier morphism is a composite of the vertical unit isomorphism and the
    -- raw precomposition isomorphism.
    change IsIso
      (((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X) ≫
        pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Xraw fRaw)
    exact IsIso.comp_isIso' hunit_iso hpre_iso
  letI : IsIso δ := hδ_iso
  letI : q.IsHomLift (eX.hom ≫ gRaw) δ := hδ
  -- Since the transported lift is an isomorphism, it is strongly cartesian for the strict
  -- composite projection over its transported base.
  exact Functor.IsStronglyCartesian.of_isIso q (eX.hom ≫ gRaw) δ

/-- Helper for Lemma 8.12.6 Support: the normalized frontier morphism used in the final source
replacement is already an isomorphism; only its strict hom-lift base remains to be supplied. -/
theorem pushforwardProjectionIsoComma_normalized_frontier_morphism_isIso
    {V : D}
    (Xraw : pushforwardProjectionIsoComma (u := u) (p := p))
    (hRaw : Xraw.obj.left = V) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let gRaw : V ⟶ q.obj Xraw := eqToHom hRaw.symm ≫ Xraw.obj.hom
    letI : IsIso Xraw.obj.hom := Xraw.property
    let fRaw : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Xraw :=
      gRaw ≫ (asIso Xraw.obj.hom).inv
    let X := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Xraw fRaw
    let δ :=
      ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X) ≫
        pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Xraw fRaw
    IsIso δ := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let gRaw : V ⟶ q.obj Xraw := eqToHom hRaw.symm ≫ Xraw.obj.hom
  letI : IsIso Xraw.obj.hom := Xraw.property
  let fRaw : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Xraw :=
    gRaw ≫ (asIso Xraw.obj.hom).inv
  let X := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Xraw fRaw
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Xraw.obj.right
    (fRaw ≫ Xraw.obj.hom)
  let δ :=
    ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X) ≫
      pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Xraw fRaw
  have hδcart :
      q.IsStronglyCartesian (eX.hom ≫ gRaw) δ := by
    -- The previous frontier theorem gives strong cartesianness over the transported base.
    simpa [q, gRaw, fRaw, X, eX, δ] using
      pushforwardProjectionIsoComma_normalized_frontier_transported_lift
        (u := u) (p := p) Xraw hRaw
  have hbase_iso : IsIso (eX.hom ≫ gRaw) := by
    -- The transported base-isomorphism side condition is cached as a frontier helper.
    simpa [q, gRaw, fRaw, X, eX] using
      pushforwardProjectionIsoComma_normalized_frontier_transported_base_isIso
        (u := u) (p := p) Xraw hRaw
  letI : q.IsStronglyCartesian (eX.hom ≫ gRaw) δ := hδcart
  letI : IsIso (eX.hom ≫ gRaw) := hbase_iso
  -- A strongly cartesian morphism above an isomorphism in the base is itself an isomorphism.
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso q (eX.hom ≫ gRaw) δ

section

omit [p.IsFibered] [HasPullbacks C] [HasEqualizers C]
  [PreservesLimitsOfShape WalkingCospan u]
  [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.6 Support: the identity morphism on the raw iso-comma object could
lift the normalized raw base map only if the strict composite projection of that object were
literally the requested source object. -/
theorem pushforwardProjectionIsoComma_id_lift_requires_strict_source
    {V : D}
    (Xraw : pushforwardProjectionIsoComma (u := u) (p := p))
    (hRaw : Xraw.obj.left = V) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let gRaw : V ⟶ q.obj Xraw := eqToHom hRaw.symm ≫ Xraw.obj.hom
    q.IsHomLift gRaw (𝟙 Xraw) → q.obj Xraw = V := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let gRaw : V ⟶ q.obj Xraw := eqToHom hRaw.symm ≫ Xraw.obj.hom
  intro h
  letI : q.IsHomLift gRaw (𝟙 Xraw) := h
  -- The domain equality for a hom-lift is exactly the missing strict source equality.
  exact IsHomLift.domain_eq q gRaw (𝟙 Xraw)

/-- Helper for Lemma 8.12.6 Support: fibredness of the strict iso-comma composite is exactly
objectwise existence of strongly cartesian lifts over literal composite-projection base maps. -/
theorem pushforwardProjectionIsoCommaForget_comp_isFibered_iff_strict_lifts :
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
      u.pushforwardProjection p).IsFibered ↔
      ∀ (Y : pushforwardProjectionIsoComma (u := u) (p := p)) (V : D)
        (g : V ⟶
          (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
            u.pushforwardProjection p).obj Y),
        ∃ X : pushforwardProjectionIsoComma (u := u) (p := p),
          ∃ φ : X ⟶ Y,
            (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
              u.pushforwardProjection p).IsStronglyCartesian g φ := by
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  -- This freezes the generic fibredness criterion at the strict composite normal form, so later
  -- proof steps can ask only for literal strongly cartesian lifts.
  simpa [q] using (isFibered_iff_exists_isStronglyCartesian q)

/-- Helper for Lemma 8.12.6 Support: if the strict iso-comma composite projection is already
fibred, it supplies the normalized strict source replacement at the literal raw base map. -/
theorem pushforwardProjectionIsoComma_normalized_frontier_source_replacement_of_isFibered
    {V : D}
    (Xraw : pushforwardProjectionIsoComma (u := u) (p := p))
    (hRaw : Xraw.obj.left = V) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let gRaw : V ⟶ q.obj Xraw := eqToHom hRaw.symm ≫ Xraw.obj.hom
    q.IsFibered →
      ∃ X' : pushforwardProjectionIsoComma (u := u) (p := p),
        ∃ δ : X' ⟶ Xraw,
          q.IsStronglyCartesian gRaw δ := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let gRaw : V ⟶ q.obj Xraw := eqToHom hRaw.symm ≫ Xraw.obj.hom
  intro hq
  letI : q.IsFibered := hq
  -- A fibered strict composite projection gives a cartesian lift over the literal raw base map.
  obtain ⟨X', δ, hδcart⟩ := IsPreFibered.exists_isCartesian q rfl gRaw
  letI : q.IsCartesian gRaw δ := hδcart
  -- Convert the chosen cartesian lift to the strongly cartesian lift needed downstream.
  exact ⟨X', δ, Functor.IsFibered.isStronglyCartesian_of_isCartesian q gRaw δ⟩

end

/-- Helper for Lemma 8.12.6 Support: once the normalized inverse-chart witness is fixed, the only remaining strict-side task is to replace its stored source chart exactly once and return a literal strict lift over `eX.inv`. -/
theorem pushforwardProjectionIsoComma_normalized_frontier_source_replacement
    {V : D}
    (Xraw : pushforwardProjectionIsoComma (u := u) (p := p))
    (hRaw : Xraw.obj.left = V) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let gRaw : V ⟶ q.obj Xraw := eqToHom hRaw.symm ≫ Xraw.obj.hom
    ∃ X' : pushforwardProjectionIsoComma (u := u) (p := p),
      ∃ δ : X' ⟶ Xraw,
        q.IsStronglyCartesian gRaw δ := by
  -- Route correction: use the construction-lift normal form, so the source comparison for the
  -- normalized frontier is an identity and the transported lift already lies over `gRaw`.
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let gRaw : V ⟶ q.obj Xraw := eqToHom hRaw.symm ≫ Xraw.obj.hom
  letI : IsIso Xraw.obj.hom := Xraw.property
  let fRaw : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Xraw :=
    gRaw ≫ (asIso Xraw.obj.hom).inv
  let X := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Xraw fRaw
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Xraw.obj.right
    (fRaw ≫ Xraw.obj.hom)
  let δ :=
    ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X) ≫
      pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Xraw fRaw
  refine ⟨_, δ, ?_⟩
  -- The transported frontier helper supplies the lift over the identity-whiskered base map;
  -- normalizing that identity gives the literal base `gRaw`.
  have hcart :
      q.IsStronglyCartesian (𝟙 V ≫ (eqToHom hRaw.symm ≫ Xraw.obj.hom)) δ := by
    simpa only [q, gRaw, fRaw, X, eX, δ,
      pushforwardProjection_precompose_modelBaseIso_hom] using
      pushforwardProjectionIsoComma_normalized_frontier_transported_lift
        (u := u) (p := p) Xraw hRaw
  simpa [gRaw] using hcart
/-- Helper for Lemma 8.12.6 Support: after normalizing the raw source-chart lift to the inverse-chart base map, the remaining strict-side step is to replace the source object once so the resulting morphism lies literally over `eX.inv`. -/
theorem pushforwardProjectionIsoComma_raw_source_chart_to_q_homLift
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let Tsec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    ∀ {X : pushforwardProjectionIsoComma (u := u) (p := p)}
      (α : X ⟶ Tsec),
      (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsStronglyCartesian eX.inv α →
      ∃ X' : pushforwardProjectionIsoComma (u := u) (p := p),
        ∃ β : X' ⟶ T,
          q.IsStronglyCartesian eX.inv β := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let Tsec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  let η := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app T)
  intro X α hα
  letI : IsIso X.obj.hom := X.property
  let hX : X.obj.left = V :=
    pushforwardProjectionIsoComma_raw_source_chart_domain_eq
      (u := u) (p := p) Y g α hα
  obtain ⟨X', δ, hδ⟩ :=
    pushforwardProjectionIsoComma_normalized_frontier_source_replacement
      (u := u) (p := p) X hX
  refine ⟨X', δ ≫ α ≫ η, ?_⟩
  -- Compose the source replacement with the normalized inverse-chart lift.
  exact
    pushforwardProjectionIsoComma_source_chart_replacement_to_q_isStronglyCartesian
      (u := u) (p := p) Y g α hα δ hδ
/-- Helper for Lemma 8.12.6 Support: after proving the transported strict lift, replace the source object once so the resulting morphism lies literally over `g`. -/
theorem pushforwardProjectionIsoComma_strict_source_replacement
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    ∃ X : pushforwardProjectionIsoComma (u := u) (p := p),
      ∃ φ : X ⟶ Y, q.IsStronglyCartesian g φ := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  obtain ⟨Xraw, α, hα⟩ :=
    pushforwardProjectionIsoComma_raw_section_source_chart_lift
      (u := u) (p := p) Y g
  obtain ⟨X', β, hβ⟩ :=
    pushforwardProjectionIsoComma_raw_source_chart_to_q_homLift
      (u := u) (p := p) Y g α hα
  let γ := pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Ysec g ≫
    ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app Y)
  have hγ : q.IsStronglyCartesian (eX.hom ≫ g) γ := by
    -- The transported raw-section lift supplies the second strongly cartesian factor.
    simpa [q, Ysec, T, eX, γ] using
      pushforwardProjectionIsoComma_raw_section_lift_isStronglyCartesian_transported
        (u := u) (p := p) Y g
  refine ⟨X', β ≫ γ, ?_⟩
  -- Compose the strict inverse-chart lift with the transported section lift and cancel `eX`.
  exact
    pushforwardProjectionIsoComma_source_replacement_comp_isStronglyCartesian
      (u := u) (p := p) Y g X' β γ hβ hγ
/-- Helper for Lemma 8.12.6 Support: after proving fibredness for the literal iso-comma projection, the remaining work is to transport that fibred structure across the comparison natural isomorphism to the strict composite `pushforwardProjectionIsoCommaForget ⋙ u.pushforwardProjection p`. -/
theorem pushforwardProjectionIsoComma_projection_transport_isFibered :
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).IsFibered := by
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro Y V g
  rcases
      pushforwardProjectionIsoComma_strict_source_replacement
        (u := u) (p := p) Y g with
    ⟨X, φ, hφ⟩
  exact ⟨X, φ, by simpa [q] using hφ⟩

section

omit [p.IsFibered] [HasPullbacks C] [HasEqualizers C]
  [PreservesLimitsOfShape WalkingCospan u]
  [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.6 Support: strongly cartesian lifts for the strict iso-comma
comparison projection package into fibredness of that strict projection. -/
theorem pushforwardProjectionIsoCommaForget_comp_isFibered_of_exists
    (h :
      ∀ (Y : pushforwardProjectionIsoComma (u := u) (p := p)) (V : D)
        (g : V ⟶
          (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
            u.pushforwardProjection p).obj Y),
        ∃ X : pushforwardProjectionIsoComma (u := u) (p := p),
          ∃ φ : X ⟶ Y,
            (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
              u.pushforwardProjection p).IsStronglyCartesian g φ) :
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
      u.pushforwardProjection p).IsFibered := by
  -- Convert the planned objectwise strict lifts into the owner API for fibredness.
  exact
    (pushforwardProjectionIsoCommaForget_comp_isFibered_iff_strict_lifts
      (u := u) (p := p)).2 h

end

/-- Helper for Lemma 8.12.6 Support: the strict iso-comma comparison projection should be
fibred before transporting fibredness back to the localized pushforward projection. -/
theorem pushforwardProjectionIsoCommaForget_comp_isFibered_aux :
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
      u.pushforwardProjection p).IsFibered := by
  -- The transplanted strict source-replacement helper gives objectwise strongly cartesian lifts
  -- for the strict forgetful composite, so the packaging theorem closes the fibredness goal.
  exact pushforwardProjectionIsoComma_projection_transport_isFibered (u := u) (p := p)


end Functor

end

end CategoryTheory
