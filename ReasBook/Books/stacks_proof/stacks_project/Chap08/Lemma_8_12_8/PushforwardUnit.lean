import StacksProject_2024.Chap08.Lemma_8_12_8.PushforwardMap

open CategoryTheory
open CategoryTheory.Limits
open scoped FibredCategoryOver
open scoped Functor

universe u v uS vS

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{v} C] [Category.{v} D]

section Pushforward

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.8: localized pushforward precomposition morphisms are strongly
cartesian. -/
private theorem pushforwardProjection_modelPrecompose_isStronglyCartesian
    {S : Type uS} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered]
    (Y : u ₚ p) {V : D} (g : V ⟶ (u.pushforwardProjection p).obj Y) :
    (u.pushforwardProjection p).IsStronglyCartesian g
      (Functor.pushforwardProjection_precompose_modelHom (u := u) (p := p) Y g) := by
  let F := Functor.pushforwardProjectionIsoCommaForgetBased (u := u) (p := p)
  have hF : F.IsEquivalenceOverBase := by
    exact BasedFunctor.IsEquivalenceOverBase.mkPrime
      (F := F)
      (Functor.pushforwardProjectionIsoCommaSectionBased (u := u) (p := p))
      (Functor.pushforwardProjectionIsoCommaForget_unitIso (u := u) (p := p))
      (Functor.pushforwardProjectionIsoCommaForget_counitIso (u := u) (p := p))
  let Yraw := (Functor.pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj Y
  let α := Functor.pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Yraw g ≫
    ((Functor.pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app Yraw)
  let q := Functor.pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
    u.pushforwardProjection p
  let fbase :=
    ((Functor.pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Yraw.obj.right (g ≫ Yraw.obj.hom)).hom) ≫ g
  have hraw : q.IsStronglyCartesian fbase α := by
    simpa [q, Yraw, α, fbase] using
      Functor.pushforwardProjectionIsoComma_raw_section_lift_isStronglyCartesian_transported
        (u := u) (p := p) Yraw g
  have hrawOwner : q.IsStronglyCartesian (q.map α) α := by
    exact @BasedFunctor.isStronglyCartesian_rebase_over_target_eq _ _ _ _ q _ _ _ _ rfl
      fbase α hraw
  have hmap := BasedFunctor.isStronglyCartesian_map_of_isEquivalenceOverBase F hF α hrawOwner
  have hmodelOwner :
      (u.pushforwardProjection p).IsStronglyCartesian
        ((u.pushforwardProjection p).map
          (Functor.pushforwardProjection_precompose_modelHom (u := u) (p := p) Y
            (g ≫ 𝟙 Y.as.obj.fst.left)))
        (Functor.pushforwardProjection_precompose_modelHom (u := u) (p := p) Y
          (g ≫ 𝟙 Y.as.obj.fst.left)) := by
    simpa [F, Yraw, α, Functor.pushforwardProjectionIsoCommaForgetBased,
      Functor.pushforwardProjectionIsoCommaSectionObj,
      Functor.pushforwardProjectionIsoComma_precomposeHom,
      Functor.pushforwardProjectionIsoComma_unitIso,
      Functor.pushforwardProjectionIsoComma_unitIsoApp,
      Functor.pushforwardProjection_precompose_modelBaseIso_hom] using hmap
  have hg : g ≫ 𝟙 Y.as.obj.fst.left = g := by
    simpa using (Category.comp_id g)
  have hmodelOwner' :
      (u.pushforwardProjection p).IsStronglyCartesian
        ((u.pushforwardProjection p).map
          (Functor.pushforwardProjection_precompose_modelHom (u := u) (p := p) Y g))
        (Functor.pushforwardProjection_precompose_modelHom (u := u) (p := p) Y g) := by
    rw [← hg]
    exact hmodelOwner
  have hmodelLift :
      (u.pushforwardProjection p).IsHomLift g
        (Functor.pushforwardProjection_precompose_modelHom (u := u) (p := p) Y g) := by
    convert Functor.pushforwardProjection_precompose_modelHom_isHomLift (u := u) (p := p) Y g using 1
    exact (Category.id_comp g).symm
  letI := hmodelOwner'
  letI := hmodelLift
  exact BasedFunctor.isStronglyCartesian_of_external_hom_lift (u.pushforwardProjection p)
    (Functor.pushforwardProjection_precompose_modelHom (u := u) (p := p) Y g)

/-- Helper for Lemma 8.12.8: after localization, a chosen source-precomposition lift still lies
over the original base morphism. -/
private theorem pushforwardProjection_Q_precompose_isHomLift
    {S : Type uS} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered]
    (A : u ₚₚ p) {V : D} (f : V ⟶ A.fst.left) :
    (u.pushforwardProjection p).IsHomLift f
      ((u.pushforwardFractions p).Q.map
        (Functor.pushforwardSourcePrecomposeHom (u := u) (p := p) A f)) := by
  -- The construction-lift projection computes on `Q.map` by the precomposition
  -- factorization lemma from Lemma 8.12.6.
  refine IsHomLift.of_fac' (u.pushforwardProjection p) f
    ((u.pushforwardFractions p).Q.map
      (Functor.pushforwardSourcePrecomposeHom (u := u) (p := p) A f)) rfl rfl ?_
  rw [Functor.pushforwardProjection_precompose_fac (u := u) (p := p) A f]
  change f = 𝟙 V ≫ f ≫ 𝟙 A.fst.left
  simp

/-- Helper for Lemma 8.12.8: a hom-lift into a canonical localized source object computes to
its prescribed base morphism. -/
private theorem pushforwardProjection_map_eq_of_homLift_to_Q_obj
    {S : Type uS} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered]
    (A : u ₚₚ p) {V : D} (f : V ⟶ A.fst.left)
    {Z : u ₚ p} (g : (u.pushforwardProjection p).obj Z ⟶ V)
    (θ : Z ⟶ (u.pushforwardFractions p).Q.obj A)
    (hθ : (u.pushforwardProjection p).IsHomLift (g ≫ f) θ) :
    (u.pushforwardProjection p).map θ = g ≫ f := by
  let P := u.pushforwardProjection p
  letI : P.IsHomLift (g ≫ f) θ := hθ
  have hfac := (IsHomLift.fac' P (g ≫ f) θ)
  have hdom : eqToHom (IsHomLift.domain_eq P (g ≫ f) θ) = 𝟙 (P.obj Z) := by
    cases IsHomLift.domain_eq P (g ≫ f) θ
    rfl
  have hcod : eqToHom (IsHomLift.codomain_eq P (g ≫ f) θ).symm = 𝟙 A.fst.left := by
    cases IsHomLift.codomain_eq P (g ≫ f) θ
    rfl
  rw [hfac, hdom, hcod]
  rw [Category.id_comp]
  exact Category.comp_id (g ≫ f)

/-- Helper for Lemma 8.12.8: strict source charts turn a hom-lift to `Q.obj A` into the
corresponding source-level base equation. -/
private theorem pushforwardProjectionStrict_map_to_Q_obj_chart
    {S : Type uS} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered]
    (A : u ₚₚ p) {V : D} (f : V ⟶ A.fst.left)
    {Z : u ₚ p} (g : (u.pushforwardProjection p).obj Z ⟶ V)
    (θ : Z ⟶ (u.pushforwardFractions p).Q.obj A)
    (hθ : (u.pushforwardProjection p).IsHomLift (g ≫ f) θ) :
    let Q := (u.pushforwardFractions p).Q
    let chartA :
        Functor.pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj A) ⟶
          (Functor.pushforwardSourceProjection u p).obj A :=
      ((Functor.pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj A)).symm ≪≫
        Functor.pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).hom
    (Functor.pushforwardProjectionStrict u p).map θ ≫ chartA =
      (Functor.pushforwardProjectionStrictObjIso (u := u) (p := p) Z).inv ≫ g ≫ f := by
  dsimp
  let Q := (u.pushforwardFractions p).Q
  let chartA :
      Functor.pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj A) ⟶
        (Functor.pushforwardSourceProjection u p).obj A :=
    ((Functor.pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj A)).symm ≪≫
      Functor.pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).hom
  let eSource := Functor.pushforwardProjectionStrictObjIso (u := u) (p := p) Z
  let eTarget := Functor.pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj A)
  have hθmap : (u.pushforwardProjection p).map θ = g ≫ f :=
    pushforwardProjection_map_eq_of_homLift_to_Q_obj (u := u) (p := p) A f g θ hθ
  have hcancelA : eTarget.hom ≫ chartA =
      𝟙 ((Functor.pushforwardSourceProjection u p).obj A) := by
    simpa [Q, chartA, eTarget] using
      Functor.pushforwardProjectionStrict_obj_Q_obj_chart_cancel (u := u) (p := p) A
  have hnat :
      eSource.hom ≫ (Functor.pushforwardProjectionStrict u p).map θ =
        (u.pushforwardProjection p).map θ ≫ eTarget.hom := by
    simpa [eSource, eTarget] using
      (Functor.pushforwardProjectionStrictIso_naturality (u := u) (p := p) θ).symm
  have hpost : ((u.pushforwardProjection p).map θ ≫ eTarget.hom) ≫ chartA = g ≫ f := by
    have h1 : ((u.pushforwardProjection p).map θ ≫ eTarget.hom) ≫ chartA =
        (u.pushforwardProjection p).map θ ≫ (eTarget.hom ≫ chartA) :=
      Category.assoc ((u.pushforwardProjection p).map θ) eTarget.hom chartA
    have h2 : (u.pushforwardProjection p).map θ ≫ (eTarget.hom ≫ chartA) =
        (u.pushforwardProjection p).map θ ≫ 𝟙 ((Functor.pushforwardSourceProjection u p).obj A) := by
      exact congrArg (fun k ↦ (u.pushforwardProjection p).map θ ≫ k) hcancelA
    have h3 : (u.pushforwardProjection p).map θ ≫
        𝟙 ((Functor.pushforwardSourceProjection u p).obj A) = g ≫ f := by
      rw [hθmap]
      exact Category.comp_id (g ≫ f)
    exact h1.trans (h2.trans h3)
  have hwhisker :
      (eSource.hom ≫ (Functor.pushforwardProjectionStrict u p).map θ) ≫ chartA = g ≫ f :=
    (congrArg (fun k ↦ k ≫ chartA) hnat).trans hpost
  apply (cancel_epi eSource.hom).1
  calc
    eSource.hom ≫ ((Functor.pushforwardProjectionStrict u p).map θ ≫ chartA) =
        (eSource.hom ≫ (Functor.pushforwardProjectionStrict u p).map θ) ≫ chartA := by
          exact (Category.assoc eSource.hom ((Functor.pushforwardProjectionStrict u p).map θ) chartA).symm
    _ = g ≫ f := hwhisker
    _ = eSource.hom ≫ (eSource.inv ≫ g ≫ f) := by
      calc
        g ≫ f = 𝟙 _ ≫ g ≫ f := by simp
        _ = (eSource.hom ≫ eSource.inv) ≫ g ≫ f := by rw [eSource.hom_inv_id]
        _ = eSource.hom ≫ (eSource.inv ≫ g ≫ f) := by simp

/-- Helper for Lemma 8.12.8: a denominator in the pushforward fraction system has an
isomorphism as its left `D`-component. -/
theorem pushforwardFractions_left_isIso
    {S : Type uS} [Category.{vS} S] (p : S ⥤ C)
    {X Y : u ₚₚ p} {s : X ⟶ Y} (hs : u.pushforwardFractions p s) :
    IsIso s.fst.left := by
  rcases hs with ⟨⟨hV, hleft⟩, _⟩
  rw [hleft]
  infer_instance

/-- Helper for Lemma 8.12.8: a right-fraction representative of a localized hom-lift into
`Q.obj A` has numerator over the expected source-level composite base map. -/
private theorem pushforwardProjection_Q_fraction_source_base_eq
    {S : Type uS} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered]
    (A : u ₚₚ p) {V : D} (f : V ⟶ A.fst.left)
    {Z : u ₚ p} (g : (u.pushforwardProjection p).obj Z ⟶ V)
    (θ : Z ⟶ (u.pushforwardFractions p).Q.obj A)
    (hθ : (u.pushforwardProjection p).IsHomLift (g ≫ f) θ)
    (ρ : (u.pushforwardFractions p).RightFraction
      (((u.pushforwardFractions p).Q).objPreimage Z) A)
    (hρnum :
      ((u.pushforwardFractions p).Q.map ρ.s) ≫
          (((u.pushforwardFractions p).Q.objObjPreimageIso Z).hom ≫ θ) =
        ((u.pushforwardFractions p).Q.map ρ.f)) :
    let gρ : ρ.X'.fst.left ⟶ V :=
      ρ.s.fst.left ≫
        (Functor.pushforwardProjectionStrictObjIso (u := u) (p := p) Z).inv ≫ g
    (Functor.pushforwardSourceProjection u p).map ρ.f = gρ ≫ f := by
  dsimp
  let Q := (u.pushforwardFractions p).Q
  let F := Functor.pushforwardProjectionStrict u p
  let chartρ :
      Functor.pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj ρ.X') ⟶
        (Functor.pushforwardSourceProjection u p).obj ρ.X' :=
    ((Functor.pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj ρ.X')).symm ≪≫
      Functor.pushforwardProjection_obj_Q_obj_base (u := u) (p := p) ρ.X').hom
  let chartZ :
      Functor.pushforwardProjectionStrictObj (u := u) (p := p)
          (Q.obj (Q.objPreimage Z)) ⟶
        (Functor.pushforwardSourceProjection u p).obj (Q.objPreimage Z) :=
    ((Functor.pushforwardProjectionStrictObjIso (u := u) (p := p)
        (Q.obj (Q.objPreimage Z))).symm ≪≫
      Functor.pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
        (Q.objPreimage Z)).hom
  let chartA :
      Functor.pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj A) ⟶
        (Functor.pushforwardSourceProjection u p).obj A :=
    ((Functor.pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj A)).symm ≪≫
      Functor.pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).hom
  let eZ := Functor.pushforwardProjectionStrictObjIso (u := u) (p := p) Z
  have hs :
      F.map (Q.map ρ.s) ≫ chartZ =
        chartρ ≫ (Functor.pushforwardSourceProjection u p).map ρ.s := by
    -- Endpoint charts identify strict projection of a localized source map with its
    -- prelocalized source projection.
    simpa [Q, F, chartρ, chartZ] using
      Functor.pushforwardProjectionIsoComma_fraction_source_chart_endpoints_exact
        (u := u) (p := p) (k := ρ.s)
  have hf :
      F.map (Q.map ρ.f) ≫ chartA =
        chartρ ≫ (Functor.pushforwardSourceProjection u p).map ρ.f := by
    -- The same endpoint-chart computation applies to the numerator.
    simpa [Q, F, chartρ, chartA] using
      Functor.pushforwardProjectionIsoComma_fraction_source_chart_endpoints_exact
        (u := u) (p := p) (k := ρ.f)
  have hchartZ :
      chartZ = F.map ((Q.objObjPreimageIso Z).hom) := by
    -- The source endpoint chart is the strict image of the canonical preimage comparison.
    simpa [Q, F, chartZ] using
      Functor.pushforwardProjectionIsoComma_preimage_chart_eq
        (u := u) (p := p) Z
  have hθchart :
      F.map θ ≫ chartA = eZ.inv ≫ g ≫ f := by
    -- The hom-lift condition on `θ` computes its strict chart.
    simpa [Q, F, chartA, eZ] using
      pushforwardProjectionStrict_map_to_Q_obj_chart (u := u) (p := p) A f g θ hθ
  have hmiddle :
      F.map (((Q.objObjPreimageIso Z).hom ≫ θ)) ≫ chartA =
        chartZ ≫ eZ.inv ≫ g ≫ f := by
    calc
      F.map (((Q.objObjPreimageIso Z).hom ≫ θ)) ≫ chartA =
          (F.map ((Q.objObjPreimageIso Z).hom) ≫ F.map θ) ≫ chartA := by
            rw [Functor.map_comp]
      _ = F.map ((Q.objObjPreimageIso Z).hom) ≫ (F.map θ ≫ chartA) := by
            simp [Category.assoc]
      _ = chartZ ≫ eZ.inv ≫ g ≫ f := by
            rw [hchartZ, hθchart]
            simp [Category.assoc]
  apply (cancel_epi chartρ).1
  calc
    chartρ ≫ (Functor.pushforwardSourceProjection u p).map ρ.f =
        F.map (Q.map ρ.f) ≫ chartA := by
          simpa using hf.symm
    _ = F.map ((Q.map ρ.s) ≫ ((Q.objObjPreimageIso Z).hom ≫ θ)) ≫ chartA := by
          rw [hρnum]
    _ = (F.map (Q.map ρ.s) ≫ F.map (((Q.objObjPreimageIso Z).hom ≫ θ))) ≫ chartA := by
          rw [Functor.map_comp]
    _ = F.map (Q.map ρ.s) ≫
          (F.map (((Q.objObjPreimageIso Z).hom ≫ θ)) ≫ chartA) := by
          simp [Category.assoc]
    _ = F.map (Q.map ρ.s) ≫ (chartZ ≫ eZ.inv ≫ g ≫ f) := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ F.map (Q.map ρ.s) ≫ k) hmiddle
    _ = (F.map (Q.map ρ.s) ≫ chartZ) ≫ eZ.inv ≫ g ≫ f := by
          simp [Category.assoc]
    _ = (chartρ ≫ (Functor.pushforwardSourceProjection u p).map ρ.s) ≫
          eZ.inv ≫ g ≫ f := by
          rw [hs]
    _ = chartρ ≫ (ρ.s.fst.left ≫ eZ.inv ≫ g) ≫ f := by
          simp [Functor.pushforwardSourceProjection, Category.assoc]

-- Route correction: the literal `Q.map (sourcePrecomposeHom A f)` chart is not definitionally
-- the fixed-preimage model chart used in the compiled fibredness proof.  The remaining bridge is
-- to transport the model strong-cartesian result through the source-chart replacement API.
/-- Helper for Lemma 8.12.8: the literal localized source-precomposition chart is strongly
cartesian over its source base map. -/
theorem pushforwardProjection_Q_sourcePrecompose_isStronglyCartesian
    {S : Type uS} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered]
    (A : u ₚₚ p) {V : D} (f : V ⟶ A.fst.left) :
    (u.pushforwardProjection p).IsStronglyCartesian f
      ((u.pushforwardFractions p).Q.map
        (Functor.pushforwardSourcePrecomposeHom (u := u) (p := p) A f)) := by
  -- Work directly with right fractions: after clearing a denominator, the source
  -- precomposition lift supplies the required factor in the prelocalized category.
  let P := u.pushforwardProjection p
  let Q := (u.pushforwardFractions p).Q
  let α := Functor.pushforwardSourcePrecomposeHom (u := u) (p := p) A f
  let T := Functor.pushforwardSourcePrecomposeObj (u := u) (p := p) A f
  have hαLift : P.IsHomLift f (Q.map α) := by
    simpa [P, Q, α] using
      pushforwardProjection_Q_precompose_isHomLift (u := u) (p := p) A f
  refine
    { toIsHomLift := hαLift
      universal_property' := ?_ }
  intro Z g θ hθ
  letI : P.IsHomLift (g ≫ f) θ := hθ
  obtain ⟨ρ, hρ⟩ :=
    Localization.exists_rightFraction Q (u.pushforwardFractions p)
      ((Q.objObjPreimageIso Z).hom ≫ θ)
  have hρnum :
      Q.map ρ.s ≫ ((Q.objObjPreimageIso Z).hom ≫ θ) = Q.map ρ.f := by
    rw [hρ]
    exact MorphismProperty.RightFraction.map_s_comp_map ρ Q
      (Localization.inverts Q (u.pushforwardFractions p))
  let gρ : ρ.X'.fst.left ⟶ V :=
    ρ.s.fst.left ≫
      (Functor.pushforwardProjectionStrictObjIso (u := u) (p := p) Z).inv ≫ g
  have hbase : (Functor.pushforwardSourceProjection u p).map ρ.f = gρ ≫ f := by
    simpa [P, Q, gρ] using
      pushforwardProjection_Q_fraction_source_base_eq (u := u) (p := p) A f g θ hθ ρ hρnum
  have hsource :
      ∃! χ₀ : ρ.X' ⟶ T,
        (Functor.pushforwardSourceProjection u p).IsHomLift gρ χ₀ ∧ χ₀ ≫ α = ρ.f := by
    simpa [T, α] using
      Functor.pushforwardProjectionIsoComma_fraction_source_factor
        (u := u) (p := p) f ρ gρ hbase
  rcases hsource with ⟨χ₀, hχ₀, hχ₀uniq⟩
  let σ : (u.pushforwardFractions p).RightFraction (Q.objPreimage Z) T :=
    MorphismProperty.RightFraction.mk ρ.s ρ.hs χ₀
  let χ : Z ⟶ Q.obj T :=
    (Q.objObjPreimageIso Z).inv ≫
      σ.map Q (Localization.inverts Q (u.pushforwardFractions p))
  have hχcomp : χ ≫ Q.map α = θ := by
    letI : IsIso (Q.map ρ.s) :=
      Localization.inverts Q (u.pushforwardFractions p) ρ.s ρ.hs
    have hσcomp :
        σ.map Q (Localization.inverts Q (u.pushforwardFractions p)) ≫ Q.map α =
          ρ.map Q (Localization.inverts Q (u.pushforwardFractions p)) := by
      apply (cancel_epi (Q.map ρ.s)).1
      calc
        Q.map ρ.s ≫
            (σ.map Q (Localization.inverts Q (u.pushforwardFractions p)) ≫ Q.map α) =
          (Q.map ρ.s ≫ σ.map Q (Localization.inverts Q (u.pushforwardFractions p))) ≫
            Q.map α := by
            simp [Category.assoc]
        _ = Q.map χ₀ ≫ Q.map α := by
            rw [MorphismProperty.RightFraction.map_s_comp_map σ Q
              (Localization.inverts Q (u.pushforwardFractions p))]
        _ = Q.map (χ₀ ≫ α) := by
            rw [Functor.map_comp]
        _ = Q.map ρ.f := by
            rw [hχ₀.2]
        _ = Q.map ρ.s ≫
              ρ.map Q (Localization.inverts Q (u.pushforwardFractions p)) := by
            exact (MorphismProperty.RightFraction.map_s_comp_map ρ Q
              (Localization.inverts Q (u.pushforwardFractions p))).symm
    apply (cancel_epi ((Q.objObjPreimageIso Z).hom)).1
    calc
      (Q.objObjPreimageIso Z).hom ≫ (χ ≫ Q.map α) =
          σ.map Q (Localization.inverts Q (u.pushforwardFractions p)) ≫ Q.map α := by
          simp [χ, Category.assoc]
      _ = ρ.map Q (Localization.inverts Q (u.pushforwardFractions p)) := hσcomp
      _ = (Q.objObjPreimageIso Z).hom ≫ θ := hρ.symm
  have hχlift : P.IsHomLift g χ := by
    let eZ := Functor.pushforwardProjectionStrictObjIso (u := u) (p := p) Z
    have hpreimage_hom :
        P.map (Q.objObjPreimageIso Z).hom = eZ.inv := by
      dsimp [P, eZ, Functor.pushforwardProjectionStrictObjIso]
      exact (Category.id_comp _).symm
    have hpreimage_inv :
        P.map (Q.objObjPreimageIso Z).inv = eZ.hom := by
      dsimp [P, eZ, Functor.pushforwardProjectionStrictObjIso]
      exact (Category.comp_id _).symm
    have hχ₀base : (Functor.pushforwardSourceProjection u p).map χ₀ = gρ := by
      letI : (Functor.pushforwardSourceProjection u p).IsHomLift gρ χ₀ := hχ₀.1
      simpa [Functor.pushforwardSourceProjection] using
        (IsHomLift.fac' (Functor.pushforwardSourceProjection u p) gρ χ₀)
    have hσden :
        P.map (Q.map ρ.s) ≫
            P.map (σ.map Q (Localization.inverts Q (u.pushforwardFractions p))) =
          P.map (Q.map χ₀) := by
      rw [← Functor.map_comp]
      rw [MorphismProperty.RightFraction.map_s_comp_map σ Q
        (Localization.inverts Q (u.pushforwardFractions p))]
    have hσbase :
        P.map (σ.map Q (Localization.inverts Q (u.pushforwardFractions p))) =
          eZ.inv ≫ g := by
      have hρsIso : IsIso ρ.s.fst.left :=
        pushforwardFractions_left_isIso (u := u) (p := p) ρ.hs
      letI : IsIso ρ.s.fst.left := hρsIso
      have hρs_base : P.map (Q.map ρ.s) = ρ.s.fst.left := by
        simpa [P, Q, Functor.pushforwardSourceProjection] using
          Functor.pushforwardProjection_fac_naturality (u := u) (p := p) ρ.s
      have hχ₀_qbase :
          P.map (Q.map χ₀) = (Functor.pushforwardSourceProjection u p).map χ₀ := by
        simpa [P, Q] using
          Functor.pushforwardProjection_fac_naturality (u := u) (p := p) χ₀
      apply (cancel_epi ρ.s.fst.left).1
      have hσden' :
          ρ.s.fst.left ≫
              P.map (σ.map Q (Localization.inverts Q (u.pushforwardFractions p))) =
            (Functor.pushforwardSourceProjection u p).map χ₀ := by
        simpa [hρs_base, hχ₀_qbase] using hσden
      have hχ₀base' :
          (Functor.pushforwardSourceProjection u p).map χ₀ =
            ρ.s.fst.left ≫ eZ.inv ≫ g := by
        rw [hχ₀base]
      exact hσden'.trans hχ₀base'
    have hχmap : P.map χ = g := by
      calc
        P.map χ =
            P.map (Q.objObjPreimageIso Z).inv ≫
              P.map (σ.map Q (Localization.inverts Q (u.pushforwardFractions p))) := by
            simpa [χ] using
              (Functor.map_comp P (Q.objObjPreimageIso Z).inv
                (σ.map Q (Localization.inverts Q (u.pushforwardFractions p))))
        _ = eZ.hom ≫ (eZ.inv ≫ g) := by
            exact congrArg₂ (fun a b ↦ a ≫ b) hpreimage_inv hσbase
        _ = g := by
            simp [Category.assoc]
    rw [← hχmap]
    exact Functor.IsHomLift.map (p := P) χ
  refine ⟨χ, ⟨hχlift, hχcomp⟩, ?_⟩
  intro χ' hχ'
  obtain ⟨τ, hτ⟩ :=
    Localization.exists_rightFraction Q (u.pushforwardFractions p)
      ((Q.objObjPreimageIso Z).hom ≫ χ')
  have hτnum :
      Q.map τ.s ≫ ((Q.objObjPreimageIso Z).hom ≫ χ') = Q.map τ.f := by
    rw [hτ]
    exact MorphismProperty.RightFraction.map_s_comp_map τ Q
      (Localization.inverts Q (u.pushforwardFractions p))
  have hτbase :
      (Functor.pushforwardSourceProjection u p).map τ.f =
        (τ.s.fst.left ≫
          (Functor.pushforwardProjectionStrictObjIso (u := u) (p := p) Z).inv ≫ g) ≫
            𝟙 V := by
    have hχ'lift_id : P.IsHomLift (g ≫ 𝟙 V) χ' := by
      simpa using hχ'.1
    simpa [P, Q, T] using
      pushforwardProjection_Q_fraction_source_base_eq
        (u := u) (p := p) T (𝟙 V) g χ' hχ'lift_id τ hτnum
  have hτ_comp_α :
      τ.map Q (Localization.inverts Q (u.pushforwardFractions p)) ≫ Q.map α =
        ρ.map Q (Localization.inverts Q (u.pushforwardFractions p)) := by
    calc
      τ.map Q (Localization.inverts Q (u.pushforwardFractions p)) ≫ Q.map α =
          ((Q.objObjPreimageIso Z).hom ≫ χ') ≫ Q.map α := by
          rw [← hτ]
      _ = (Q.objObjPreimageIso Z).hom ≫ θ := by
          rw [Category.assoc, hχ'.2]
      _ = ρ.map Q (Localization.inverts Q (u.pushforwardFractions p)) := hρ
  let τα : (u.pushforwardFractions p).RightFraction (Q.objPreimage Z) A :=
    MorphismProperty.RightFraction.mk τ.s τ.hs (τ.f ≫ α)
  have hτα_map :
      τα.map Q (Localization.inverts Q (u.pushforwardFractions p)) =
        τ.map Q (Localization.inverts Q (u.pushforwardFractions p)) ≫ Q.map α := by
    letI : IsIso (Q.map τ.s) :=
      Localization.inverts Q (u.pushforwardFractions p) τ.s τ.hs
    apply (cancel_epi (Q.map τ.s)).1
    calc
      Q.map τ.s ≫ τα.map Q (Localization.inverts Q (u.pushforwardFractions p)) =
          Q.map (τ.f ≫ α) := by
          exact MorphismProperty.RightFraction.map_s_comp_map τα Q
            (Localization.inverts Q (u.pushforwardFractions p))
      _ = Q.map τ.f ≫ Q.map α := by
          rw [Functor.map_comp]
      _ =
          (Q.map τ.s ≫ τ.map Q (Localization.inverts Q (u.pushforwardFractions p))) ≫
            Q.map α := by
          rw [MorphismProperty.RightFraction.map_s_comp_map τ Q
            (Localization.inverts Q (u.pushforwardFractions p))]
      _ =
          Q.map τ.s ≫
            (τ.map Q (Localization.inverts Q (u.pushforwardFractions p)) ≫ Q.map α) := by
          simp [Category.assoc]
  have hταρ :
      MorphismProperty.RightFractionRel τα ρ := by
    rw [← MorphismProperty.RightFraction.map_eq_iff Q (u.pushforwardFractions p)]
    rw [hτα_map]
    exact hτ_comp_α
  rcases hταρ with ⟨M, aτ, aρ, hden, hnum, hmem⟩
  have hnum_T : aτ ≫ τ.f = aρ ≫ χ₀ := by
    let Psrc := Functor.pushforwardSourceProjection u p
    let eZ := Functor.pushforwardProjectionStrictObjIso (u := u) (p := p) Z
    let hM : M.fst.left ⟶ V := aρ.fst.left ≫ gρ
    have hτbase' : Psrc.map τ.f = τ.s.fst.left ≫ eZ.inv ≫ g := by
      simpa [Psrc, eZ] using hτbase
    have hden_left : aτ.fst.left ≫ τ.s.fst.left = aρ.fst.left ≫ ρ.s.fst.left := by
      simpa [Category.assoc] using congrArg (fun k ↦ k.fst.left) hden
    have hχ₀base_src : Psrc.map χ₀ = gρ := by
      letI : Psrc.IsHomLift gρ χ₀ := hχ₀.1
      simpa [Psrc] using (IsHomLift.fac' Psrc gρ χ₀)
    have hleft_base : Psrc.map (aτ ≫ τ.f) = hM := by
      calc
        Psrc.map (aτ ≫ τ.f) = Psrc.map aτ ≫ Psrc.map τ.f := by
          rw [Functor.map_comp]
        _ = aτ.fst.left ≫ (τ.s.fst.left ≫ eZ.inv ≫ g) := by
          rw [hτbase']
          rfl
        _ = (aτ.fst.left ≫ τ.s.fst.left) ≫ eZ.inv ≫ g := by
          simp [Category.assoc]
        _ = (aρ.fst.left ≫ ρ.s.fst.left) ≫ eZ.inv ≫ g := by
          rw [hden_left]
        _ = aρ.fst.left ≫ gρ := by
          simpa [gρ, eZ, Functor.pushforwardProjectionStrictObjIso, Category.assoc]
    have hright_base : Psrc.map (aρ ≫ χ₀) = hM := by
      calc
        Psrc.map (aρ ≫ χ₀) = Psrc.map aρ ≫ Psrc.map χ₀ := by
          rw [Functor.map_comp]
        _ = aρ.fst.left ≫ gρ := by
          rw [hχ₀base_src]
          rfl
    have hleftLift : Psrc.IsHomLift hM (aτ ≫ τ.f) := by
      rw [← hleft_base]
      exact Functor.IsHomLift.map (p := Psrc) (aτ ≫ τ.f)
    have hrightLift : Psrc.IsHomLift hM (aρ ≫ χ₀) := by
      rw [← hright_base]
      exact Functor.IsHomLift.map (p := Psrc) (aρ ≫ χ₀)
    letI : Psrc.IsStronglyCartesian f α :=
      Functor.pushforwardSource_precompose_isStronglyCartesian (u := u) (p := p) A f
    letI : Psrc.IsHomLift hM (aτ ≫ τ.f) := hleftLift
    letI : Psrc.IsHomLift hM (aρ ≫ χ₀) := hrightLift
    have hcomp_T : (aτ ≫ τ.f) ≫ α = (aρ ≫ χ₀) ≫ α := by
      calc
        (aτ ≫ τ.f) ≫ α = aτ ≫ (τ.f ≫ α) := by
          simp [Category.assoc]
        _ = aτ ≫ τα.f := by
          rfl
        _ = aρ ≫ ρ.f := hnum
        _ = aρ ≫ (χ₀ ≫ α) := by
          rw [hχ₀.2]
        _ = (aρ ≫ χ₀) ≫ α := by
          simp [Category.assoc]
    exact Functor.IsStronglyCartesian.ext Psrc f α hM hcomp_T
  have hτσ : MorphismProperty.RightFractionRel τ σ := by
    exact ⟨M, aτ, aρ, hden, hnum_T, hmem⟩
  have hτ_eq_σ :
      τ.map Q (Localization.inverts Q (u.pushforwardFractions p)) =
        σ.map Q (Localization.inverts Q (u.pushforwardFractions p)) := by
    rw [MorphismProperty.RightFraction.map_eq_iff Q (u.pushforwardFractions p)]
    exact hτσ
  apply (cancel_epi ((Q.objObjPreimageIso Z).hom)).1
  calc
    (Q.objObjPreimageIso Z).hom ≫ χ' =
        τ.map Q (Localization.inverts Q (u.pushforwardFractions p)) := hτ
    _ = σ.map Q (Localization.inverts Q (u.pushforwardFractions p)) := hτ_eq_σ
    _ = (Q.objObjPreimageIso Z).hom ≫ χ := by
        simp [χ, Category.assoc]

/-- Helper for Lemma 8.12.8: after applying the localized pushforward projection, the inverse
of an isomorphism cancels its forward map on the left. -/
theorem pushforwardProjection_map_inv_comp_map
    {S : Type uS} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered]
    {A B : u ₚ p} (s : A ⟶ B) [IsIso s] :
    (u.pushforwardProjection p).map (inv s) ≫
        (u.pushforwardProjection p).map s =
      𝟙 ((u.pushforwardProjection p).obj B) := by
  -- Collapse the two projected maps to the projection of `inv s ≫ s`, then use the
  -- construction-lift identity computation.
  rw [← Functor.pushforwardProjection_map_comp]
  rw [IsIso.inv_hom_id]
  exact Functor.pushforwardProjection_map_id (u := u) (p := p) B

/-- The canonical functor from `X` to the prelocalized source category `uₚₚ X`. It sends
`x / U` to `(U, id_{u(U)}, x)`. -/
abbrev pushforwardFibredCategoryUnitPrelocalized
    (u : C ⥤ D) (X : FibredCategoryOver C) :
    X.S ⥤ u ₚₚ X.p where
  obj x :=
    { fst :=
        { left := u.obj (X.p.obj x)
          right := X.p.obj x
          hom := 𝟙 (u.obj (X.p.obj x)) }
      snd := x
      iso := Iso.refl (X.p.obj x) }
  map {x y} f :=
    { fst :=
        { left := u.map (X.p.map f)
          right := X.p.map f }
      snd := f }

/-- The canonical functor from `X` to the localized pushforward fibred category `uₚ X`. -/
noncomputable abbrev pushforwardFibredCategoryUnit
    (X : FibredCategoryOver C) :
    X.S ⥤ (FibredCategoryOver.pushforward u X).S :=
  pushforwardFibredCategoryUnitPrelocalized u X ⋙
    (u.pushforwardFractions X.p).Q

/-- Helper for Lemma 8.12.8: the prelocalized unit map factors through a denominator followed by
the source-precomposition chart. -/
private theorem pushforwardFibredCategoryUnitPrelocalized_factor_sourcePrecompose
    (X : FibredCategoryOver C) {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    ∃ γ :
        (pushforwardFibredCategoryUnitPrelocalized u X).obj a ⟶
          Functor.pushforwardSourcePrecomposeObj (u := u) (p := X.p)
            ((pushforwardFibredCategoryUnitPrelocalized u X).obj b)
            (u.map (X.p.map φ)),
      u.pushforwardFractions X.p γ ∧
        γ ≫
            Functor.pushforwardSourcePrecomposeHom (u := u) (p := X.p)
              ((pushforwardFibredCategoryUnitPrelocalized u X).obj b)
              (u.map (X.p.map φ)) =
          (pushforwardFibredCategoryUnitPrelocalized u X).map φ := by
  -- The denominator keeps the `D`-source fixed and carries the strongly cartesian `X`-arrow.
  let A : u ₚₚ X.p := (pushforwardFibredCategoryUnitPrelocalized u X).obj b
  let sourceBase : u.obj (X.p.obj a) ⟶ A.fst.left := u.map (X.p.map φ)
  let γ :
      (pushforwardFibredCategoryUnitPrelocalized u X).obj a ⟶
        Functor.pushforwardSourcePrecomposeObj (u := u) (p := X.p) A sourceBase :=
    { fst :=
        { left := 𝟙 (u.obj (X.p.obj a))
          right := X.p.map φ }
      snd := φ }
  refine ⟨γ, ?_, ?_⟩
  · -- Membership in the denominator property is verticality in `D` plus the given strong
    -- cartesianness in `X`.
    constructor
    · refine ⟨rfl, ?_⟩
      rfl
    · simpa [γ] using hφ
  · -- The factorization is checked componentwise in the pullback source category.
    apply CategoricalPullback.hom_ext
    · apply CategoryTheory.Comma.hom_ext
      · simp [γ, A, sourceBase, pushforwardFibredCategoryUnitPrelocalized,
          Functor.pushforwardSourcePrecomposeObj,
          Functor.pushforwardSourcePrecomposeHom]
      · simp [γ, A, sourceBase, pushforwardFibredCategoryUnitPrelocalized,
          Functor.pushforwardSourcePrecomposeObj,
          Functor.pushforwardSourcePrecomposeHom]
    · simp [γ, A, sourceBase, pushforwardFibredCategoryUnitPrelocalized,
        Functor.pushforwardSourcePrecomposeObj,
        Functor.pushforwardSourcePrecomposeHom]

/-- Helper for Lemma 8.12.8: the canonical unit morphism of the pushforward construction is a
chosen strongly cartesian precomposition morphism after localization. -/
theorem pushforwardFibredCategoryUnit_preservesStronglyCartesian
    (X : FibredCategoryOver C) {a b : X.S} (φ : a ⟶ b)
    (_hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    (FibredCategoryOver.pushforward u X).p.IsStronglyCartesian
      ((FibredCategoryOver.pushforward u X).p.map ((pushforwardFibredCategoryUnit u X).map φ))
      ((pushforwardFibredCategoryUnit u X).map φ) := by
  -- Factor the unit arrow into a denominator and the literal source-precomposition chart, then
  -- compose the two strong-cartesian pieces after localization.
  let pU := (FibredCategoryOver.pushforward u X).p
  let A : u ₚₚ X.p := (pushforwardFibredCategoryUnitPrelocalized u X).obj b
  let sourceBase : u.obj (X.p.obj a) ⟶ A.fst.left := u.map (X.p.map φ)
  let Q := (u.pushforwardFractions X.p).Q
  let β := Q.map (Functor.pushforwardSourcePrecomposeHom (u := u) (p := X.p) A sourceBase)
  obtain ⟨γ, hγmem, hγcomp⟩ :=
    pushforwardFibredCategoryUnitPrelocalized_factor_sourcePrecompose u X φ _hφ
  have hunit :
      Q.map γ ≫ β = (pushforwardFibredCategoryUnit u X).map φ := by
    -- Localization respects the prelocalized factorization of the unit map.
    simpa [Q, β, pushforwardFibredCategoryUnit, A, sourceBase, Functor.map_comp] using
      congrArg (fun k ↦ Q.map k) hγcomp
  have hβLift : pU.IsHomLift sourceBase β := by
    simpa [pU, β, FibredCategoryOver.pushforward_p] using
      pushforwardProjection_Q_precompose_isHomLift (u := u) (p := X.p) A sourceBase
  letI : pU.IsFibered := by
    simpa [pU, FibredCategoryOver.pushforward_p] using
      Functor.pushforwardProjection_isFibered u X.p
  have hγIso : IsIso (Q.map γ) :=
    Localization.inverts Q (u.pushforwardFractions X.p) γ hγmem
  have hγLift : pU.IsHomLift (pU.map (Q.map γ)) (Q.map γ) := by
    infer_instance
  letI : IsIso (Q.map γ) := hγIso
  letI : pU.IsHomLift (pU.map (Q.map γ)) (Q.map γ) := hγLift
  have hγ :
      pU.IsStronglyCartesian (pU.map (Q.map γ)) (Q.map γ) :=
    @Functor.IsStronglyCartesian.of_isIso _ _ _ _ pU _ _ _ _
      (pU.map (Q.map γ)) (Q.map γ) hγLift hγIso
  have hβ :
      pU.IsStronglyCartesian sourceBase β := by
    simpa [pU, FibredCategoryOver.pushforward_p, β] using
      pushforwardProjection_Q_sourcePrecompose_isStronglyCartesian
        (u := u) (p := X.p) A sourceBase
  letI : pU.IsStronglyCartesian (pU.map (Q.map γ)) (Q.map γ) := hγ
  letI : pU.IsStronglyCartesian sourceBase β := hβ
  have hcomp :
      pU.IsStronglyCartesian (pU.map (Q.map γ) ≫ sourceBase)
        (Q.map γ ≫ β) := by
    exact @Functor.IsStronglyCartesian.comp _ _ _ _ pU _ _ _ _ _ _ _ _ _ _ hγ hβ
  have hunitExternal :
      pU.IsStronglyCartesian (pU.map (Q.map γ) ≫ sourceBase)
        ((pushforwardFibredCategoryUnit u X).map φ) := by
    rw [← hunit]
    exact hcomp
  letI :
      pU.IsStronglyCartesian (pU.map (Q.map γ) ≫ sourceBase)
        ((pushforwardFibredCategoryUnit u X).map φ) :=
    hunitExternal
  -- Rebase the external source map to the owner projection map of the same unit arrow.
  have hb :
      pU.obj ((pushforwardFibredCategoryUnit u X).obj b) = A.fst.left := by
    rfl
  exact BasedFunctor.isStronglyCartesian_rebase_over_target_eq
    (p := pU) (hb := hb)
    (f := pU.map (Q.map γ) ≫ sourceBase)
    (φ := (pushforwardFibredCategoryUnit u X).map φ)

/-- Helper for Lemma 8.12.8: before localizing, the canonical unit has the expected projection
to the base category `D`. -/
private theorem pushforwardFibredCategoryUnitPrelocalized_comp_sourceProjection
    (X : FibredCategoryOver C) :
    pushforwardFibredCategoryUnitPrelocalized u X ⋙
      Functor.pushforwardSourceProjection u X.p = X.p ⋙ u := by
  -- The prelocalized unit was chosen with left component `u.obj (X.p.obj x)` and left map
  -- `u.map (X.p.map f)`, so both object and morphism maps are definitionally the base composite.
  rfl

-- Proof sketch: the prelocalized unit maps `x / U` to `(U, id_{u(U)}, x)`, whose image under
-- the prelocalized projection is `u.obj U`. Passing through the localization does not change the
-- resulting base functor.
/-- Composing the canonical unit `X ⥤ uₚ X` with the projection to `D` recovers `u ∘ X.p`. -/
theorem pushforwardFibredCategoryUnit_comp_projection
    (X : FibredCategoryOver C) :
    pushforwardFibredCategoryUnit u X ⋙ (FibredCategoryOver.pushforward u X).p = X.p ⋙ u := by
  -- The strict construction lift computes on the image of the localization functor by
  -- `Localization.Construction.fac`, then the prelocalized unit computes literally.
  rw [pushforwardFibredCategoryUnit, FibredCategoryOver.pushforward_p]
  have hfac :
      (u.pushforwardFractions X.p).Q ⋙ u.pushforwardProjection X.p =
        Functor.pushforwardSourceProjection u X.p := by
    rw [Functor.pushforwardProjection]
    exact Localization.Construction.fac _ _
  -- Whisker the localization computation by the prelocalized unit, then finish with the
  -- literal source-projection computation for that unit.
  calc
    pushforwardFibredCategoryUnitPrelocalized u X ⋙ (u.pushforwardFractions X.p).Q ⋙
        u.pushforwardProjection X.p =
      pushforwardFibredCategoryUnitPrelocalized u X ⋙
        ((u.pushforwardFractions X.p).Q ⋙ u.pushforwardProjection X.p) := by
        rfl
    _ = pushforwardFibredCategoryUnitPrelocalized u X ⋙
        Functor.pushforwardSourceProjection u X.p := by
        rw [hfac]
    _ = X.p ⋙ u :=
        pushforwardFibredCategoryUnitPrelocalized_comp_sourceProjection u X

/-- Helper for Lemma 8.12.8: the canonical unit morphism in the localized pushforward lies over
the image under `u` of the original base morphism. -/
private theorem pushforwardFibredCategoryUnit_map_isHomLift
    (X : FibredCategoryOver C) {a b : X.S} (φ : a ⟶ b) :
    (FibredCategoryOver.pushforward u X).p.IsHomLift (u.map (X.p.map φ))
      ((pushforwardFibredCategoryUnit u X).map φ) := by
  -- The projection computation for the unit gives the base map of every unit morphism.
  let η := pushforwardFibredCategoryUnit u X
  let pU := (FibredCategoryOver.pushforward u X).p
  let hfun : η ⋙ pU = X.p ⋙ u := pushforwardFibredCategoryUnit_comp_projection u X
  let ha : pU.obj (η.obj a) = u.obj (X.p.obj a) := Functor.congr_obj hfun a
  let hb : pU.obj (η.obj b) = u.obj (X.p.obj b) := Functor.congr_obj hfun b
  refine IsHomLift.of_fac' (FibredCategoryOver.pushforward u X).p
    (u.map (X.p.map φ)) ((pushforwardFibredCategoryUnit u X).map φ) ha hb ?_
  simpa [η, pU, hfun, ha, hb, Functor.comp_map] using Functor.congr_hom hfun φ

end Pushforward

end

end CategoryTheory
