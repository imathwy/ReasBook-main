import stacks_proof.stacks_project.Chap08.Lemma_8_12_6.SourcePrecomposition
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

/-- Helper for Lemma 8.12.6: the localization comparison at the descended source object identifies
its base under `u.pushforwardProjection p` with the source-side object `V`. -/
noncomputable abbrev pushforwardProjection_precompose_baseIso
    (Y₀ : u ₚₚ p) {V : D} (sourceBase : V ⟶ Y₀.fst.left) :
    (u.pushforwardProjection p).obj
        ((u.pushforwardFractions p).Q.obj
          (pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase)) ≅
      V :=
  Iso.refl V

/-- Helper for Lemma 8.12.6: with the construction localization lift, the precomposition
comparison chart has identity forward map. -/
@[simp]
theorem pushforwardProjection_precompose_baseIso_hom
    (Y₀ : u ₚₚ p) {V : D} (sourceBase : V ⟶ Y₀.fst.left) :
    (pushforwardProjection_precompose_baseIso (u := u) (p := p) Y₀ sourceBase).hom =
      𝟙 _ := by
  -- Unfold only the owner definitions; the construction-lift comparison computes on objects.
  rfl

/-- Helper for Lemma 8.12.6: on objects coming directly from `u ₚₚ p`, the localized projection
is canonically identified with the source projection by the localization comparison isomorphism. -/
noncomputable abbrev pushforwardProjection_obj_Q_obj_base
    (A : u ₚₚ p) :
    (u.pushforwardProjection p).obj ((u.pushforwardFractions p).Q.obj A) ≅
      (pushforwardSourceProjection u p).obj A :=
  Iso.refl ((pushforwardSourceProjection u p).obj A)

/-- Helper for Lemma 8.12.6: with the construction localization lift, the comparison on
canonical `Q.obj` objects has identity forward map. -/
@[simp]
theorem pushforwardProjection_obj_Q_obj_base_hom
    (A : u ₚₚ p) :
    (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).hom = 𝟙 _ := by
  -- This is the same construction-lift computation away from the precomposition wrapper.
  rfl

/-- Helper for Lemma 8.12.6: the construction-lift projection preserves identity maps in the
localized pushforward category. -/
@[simp]
theorem pushforwardProjection_map_id (Y : u ₚ p) :
    (u.pushforwardProjection p).map (𝟙 Y) = 𝟙 _ := by
  -- Keep identity-map normalization behind a named lemma so simp need not unfold the quotient
  -- construction of the localization lift.
  exact Functor.map_id (u.pushforwardProjection p) Y

/-- Helper for Lemma 8.12.6: the construction-lift projection preserves composition in the
localized pushforward category. -/
@[simp]
theorem pushforwardProjection_map_comp {X Y Z : u ₚ p} (ψ : X ⟶ Y) (χ : Y ⟶ Z) :
    (u.pushforwardProjection p).map (ψ ≫ χ) =
      (u.pushforwardProjection p).map ψ ≫ (u.pushforwardProjection p).map χ := by
  -- Keep composition normalization behind a named lemma for stable strict-model rewrites.
  exact Functor.map_comp (u.pushforwardProjection p) ψ χ

/-- Helper for Lemma 8.12.6: after descent through `Q`, the chosen precomposition morphism is a
hom-lift for the transported base map coming from the localization comparison at the source
object. -/
theorem pushforwardProjection_precompose_toIsHomLift_transported
    (Y : u ₚ p) {V : D} (f : V ⟶ (u.pushforwardProjection p).obj Y) :
    let Q := (u.pushforwardFractions p).Q
    let Y₀ := Q.objPreimage Y
    let eY : Q.obj Y₀ ≅ Y := Q.objObjPreimageIso Y
    let sourceBase : V ⟶ Y₀.fst.left :=
      f ≫ (u.pushforwardProjection p).map eY.inv
    let X₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
    let φ₀ := pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase
    let X : u ₚ p := Q.obj X₀
    let φ : X ⟶ Y := Q.map φ₀ ≫ eY.hom
    let eX := pushforwardProjection_precompose_baseIso (u := u) (p := p) Y₀ sourceBase
    (u.pushforwardProjection p).IsHomLift (eX.hom ≫ f) φ := by
  -- Work in the fixed source-preimage chart and rewrite the descended base map using the
  -- construction-lift computation on `Q`.
  dsimp [pushforwardProjection_precompose_baseIso]
  let Q := (u.pushforwardFractions p).Q
  let Y₀ := Q.objPreimage Y
  let eY : Q.obj Y₀ ≅ Y := Q.objObjPreimageIso Y
  let sourceBase : V ⟶ Y₀.fst.left :=
    f ≫ (u.pushforwardProjection p).map eY.inv
  let X₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
  let φ₀ := pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase
  let X : u ₚ p := Q.obj X₀
  let φ : X ⟶ Y := Q.map φ₀ ≫ eY.hom
  let eX :
      (u.pushforwardProjection p).obj X ≅ V :=
    Iso.refl V
  have hfac' :
      (u.pushforwardProjection p).map (Q.map φ₀) =
        sourceBase :=
      by
    -- The prelocalized precomposition arrow projects to the chosen source-base map.
    simpa [Q, φ₀, sourceBase] using
      pushforwardProjection_precompose_fac (u := u) (p := p) Y₀ sourceBase
  have htarget_collapse :
      sourceBase ≫ (u.pushforwardProjection p).map eY.hom = f := by
    -- The chosen preimage isomorphism cancels on the target side.
    have heY :
        (u.pushforwardProjection p).map eY.inv ≫
            (u.pushforwardProjection p).map eY.hom =
          𝟙 _ := by
      simpa using ((u.pushforwardProjection p).mapIso eY).inv_hom_id
    calc
      sourceBase ≫ (u.pushforwardProjection p).map eY.hom
          = (f ≫ (u.pushforwardProjection p).map eY.inv) ≫
              (u.pushforwardProjection p).map eY.hom := by
            dsimp [sourceBase]
            rfl
      _ = f ≫ ((u.pushforwardProjection p).map eY.inv ≫
              (u.pushforwardProjection p).map eY.hom) := by
            simp [Category.assoc]
      _ = f ≫ 𝟙 _ := by
            rw [heY]
      _ = f := by
            simp
  -- Rewrite the descended base map through the source equation and then collapse the two
  -- comparison isomorphisms on the target object.
  have hφmap : (u.pushforwardProjection p).map φ = f := by
    calc
    (u.pushforwardProjection p).map φ
        = (u.pushforwardProjection p).map (Q.map φ₀) ≫
            (u.pushforwardProjection p).map eY.hom := by
              change
                (u.pushforwardProjection p).map (Q.map φ₀ ≫ eY.hom) =
                  (u.pushforwardProjection p).map (Q.map φ₀) ≫
                    (u.pushforwardProjection p).map eY.hom
              exact Functor.map_comp (u.pushforwardProjection p) (Q.map φ₀) eY.hom
    _ = sourceBase ≫ (u.pushforwardProjection p).map eY.hom := by
              exact congrArg (fun k ↦ k ≫ (u.pushforwardProjection p).map eY.hom) hfac'
    _ = f := htarget_collapse
  refine IsHomLift.of_fac' (u.pushforwardProjection p) (eX.hom ≫ f) φ rfl rfl ?_
  rw [hφmap]
  dsimp [eX]
  rw [Category.id_comp, Category.comp_id]
  exact (Category.id_comp f).symm

/-- Helper for Lemma 8.12.6: the descended source precomposition arrow already gives a localized
model lift, with the only remaining issue being the comparison isomorphism on its domain object
over `V`. -/
theorem pushforwardProjection_precompose_transported_model_lift
    (Y : u ₚ p) {V : D} (f : V ⟶ (u.pushforwardProjection p).obj Y) :
    let Q := (u.pushforwardFractions p).Q
    let Y₀ := Q.objPreimage Y
    let eY : Q.obj Y₀ ≅ Y := Q.objObjPreimageIso Y
    let sourceBase : V ⟶ Y₀.fst.left :=
      f ≫ (u.pushforwardProjection p).map eY.inv
    let X₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
    let φ₀ := pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase
    let X : u ₚ p := Q.obj X₀
    let φ : X ⟶ Y := Q.map φ₀ ≫ eY.hom
    ∃ eX : (u.pushforwardProjection p).obj X ≅ V,
      (u.pushforwardProjection p).IsHomLift (eX.hom ≫ f) φ := by
  classical
  dsimp
  let eX := pushforwardProjection_precompose_baseIso (u := u) (p := p)
    ((u.pushforwardFractions p).Q.objPreimage Y)
    (f ≫
      (u.pushforwardProjection p).map (((u.pushforwardFractions p).Q.objObjPreimageIso Y).inv))
  -- Package the already-verified transported lift so the main theorem can focus only on
  -- strictifying the comparison isomorphism `eX`.
  refine ⟨eX, ?_⟩
  exact
    pushforwardProjection_precompose_toIsHomLift_transported
      (u := u) (p := p) Y f

/-- Helper for Lemma 8.12.6: after transporting a localized morphism into fixed source charts, we
can choose a right-fraction representative for it. -/
theorem pushforwardProjection_preimage_exists_rightFraction
    {Y Z : u ₚ p} (ψ : Z ⟶ Y) :
    let Q := (u.pushforwardFractions p).Q
    ∃ ρ : (u.pushforwardFractions p).RightFraction (Q.objPreimage Z) (Q.objPreimage Y),
      (Q.objObjPreimageIso Z).hom ≫ ψ ≫ (Q.objObjPreimageIso Y).inv =
        ρ.map Q (Localization.inverts Q (u.pushforwardFractions p)) := by
  classical
  dsimp
  -- This is the canonical right-fraction presentation of a localization morphism.
  exact Localization.exists_rightFraction ((u.pushforwardFractions p).Q) (u.pushforwardFractions p)
    (((u.pushforwardFractions p).Q.objObjPreimageIso Z).hom ≫ ψ ≫
      ((u.pushforwardFractions p).Q.objObjPreimageIso Y).inv)

/-- Helper for Lemma 8.12.6: the strict model uses the chosen source preimage of a localized
object as its literal base object in `D`. -/
noncomputable abbrev pushforwardProjectionStrictObj (Y : u ₚ p) : D :=
  (((u.pushforwardFractions p).Q).objPreimage Y).fst.left

/-- Helper for Lemma 8.12.6: the chart from the canonical localized projection to the fixed source
preimage base object. -/
noncomputable abbrev pushforwardProjectionStrictObjIso (Y : u ₚ p) :
    (u.pushforwardProjection p).obj Y ≅ pushforwardProjectionStrictObj (u := u) (p := p) Y :=
  (u.pushforwardProjection p).mapIso (((u.pushforwardFractions p).Q.objObjPreimageIso Y).symm) ≪≫
    pushforwardProjection_obj_Q_obj_base (u := u) (p := p)
      (((u.pushforwardFractions p).Q).objPreimage Y)

/-- Helper for Lemma 8.12.6: on morphisms, the strict model is obtained by conjugating the
canonical localized projection with the chosen source charts. -/
noncomputable abbrev pushforwardProjectionStrictMap {X Y : u ₚ p} (ψ : X ⟶ Y) :
    pushforwardProjectionStrictObj (u := u) (p := p) X ⟶
      pushforwardProjectionStrictObj (u := u) (p := p) Y :=
  (pushforwardProjectionStrictObjIso (u := u) (p := p) X).inv ≫
    (u.pushforwardProjection p).map ψ ≫
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Y).hom

/-- Helper for Lemma 8.12.6: the strict model preserves identities because the chart
conjugation cancels at the identity map. -/
theorem pushforwardProjectionStrict_map_id (X : u ₚ p) :
    pushforwardProjectionStrictMap (u := u) (p := p) (𝟙 X) =
      𝟙 (pushforwardProjectionStrictObj (u := u) (p := p) X) := by
  -- Normalize the conjugated identity and cancel the chart isomorphism.
  let chart := pushforwardProjectionStrictObjIso (u := u) (p := p) X
  change chart.inv ≫ (u.pushforwardProjection p).map (𝟙 X) ≫ chart.hom =
    𝟙 (pushforwardProjectionStrictObj (u := u) (p := p) X)
  rw [Functor.map_id]
  simpa [chart, Category.assoc] using
    (pushforwardProjectionStrictObjIso (u := u) (p := p) X).inv_hom_id

/-- Helper for Lemma 8.12.6: the strict model preserves composition because the middle chart
components cancel. -/
theorem pushforwardProjectionStrict_map_comp {X Y Z : u ₚ p}
    (ψ : X ⟶ Y) (χ : Y ⟶ Z) :
    pushforwardProjectionStrictMap (u := u) (p := p) (ψ ≫ χ) =
      pushforwardProjectionStrictMap (u := u) (p := p) ψ ≫
        pushforwardProjectionStrictMap (u := u) (p := p) χ := by
  -- Expand the two conjugations and cancel the intermediate chart isomorphism.
  have hchartY :
      (pushforwardProjectionStrictObjIso (u := u) (p := p) Y).hom ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) Y).inv =
        𝟙 ((u.pushforwardProjection p).obj Y) := by
    exact (pushforwardProjectionStrictObjIso (u := u) (p := p) Y).hom_inv_id
  calc
    pushforwardProjectionStrictMap (u := u) (p := p) (ψ ≫ χ)
        =
          (pushforwardProjectionStrictObjIso (u := u) (p := p) X).inv ≫
            (u.pushforwardProjection p).map ψ ≫
              (u.pushforwardProjection p).map χ ≫
                (pushforwardProjectionStrictObjIso (u := u) (p := p) Z).hom := by
          change
            (pushforwardProjectionStrictObjIso (u := u) (p := p) X).inv ≫
                (u.pushforwardProjection p).map (ψ ≫ χ) ≫
                  (pushforwardProjectionStrictObjIso (u := u) (p := p) Z).hom =
              (pushforwardProjectionStrictObjIso (u := u) (p := p) X).inv ≫
                (u.pushforwardProjection p).map ψ ≫
                  (u.pushforwardProjection p).map χ ≫
                    (pushforwardProjectionStrictObjIso (u := u) (p := p) Z).hom
          rw [Functor.map_comp]
          simp [Category.assoc]
    _ =
          (pushforwardProjectionStrictObjIso (u := u) (p := p) X).inv ≫
            (u.pushforwardProjection p).map ψ ≫
              ((pushforwardProjectionStrictObjIso (u := u) (p := p) Y).hom ≫
                (pushforwardProjectionStrictObjIso (u := u) (p := p) Y).inv) ≫
                  (u.pushforwardProjection p).map χ ≫
                    (pushforwardProjectionStrictObjIso (u := u) (p := p) Z).hom := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                (pushforwardProjectionStrictObjIso (u := u) (p := p) X).inv ≫
                  (u.pushforwardProjection p).map ψ ≫ k ≫
                    (u.pushforwardProjection p).map χ ≫
                      (pushforwardProjectionStrictObjIso (u := u) (p := p) Z).hom)
              hchartY.symm
    _ = pushforwardProjectionStrictMap (u := u) (p := p) ψ ≫
          pushforwardProjectionStrictMap (u := u) (p := p) χ := by
          simp [pushforwardProjectionStrictMap, Category.assoc]

/-- Helper for Lemma 8.12.6: the strictified projection keeps the localized total category fixed
but replaces the object part by the chosen source-chart base object. -/
noncomputable abbrev pushforwardProjectionStrict :
    u ₚ p ⥤ D :=
  { obj := pushforwardProjectionStrictObj (u := u) (p := p)
    map := fun ψ ↦ pushforwardProjectionStrictMap (u := u) (p := p) ψ
    map_id := pushforwardProjectionStrict_map_id (u := u) (p := p)
    map_comp := pushforwardProjectionStrict_map_comp (u := u) (p := p) }

/-- Helper for Lemma 8.12.6: the chart isomorphisms are natural, so they assemble into a
comparison natural isomorphism from the canonical localized projection to the strict model. -/
theorem pushforwardProjectionStrictIso_naturality {X Y : u ₚ p} (ψ : X ⟶ Y) :
    (u.pushforwardProjection p).map ψ ≫
        (pushforwardProjectionStrictObjIso (u := u) (p := p) Y).hom =
      (pushforwardProjectionStrictObjIso (u := u) (p := p) X).hom ≫
        (pushforwardProjectionStrict u p).map ψ := by
  -- After unfolding the strict map, the left chart immediately cancels.
  have hchartX :
      (pushforwardProjectionStrictObjIso (u := u) (p := p) X).hom ≫
          (pushforwardProjectionStrictObjIso (u := u) (p := p) X).inv =
        𝟙 ((u.pushforwardProjection p).obj X) := by
    exact (pushforwardProjectionStrictObjIso (u := u) (p := p) X).hom_inv_id
  calc
    (u.pushforwardProjection p).map ψ ≫
        (pushforwardProjectionStrictObjIso (u := u) (p := p) Y).hom
        =
          (u.pushforwardProjection p).map ψ ≫
            (pushforwardProjectionStrictObjIso (u := u) (p := p) Y).hom := by rfl
    _ =
          (pushforwardProjectionStrictObjIso (u := u) (p := p) X).hom ≫
            (pushforwardProjectionStrictObjIso (u := u) (p := p) X).inv ≫
              (u.pushforwardProjection p).map ψ ≫
                (pushforwardProjectionStrictObjIso (u := u) (p := p) Y).hom := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                k ≫ (u.pushforwardProjection p).map ψ ≫
                  (pushforwardProjectionStrictObjIso (u := u) (p := p) Y).hom)
              hchartX.symm
    _ =
          (pushforwardProjectionStrictObjIso (u := u) (p := p) X).hom ≫
            (pushforwardProjectionStrict u p).map ψ := by
          simp [pushforwardProjectionStrict, pushforwardProjectionStrictMap, Category.assoc]

/-- Helper for Lemma 8.12.6: the canonical localized projection is naturally isomorphic to its
strict source-chart model. -/
noncomputable abbrev pushforwardProjectionStrictIso :
    u.pushforwardProjection p ≅ pushforwardProjectionStrict u p :=
  NatIso.ofComponents
    (fun Y ↦ pushforwardProjectionStrictObjIso (u := u) (p := p) Y)
    (fun ψ ↦ pushforwardProjectionStrictIso_naturality (u := u) (p := p) ψ)

/-- Helper for Lemma 8.12.6: on an object `Q.obj A`, the explicit target chart used in the
strict-model rewrite is exactly the composite of the inverse strict chart with the source-side
localization comparison. -/
theorem pushforwardProjectionStrict_obj_Q_obj_chart_hom
    (A : u ₚₚ p) :
    ((pushforwardProjectionStrictObjIso (u := u) (p := p)
        ((u.pushforwardFractions p).Q.obj A)).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).hom =
        (pushforwardProjectionStrictObjIso (u := u) (p := p)
            ((u.pushforwardFractions p).Q.obj A)).inv ≫
          (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).hom := by
  -- This is the literal `Iso.trans_hom` expansion that the strict-model rewrite needs.
  rw [Iso.trans_hom]
  rfl

/-- Helper for Lemma 8.12.6: after composing the strict chart with the explicit comparison chart
on `Q.obj A`, the intermediate strictification isomorphism cancels and only the source-side
localization comparison remains. -/
theorem pushforwardProjectionStrict_obj_Q_obj_chart_cancel
    (A : u ₚₚ p) :
    (pushforwardProjectionStrictObjIso (u := u) (p := p)
        ((u.pushforwardFractions p).Q.obj A)).hom ≫
      (((pushforwardProjectionStrictObjIso (u := u) (p := p)
            ((u.pushforwardFractions p).Q.obj A)).symm ≪≫
          pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).hom) =
        (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).hom := by
  -- Expand the explicit chart and cancel the strictification isomorphism as one composite.
  rw [pushforwardProjectionStrict_obj_Q_obj_chart_hom (u := u) (p := p) A]
  simpa [Category.assoc] using
    Iso.hom_inv_id_assoc
      (pushforwardProjectionStrictObjIso (u := u) (p := p)
        ((u.pushforwardFractions p).Q.obj A))
      ((pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).hom)

/-- Helper for Lemma 8.12.6: on arrows coming directly from the source category, the strict model
rewrites back to the source projection after composing with the chart isomorphisms from the
chosen source preimages. -/
theorem pushforwardProjectionStrict_map_Q_map
    {A B : u ₚₚ p} (k : A ⟶ B) :
    (pushforwardProjectionStrict u p).map ((u.pushforwardFractions p).Q.map k) ≫
        ((pushforwardProjectionStrictObjIso (u := u) (p := p)
            ((u.pushforwardFractions p).Q.obj B)).symm ≪≫
          pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).hom =
      ((pushforwardProjectionStrictObjIso (u := u) (p := p)
          ((u.pushforwardFractions p).Q.obj A)).symm ≪≫
        pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).hom ≫
          (pushforwardSourceProjection u p).map k := by
  -- Rewrite the strict-model map as a conjugated localized map and cancel the target chart.
  let chartA :=
    pushforwardProjectionStrictObjIso (u := u) (p := p) ((u.pushforwardFractions p).Q.obj A)
  let chartB :=
    pushforwardProjectionStrictObjIso (u := u) (p := p) ((u.pushforwardFractions p).Q.obj B)
  calc
    (pushforwardProjectionStrict u p).map ((u.pushforwardFractions p).Q.map k) ≫
        ((pushforwardProjectionStrictObjIso (u := u) (p := p)
            ((u.pushforwardFractions p).Q.obj B)).symm ≪≫
          pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).hom
        =
          chartA.inv ≫
            (u.pushforwardProjection p).map ((u.pushforwardFractions p).Q.map k) ≫
              chartB.hom ≫
                (((pushforwardProjectionStrictObjIso (u := u) (p := p)
                      ((u.pushforwardFractions p).Q.obj B)).symm ≪≫
                    pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).hom) := by
          simp [pushforwardProjectionStrict, pushforwardProjectionStrictMap, chartA, chartB,
            Category.assoc]
    _ =
          (chartA.inv ≫
            (u.pushforwardProjection p).map ((u.pushforwardFractions p).Q.map k)) ≫
              (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).hom := by
          -- The strict target chart disappears after postcomposing with the explicit comparison.
          simpa [chartA, chartB, Category.assoc] using
            congrArg (fun t ↦ (chartA.inv ≫ (u.pushforwardProjection p).map
              ((u.pushforwardFractions p).Q.map k)) ≫ t)
              (pushforwardProjectionStrict_obj_Q_obj_chart_cancel (u := u) (p := p) B)
    _ =
          chartA.inv ≫ (pushforwardSourceProjection u p).map k := by
          -- The construction-lift computation rewrites the localized source arrow after the
          -- target comparison chart has reduced to the identity.
          have htarget :
              (u.pushforwardProjection p).map ((u.pushforwardFractions p).Q.map k) ≫
                  (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).hom =
                (pushforwardSourceProjection u p).map k := by
            rw [pushforwardProjection_obj_Q_obj_base_hom (u := u) (p := p) B]
            calc
              (u.pushforwardProjection p).map ((u.pushforwardFractions p).Q.map k) ≫
                    𝟙 ((u.pushforwardProjection p).obj ((u.pushforwardFractions p).Q.obj B))
                  =
                (u.pushforwardProjection p).map ((u.pushforwardFractions p).Q.map k) :=
                  Category.comp_id
                    ((u.pushforwardProjection p).map ((u.pushforwardFractions p).Q.map k))
              _ = (pushforwardSourceProjection u p).map k :=
                  pushforwardProjection_fac_naturality (u := u) (p := p) k
          exact
            (Category.assoc chartA.inv
                ((u.pushforwardProjection p).map ((u.pushforwardFractions p).Q.map k))
                (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).hom).trans
              (congrArg (fun t ↦ chartA.inv ≫ t) htarget)
    _ =
          chartA.inv ≫
            (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).hom ≫
              (pushforwardSourceProjection u p).map k := by
          -- Reinsert the source comparison chart in the explicit endpoint shape.
          rw [pushforwardProjection_obj_Q_obj_base_hom (u := u) (p := p) A]
          rw [← Category.assoc]
          exact congrArg (fun t ↦ t ≫ (pushforwardSourceProjection u p).map k)
            (Category.comp_id chartA.inv).symm
    _ =
          ((pushforwardProjectionStrictObjIso (u := u) (p := p)
              ((u.pushforwardFractions p).Q.obj A)).symm ≪≫
            pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).hom ≫
              (pushforwardSourceProjection u p).map k := by
          -- Repackage the source chart into the explicit composite used by the source proof.
          simpa [chartA, Category.assoc] using
            congrArg (fun t ↦ t ≫ (pushforwardSourceProjection u p).map k)
              (pushforwardProjectionStrict_obj_Q_obj_chart_hom (u := u) (p := p) A)

end Functor

end

end CategoryTheory
