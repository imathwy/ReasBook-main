import StacksProject_2024.Chap08.Lemma_8_12_6.StrictProjection
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

/-- Helper for Lemma 8.12.6: the iso-comma comparison model keeps track of a literal base object
`V : D` together with an isomorphism `V ≅ (u.pushforwardProjection p).obj Y`. -/
abbrev pushforwardProjectionIsoCommaProperty :
    ObjectProperty (Comma (𝟭 D) (u.pushforwardProjection p)) :=
  fun X ↦ IsIso X.hom

/-- Helper for Lemma 8.12.6: the source-faithful comparison total category is the full
subcategory of `Comma (𝟭 D) (u.pushforwardProjection p)` on isomorphism arrows. -/
abbrev pushforwardProjectionIsoComma :=
  (pushforwardProjectionIsoCommaProperty (u := u) (p := p)).FullSubcategory

/-- Helper for Lemma 8.12.6: the iso-comma model projects to `D` by forgetting the localized
object and retaining the literal source object `V`. -/
noncomputable abbrev pushforwardProjectionIsoCommaProjection :
    pushforwardProjectionIsoComma (u := u) (p := p) ⥤ D :=
  (pushforwardProjectionIsoCommaProperty (u := u) (p := p)).ι ⋙
    Comma.fst (𝟭 D) (u.pushforwardProjection p)

/-- Helper for Lemma 8.12.6: forgetting the chosen comparison isomorphism sends an iso-comma
object back to its underlying localized object. -/
noncomputable abbrev pushforwardProjectionIsoCommaForget :
    pushforwardProjectionIsoComma (u := u) (p := p) ⥤ u ₚ p :=
  (pushforwardProjectionIsoCommaProperty (u := u) (p := p)).ι ⋙
    Comma.snd (𝟭 D) (u.pushforwardProjection p)

/-- Helper for Lemma 8.12.6: the identity chart on a localized object gives a canonical object of
the iso-comma model. -/
noncomputable abbrev pushforwardProjectionIsoCommaSectionObj
    (Y : u ₚ p) :
    pushforwardProjectionIsoComma (u := u) (p := p) :=
  ⟨{ left := (u.pushforwardProjection p).obj Y
     right := Y
     hom := 𝟙 ((u.pushforwardProjection p).obj Y) }, by
    simpa using (show IsIso (𝟙 ((u.pushforwardProjection p).obj Y)) from inferInstance)⟩

/-- Helper for Lemma 8.12.6: a localized morphism induces the evident map between the identity
chart objects in the iso-comma model. -/
noncomputable abbrev pushforwardProjectionIsoCommaSectionMap
    {X Y : u ₚ p} (ψ : X ⟶ Y) :
    pushforwardProjectionIsoCommaSectionObj (u := u) (p := p) X ⟶
      pushforwardProjectionIsoCommaSectionObj (u := u) (p := p) Y :=
  ObjectProperty.homMk
    { left := (u.pushforwardProjection p).map ψ
      right := ψ
      w := by simp }

/-- Helper for Lemma 8.12.6: the identity chart defines a section from the localized pushforward
category to the iso-comma comparison model. -/
noncomputable abbrev pushforwardProjectionIsoCommaSection :
    u ₚ p ⥤ pushforwardProjectionIsoComma (u := u) (p := p) where
  obj := pushforwardProjectionIsoCommaSectionObj (u := u) (p := p)
  map := fun ψ ↦ pushforwardProjectionIsoCommaSectionMap (u := u) (p := p) ψ
  map_id := by
    intro X
    apply (ObjectProperty.ι (pushforwardProjectionIsoCommaProperty (u := u) (p := p))).map_injective
    apply CategoryTheory.Comma.hom_ext
    · exact pushforwardProjection_map_id (u := u) (p := p) X
    · rfl
  map_comp := by
    intro X Y Z ψ χ
    apply (ObjectProperty.ι (pushforwardProjectionIsoCommaProperty (u := u) (p := p))).map_injective
    apply CategoryTheory.Comma.hom_ext
    · exact pushforwardProjection_map_comp (u := u) (p := p) ψ χ
    · rfl

/-- Helper for Lemma 8.12.6: the chosen comma isomorphism identifies an iso-comma object with the
identity chart on its underlying localized object. -/
noncomputable abbrev pushforwardProjectionIsoComma_unitIsoApp
    (X : pushforwardProjectionIsoComma (u := u) (p := p)) :
    X ≅
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj X) := by
  let hX : IsIso X.obj.hom := X.property
  letI : IsIso X.obj.hom := hX
  -- The source object already carries the comparison isomorphism needed for the unit component.
  refine ObjectProperty.isoMk (P := pushforwardProjectionIsoCommaProperty (u := u) (p := p)) ?_
  refine
    { hom :=
        { left := X.obj.hom
          right := 𝟙 X.obj.right
          w := by
            have hmap :
                (u.pushforwardProjection p).map (𝟙 X.obj.right) =
                  𝟙 ((u.pushforwardProjection p).obj X.obj.right) :=
              pushforwardProjection_map_id (u := u) (p := p) X.obj.right
            calc
              (𝟭 D).map X.obj.hom ≫
                  ((pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
                    ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj X)).obj.hom
                  = X.obj.hom := by
                    simp [pushforwardProjectionIsoCommaSectionObj,
                      pushforwardProjectionIsoCommaForget]
              _ =
                  X.obj.hom ≫ 𝟙 ((u.pushforwardProjection p).obj X.obj.right) :=
                (Category.comp_id X.obj.hom).symm
              _ = X.obj.hom ≫ (u.pushforwardProjection p).map (𝟙 X.obj.right) := by
                rw [hmap] }
      inv :=
        { left := (asIso X.obj.hom).inv
          right := 𝟙 X.obj.right
          w := by
            have hmap :
                (u.pushforwardProjection p).map (𝟙 X.obj.right) =
                  𝟙 ((u.pushforwardProjection p).obj X.obj.right) :=
              pushforwardProjection_map_id (u := u) (p := p) X.obj.right
            change (asIso X.obj.hom).inv ≫ X.obj.hom =
              𝟙 ((u.pushforwardProjection p).obj X.obj.right) ≫
                (u.pushforwardProjection p).map (𝟙 X.obj.right)
            calc
              (asIso X.obj.hom).inv ≫ X.obj.hom =
                  𝟙 ((u.pushforwardProjection p).obj X.obj.right) :=
                (asIso X.obj.hom).inv_hom_id
              _ = 𝟙 ((u.pushforwardProjection p).obj X.obj.right) ≫
                    (u.pushforwardProjection p).map (𝟙 X.obj.right) := by
                rw [hmap]
                simp } }

/-- Helper for Lemma 8.12.6: the unit isomorphism for the forget/section equivalence is exactly
the stored comma isomorphism on each iso-comma object. -/
noncomputable abbrev pushforwardProjectionIsoComma_unitIso :
    𝟭 (pushforwardProjectionIsoComma (u := u) (p := p)) ≅
      pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
        pushforwardProjectionIsoCommaSection (u := u) (p := p) :=
  NatIso.ofComponents
    (fun X ↦ pushforwardProjectionIsoComma_unitIsoApp (u := u) (p := p) X)
    (fun {X Y} φ ↦ by
      -- Naturality is exactly the defining square of a comma morphism.
      apply (ObjectProperty.ι (pushforwardProjectionIsoCommaProperty (u := u) (p := p))).map_injective
      apply CategoryTheory.Comma.hom_ext
      · change
          φ.hom.left ≫ Y.obj.hom =
            X.obj.hom ≫ (u.pushforwardProjection p).map φ.hom.right
        simpa using φ.hom.w
      · simp [pushforwardProjectionIsoComma_unitIsoApp])

/-- Helper for Lemma 8.12.6: the fixed source-preimage base map attached to a localized object and
base arrow. -/
noncomputable abbrev pushforwardProjection_precompose_sourceBase
    (Y : u ₚ p) {V : D} (f : V ⟶ (u.pushforwardProjection p).obj Y) :
    V ⟶ (((u.pushforwardFractions p).Q).objPreimage Y).fst.left :=
  f ≫ (u.pushforwardProjection p).map (((u.pushforwardFractions p).Q.objObjPreimageIso Y).inv)

/-- Helper for Lemma 8.12.6: the localized domain object obtained by precomposing in fixed source
charts. -/
noncomputable abbrev pushforwardProjection_precompose_modelObj
    (Y : u ₚ p) {V : D} (f : V ⟶ (u.pushforwardProjection p).obj Y) :
    u ₚ p :=
  let Q := (u.pushforwardFractions p).Q
  let Y₀ := Q.objPreimage Y
  let sourceBase := pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y f
  let X₀ := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
  Q.obj X₀

/-- Helper for Lemma 8.12.6: the localized precomposition morphism produced in fixed source
charts. -/
noncomputable abbrev pushforwardProjection_precompose_modelHom
    (Y : u ₚ p) {V : D} (f : V ⟶ (u.pushforwardProjection p).obj Y) :
    pushforwardProjection_precompose_modelObj (u := u) (p := p) Y f ⟶ Y :=
  let Q := (u.pushforwardFractions p).Q
  let Y₀ := Q.objPreimage Y
  let eY : Q.obj Y₀ ≅ Y := Q.objObjPreimageIso Y
  let sourceBase := pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y f
  let φ₀ := pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase
  Q.map φ₀ ≫ eY.hom

/-- Helper for Lemma 8.12.6: the transported model lift comes with a comparison isomorphism from
its localized base object to the requested source object in `D`. -/
noncomputable abbrev pushforwardProjection_precompose_modelBaseIso
    (Y : u ₚ p) {V : D} (f : V ⟶ (u.pushforwardProjection p).obj Y) :
    (u.pushforwardProjection p).obj
        (pushforwardProjection_precompose_modelObj (u := u) (p := p) Y f) ≅ V :=
  -- Route correction: use the literal source-chart comparison on the fixed preimage object `T₀`
  -- instead of an opaque `Classical.choose`d isomorphism.
  pushforwardProjection_precompose_baseIso (u := u) (p := p)
    (((u.pushforwardFractions p).Q).objPreimage Y)
    (pushforwardProjection_precompose_sourceBase (u := u) (p := p) Y f)

/-- Helper for Lemma 8.12.6: with the construction localization lift, the model-base
comparison chart has identity forward map. -/
@[simp]
theorem pushforwardProjection_precompose_modelBaseIso_hom
    (Y : u ₚ p) {V : D} (f : V ⟶ (u.pushforwardProjection p).obj Y) :
    (pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y f).hom =
      𝟙 _ := by
  -- Delegate the computation to the fixed source-preimage comparison chart.
  rfl

/-- Helper for Lemma 8.12.6: the chosen localized precomposition morphism is already a hom-lift
for the transported base map given by the comparison isomorphism on its source object. -/
theorem pushforwardProjection_precompose_modelHom_isHomLift
    (Y : u ₚ p) {V : D} (f : V ⟶ (u.pushforwardProjection p).obj Y) :
    (u.pushforwardProjection p).IsHomLift
      ((pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y f).hom ≫ f)
      (pushforwardProjection_precompose_modelHom (u := u) (p := p) Y f) := by
  -- Route correction: after making the base comparison canonical, the hom-lift is the earlier
  -- transported source-chart proof with only definitional unfolding remaining.
  simpa [pushforwardProjection_precompose_modelBaseIso, pushforwardProjection_precompose_modelHom,
    pushforwardProjection_precompose_modelObj, pushforwardProjection_precompose_sourceBase] using
    pushforwardProjection_precompose_toIsHomLift_transported (u := u) (p := p) Y f

/-- Helper for Lemma 8.12.6: package the transported localized precomposition lift as an actual
object of the iso-comma model lying literally over the requested base object. -/
noncomputable abbrev pushforwardProjectionIsoComma_precomposeObj
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y) :
    pushforwardProjectionIsoComma (u := u) (p := p) :=
  ⟨{ left := V
     right := pushforwardProjection_precompose_modelObj (u := u) (p := p) Y.obj.right
       (f ≫ Y.obj.hom)
     hom := (pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
       (f ≫ Y.obj.hom)).inv }, by
    simpa using
      (show IsIso
        ((pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom)).inv) from inferInstance)⟩

/-- Helper for Lemma 8.12.6: the transported localized precomposition lift defines the expected
iso-comma morphism above the chosen base map. -/
noncomputable abbrev pushforwardProjectionIsoComma_precomposeHom
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y) :
    pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f ⟶ Y :=
  ObjectProperty.homMk
    { left := f
      right := pushforwardProjection_precompose_modelHom (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)
      w := by
        let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom)
        letI :
            (u.pushforwardProjection p).IsHomLift (eX.hom ≫ (f ≫ Y.obj.hom))
              (pushforwardProjection_precompose_modelHom (u := u) (p := p) Y.obj.right
                (f ≫ Y.obj.hom)) :=
          pushforwardProjection_precompose_modelHom_isHomLift
            (u := u) (p := p) Y.obj.right (f ≫ Y.obj.hom)
        have hfac :
            (u.pushforwardProjection p).map
                (pushforwardProjection_precompose_modelHom (u := u) (p := p) Y.obj.right
                  (f ≫ Y.obj.hom)) =
              eX.hom ≫ (f ≫ Y.obj.hom) := by
          simpa [eX, Category.assoc] using
            (IsHomLift.fac' (u.pushforwardProjection p) (eX.hom ≫ (f ≫ Y.obj.hom))
              (pushforwardProjection_precompose_modelHom (u := u) (p := p) Y.obj.right
                (f ≫ Y.obj.hom)))
        -- Cancel the transported source chart so the comma square is literally over `f`.
        calc
          f ≫ Y.obj.hom = (eX.inv ≫ eX.hom) ≫ (f ≫ Y.obj.hom) := by
            simp [Category.assoc]
          _ = eX.inv ≫ (eX.hom ≫ (f ≫ Y.obj.hom)) := by
            simp [Category.assoc]
          _ =
              (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom ≫
                (u.pushforwardProjection p).map
                  (pushforwardProjection_precompose_modelHom (u := u) (p := p) Y.obj.right
                    (f ≫ Y.obj.hom)) := by
              simpa [pushforwardProjectionIsoComma_precomposeObj, eX, hfac]
                using congrArg (fun k ↦ eX.inv ≫ k) hfac.symm }

/-- Helper for Lemma 8.12.6: the iso-comma precomposition morphism is a literal hom-lift over the
requested base map because its left component is exactly that map. -/
theorem pushforwardProjectionIsoComma_precomposeHom_isHomLift
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y) :
    (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift f
      (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f) := by
  -- The projection remembers only the left comma component, which was chosen to be `f`.
  refine IsHomLift.of_fac' (pushforwardProjectionIsoCommaProjection (u := u) (p := p)) f
    (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f) rfl rfl ?_
  simp [pushforwardProjectionIsoCommaProjection, pushforwardProjectionIsoComma_precomposeHom]

/-- Helper for Lemma 8.12.6: after forgetting the chosen source comparison isomorphism, the
iso-comma precomposition morphism already lies over the transported base map obtained by canceling
that source isomorphism on the left. -/
theorem pushforwardProjectionIsoComma_precomposeHom_forget_fac
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y) :
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).map
        (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f) =
      eX.hom ≫ f ≫ Y.obj.hom := by
  -- Route correction: use the canonical hom-lift on the right component directly, instead of
  -- canceling the iso-comma object's stored chart through `asIso`.
  dsimp
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
    (f ≫ Y.obj.hom)
  letI :
      (u.pushforwardProjection p).IsHomLift (eX.hom ≫ (f ≫ Y.obj.hom))
        (pushforwardProjection_precompose_modelHom (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom)) :=
    pushforwardProjection_precompose_modelHom_isHomLift
      (u := u) (p := p) Y.obj.right (f ≫ Y.obj.hom)
  -- The forgetful composite keeps exactly the right component, so `IsHomLift.fac'` gives the
  -- desired base equation after unfolding the iso-comma morphism.
  simpa [eX, pushforwardProjectionIsoCommaForget, pushforwardProjectionIsoComma_precomposeHom,
    Category.assoc] using
    (IsHomLift.fac' (u.pushforwardProjection p) (eX.hom ≫ (f ≫ Y.obj.hom))
      (pushforwardProjection_precompose_modelHom (u := u) (p := p) Y.obj.right
        (f ≫ Y.obj.hom)))

/-- Helper for Lemma 8.12.6: once the target comparison isomorphism is canceled, the raw
iso-comma precomposition morphism is already a lift for the composite projection over the
transported base map `eX.hom ≫ g`. -/
theorem pushforwardProjectionIsoCommaForget_precompose_isHomLift_transported
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    [IsIso Y.obj.hom]
    {V : D}
    (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    (g :
      V ⟶ (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
        u.pushforwardProjection p).obj Y)
    (hf : f ≫ Y.obj.hom = g) :
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).IsHomLift
      (eX.hom ≫ g)
      (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f) := by
  -- Rewrite the composite projection map into the literal base equation already isolated above.
  refine
    IsHomLift.of_fac
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p)
      ((pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom)).hom ≫ g)
      (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f)
      rfl rfl ?_
  -- Route correction: the current file already exposes the needed map formula, so only the
  -- target-side strictification `f ≫ Y.obj.hom = g` remains to be substituted.
  have hmap :
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).map
          (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f) =
        (pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
            (f ≫ Y.obj.hom)).hom ≫
          f ≫ Y.obj.hom := by
    simpa [Category.assoc] using
      pushforwardProjectionIsoComma_precomposeHom_forget_fac
        (u := u) (p := p) Y f
  have hbase :
      (pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom)).hom ≫ g =
      (pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom)).hom ≫
        f ≫ Y.obj.hom := by
    simpa [Category.assoc] using congrArg
      (fun k ↦
        (pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom)).hom ≫ k)
      hf.symm
  simpa [Category.assoc] using hbase.trans hmap.symm

/-- Helper for Lemma 8.12.6: in the iso-comma model, once source and target objects are fixed, the
right localized component determines the whole morphism. -/
theorem pushforwardProjectionIsoComma_hom_ext_right
    {X Y : pushforwardProjectionIsoComma (u := u) (p := p)}
    (η θ : X ⟶ Y) (hright : η.hom.right = θ.hom.right) :
    η = θ := by
  let hY : IsIso Y.obj.hom := Y.property
  have hleft : η.hom.left = θ.hom.left := by
    have hηw :
        (𝟭 D).map η.hom.left ≫ Y.obj.hom =
          X.obj.hom ≫ (u.pushforwardProjection p).map θ.hom.right := by
      simpa [hright] using η.hom.w
    have hθw :
        (𝟭 D).map θ.hom.left ≫ Y.obj.hom =
          X.obj.hom ≫ (u.pushforwardProjection p).map θ.hom.right := by
      simpa using θ.hom.w
    apply (cancel_mono Y.obj.hom).1
    -- Both left components are forced by the same right component via the comma square.
    simpa using hηw.trans hθw.symm
  apply (ObjectProperty.ι (pushforwardProjectionIsoCommaProperty (u := u) (p := p))).map_injective
  apply CategoryTheory.Comma.hom_ext
  · exact hleft
  · exact hright

/-- Helper for Lemma 8.12.6: once the right localized component has been descended, the
corresponding iso-comma factor is obtained by pairing it with the chosen base arrow on the left. -/
noncomputable abbrev pushforwardProjectionIsoComma_factorHom
    {Y Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {h : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V}
    (χr : Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
      (u := u) (p := p) Y f).obj.right)
    (hχr :
      h ≫ (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom =
        Z.obj.hom ≫ (u.pushforwardProjection p).map χr) :
    Z ⟶ pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f :=
  ObjectProperty.homMk
    { left := h
      right := χr
      w := hχr }

/-- Helper for Lemma 8.12.6: the packaged iso-comma factor is a literal lift of the chosen left
base arrow because the projection forgets the right component. -/
theorem pushforwardProjectionIsoComma_factorHom_isHomLift
    {Y Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {h : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V}
    (χr : Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
      (u := u) (p := p) Y f).obj.right)
    (hχr :
      h ≫ (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom =
        Z.obj.hom ≫ (u.pushforwardProjection p).map χr) :
    (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift h
      (pushforwardProjectionIsoComma_factorHom (u := u) (p := p) f χr hχr) := by
  -- The projection to `D` remembers only the left comma component of the packaged factor.
  refine IsHomLift.of_fac' (pushforwardProjectionIsoCommaProjection (u := u) (p := p)) h
    (pushforwardProjectionIsoComma_factorHom (u := u) (p := p) f χr hχr) rfl rfl ?_
  simp [pushforwardProjectionIsoCommaProjection, pushforwardProjectionIsoComma_factorHom]

/-- Helper for Lemma 8.12.6: after the right component is descended, the resulting packaged
iso-comma factor composes to the original morphism, and the left component follows automatically
from `pushforwardProjectionIsoComma_hom_ext_right`. -/
theorem pushforwardProjectionIsoComma_factorHom_comp
    {Y Z : pushforwardProjectionIsoComma (u := u) (p := p)}
    {V : D} (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    {h : (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Z ⟶ V}
    {θ : Z ⟶ Y}
    (χr : Z.obj.right ⟶ (pushforwardProjectionIsoComma_precomposeObj
      (u := u) (p := p) Y f).obj.right)
    (hχr :
      h ≫ (pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f).obj.hom =
        Z.obj.hom ≫ (u.pushforwardProjection p).map χr)
    (hfacr :
      χr ≫ (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f).hom.right =
        θ.hom.right) :
    pushforwardProjectionIsoComma_factorHom (u := u) (p := p) f χr hχr ≫
        pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f =
      θ := by
  -- Route correction: once the right component is available, avoid redoing the comma-square
  -- algebra and recover the full equality by right-component extensionality.
  apply pushforwardProjectionIsoComma_hom_ext_right (u := u) (p := p)
  simpa [pushforwardProjectionIsoComma_factorHom, pushforwardProjectionIsoComma_precomposeHom]
    using hfacr

/-- Helper for Lemma 8.12.6: forgetting the identity chart recovers the original localized object
and morphism without further transport. -/
noncomputable abbrev pushforwardProjectionIsoComma_counitIso :
    pushforwardProjectionIsoCommaSection (u := u) (p := p) ⋙
        pushforwardProjectionIsoCommaForget (u := u) (p := p) ≅
      𝟭 (u ₚ p) :=
  NatIso.ofComponents
    (fun X ↦ Iso.refl X)
    (fun {X Y} ψ ↦ by
      simp [pushforwardProjectionIsoCommaSection, pushforwardProjectionIsoCommaSectionMap])

/-- Helper for Lemma 8.12.6: the forgetful functor from the iso-comma model is an ordinary
equivalence of total categories, with quasi-inverse given by the identity chart section. -/
noncomputable abbrev pushforwardProjectionIsoComma_forget_equivalence :
    pushforwardProjectionIsoComma (u := u) (p := p) ≌ u ₚ p where
  functor := pushforwardProjectionIsoCommaForget (u := u) (p := p)
  inverse := pushforwardProjectionIsoCommaSection (u := u) (p := p)
  unitIso := pushforwardProjectionIsoComma_unitIso (u := u) (p := p)
  counitIso := pushforwardProjectionIsoComma_counitIso (u := u) (p := p)
  functor_unitIso_comp := by
    intro X
    rfl

/-- Helper for Lemma 8.12.6: the iso-comma projection to `D` is naturally isomorphic to the
forgetful functor followed by the canonical localized projection. -/
noncomputable abbrev pushforwardProjectionIsoComma_projectionIso :
    pushforwardProjectionIsoCommaProjection (u := u) (p := p) ≅
      pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p :=
  NatIso.ofComponents
    (fun X ↦ by
      let hX : IsIso X.obj.hom := X.property
      exact @asIso _ _ _ _ X.obj.hom hX)
    (fun {X Y} φ ↦ by
      -- Naturality again reduces to the defining commutative square of `φ` in the comma category.
      change
        φ.hom.left ≫ Y.obj.hom =
          X.obj.hom ≫ (u.pushforwardProjection p).map φ.hom.right
      simpa using φ.hom.w)

/-- Helper for Lemma 8.12.6: the forgetful functor from the iso-comma comparison model is a
strict based functor once the source projection is taken to be the literal composite
`pushforwardProjectionIsoCommaForget ⋙ u.pushforwardProjection p`. -/
noncomputable abbrev pushforwardProjectionIsoCommaForgetBased :
    BasedCategory.ofFunctor
        (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p) ⥤ᵇ
      BasedCategory.ofFunctor (u.pushforwardProjection p) :=
  { toFunctor := pushforwardProjectionIsoCommaForget (u := u) (p := p)
    w := rfl }

/-- Helper for Lemma 8.12.6: the identity-chart section followed by forget is literally the
identity on `u ₚ p`, so the section is also strict over `u.pushforwardProjection p`. -/
theorem pushforwardProjectionIsoCommaSection_comp_projection_eq :
    pushforwardProjectionIsoCommaSection (u := u) (p := p) ⋙
        pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
          u.pushforwardProjection p =
      u.pushforwardProjection p := by
  -- The section only inserts identity comparison arrows, so forgetting them changes nothing.
  rfl

/-- Helper for Lemma 8.12.6: the identity-chart section followed by the raw iso-comma projection
is literally the canonical localized pushforward projection. -/
theorem pushforwardProjectionIsoCommaSection_comp_rawProjection_eq :
    pushforwardProjectionIsoCommaSection (u := u) (p := p) ⋙
        pushforwardProjectionIsoCommaProjection (u := u) (p := p) =
      u.pushforwardProjection p := by
  -- The section object uses the identity comparison arrow, so the raw left projection is exactly
  -- the base object of the localized target.
  rfl

/-- Helper for Lemma 8.12.6: the identity-chart section repackages as a strict based functor back
to the iso-comma model over the composite base. -/
noncomputable abbrev pushforwardProjectionIsoCommaSectionBased :
    BasedCategory.ofFunctor (u.pushforwardProjection p) ⥤ᵇ
      BasedCategory.ofFunctor
        (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p) :=
  { toFunctor := pushforwardProjectionIsoCommaSection (u := u) (p := p)
    w := pushforwardProjectionIsoCommaSection_comp_projection_eq (u := u) (p := p) }

/-- Helper for Lemma 8.12.6: after forgetting to the localized category and re-inserting the
identity comparison chart, one gets a strict based functor from the composite projection back to
the raw iso-comma projection. -/
noncomputable abbrev pushforwardProjectionIsoCommaRetractBased :
    BasedCategory.ofFunctor
        (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p) ⥤ᵇ
      BasedCategory.ofFunctor (pushforwardProjectionIsoCommaProjection (u := u) (p := p)) :=
  { toFunctor :=
      pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
        pushforwardProjectionIsoCommaSection (u := u) (p := p)
    w := by
      -- Associate once and then collapse the inserted identity-chart section to the raw
      -- projection formula.
      rw [Functor.assoc]
      exact congrArg (Functor.comp (pushforwardProjectionIsoCommaForget (u := u) (p := p)))
        (pushforwardProjectionIsoCommaSection_comp_rawProjection_eq (u := u) (p := p)) }

/-- Helper for Lemma 8.12.6: each component of the forget/section unit is vertical for the
composite base projection because its right component is the identity on the localized object. -/
theorem pushforwardProjectionIsoComma_unitIso_hom_app_isHomLift
    (X : pushforwardProjectionIsoComma (u := u) (p := p)) :
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).IsHomLift
      (𝟙 ((u.pushforwardProjection p).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj X)))
      ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).hom.app X) := by
  -- The unit component fixes the localized right object, so its image in `D` is the identity.
  refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
  simpa [pushforwardProjectionIsoCommaForget, pushforwardProjectionIsoComma_unitIso,
    pushforwardProjectionIsoComma_unitIsoApp] using
      (pushforwardProjection_map_id (u := u) (p := p) X.obj.right)

/-- Helper for Lemma 8.12.6: the inverse component of the forget/section unit is also vertical for
the composite base projection, since vertical isomorphisms stay over the identity after inversion.
-/
theorem pushforwardProjectionIsoComma_unitIso_inv_app_isHomLift
    (X : pushforwardProjectionIsoComma (u := u) (p := p)) :
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).IsHomLift
      (𝟙 ((u.pushforwardProjection p).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj X)))
      ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X) := by
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let e := (pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).app X
  letI :
      q.IsHomLift (𝟙 (q.obj X))
        e.hom :=
    pushforwardProjectionIsoComma_unitIso_hom_app_isHomLift (u := u) (p := p) X
  -- Route correction: isolate only the inverse-verticality fact here; the stronger
  -- postcomposition-to-cartesian step still depends on the unfinished source strictification.
  change q.IsHomLift (𝟙 (q.obj X)) e.inv
  have heinv : CategoryTheory.inv e.hom = e.inv := by
    -- Both arrows are inverses to `e.hom`, so right-cancellation identifies them.
    apply (cancel_mono e.hom).1
    calc
      CategoryTheory.inv e.hom ≫ e.hom = 𝟙 ((pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
            pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj X) := by
          simp
      _ = e.inv ≫ e.hom := by
          simpa using e.inv_hom_id.symm
  rw [← heinv]
  -- The inverse of a vertical comparison isomorphism remains vertical over the same identity.
  exact IsHomLift.lift_id_inv_isIso (p := q) (q.obj X) e.hom

/-- Helper for Lemma 8.12.6: the inverse unit comparison is strongly cartesian for the strict
composite projection because it is a vertical isomorphism. -/
theorem pushforwardProjectionIsoComma_unitIso_inv_app_isStronglyCartesian
    (X : pushforwardProjectionIsoComma (u := u) (p := p)) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    q.IsStronglyCartesian
      (𝟙 ((u.pushforwardProjection p).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj X)))
      ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X) := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  letI :
      q.IsHomLift (𝟙 (q.obj X))
        ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X) :=
    pushforwardProjectionIsoComma_unitIso_inv_app_isHomLift (u := u) (p := p) X
  -- A vertical isomorphism is automatically strongly cartesian over the identity.
  exact
    Functor.IsStronglyCartesian.of_isIso q (𝟙 (q.obj X))
      ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X)

/-- Helper for Lemma 8.12.6: precomposing the raw transported lift with the inverse unit
comparison leaves the same transported base map for the composite projection. -/
theorem pushforwardProjectionIsoCommaForget_unit_inv_precompose_isHomLift_transported
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    [IsIso Y.obj.hom]
    {V : D}
    (f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y)
    (g :
      V ⟶ (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
        u.pushforwardProjection p).obj Y)
    (hf : f ≫ Y.obj.hom = g) :
    let X := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).IsHomLift
      (eX.hom ≫ g)
      ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X ≫
        pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f) := by
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let X := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f
  have hη :
      q.IsHomLift (𝟙 (q.obj X))
        ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X) := by
    -- The inverse unit comparison is vertical for the composite projection.
    simpa [q, X] using
      pushforwardProjectionIsoComma_unitIso_inv_app_isHomLift (u := u) (p := p) X
  have hφ :
      q.IsHomLift
        ((pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
          (f ≫ Y.obj.hom)).hom ≫ g)
        (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f) := by
    -- Reuse the transported base computation for the raw precomposition morphism.
    simpa [q] using
      pushforwardProjectionIsoCommaForget_precompose_isHomLift_transported
        (u := u) (p := p) Y f g hf
  -- Precomposing with a vertical comparison preserves the transported base map.
  exact @IsHomLift.comp_lift_id_left' _ _ _ _ q _ _ _ (q.obj X)
    ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X) hη
    _ _
    ((pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)).hom ≫ g)
    (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f) hφ

/-- Helper for Lemma 8.12.6: after rewriting the raw base map by the stored iso-comma chart on
`Y`, the candidate composite arrow for the strict projection is explicit and its transported base
map is exactly the one isolated by the unit-inverse hom-lift theorem. -/
theorem pushforwardProjectionIsoComma_precompose_over_composite_isHomLift
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    [IsIso Y.obj.hom]
    {V : D}
    (g : V ⟶ (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
      u.pushforwardProjection p).obj Y) :
    let f : V ⟶ (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).obj Y :=
      g ≫ (asIso Y.obj.hom).inv
    let X := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Y f
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p) Y.obj.right
      (f ≫ Y.obj.hom)
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).IsHomLift
      (eX.hom ≫ g)
      ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app X ≫
        pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Y f) := by
  -- Route correction: freeze the raw left component as `f := g ≫ Y.obj.hom⁻¹` so the remaining
  -- transport obstruction is visible as the extra source comparison `eX.hom`.
  dsimp
  exact
    pushforwardProjectionIsoCommaForget_unit_inv_precompose_isHomLift_transported
      (u := u) (p := p) Y
      (g ≫ (asIso Y.obj.hom).inv)
      g
      (by simp [Category.assoc])

/-- Helper for Lemma 8.12.6: the ordinary unit isomorphism of the forget/section equivalence is
already a based natural isomorphism over the composite base. -/
noncomputable abbrev pushforwardProjectionIsoCommaForget_unitIso :
    BasedFunctor.id (BasedCategory.ofFunctor
        (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p)) ≅
      BasedFunctor.comp
        (pushforwardProjectionIsoCommaForgetBased (u := u) (p := p))
        (pushforwardProjectionIsoCommaSectionBased (u := u) (p := p)) :=
  BasedNatIso.mkNatIso
    (pushforwardProjectionIsoComma_unitIso (u := u) (p := p))
    (fun X ↦ pushforwardProjectionIsoComma_unitIso_hom_app_isHomLift (u := u) (p := p) X)

/-- Helper for Lemma 8.12.6: the section/forget counit is componentwise the identity, hence
vertical for the localized pushforward projection. -/
theorem pushforwardProjectionIsoComma_counitIso_hom_app_isHomLift
    (X : u ₚ p) :
    (u.pushforwardProjection p).IsHomLift
      (𝟙 ((u.pushforwardProjection p).obj X))
      ((pushforwardProjectionIsoComma_counitIso (u := u) (p := p)).hom.app X) := by
  -- The counit does nothing on the localized object, so it lies over the identity by definition.
  refine IsHomLift.of_fac' (u.pushforwardProjection p) (𝟙 ((u.pushforwardProjection p).obj X))
    ((pushforwardProjectionIsoComma_counitIso (u := u) (p := p)).hom.app X) rfl rfl ?_
  simpa [pushforwardProjectionIsoComma_counitIso] using
    (pushforwardProjection_map_id (u := u) (p := p) X)

/-- Helper for Lemma 8.12.6: the ordinary counit of the forget/section equivalence is likewise a
based natural isomorphism over `u.pushforwardProjection p`. -/
noncomputable abbrev pushforwardProjectionIsoCommaForget_counitIso :
    BasedFunctor.comp
        (pushforwardProjectionIsoCommaSectionBased (u := u) (p := p))
        (pushforwardProjectionIsoCommaForgetBased (u := u) (p := p)) ≅
      BasedFunctor.id (BasedCategory.ofFunctor (u.pushforwardProjection p)) :=
  BasedNatIso.mkNatIso
    (pushforwardProjectionIsoComma_counitIso (u := u) (p := p))
    (fun X ↦ pushforwardProjectionIsoComma_counitIso_hom_app_isHomLift (u := u) (p := p) X)

/-- Helper for Lemma 8.12.6: after replacing the raw iso-comma projection by the strict composite
`pushforwardProjectionIsoCommaForget ⋙ u.pushforwardProjection p`, the forgetful comparison is an
equivalence over the base, so fibredness transports across it. -/
theorem pushforwardProjectionIsoComma_forget_comp_isFibered_iff :
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).IsFibered ↔
      (u.pushforwardProjection p).IsFibered := by
  let F := pushforwardProjectionIsoCommaForgetBased (u := u) (p := p)
  have hF : F.IsEquivalenceOverBase := by
    -- The source and target are already equivalent on the nose over the strict composite base.
    exact BasedFunctor.IsEquivalenceOverBase.mkPrime
      (F := F)
      (pushforwardProjectionIsoCommaSectionBased (u := u) (p := p))
      (pushforwardProjectionIsoCommaForget_unitIso (u := u) (p := p))
      (pushforwardProjectionIsoCommaForget_counitIso (u := u) (p := p))
  exact BasedFunctor.isFibered_iff_of_equivalence_over_base F hF

end Functor

end

end CategoryTheory
