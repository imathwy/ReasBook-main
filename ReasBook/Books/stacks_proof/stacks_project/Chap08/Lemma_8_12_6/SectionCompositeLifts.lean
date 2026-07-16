import stacks_proof.stacks_project.Chap08.Lemma_8_12_6.IsoCommaModel
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

/-- Helper for Lemma 8.12.6: the literal section object over `forget Y` lies over the same base
object in `D` as `Y` itself for the strict composite projection. -/
theorem pushforwardProjectionIsoComma_section_base_eq
    (Y : pushforwardProjectionIsoComma (u := u) (p := p)) :
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj
        ((pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
          ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)) =
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y := by
  -- The section object keeps the same localized right component, so the strict composite
  -- projection lands on the same base object by definition.
  rfl

/-- Helper for Lemma 8.12.6: the section object over `forget Y` carries the identity comparison
map to the localized base object. -/
theorem pushforwardProjectionIsoComma_section_hom_id
    (Y : pushforwardProjectionIsoComma (u := u) (p := p)) :
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    Ysec.obj.hom = 𝟙 ((u.pushforwardProjection p).obj Y.obj.right) := by
  -- Expanding the section object shows that its comparison arrow is literally the identity.
  simp [pushforwardProjectionIsoCommaSection, pushforwardProjectionIsoCommaSectionObj,
    pushforwardProjectionIsoCommaForget]

/-- Helper for Lemma 8.12.6: before postcomposing with the unit inverse, the section-object
precomposition morphism already lies over the transported base map for the strict composite
projection. -/
theorem pushforwardProjectionIsoComma_section_precompose_isHomLift_transported
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    q.IsHomLift (eX.hom ≫ g)
      (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Ysec g) := by
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  have hYsec_hom : Ysec.obj.hom = 𝟙 ((u.pushforwardProjection p).obj Y.obj.right) := by
    -- The section-object chart is the identity, so the strict base map is unchanged.
    simpa [Ysec] using pushforwardProjectionIsoComma_section_hom_id (u := u) (p := p) Y
  letI : IsIso Ysec.obj.hom := by
    change IsIso (𝟙 ((u.pushforwardProjection p).obj Y.obj.right))
    infer_instance
  have hgYsec : g ≫ Ysec.obj.hom = g := by
    -- The source proof's section chart is fixed, so no further transport remains on the target.
    rw [hYsec_hom]
    exact Category.comp_id g
  -- Reuse the raw transported hom-lift theorem exactly at the identity-chart section object.
  simpa [q, Ysec, Category.assoc] using
    (pushforwardProjectionIsoCommaForget_precompose_isHomLift_transported
      (u := u) (p := p) Ysec g g hgYsec)

/-- Helper for Lemma 8.12.6: the current section-object candidate already gives a hom-lift for
the strict composite projection after transporting along the source comparison `eX.hom`. -/
theorem pushforwardProjectionIsoComma_raw_section_lift_isHomLift_transported
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    q.IsHomLift (eX.hom ≫ g)
      (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Ysec g ≫
        ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app Y)) := by
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  have hpre :
      q.IsHomLift
        ((pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
            Ysec.obj.right (g ≫ Ysec.obj.hom)).hom ≫ g)
        (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Ysec g) := by
    -- The transported preunit hom-lift is now recorded separately on the fixed identity chart.
    simpa [q, Ysec] using
      pushforwardProjectionIsoComma_section_precompose_isHomLift_transported
        (u := u) (p := p) Y g
  have hunit :
      q.IsHomLift (𝟙 (q.obj Y))
        ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app Y) := by
    -- The inverse unit comparison is vertical for the strict composite projection.
    simpa [q] using
      pushforwardProjectionIsoComma_unitIso_inv_app_isHomLift (u := u) (p := p) Y
  letI :
      q.IsHomLift
        ((pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
            Ysec.obj.right (g ≫ Ysec.obj.hom)).hom ≫ g)
        (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Ysec g) :=
    hpre
  letI :
      q.IsHomLift (𝟙 (q.obj Y))
        ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app Y) :=
    hunit
  -- Postcomposing with the vertical unit inverse keeps the same transported base map.
  have hcomp :
      q.IsHomLift
        (((pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
              Ysec.obj.right (g ≫ Ysec.obj.hom)).hom ≫ g) ≫ 𝟙 (q.obj Y))
        (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Ysec g ≫
          ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app Y)) := by
    exact
      @CategoryTheory.IsHomLift.comp _ _ _ _ q
        _ _ _ _ _ _
        ((pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
            Ysec.obj.right (g ≫ Ysec.obj.hom)).hom ≫ g)
        (𝟙 (q.obj Y))
        (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Ysec g)
        ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app Y)
        hpre hunit
  simpa [q, Ysec, Category.assoc] using hcomp

/-- Helper for Lemma 8.12.6: once the strict composite projection map of a morphism into the
identity-chart section object is known explicitly, its raw left component is forced by the comma
square. -/
theorem pushforwardProjectionIsoComma_section_lift_left_of_map_eq
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y)
    {W : pushforwardProjectionIsoComma (u := u) (p := p)}
    (h :
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj W ⟶
        (u.pushforwardProjection p).obj
          (pushforwardProjection_precompose_modelObj (u := u) (p := p)
            ((pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
              ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)).obj.right
            (g ≫
              ((pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
                ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)).obj.hom)))
    (τ :
      W ⟶ (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y))
    (hτq :
      let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
      let Ysec :=
        (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
          ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
      let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
        Ysec.obj.right (g ≫ Ysec.obj.hom)
      q.map τ = h ≫ eX.hom ≫ g) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    τ.hom.left = W.obj.hom ≫ h ≫ eX.hom ≫ g := by
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  have hYsec_hom : Ysec.obj.hom = 𝟙 ((u.pushforwardProjection p).obj Y.obj.right) := by
    -- The section object carries the identity comparison arrow.
    simpa [Ysec] using pushforwardProjectionIsoComma_section_hom_id (u := u) (p := p) Y
  have hleft0 : τ.hom.left = W.obj.hom ≫ q.map τ := by
    -- The target identity chart turns the comma square for `τ` into the literal raw left
    -- component formula needed in the source proof.
    simpa [q, Ysec, pushforwardProjectionIsoCommaForget, hYsec_hom, Category.assoc] using
      τ.hom.w
  have hleft1 : W.obj.hom ≫ q.map τ = W.obj.hom ≫ h ≫ eX.hom ≫ g := by
    simpa [Category.assoc] using congrArg (fun k ↦ W.obj.hom ≫ k) hτq
  exact hleft0.trans hleft1

/-- Helper for Lemma 8.12.6: once the strict composite projection map of a morphism into the
strict precomposition object is known explicitly, the comma square rewrites the left component
after postcomposing with the source chart. -/
theorem pushforwardProjectionIsoComma_precomposeObj_lift_left_comp_hom_of_map_eq
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y)
    {W : pushforwardProjectionIsoComma (u := u) (p := p)}
    (h :
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj W ⟶
        (u.pushforwardProjection p).obj
          (pushforwardProjection_precompose_modelObj (u := u) (p := p)
            ((pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
              ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)).obj.right
            (g ≫
              ((pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
                ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)).obj.hom)))
    (η :
      W ⟶ pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p)
        ((pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
          ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)) g)
    (hηq :
      let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
      q.map η = h) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p)
      ((pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)) g
    η.hom.left ≫ T.obj.hom = W.obj.hom ≫ h := by
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p)
    ((pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)) g
  have hleft0 : η.hom.left ≫ T.obj.hom = W.obj.hom ≫ q.map η := by
    -- The strict precomposition object's source chart is the only extra factor in the comma
    -- square.
    simpa [q, T, pushforwardProjectionIsoCommaForget, Category.assoc] using η.hom.w
  have hleft1 : W.obj.hom ≫ q.map η = W.obj.hom ≫ h := by
    simpa [Category.assoc] using congrArg (fun k ↦ W.obj.hom ≫ k) hηq
  exact hleft0.trans hleft1

/-- Helper for Lemma 8.12.6: the stored chart on the strict precomposition object is literally the
inverse of the base isomorphism `eX` used in the source proof. -/
theorem pushforwardProjectionIsoComma_precomposeObj_hom_eq
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    T.obj.hom = eX.inv := by
  rfl

/-- Helper for Lemma 8.12.6: the precomposition object's stored chart cancels with `eX.hom`,
recovering the identity on the strict target base object. -/
theorem pushforwardProjectionIsoComma_precomposeObj_hom_comp_baseIso_hom
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    T.obj.hom ≫ eX.hom = 𝟙 _ := by
  dsimp
  -- The stored chart on the precomposition object is literally `eX.inv`, so composing with
  -- `eX.hom` is exactly `inv_hom_id`.
  simpa [pushforwardProjectionIsoComma_precomposeObj,
    pushforwardProjection_precompose_modelBaseIso] using
    (pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      ((pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)).obj.right
      (g ≫
        ((pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
          ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)).obj.hom)).inv_hom_id

/-- Helper for Lemma 8.12.6: a morphism into the identity-chart section object whose strict
projection map is `h ≫ eX.hom ≫ g` is already a raw lift for the literal projection after
transporting the base along `W.obj.hom`. -/
theorem pushforwardProjectionIsoComma_raw_section_tau_isHomLift
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    ∀ {W : pushforwardProjectionIsoComma (u := u) (p := p)}
      (h : q.obj W ⟶ q.obj T) (τ : W ⟶ Ysec),
      q.map τ = h ≫ eX.hom ≫ g →
      r.IsHomLift (W.obj.hom ≫ h ≫ eX.hom ≫ g) τ := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  intro W h τ hτq
  -- The section object's stored chart is the identity, so the raw left component of `τ` is
  -- exactly the transported strict base equation.
  refine IsHomLift.of_fac' r (W.obj.hom ≫ h ≫ eX.hom ≫ g) τ rfl rfl ?_
  simpa [r, pushforwardProjectionIsoCommaProjection, Category.assoc] using
    pushforwardProjectionIsoComma_section_lift_left_of_map_eq
      (u := u) (p := p) Y g h τ hτq

/-- Helper for Lemma 8.12.6: once the strict composite projection equation is fixed, the raw
section-object universal property produces a unique factor and the source chart on the
precomposition object cancels to show that factor is literally a `q`-lift over `h`. -/
theorem pushforwardProjectionIsoComma_raw_section_factor_map_eq
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    ∀ {W : pushforwardProjectionIsoComma (u := u) (p := p)}
      (h : q.obj W ⟶ q.obj T) (χ : W ⟶ T),
      r.IsHomLift (W.obj.hom ≫ h ≫ eX.hom) χ →
      W.obj.hom ≫ q.map χ = W.obj.hom ≫ h := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  intro W h χ hχ
  let _ : r.IsHomLift (W.obj.hom ≫ h ≫ eX.hom) χ := hχ
  have hleft : χ.hom.left = W.obj.hom ≫ h ≫ eX.hom := by
    -- The raw lift hypothesis fixes the left component of `χ` to the transported base map.
    simpa [r, pushforwardProjectionIsoCommaProjection, Category.assoc] using
      (IsHomLift.fac' r (W.obj.hom ≫ h ≫ eX.hom) χ)
  have hchart : T.obj.hom = eX.inv := by
    -- The strict precomposition object stores exactly the inverse source chart.
    simpa [Ysec, T, eX] using
      pushforwardProjectionIsoComma_precomposeObj_hom_eq
        (u := u) (p := p) Y g
  have hcancel : eX.hom ≫ T.obj.hom = 𝟙 (q.obj T) := by
    -- Replacing the stored chart by `eX.inv` exposes the source-side cancellation.
    rw [hchart]
    exact eX.hom_inv_id
  have hcancel_whiskered :
      W.obj.hom ≫ h ≫ eX.hom ≫ T.obj.hom = W.obj.hom ≫ h ≫ 𝟙 (q.obj T) := by
    -- Whisker the chart cancellation by the fixed source-side composite.
    simpa [Category.assoc] using congrArg (fun k ↦ W.obj.hom ≫ h ≫ k) hcancel
  have htail : W.obj.hom ≫ h ≫ 𝟙 (q.obj T) = W.obj.hom ≫ h := by
    -- Remove the terminal identity on the strict-side map before canceling the source chart.
    simpa [q, T, Ysec, pushforwardProjectionIsoCommaSection,
      pushforwardProjectionIsoCommaSectionObj, pushforwardProjectionIsoCommaForget,
      Category.assoc] using congrArg (fun k ↦ W.obj.hom ≫ k) (Category.comp_id h)
  have hcomp : χ.hom.left ≫ T.obj.hom = W.obj.hom ≫ h := by
    -- Substitute the raw left component of `χ` and then cancel the stored source chart.
    rw [hleft]
    simpa [Category.assoc] using hcancel_whiskered.trans htail
  have hw : W.obj.hom ≫ q.map χ = χ.hom.left ≫ T.obj.hom := by
    -- The comma square of `χ` rewrites the strict projection map through the target chart.
    simpa [q, T, Category.assoc] using χ.hom.w.symm
  exact hw.trans hcomp

end Functor

end

end CategoryTheory
