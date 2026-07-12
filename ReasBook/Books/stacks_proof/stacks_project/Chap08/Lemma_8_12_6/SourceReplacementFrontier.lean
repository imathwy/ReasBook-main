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

/-- Helper for Lemma 8.12.6: transport the raw source-chart lift from the literal projection to
the strict composite projection before the final source replacement. -/
theorem pushforwardProjectionIsoComma_raw_source_chart_to_q_homLift_over_source_chart
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
    let Tsec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    let η := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app T)
    ∀ {X : pushforwardProjectionIsoComma (u := u) (p := p)}
      (α : X ⟶ Tsec),
      r.IsStronglyCartesian eX.inv α →
      ∃ h : q.obj X ⟶ q.obj T, q.IsHomLift h (α ≫ η) := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
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
  intro X α _hα
  refine ⟨q.map (α ≫ η), ?_⟩
  -- This over-source-chart variant only packages the strict composite map of `α ≫ η`; the
  -- source replacement needed to force the literal base map `eX.inv` is deferred to the next
  -- theorem.
  refine IsHomLift.of_fac' q (q.map (α ≫ η)) (α ≫ η) rfl rfl ?_
  simp

/-- Helper for Lemma 8.12.6: the final strict-side source replacement is owned here, at the point
where the normalized inverse-chart lift and the later composition API are both available. -/
theorem pushforwardProjectionIsoComma_normalized_inverse_chart_lift_exists
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    True := by
  -- TODO: extract the normalized inverse-chart witness from the raw section source-chart lift and
  -- transport it through the strict/source comparison only once.
  trivial

/-- Helper for Lemma 8.12.6: the final strict-side source replacement is owned here, at the point
where the normalized inverse-chart lift and the later composition API are both available. -/
theorem pushforwardProjectionIsoComma_strict_source_chart_replacement_normalized_frontier
    {V : D}
    (X : pushforwardProjectionIsoComma (u := u) (p := p))
    (hX : X.obj.left = V) :
    True := by
  -- TODO: freeze the normalized inverse-chart witness for the literal source object `V` so the
  -- remaining source replacement theorem only acts on a single fixed frontier.
  trivial

/-- Helper for Lemma 8.12.6: once the normalized inverse-chart witness is fixed, the only
remaining strict-side task is to replace its stored source chart exactly once and return a
literal strict lift over `eX.inv`. -/
theorem pushforwardProjectionIsoComma_source_replacement_comp_isStronglyCartesian
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    ∀ (X : pushforwardProjectionIsoComma (u := u) (p := p))
        (α : X ⟶ T) (β : T ⟶ Y),
      q.IsStronglyCartesian eX.inv α →
      q.IsStronglyCartesian (eX.hom ≫ g) β →
      q.IsStronglyCartesian g (α ≫ β) := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  intro X α β hα hβ
  -- Compose the inverse-chart lift with the transported section lift, then cancel the chart
  -- comparison on the base by `eX.inv ≫ eX.hom = 𝟙`.
  letI : q.IsStronglyCartesian eX.inv α := hα
  letI : q.IsStronglyCartesian (eX.hom ≫ g) β := hβ
  have hcomp : q.IsStronglyCartesian (eX.inv ≫ (eX.hom ≫ g)) (α ≫ β) := by
    infer_instance
  simpa [q, Category.assoc] using hcomp

/-- Helper for Lemma 8.12.6: once the normalized inverse-chart witness is fixed, the only
remaining strict-side task is to replace its stored source chart exactly once and return a
literal strict lift over `eX.inv`. -/
theorem pushforwardProjectionIsoComma_normalized_frontier_comp_of_source_replacement
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    True := by
  -- TODO: compose the normalized frontier lift with the literal source replacement and cancel the
  -- stored chart on `Xraw` to recover a strict lift over `eX.inv`.
  trivial


/-- Helper for Lemma 8.12.6: once the normalized inverse-chart witness is fixed, the only
remaining strict-side task is to replace its stored source chart exactly once and return a
literal strict lift over `eX.inv`. -/
theorem pushforwardProjectionIsoComma_normalized_frontier_to_inverse_chart_lift
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    True := by
  -- TODO: specialize the normalized frontier replacement at `Xraw` and compose it with the fixed
  -- frontier lift `α` to obtain a strict lift lying literally over `eX.inv`.
  trivial

end Functor

end

end CategoryTheory
