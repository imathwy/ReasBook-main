import StacksProject_2024.stacks_project.Chap18.Definition_18_7_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_20_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_38_2
import StacksProject_2024.stacks_project.Chap21.Situation_21_38_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.FibredCategoryMor
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

/-
Domain-style sampling for Lemma 21.38.4:
- primary domain: localized morphisms of topoi in the inherited ringed-topos situation, obtained
  from localized morphisms of ringed sites over slice categories;
- sampled owner declarations:
  `RingedSite.Hom.localization`,
  `RingedSite.Hom.toMorphismOfTopoi`,
  `projectionRingedSiteHom`,
  `MorphismOfTopoiIn.comp`;
- best owner abstraction: this lemma is a `bridge/view` statement built from the canonical
  localized ringed-site morphisms `projectionRingedSiteHom D C'`,
  `u.inheritedRingedSiteHom`, and `projectionRingedSiteHom D C`, viewed through
  `RingedSite.Hom.toMorphismOfTopoi`. The
  source-facing mathematical content is the existence of the section `σ'`; the comparison
  identities are derived theorem data, and the target localized projection is the canonical one
  for `C`, transported only inside the theorem statement along
  `V = p'(U') = p(u(U'))`.
- primitive data: the ringed site `D`, the fibred categories `C`, `C'`, the morphism
  `u : C' ⟶ C`, and the object `U'`;
- derived API: the three canonical localized morphisms of topoi and the direct existential
  statement for `σ'`.

Source/core/bridge triage:
- `source-facing`: the existence of `σ'` with the two section equalities and the two inverse-image
  identifications;
- `core/canonical`: `RingedSite.Hom.localization`, `RingedSite.Hom.toMorphismOfTopoi`, and
  `MorphismOfTopoiIn.comp`;
- `bridge/view`: the present localized comparison statement, relating the two section
  constructions through `u.inheritedRingedSiteHom : inheritedRingedSite D C ⟶
  inheritedRingedSite D C'`, with the target-projection transport kept local to the theorem
  statement. -/

section localizedComparison

variable {D : RingedSite.{u, v}}
variable {C C' : FibredCategoryOver.{u, v} D}

/-- The projection of `u(U')` along `C.p` is the same object of `D` as the projection of `U'`
along `C'.p`. This is the objectwise form of the defining commutativity
`toFunctor u ⋙ C.p = C'.p`. -/
theorem inheritedRingedSiteHom_projection_obj_eq (f : C' ⟶ C) (U' : C'.S) :
    C.p.obj ((toFunctor f).obj U') = C'.p.obj U' := by
  let h : toFunctor f ⋙ C.p = C'.p := FibredCategoryMor.comm f
  simpa using congrArg (fun F : C'.S ⥤ D ↦ F.obj U') h

variable (u : C' ⟶ C)
variable (U' : C'.S)
variable [IsMorphismOfSites (inheritedTopology D.siteTopology C') D.siteTopology C'.p]
variable [IsMorphismOfSites (inheritedTopology D.siteTopology C) D.siteTopology C.p]
variable [IsMorphismOfSites
  (inheritedTopology D.siteTopology C')
  (inheritedTopology D.siteTopology C)
  (toFunctor u)]

/-- The comparison functor on slice sites induced by `u.inheritedRingedSiteHom` is continuous. -/
instance inheritedRingedSiteHom_overPost_isContinuous :
    (Over.post (inheritedRingedSiteHom u).base).IsContinuous
      ((inheritedRingedSite D C').siteTopology.over U')
      ((inheritedRingedSite D C).siteTopology.over
        ((inheritedRingedSiteHom u).base.obj U')) := by
  simpa [FibredCategoryMor.inheritedRingedSiteHom_base, inheritedRingedSite] using
    (show (Over.post (toFunctor u)).IsContinuous
      ((inheritedTopology D.siteTopology C').over U')
      ((inheritedTopology D.siteTopology C).over ((toFunctor u).obj U')) from inferInstance)

/-- The comparison functor on slice sites induced by `u.inheritedRingedSiteHom` preserves finite
limits as soon as the source-facing slice functor `Over.post (toFunctor u)` does. -/
instance inheritedRingedSiteHom_overPost_preservesFiniteLimits
    [∀ Q : (Over U')ᵒᵖ ⥤ Type (max u v),
      (Over.post (toFunctor u)).op.HasLeftKanExtension Q]
    [PreservesFiniteLimits
      ((Over.post (toFunctor u)).sheafPullback
        (Type (max u v))
        ((inheritedTopology D.siteTopology C').over U')
        ((inheritedTopology D.siteTopology C).over ((toFunctor u).obj U')))] :
    PreservesFiniteLimits
      ((Over.post (inheritedRingedSiteHom u).base).sheafPullback
        (Type (max u v))
        ((inheritedRingedSite D C').siteTopology.over U')
        ((inheritedRingedSite D C).siteTopology.over
          ((inheritedRingedSiteHom u).base.obj U'))) := by
  simpa [FibredCategoryMor.inheritedRingedSiteHom_base, inheritedRingedSite] using
    (show PreservesFiniteLimits
      ((Over.post (toFunctor u)).sheafPullback
        (Type (max u v))
      ((inheritedTopology D.siteTopology C').over U')
        ((inheritedTopology D.siteTopology C).over ((toFunctor u).obj U'))) from inferInstance)

/-- The localized comparison functor induced by `u.inheritedRingedSiteHom` is continuous. -/
instance localizedInheritedRingedSiteHom_isContinuous :
    ((inheritedRingedSiteHom u).localization U').base.IsContinuous
      (((inheritedRingedSite D C').localization U').siteTopology)
      (((inheritedRingedSite D C).localization
        ((inheritedRingedSiteHom u).base.obj U')).siteTopology) :=
  ((inheritedRingedSiteHom u).localization U').isMorphismOfSites.toIsContinuous

/-- The localized comparison morphism induced by `u.inheritedRingedSiteHom` preserves finite
limits, so it canonically defines the localized morphism of topoi used in Lemma `21.38.4`. -/
instance localizedInheritedRingedSiteHom_preservesFiniteLimits
    [∀ Q : (Over U')ᵒᵖ ⥤ Type (max u v),
      (Over.post (toFunctor u)).op.HasLeftKanExtension Q]
    [PreservesFiniteLimits
      ((Over.post (toFunctor u)).sheafPullback
        (Type (max u v))
        ((inheritedTopology D.siteTopology C').over U')
        ((inheritedTopology D.siteTopology C).over ((toFunctor u).obj U')))] :
    PreservesFiniteLimits
      (((inheritedRingedSiteHom u).localization U').base.sheafPullback
        (Type (max u v))
        (((inheritedRingedSite D C').localization U').siteTopology)
        (((inheritedRingedSite D C).localization
          ((inheritedRingedSiteHom u).base.obj U')).siteTopology)) := by
  simpa [FibredCategoryMor.inheritedRingedSiteHom_base, inheritedRingedSite,
    RingedSite.Hom.localization, RingedSite.localization] using
    (show PreservesFiniteLimits
      (((inheritedRingedSiteHom u).localization U').base.sheafPullback
        (Type (max u v))
        (((inheritedRingedSite D C').localization U').siteTopology)
        (((inheritedRingedSite D C).localization
          ((inheritedRingedSiteHom u).base.obj U')).siteTopology)) from
      RingedSite.Hom.localization_sheafPullback_preservesFiniteLimits
        (inheritedRingedSiteHom u) U')

end localizedComparison

-- Proof sketch: apply Lemma `21.38.2` to `C'` and `U'` to obtain a section `σ'` of `π'`.
-- Compose with the localized comparison morphism induced by `u`, and insert the inverse
-- common-base bridge `ν⁻¹`; the theorem-local inverse-image square with `g'`, `π'`, `π`, and
-- `ν` then identifies the resulting morphism as a section of `π` for `U = u(U')`.
/-- Lemma 21.38.4: for `U' : C'.S`, with `U = u(U')` and `V = p'(U')`, let
`π' : Sh(C'/U') ⟶ Sh(D/p'(U'))`, `g' : Sh(C'/U') ⟶ Sh(C/u(U'))`, and
`π : Sh(C/u(U')) ⟶ Sh(D/p(u(U')))` be the canonical localized morphisms of topoi. Then there
exists `σ' : Sh(D/p'(U')) ⟶ Sh(C'/U')` such that `π' ≫ σ' = 𝟙`, and the induced morphism
`σ : Sh(D/p(u(U'))) ⟶ Sh(C/u(U'))`, obtained from `σ'` by composing with the canonical localized
comparison morphism `g'` and the common-base identification `ν⁻¹`, is a section of `π`; the
corresponding inverse-image functors are `π' _*` and `π _*`. -/
@[stacks 08PB]
theorem localized_comparison_morphism_has_section
    {D : RingedSite.{u, v}} {C C' : FibredCategoryOver.{u, v} D}
    (u : C' ⟶ C) (U' : C'.S)
    [IsMorphismOfSites (inheritedTopology D.siteTopology C') D.siteTopology C'.p]
    [IsMorphismOfSites (inheritedTopology D.siteTopology C) D.siteTopology C.p]
    [HasWeakSheafify (D.siteTopology.over (C'.p.obj U')) (Type (max u v))]
    [IsMorphismOfSites
      (inheritedTopology D.siteTopology C')
      (inheritedTopology D.siteTopology C)
      (toFunctor u)]
    [∀ Q : (Over U')ᵒᵖ ⥤ Type (max u v),
      (Over.post C'.p).op.HasLeftKanExtension Q]
    [∀ Q : (Over ((toFunctor u).obj U'))ᵒᵖ ⥤ Type (max u v),
      (Over.post C.p).op.HasLeftKanExtension Q]
    [∀ Q : (Over U')ᵒᵖ ⥤ Type (max u v),
      (Over.post (toFunctor u)).op.HasLeftKanExtension Q]
    [PreservesFiniteLimits
      ((Over.post C'.p).sheafPullback
        (Type (max u v))
        ((inheritedTopology D.siteTopology C').over U')
        (D.siteTopology.over (C'.p.obj U')))]
    [PreservesFiniteLimits
      ((Over.post C.p).sheafPullback
        (Type (max u v))
        ((inheritedTopology D.siteTopology C).over ((toFunctor u).obj U'))
        (D.siteTopology.over (C.p.obj ((toFunctor u).obj U'))))]
    [PreservesFiniteLimits
      ((Over.post (toFunctor u)).sheafPullback
        (Type (max u v))
        ((inheritedTopology D.siteTopology C').over U')
        ((inheritedTopology D.siteTopology C).over ((toFunctor u).obj U')))] :
    let π' := ((projectionRingedSiteHom D C').localization U').toMorphismOfTopoi
    let g' := ((inheritedRingedSiteHom u).localization U').toMorphismOfTopoi
    let π := ((projectionRingedSiteHom D C).localization ((toFunctor u).obj U')).toMorphismOfTopoi
    let νInv :=
      cast
        (congrArg
          (fun W ↦
            MorphismOfTopoiIn
              ((D.localization W).siteTopology)
              ((D.localization (C'.p.obj U')).siteTopology))
          (inheritedRingedSiteHom_projection_obj_eq u U').symm)
        (MorphismOfTopoiIn.id ((D.localization (C'.p.obj U')).siteTopology))
    ∃ σ' :
        MorphismOfTopoiIn
          ((D.localization (C'.p.obj U')).siteTopology)
          (((inheritedRingedSite D C').localization U').siteTopology),
      let σ :=
        MorphismOfTopoiIn.comp νInv (MorphismOfTopoiIn.comp σ' g')
      MorphismOfTopoiIn.comp σ' π' =
          MorphismOfTopoiIn.id ((D.localization (C'.p.obj U')).siteTopology) ∧
      MorphismOfTopoiIn.comp σ π =
          MorphismOfTopoiIn.id ((D.localization (C.p.obj ((toFunctor u).obj U'))).siteTopology) ∧
        σ'⁻¹ = π' _* ∧
        σ⁻¹ = π _* := by
  sorry

end FibredCategoryOver
end CategoryTheory
