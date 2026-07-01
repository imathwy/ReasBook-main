import Mathlib
import stacks_project.Chap18.Lemma_18_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [LocallySmall.{max u v} C]

/- Domain-style sampling:
- primary domain: points of a Grothendieck topology and stalk functors on sheaves and presheaves
  of modules over a sheaf of rings;
- sampled owner declarations:
  `GrothendieckTopology.Point.presheafFiber`,
  `GrothendieckTopology.Point.sheafFiber`,
  `PresheafOfModules.sheafificationCompToSheaf`,
  `GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso`;
- best owner abstraction: the site point `p` together with the module-valued stalk functors below;
  the underlying additive stalk functors are derived by composing with the canonical forgetful
  functors `PresheafOfModules.toPresheaf` and `SheafOfModules.toSheaf`;
- source/core/bridge triage:
  `source-facing`: the three clauses of Lemma 18.36.3 about exactness and stalk/sheafification
    comparison for `\mathcal O`-modules;
  `core/canonical`: the owner point `p`, its canonical additive fiber functors
    `p.presheafFiber` and `p.sheafFiber`, and the canonical sheafification/stalk comparison
    isomorphisms;
  `bridge/view`: the module-valued stalk functors and their underlying additive specializations;
- primitive data: the point `p`, the sheaf of rings `𝒪`, and the module sheaf/presheaf under
  consideration;
- derived API: the additive underlying stalk functors, the exactness theorems, and the
  sheafification comparison below. -/

/-- The stalk ring `\mathcal O_p` of a sheaf of rings `\mathcal O` at the point `p`. -/
abbrev point_stalk_ring (p : GrothendieckTopology.Point.{max u v} J)
    (𝒪 : Sheaf J RingCat.{max u v}) : RingCat.{max u v} :=
  p.presheafFiber.obj 𝒪.obj

/-- The stalk functor on presheaves of `\mathcal O`-modules at the point `p`. -/
abbrev point_presheaf_module_stalk_functor (p : GrothendieckTopology.Point.{max u v} J)
    (𝒪 : Sheaf J RingCat.{max u v}) :
    PresheafOfModules 𝒪.obj ⥤ ModuleCat (point_stalk_ring p 𝒪) :=
  PresheafOfModules.pushforward₀ (CategoryOfElements.π p.fiber) 𝒪.obj ⋙
    PresheafOfModules.colimitFunctor
      (p.isColimitPresheafFiberCocone 𝒪.obj)

/-- The stalk functor on sheaves of `\mathcal O`-modules at the point `p`. -/
abbrev point_sheaf_module_stalk_functor (p : GrothendieckTopology.Point.{max u v} J)
    (𝒪 : Sheaf J RingCat.{max u v}) :
    SheafOfModules 𝒪 ⥤ ModuleCat (point_stalk_ring p 𝒪) :=
  SheafOfModules.forget 𝒪 ⋙ point_presheaf_module_stalk_functor p 𝒪

/-- The underlying abelian-group-valued stalk functor on presheaves of `\mathcal O`-modules at
the point `p`. -/
abbrev point_presheaf_module_stalk_underlying_functor
    (p : GrothendieckTopology.Point.{max u v} J) (𝒪 : Sheaf J RingCat.{max u v}) :
    PresheafOfModules 𝒪.obj ⥤ AddCommGrpCat.{max u v} :=
  PresheafOfModules.toPresheaf 𝒪.obj ⋙ p.presheafFiber

/-- The underlying abelian-group-valued stalk functor on sheaves of `\mathcal O`-modules at the
point `p`. -/
abbrev point_sheaf_module_stalk_underlying_functor
    (p : GrothendieckTopology.Point.{max u v} J) (𝒪 : Sheaf J RingCat.{max u v}) :
    SheafOfModules 𝒪 ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf 𝒪 ⋙ p.sheafFiber

variable (p : GrothendieckTopology.Point.{max u v} J)
variable (𝒪 : Sheaf J RingCat.{max u v})

section SheafExactness

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

-- Proof sketch: forget a sheaf of `\mathcal O`-modules to its underlying abelian sheaf, apply
-- exactness of the abelian stalk functor from Lemma `18.36.2`, and use Lemma `18.14.1` to pass
-- exactness back to the module-valued stalk functor.
/-- Lemma 18.36.3 (1): for a ringed site `(\mathcal C, \mathcal O)` and a point `p` of
`\mathcal C`, the stalk functor `\mathrm{Mod}(\mathcal O) ⥤ \mathrm{Mod}(\mathcal O_p)` is
exact. -/
lemma point_sheaf_module_stalk_exact :
    exactFunctor (SheafOfModules 𝒪) (ModuleCat (point_stalk_ring p 𝒪))
      (point_sheaf_module_stalk_functor p 𝒪) := sorry

end SheafExactness

section SheafColimits

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

private theorem toSheaf_preservesColimits :
    PreservesColimits (SheafOfModules.toSheaf 𝒪) := by
  sorry

/- The module-valued stalk functor is the canonical site-point owner. Its colimit preservation is
proved once here and downstream ringed-space statements should specialize this instance rather than
reprove it. -/
theorem point_sheaf_module_stalk_functor_preservesColimits :
    PreservesColimits (point_sheaf_module_stalk_functor p 𝒪) := by
  let F : SheafOfModules 𝒪 ⥤ ModuleCat (point_stalk_ring p 𝒪) :=
    point_sheaf_module_stalk_functor p 𝒪
  let G : ModuleCat (point_stalk_ring p 𝒪) ⥤ AddCommGrpCat.{max u v} :=
    forget₂ _ _
  let _ : PreservesColimits (F ⋙ G) := by
    let _ : PreservesColimits (SheafOfModules.toSheaf 𝒪) :=
      toSheaf_preservesColimits 𝒪
    let _ : PreservesColimits
        (p.sheafFiber : Sheaf J AddCommGrpCat.{max u v} ⥤ AddCommGrpCat.{max u v}) := by
      infer_instance
    change PreservesColimits (SheafOfModules.toSheaf 𝒪 ⋙ p.sheafFiber)
    exact comp_preservesColimits _ _
  let _ : PreservesColimits G := by
    infer_instance
  let _ : ReflectsColimits G := by
    exact reflectsColimits_of_reflectsIsomorphisms
  exact preservesColimits_of_reflects_of_preserves F G

noncomputable instance pointSheafModuleStalkFunctorPreservesColimits :
    PreservesColimits (point_sheaf_module_stalk_functor p 𝒪) :=
  point_sheaf_module_stalk_functor_preservesColimits p 𝒪

end SheafColimits

-- Proof sketch: the presheaf-module stalk functor is obtained by pulling back a presheaf of
-- modules to the fiber category of `p` and then taking the filtered colimit module; exactness
-- follows from exactness of the underlying abelian-group stalk functor from Lemma `18.36.2`.
/-- Lemma 18.36.3 (2): for a ringed site `(\mathcal C, \mathcal O)` and a point `p` of
`\mathcal C`, the stalk functor `\mathrm{PMod}(\mathcal O) ⥤ \mathrm{Mod}(\mathcal O_p)` is
exact. -/
lemma point_presheaf_module_stalk_exact :
    exactFunctor (PresheafOfModules 𝒪.obj) (ModuleCat (point_stalk_ring p 𝒪))
      (point_presheaf_module_stalk_functor p 𝒪) := sorry

section Sheafification

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/- Companion to Lemma 18.36.3 (3): after forgetting the `\mathcal O_p`-module structure, the
module-valued comparison below is the canonical additive sheafification/stalk comparison obtained
from `PresheafOfModules.sheafificationCompToSheaf (𝟙 𝒪.obj)` and
`p.presheafToSheafCompSheafFiberIso AddCommGrpCat`. -/
noncomputable def point_presheaf_module_stalk_sheafification_underlying_iso :
    point_presheaf_module_stalk_underlying_functor p 𝒪 ≅
      PresheafOfModules.sheafification (𝟙 𝒪.obj) ⋙
        point_sheaf_module_stalk_underlying_functor p 𝒪 :=
  (Functor.isoWhiskerLeft (PresheafOfModules.toPresheaf 𝒪.obj)
      (p.presheafToSheafCompSheafFiberIso AddCommGrpCat.{max u v})).symm ≪≫
    (Functor.associator (PresheafOfModules.toPresheaf 𝒪.obj)
      (presheafToSheaf J AddCommGrpCat.{max u v}) p.sheafFiber).symm ≪≫
    Functor.isoWhiskerRight
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 𝒪.obj)).symm p.sheafFiber ≪≫
    Functor.associator (PresheafOfModules.sheafification (𝟙 𝒪.obj))
      (SheafOfModules.toSheaf 𝒪) p.sheafFiber

/-- Lemma 18.36.3 (3): for a presheaf `\mathcal F` of `\mathcal O`-modules, the canonical map
`\mathcal F_p ⟶ (\mathcal F^{\#})_p` in `\mathrm{Mod}(\mathcal O_p)` is an isomorphism. This is
the module-valued comparison between the presheaf stalk functor and the sheafified sheaf stalk
functor; its underlying additive comparison is
`point_presheaf_module_stalk_sheafification_underlying_iso`. -/
private noncomputable def point_presheaf_module_stalk_to_sheafification_hom
    (ℱ : PresheafOfModules 𝒪.obj) :
    (point_presheaf_module_stalk_functor p 𝒪).obj ℱ ⟶
      (PresheafOfModules.sheafification (𝟙 𝒪.obj) ⋙ point_sheaf_module_stalk_functor p 𝒪).obj ℱ :=
  (point_presheaf_module_stalk_functor p 𝒪).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 𝒪.obj)).unit.app ℱ) ≫
    (ModuleCat.restrictScalarsId (point_stalk_ring p 𝒪)).hom.app
      ((point_sheaf_module_stalk_functor p 𝒪).obj
        ((PresheafOfModules.sheafification (𝟙 𝒪.obj)).obj ℱ))

noncomputable def point_presheaf_module_stalk_sheafification_iso :
    point_presheaf_module_stalk_functor p 𝒪 ≅
      PresheafOfModules.sheafification (𝟙 𝒪.obj) ⋙ point_sheaf_module_stalk_functor p 𝒪 :=
  NatIso.ofComponents
    (fun ℱ ↦ by
      let φ := point_presheaf_module_stalk_to_sheafification_hom p 𝒪 ℱ
      haveI : IsIso φ := by
        let F := forget₂ (ModuleCat (point_stalk_ring p 𝒪)) AddCommGrpCat.{max u v}
        haveI : IsIso (F.map φ) := by
          change IsIso
            (p.presheafFiber.map
              (CategoryTheory.toSheafify J
                ((PresheafOfModules.toPresheaf 𝒪.obj).obj ℱ)))
          infer_instance
        exact isIso_of_reflects_iso φ F
      exact asIso φ)
    (fun {ℱ 𝒢} f ↦ by
      let F := forget₂ (ModuleCat (point_stalk_ring p 𝒪)) AddCommGrpCat.{max u v}
      have hℱ :
          F.map (point_presheaf_module_stalk_to_sheafification_hom p 𝒪 ℱ) =
            (point_presheaf_module_stalk_sheafification_underlying_iso p 𝒪).hom.app ℱ := by
        change p.presheafFiber.map
            (CategoryTheory.toSheafify J
              ((PresheafOfModules.toPresheaf 𝒪.obj).obj ℱ)) = _
        simp [point_presheaf_module_stalk_sheafification_underlying_iso,
          GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso,
          PresheafOfModules.sheafificationCompToSheaf]
        erw [Functor.map_id]
        exact (Category.comp_id
          (p.presheafFiber.map
            (CategoryTheory.toSheafify J
              ((PresheafOfModules.toPresheaf 𝒪.obj).obj ℱ)))).symm
      have h𝒢 :
          F.map (point_presheaf_module_stalk_to_sheafification_hom p 𝒪 𝒢) =
            (point_presheaf_module_stalk_sheafification_underlying_iso p 𝒪).hom.app 𝒢 := by
        change p.presheafFiber.map
            (CategoryTheory.toSheafify J
              ((PresheafOfModules.toPresheaf 𝒪.obj).obj 𝒢)) = _
        simp [point_presheaf_module_stalk_sheafification_underlying_iso,
          GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso,
          PresheafOfModules.sheafificationCompToSheaf]
        erw [Functor.map_id]
        exact (Category.comp_id
          (p.presheafFiber.map
            (CategoryTheory.toSheafify J
              ((PresheafOfModules.toPresheaf 𝒪.obj).obj 𝒢)))).symm
      apply F.map_injective
      rw [Functor.map_comp, Functor.map_comp]
      change F.map ((point_presheaf_module_stalk_functor p 𝒪).map f) ≫
          F.map (point_presheaf_module_stalk_to_sheafification_hom p 𝒪 𝒢) =
        F.map (point_presheaf_module_stalk_to_sheafification_hom p 𝒪 ℱ) ≫
            F.map ((PresheafOfModules.sheafification (𝟙 𝒪.obj) ⋙
              point_sheaf_module_stalk_functor p 𝒪).map f)
      rw [hℱ, h𝒢]
      change (point_presheaf_module_stalk_underlying_functor p 𝒪).map f ≫
          (point_presheaf_module_stalk_sheafification_underlying_iso p 𝒪).hom.app 𝒢 =
        (point_presheaf_module_stalk_sheafification_underlying_iso p 𝒪).hom.app ℱ ≫
            ((PresheafOfModules.sheafification (𝟙 𝒪.obj) ⋙
                point_sheaf_module_stalk_underlying_functor p 𝒪).map f)
      simpa using
        (point_presheaf_module_stalk_sheafification_underlying_iso p 𝒪).hom.naturality f)

end Sheafification

end CategoryTheory
