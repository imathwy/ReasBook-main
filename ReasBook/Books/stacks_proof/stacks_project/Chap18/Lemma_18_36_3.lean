import Mathlib
import StacksProject_2024.Chap18.Definition_18_9_1
import StacksProject_2024.Chap18.Lemma_18_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [LocallySmall.{max u v} C]

namespace GrothendieckTopology.Point

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
    `p.presheafFiber` and `p.sheafFiber`, the source-facing owners
    `p.stalkRing`, `p.presheafModuleStalkFunctor`, `p.sheafModuleStalkFunctor`, and the canonical
    sheafification/stalk comparison isomorphisms;
  `bridge/view`: the underlying additive specializations of the module-valued stalk functors;
- primitive data: the point `p`, the sheaf of rings `𝒪`, and the module sheaf/presheaf under
  consideration;
- derived API: the additive underlying stalk functors, the exactness theorems, and the
  sheafification comparison below. -/

/-- The stalk ring `\mathcal O_p` of a sheaf of rings `\mathcal O` at the point `p`. -/
abbrev stalkRing (p : GrothendieckTopology.Point.{max u v} J)
    (𝒪 : Sheaf J RingCat.{max u v}) : RingCat.{max u v} :=
  p.presheafFiber.obj 𝒪.obj

/-- The stalk functor on presheaves of `\mathcal O`-modules at the point `p`. -/
abbrev presheafModuleStalkFunctor (p : GrothendieckTopology.Point.{max u v} J)
    (𝒪 : Sheaf J RingCat.{max u v}) :
    PMod(𝒪.obj) ⥤ ModuleCat (p.stalkRing 𝒪) :=
  PresheafOfModules.pushforward₀ (CategoryOfElements.π p.fiber) 𝒪.obj ⋙
    PresheafOfModules.colimitFunctor
      (p.isColimitPresheafFiberCocone 𝒪.obj)

/-- The stalk functor on sheaves of `\mathcal O`-modules at the point `p`. -/
abbrev sheafModuleStalkFunctor (p : GrothendieckTopology.Point.{max u v} J)
    (𝒪 : Sheaf J RingCat.{max u v}) :
    Mod(𝒪) ⥤ ModuleCat (p.stalkRing 𝒪) :=
  SheafOfModules.forget 𝒪 ⋙ p.presheafModuleStalkFunctor 𝒪

variable (p : GrothendieckTopology.Point.{max u v} J)
variable (𝒪 : Sheaf J RingCat.{max u v})

-- Proof sketch: this exactness statement is source-facing and should remain independent of any
-- auxiliary sheafification infrastructure used by one particular proof route. The proof should
-- therefore be organized around the intrinsic module-valued stalk functor itself rather than
-- leaking hypotheses from `Lemma_18_14_1` into the theorem statement.
/-- Lemma 18.36.3 (1): for a ringed site `(\mathcal C, \mathcal O)` and a point `p` of
`\mathcal C`, the stalk functor `\mathrm{Mod}(\mathcal O) ⥤ \mathrm{Mod}(\mathcal O_p)` is
exact. -/
@[stacks 04EQ]
lemma sheafModuleStalk_exact :
    exactFunctor (Mod(𝒪)) (ModuleCat (p.stalkRing 𝒪))
      (p.sheafModuleStalkFunctor 𝒪) := by
  let G : ModuleCat (p.stalkRing 𝒪) ⥤ AddCommGrpCat.{max u v} :=
    forget₂ _ _
  -- After forgetting the `𝒪_p`-module structure, the stalk functor is the usual additive stalk.
  have hlim : PreservesFiniteLimits (p.sheafModuleStalkFunctor 𝒪) := by
    have : PreservesFiniteLimits (p.sheafModuleStalkFunctor 𝒪 ⋙ G) := by
      have hToSheaf :
          exactFunctor (Mod(𝒪)) (Sheaf J AddCommGrpCat.{max u v})
            (SheafOfModules.toSheaf 𝒪) :=
        (ExactFunctor.of (SheafOfModules.toSheaf 𝒪)).property
      have hFiber :
          exactFunctor (Sheaf J AddCommGrpCat.{max u v}) AddCommGrpCat.{max u v}
            p.sheafFiber :=
        (ExactFunctor.of p.sheafFiber).property
      let _ : PreservesFiniteLimits (SheafOfModules.toSheaf 𝒪) :=
        ((exactFunctor_iff (SheafOfModules.toSheaf 𝒪)).1 hToSheaf).1
      let _ : PreservesFiniteLimits p.sheafFiber :=
        ((exactFunctor_iff p.sheafFiber).1 hFiber).1
      change PreservesFiniteLimits (SheafOfModules.toSheaf 𝒪 ⋙ p.sheafFiber)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves
      (p.sheafModuleStalkFunctor 𝒪) G
  -- The same reflection argument upgrades finite-colimit preservation from abelian groups.
  have hcolim : PreservesFiniteColimits (p.sheafModuleStalkFunctor 𝒪) := by
    have : PreservesFiniteColimits (p.sheafModuleStalkFunctor 𝒪 ⋙ G) := by
      have hToSheaf :
          exactFunctor (Mod(𝒪)) (Sheaf J AddCommGrpCat.{max u v})
            (SheafOfModules.toSheaf 𝒪) :=
        (ExactFunctor.of (SheafOfModules.toSheaf 𝒪)).property
      have hFiber :
          exactFunctor (Sheaf J AddCommGrpCat.{max u v}) AddCommGrpCat.{max u v}
            p.sheafFiber :=
        (ExactFunctor.of p.sheafFiber).property
      let _ : PreservesFiniteColimits (SheafOfModules.toSheaf 𝒪) :=
        ((exactFunctor_iff (SheafOfModules.toSheaf 𝒪)).1 hToSheaf).2
      let _ : PreservesFiniteColimits p.sheafFiber :=
        ((exactFunctor_iff p.sheafFiber).1 hFiber).2
      change PreservesFiniteColimits (SheafOfModules.toSheaf 𝒪 ⋙ p.sheafFiber)
      infer_instance
    exact preservesFiniteColimits_of_reflects_of_preserves
      (p.sheafModuleStalkFunctor 𝒪) G
  -- Exactness is equivalent to preserving finite limits and finite colimits in this abelian setting.
  exact (exactFunctor_iff (p.sheafModuleStalkFunctor 𝒪)).2 ⟨hlim, hcolim⟩

section SheafColimits

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

private theorem toSheaf_preservesColimits :
    PreservesColimits (SheafOfModules.toSheaf.{max u v} 𝒪) := by
  -- This is the imported colimit-preservation instance from Lemma `18.14.2`.
  infer_instance

/- The module-valued stalk functor is the canonical site-point owner. Its colimit preservation is
proved once here and registered as an instance rather than a parallel named theorem. -/
private theorem sheafModuleStalk_preservesColimits :
    PreservesColimits (p.sheafModuleStalkFunctor 𝒪) := by
  let F : Mod(𝒪) ⥤ ModuleCat (p.stalkRing 𝒪) :=
    p.sheafModuleStalkFunctor 𝒪
  let G : ModuleCat (p.stalkRing 𝒪) ⥤ AddCommGrpCat.{max u v} :=
    forget₂ _ _
  let _ : PreservesColimits (F ⋙ G) := by
    let _ : PreservesColimits (SheafOfModules.toSheaf.{max u v} 𝒪) :=
      toSheaf_preservesColimits 𝒪
    let _ : PreservesColimits
        (p.sheafFiber : Sheaf J AddCommGrpCat.{max u v} ⥤ AddCommGrpCat.{max u v}) := by
      infer_instance
    change PreservesColimits (SheafOfModules.toSheaf.{max u v} 𝒪 ⋙ p.sheafFiber)
    exact comp_preservesColimits _ _
  let _ : PreservesColimits G := by
    infer_instance
  let _ : ReflectsColimits G := by
    exact reflectsColimits_of_reflectsIsomorphisms
  exact preservesColimits_of_reflects_of_preserves F G

noncomputable instance sheafModuleStalkFunctorPreservesColimits :
    PreservesColimits (p.sheafModuleStalkFunctor 𝒪) :=
  sheafModuleStalk_preservesColimits p 𝒪

end SheafColimits

-- Proof sketch: the presheaf-module stalk functor is obtained by pulling back a presheaf of
-- modules to the fiber category of `p` and then taking the filtered colimit module; exactness
-- follows from exactness of the underlying abelian-group stalk functor from Lemma `18.36.2`.
/-- Lemma 18.36.3 (2): for a ringed site `(\mathcal C, \mathcal O)` and a point `p` of
`\mathcal C`, the stalk functor `\mathrm{PMod}(\mathcal O) ⥤ \mathrm{Mod}(\mathcal O_p)` is
exact. -/
@[stacks 04EQ]
lemma presheafModuleStalk_exact :
    exactFunctor (PMod(𝒪.obj)) (ModuleCat (p.stalkRing 𝒪))
      (p.presheafModuleStalkFunctor 𝒪) := by
  let G : ModuleCat (p.stalkRing 𝒪) ⥤ AddCommGrpCat.{max u v} :=
    forget₂ _ _
  -- After forgetting modules, this is the additive presheaf stalk functor from Lemma `18.36.2`.
  have hlim : PreservesFiniteLimits (p.presheafModuleStalkFunctor 𝒪) := by
    have : PreservesFiniteLimits (p.presheafModuleStalkFunctor 𝒪 ⋙ G) := by
      have hToPresheaf :
          exactFunctor (PMod(𝒪.obj)) (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
            (PresheafOfModules.toPresheaf 𝒪.obj) :=
        (ExactFunctor.of (PresheafOfModules.toPresheaf 𝒪.obj)).property
      have hFiber :
          exactFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) AddCommGrpCat.{max u v}
            p.presheafFiber :=
        (ExactFunctor.of p.presheafFiber).property
      let _ : PreservesFiniteLimits (PresheafOfModules.toPresheaf 𝒪.obj) :=
        ((exactFunctor_iff (PresheafOfModules.toPresheaf 𝒪.obj)).1 hToPresheaf).1
      let _ : PreservesFiniteLimits p.presheafFiber :=
        ((exactFunctor_iff p.presheafFiber).1 hFiber).1
      change PreservesFiniteLimits
        (PresheafOfModules.toPresheaf 𝒪.obj ⋙ p.presheafFiber)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves
      (p.presheafModuleStalkFunctor 𝒪) G
  -- Reflection through the module forgetful functor also upgrades finite-colimit preservation.
  have hcolim : PreservesFiniteColimits (p.presheafModuleStalkFunctor 𝒪) := by
    have : PreservesFiniteColimits (p.presheafModuleStalkFunctor 𝒪 ⋙ G) := by
      have hToPresheaf :
          exactFunctor (PMod(𝒪.obj)) (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
            (PresheafOfModules.toPresheaf 𝒪.obj) :=
        (ExactFunctor.of (PresheafOfModules.toPresheaf 𝒪.obj)).property
      have hFiber :
          exactFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) AddCommGrpCat.{max u v}
            p.presheafFiber :=
        (ExactFunctor.of p.presheafFiber).property
      let _ : PreservesFiniteColimits (PresheafOfModules.toPresheaf 𝒪.obj) :=
        ((exactFunctor_iff (PresheafOfModules.toPresheaf 𝒪.obj)).1 hToPresheaf).2
      let _ : PreservesFiniteColimits p.presheafFiber :=
        ((exactFunctor_iff p.presheafFiber).1 hFiber).2
      change PreservesFiniteColimits
        (PresheafOfModules.toPresheaf 𝒪.obj ⋙ p.presheafFiber)
      infer_instance
    exact preservesFiniteColimits_of_reflects_of_preserves
      (p.presheafModuleStalkFunctor 𝒪) G
  -- Exactness again amounts to preservation of finite limits and colimits.
  exact (exactFunctor_iff (p.presheafModuleStalkFunctor 𝒪)).2 ⟨hlim, hcolim⟩

section Sheafification

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/- Companion to Lemma 18.36.3 (3): after forgetting the `\mathcal O_p`-module structure, the
module-valued comparison below is the canonical additive sheafification/stalk comparison obtained
from `PresheafOfModules.sheafificationCompToSheaf (𝟙 𝒪.obj)` and
`p.presheafToSheafCompSheafFiberIso AddCommGrpCat`. -/
private noncomputable def presheafModuleStalkSheafificationUnderlyingIso :
    PresheafOfModules.toPresheaf 𝒪.obj ⋙ p.presheafFiber ≅
      PresheafOfModules.sheafification (𝟙 𝒪.obj) ⋙ SheafOfModules.toSheaf 𝒪 ⋙ p.sheafFiber :=
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
functor; its underlying additive comparison is the canonical composite built from
`PresheafOfModules.sheafificationCompToSheaf (𝟙 𝒪.obj)` and
`p.presheafToSheafCompSheafFiberIso AddCommGrpCat`. -/
private noncomputable def presheafModuleStalkToSheafification_hom
    (ℱ : PMod(𝒪.obj)) :
    (p.presheafModuleStalkFunctor 𝒪).obj ℱ ⟶
      (PresheafOfModules.sheafification (𝟙 𝒪.obj) ⋙ p.sheafModuleStalkFunctor 𝒪).obj ℱ :=
  (p.presheafModuleStalkFunctor 𝒪).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 𝒪.obj)).unit.app ℱ) ≫
    (ModuleCat.restrictScalarsId (p.stalkRing 𝒪)).hom.app
      ((p.sheafModuleStalkFunctor 𝒪).obj
        ((PresheafOfModules.sheafification (𝟙 𝒪.obj)).obj ℱ))

noncomputable def presheafModuleStalkSheafificationIso :
    p.presheafModuleStalkFunctor 𝒪 ≅
      PresheafOfModules.sheafification (𝟙 𝒪.obj) ⋙ p.sheafModuleStalkFunctor 𝒪 :=
  NatIso.ofComponents
    (fun ℱ ↦ by
      let φ := presheafModuleStalkToSheafification_hom p 𝒪 ℱ
      haveI : IsIso φ := by
        let F := forget₂ (ModuleCat (p.stalkRing 𝒪)) AddCommGrpCat.{max u v}
        haveI : IsIso (F.map φ) := by
          change IsIso
            (p.presheafFiber.map
              (CategoryTheory.toSheafify J
                ((PresheafOfModules.toPresheaf 𝒪.obj).obj ℱ)))
          infer_instance
        exact isIso_of_reflects_iso φ F
      exact asIso φ)
    (fun {ℱ 𝒢} f ↦ by
      let F := forget₂ (ModuleCat (p.stalkRing 𝒪)) AddCommGrpCat.{max u v}
      have hℱ :
          F.map (presheafModuleStalkToSheafification_hom p 𝒪 ℱ) =
            (presheafModuleStalkSheafificationUnderlyingIso p 𝒪).hom.app ℱ := by
        change p.presheafFiber.map
            (CategoryTheory.toSheafify J
              ((PresheafOfModules.toPresheaf 𝒪.obj).obj ℱ)) = _
        simp [presheafModuleStalkSheafificationUnderlyingIso,
          GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso,
          PresheafOfModules.sheafificationCompToSheaf]
        erw [Functor.map_id]
        exact (Category.comp_id
          (p.presheafFiber.map
            (CategoryTheory.toSheafify J
              ((PresheafOfModules.toPresheaf 𝒪.obj).obj ℱ)))).symm
      have h𝒢 :
          F.map (presheafModuleStalkToSheafification_hom p 𝒪 𝒢) =
            (presheafModuleStalkSheafificationUnderlyingIso p 𝒪).hom.app 𝒢 := by
        change p.presheafFiber.map
            (CategoryTheory.toSheafify J
              ((PresheafOfModules.toPresheaf 𝒪.obj).obj 𝒢)) = _
        simp [presheafModuleStalkSheafificationUnderlyingIso,
          GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso,
          PresheafOfModules.sheafificationCompToSheaf]
        erw [Functor.map_id]
        exact (Category.comp_id
          (p.presheafFiber.map
            (CategoryTheory.toSheafify J
              ((PresheafOfModules.toPresheaf 𝒪.obj).obj 𝒢)))).symm
      apply F.map_injective
      rw [Functor.map_comp, Functor.map_comp]
      change F.map ((p.presheafModuleStalkFunctor 𝒪).map f) ≫
          F.map (presheafModuleStalkToSheafification_hom p 𝒪 𝒢) =
        F.map (presheafModuleStalkToSheafification_hom p 𝒪 ℱ) ≫
            F.map ((PresheafOfModules.sheafification (𝟙 𝒪.obj) ⋙
              p.sheafModuleStalkFunctor 𝒪).map f)
      rw [hℱ, h𝒢]
      change (PresheafOfModules.toPresheaf 𝒪.obj ⋙ p.presheafFiber).map f ≫
          (presheafModuleStalkSheafificationUnderlyingIso p 𝒪).hom.app 𝒢 =
        (presheafModuleStalkSheafificationUnderlyingIso p 𝒪).hom.app ℱ ≫
            ((PresheafOfModules.sheafification (𝟙 𝒪.obj) ⋙
                SheafOfModules.toSheaf 𝒪 ⋙ p.sheafFiber).map f)
      simpa using
        (presheafModuleStalkSheafificationUnderlyingIso p 𝒪).hom.naturality f)

end Sheafification

end GrothendieckTopology.Point

end CategoryTheory
