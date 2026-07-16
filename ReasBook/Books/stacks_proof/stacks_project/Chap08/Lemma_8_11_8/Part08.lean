import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_proof.stacks_project.Chap07.Lemma_7_26_4.Index
import stacks_proof.stacks_project.Chap07.Lemma_7_26_6
import stacks_proof.stacks_project.Chap08.Lemma_8_3_7
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Definition_8_11_1
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.CoherenceAPI
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part08BaseComponent
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part08AssemblyBridges
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part08FixedBridge

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

/-- Bridge iso for Lemma 8.11.8 (source side). A recent Mathlib refactor broke the *definitional*
identification between the iterated pullback of the abstract `toDescentData (· .f)` datum of
`automorphismUnderlyingSheaf y` and the automorphism sheaf of the local-overlap source object
`(K.f ≫ g₁) ^*[cpc] (chosen_gerbe_cover_object U I₁.base)`. The genuine bridge iso (which used to be
`rfl`) is now named explicitly, mirroring the upstream `Part06.pullback_cover_source_component_iso`. -/
private noncomputable def exposed_middle_descent_source_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C}
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.obj
            ((((J.pseudofunctorOver (Type (max u v))).toDescentData
                (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).obj I₁))) ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (K.f ≫ g₁))) :=
  -- Base-change the abstract `I₁.f ^* y` datum, identify it with the chosen-cover source object via
  -- the gerbe-local automorphism comparison, then collapse the `K.f`/`g₁` pullbacks (`mapComp`) and
  -- base-change through `K.f ≫ g₁` and `L.f` to reach `autom (L.f ^* local_overlap_source_object)`.
  ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y ≪≫
            (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
              (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).symm))) ≪≫
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      ((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp
            g₁.op.toLoc K.f.op.toLoc)).app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base))).symm ≪≫
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ g₁)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)) ≪≫
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f _

/-- Bridge iso for Lemma 8.11.8 (target side); the target analogue of
`exposed_middle_descent_source_bridge`. -/
private noncomputable def exposed_middle_descent_target_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C}
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.obj
            ((((J.pseudofunctorOver (Type (max u v))).toDescentData
                (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).obj I₂))) ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₂ := I₂.base) (K.f ≫ g₂))) :=
  -- Target analogue of `exposed_middle_descent_source_bridge` (on `I₂`/`g₂`).
  ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y ≪≫
            (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
              (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).symm))) ≪≫
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      ((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp
            g₂.op.toLoc K.f.op.toLoc)).app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base))).symm ≪≫
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ g₂)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)) ≪≫
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f _

/-- Bridge iso for Lemma 8.11.8: the refactor broke the definitional identification between the
abstract `toDescentData (· .f)` datum of `automorphismUnderlyingSheaf y` at `I₁` and the chosen
descent datum `chosen_cover_descent_datum` at `I₁.base`, after pulling to the secondary cover.
The genuine bridge iso is named here so downstream assembly can stay in a stable normal form. -/
private noncomputable def to_chosen_middle_descent_source_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C}
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.obj
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.obj
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.obj
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).obj I₁))).obj K)).obj L ≅
      ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.obj
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.obj
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.obj
          ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).obj I₁.base))).obj K)).obj L :=
  -- Inner identification `I₁.f ^* y` ⟶ chosen-cover descent datum component: base-change, then the
  -- gerbe-local automorphism comparison, then the chosen-cover descent-datum cover iso; mapped
  -- through the `g₁`/`K.f`/`L.f` pullback shells (which the cover-descent functor applies).
  ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
    (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y ≪≫
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).symm ≪≫
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).symm)))

/-- Bridge iso for Lemma 8.11.8 (target side); the target analogue of
`to_chosen_middle_descent_source_bridge`. -/
private noncomputable def to_chosen_middle_descent_target_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C}
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.obj
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.obj
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.obj
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).obj I₂))).obj K)).obj L ≅
      ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.obj
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.obj
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.obj
          ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).obj I₂.base))).obj K)).obj L :=
  -- Target analogue of `to_chosen_middle_descent_source_bridge` (on `I₂`/`g₂`).
  ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
    (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y ≪≫
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
            (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).symm ≪≫
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).symm)))

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem pullback_cover_target_secondary_cover_exposed_middle_component_expose
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
        ((((J.pseudofunctorOver (Type (max u v))).toDescentData
            (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))) := by
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)) _ L,
    localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂) _ K]
  rfl
/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem chosen_cover_overlap_map_to_secondary_cover_descent_component_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow)
    (S : (Over L.Y)ᵒᵖ) :
    ((((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
      ((((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))) ≫
          (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂
              (_hf₁ := hf₁) (_hf₂ := hf₂))) ≫
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂)))))).hom L).1.app S =
      (((secondary_cover_descent_iso_on_local_overlap
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).hom).hom L).1.app S :=
  congrArg (fun m ↦ (m.hom L).1.app S)
    (chosen_cover_overlap_map_to_secondary_cover_descent
      (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ hf₁ hf₂ K)
/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem pullback_cover_target_secondary_cover_exposed_middle_component_expose_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow)
    (S : (Over L.Y)ᵒᵖ) :
    (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂)))).1.app S =
      ((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L).1.app
        S) :=
  congrArg (fun m ↦ m.1.app S)
    (pullback_cover_target_secondary_cover_exposed_middle_component_expose
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L).symm
/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem pullback_cover_target_secondary_cover_source_boundary_expose
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K)).hom L =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
              (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))) := by
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)) _ L,
    localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂) _ K]
  rfl
/-- Helper for Lemma 8.11.8: on the self-leg of the fixed secondary-cover refinement `L`, the
source-side descent datum is already the explicit `mapComp'` boundary shell. This isolates the
right-hand normalization from the remaining common-owner comparison. -/
private theorem pullback_cover_target_secondary_cover_source_common_owner_iso_eq_local_overlap_source_iso
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y Z : C} {q : Y ⟶ U}
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    chosen_local_common_owner_source_iso
        (𝒮 := 𝒮) hGerbe
        (x := local_overlap_source_object
          (𝒮 := 𝒮)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (K.f ≫ g₁))
        (z := local_overlap_target_object
          (𝒮 := 𝒮)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₂ := I₂.base) (K.f ≫ g₂))
        (q := L.f) (K := L) (g := 𝟙 L.Y) (hg := Category.id_comp L.f) =
      local_overlap_common_owner_source_iso
        (𝒮 := 𝒮) hGerbe
        (S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (xS := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (I₁ := I₁.base) (I₂ := I₂.base) (f₁ := K.f ≫ g₁) (f₂ := K.f ≫ g₂)
        (q := L.f) (K := L) (g := 𝟙 L.Y) (hg := Category.id_comp L.f) :=
  rfl
/-- Helper for Lemma 8.11.8: on the self-leg of the fixed secondary-cover refinement `L`, the
source-side descent datum is already the explicit `mapComp'` boundary shell. This isolates the
right-hand normalization from the remaining common-owner comparison. -/
private theorem pullback_cover_target_secondary_cover_source_boundary_self_leg_normalize
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (local_overlap_source_secondary_descent_data
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          L.f.op.toLoc (𝟙 L.Y).op.toLoc L.f.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (local_overlap_source_secondary_sheaf
          (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (K.f ≫ g₁))) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
          L.f.op.toLoc (𝟙 L.Y).op.toLoc L.f.op.toLoc (by cat_disch)).hom.toNatTrans.app
          (local_overlap_source_secondary_sheaf
            (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (K.f ≫ g₁))) :=
  local_overlap_source_secondary_transition_normalize
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
    (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)
    (q := L.f) (K₁ := L) (K₂ := L) (𝟙 L.Y) (𝟙 L.Y)
    (Category.id_comp L.f) (Category.id_comp L.f)
/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem pullback_cover_target_secondary_cover_source_boundary_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K)).hom L =
        ((assembly_clai_source_to_ssdd_bridge
            (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
          (local_overlap_source_secondary_descent_data
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
            L.f (𝟙 L.Y) (𝟙 L.Y) ≫
          (assembly_clai_target_to_ssdd_bridge
            (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv) := by
  -- The secondary descent self-leg transition is the identity (`mapComp.inv ≫ mapComp.hom`).
  have hid :
      (local_overlap_source_secondary_descent_data (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) = 𝟙 _ := by
    rw [pullback_cover_target_secondary_cover_source_boundary_self_leg_normalize
      (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ K L]
    simpa [Cat.Hom.toNatIso] using
      Iso.inv_hom_id_app (Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
          L.f.op.toLoc (𝟙 L.Y).op.toLoc L.f.op.toLoc (by cat_disch)))
        (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (K.f ≫ g₁))
  -- `assembly_clai_target_to_ssdd_bridge = shells(gerbe.symm) ≪≫ assembly_clai_source_to_ssdd_bridge`,
  -- so its inverse cancels `source_bridge.hom` and re-exposes `shells(gerbe.hom)`, which is the
  -- (functor-mapped) LHS by `localizedSheafToCoverDescentEquivalence_functor_map_component`.
  rw [hid, Category.id_comp,
    localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)) _ L,
    localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂) _ K]
  simp only [assembly_clai_target_to_ssdd_bridge, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv]
  exact (Iso.hom_inv_id_assoc _ _).symm

private theorem cancel_two_left_iso {D : Type*} [Category D]
    {O₀ O₁ O₂ O₃ O₄ : D}
    {a : O₀ ⟶ O₁} {b : O₁ ⟶ O₂} (e : O₃ ≅ O₂) (tail : O₂ ⟶ O₄) :
    (a ≫ b ≫ e.inv) ≫ e.hom ≫ tail = a ≫ b ≫ tail := by
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]

private theorem cancel_left_iso {D : Type*} [Category D]
    {O₀ O₁ O₂ O₃ : D}
    {a : O₀ ⟶ O₁} (e : O₂ ≅ O₁) (tail : O₁ ⟶ O₃) :
    (a ≫ e.inv) ≫ e.hom ≫ tail = a ≫ tail := by
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]

private theorem cancel_left_iso_nested {D : Type*} [Category D]
    {O₀ O₁ O₂ O₃ O₄ : D}
    {a : O₀ ⟶ O₁} {b : O₁ ⟶ O₂} (e : O₃ ≅ O₂) (tail : O₂ ⟶ O₄) :
    ((a ≫ (b ≫ e.inv)) ≫ e.hom) ≫ tail = (a ≫ b) ≫ tail := by
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]

private theorem mapComp'_inv_app_eq_mapComp_adapter {B : Type*} [Bicategory B]
    [Bicategory.Strict B] (F : Pseudofunctor B Cat)
    {b₀ b₁ b₂ : B} {a : b₀ ⟶ b₁} {b : b₁ ⟶ b₂}
    {c : b₀ ⟶ b₂} {w : a ≫ b = c} {X : (F.obj b₀)} :
    (F.mapComp' a b c w).inv.toNatTrans.app X =
      (F.mapComp a b).inv.toNatTrans.app X ≫ eqToHom (by rw [w]) := by
  subst w
  simp only [Pseudofunctor.mapComp'_eq_mapComp, eqToHom_refl, Category.comp_id]

private theorem mapComp'_hom_app_eq_mapComp_adapter {B : Type*} [Bicategory B]
    [Bicategory.Strict B] (F : Pseudofunctor B Cat)
    {b₀ b₁ b₂ : B} {a : b₀ ⟶ b₁} {b : b₁ ⟶ b₂}
    {c : b₀ ⟶ b₂} {w : a ≫ b = c} {X : (F.obj b₀)} :
    (F.mapComp' a b c w).hom.toNatTrans.app X =
      eqToHom (by rw [w]) ≫ (F.mapComp a b).hom.toNatTrans.app X := by
  subst w
  simp only [Pseudofunctor.mapComp'_eq_mapComp, eqToHom_refl, Category.id_comp]

private theorem cover_cancel_adapter {D1 D2 D3 D4 : Type*} [Category D1]
    [Category D2] [Category D3] [Category D4]
    (Ga : Functor D1 D2) (Gb : Functor D2 D3) (Gc : Functor D3 D4)
    {a b c : D1} (e : a ≅ b) (z : b ⟶ c) :
    Gc.map (Gb.map (Ga.map e.inv)) ≫ Gc.map (Gb.map (Ga.map e.hom ≫ Ga.map z)) =
      Gc.map (Gb.map (Ga.map z)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Functor.map_id, Category.id_comp]

private theorem cover_cancel_adapter_tail {D1 D2 D3 D4 : Type*} [Category D1]
    [Category D2] [Category D3] [Category D4]
    (Ga : Functor D1 D2) (Gb : Functor D2 D3) (Gc : Functor D3 D4)
    {a b : D1} {z : D4} (e : a ≅ b) (tail : Gc.obj (Gb.obj (Ga.obj b)) ⟶ z) :
    Gc.map (Gb.map (Ga.map e.inv)) ≫ Gc.map (Gb.map (Ga.map e.hom)) ≫ tail =
      tail := by
  rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    Iso.inv_hom_id, Functor.map_id, Functor.map_id, Functor.map_id, Category.id_comp]

/-- Helper for Lemma 8.11.8: source-side three-fold base-change merge in the unprimed
`mapComp` normal form produced by expanding `toDescentData`. -/
private theorem srcmerge_unprimed_adapter
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W X : C} (x : 𝒮.p.Fiber X) {D : Sheaf (J.over X) (Type (max u v))}
    (cov : D ⟶ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (g : V ⟶ X) (Kf : W ⟶ V) (Lf : U ⟶ W) :
    ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map cov)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).mapComp
            g.op.toLoc Kf.op.toLoc).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (Kf ≫ g) x).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        ((Kf ≫ g) ^*[canonicalPullbackChoice 𝒮.p] x)).hom =
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map cov ≫
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g x).hom) ≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Kf
            (g ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        (Kf ^*[canonicalPullbackChoice 𝒮.p] (g ^*[canonicalPullbackChoice 𝒮.p] x))).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor Lf).map
          ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).inv)).hom := by
  -- Convert the primed merge statement to the unprimed `mapComp` shape appearing after
  -- `toDescentData` unfolds.
  have w₁ : g.op.toLoc ≫ Kf.op.toLoc = (Kf ≫ g).op.toLoc := by
    simp [← Quiver.Hom.comp_toLoc, ← op_comp]
  simpa only [mapComp'_inv_app_eq_mapComp_adapter, Functor.map_comp, Category.assoc,
    eqToHom_map, op_comp, Quiver.Hom.comp_toLoc, eqToHom_refl, Category.comp_id] using
    (srcmerge (𝒮 := 𝒮) hAbelian x (cov := cov) g Kf Lf w₁)

private theorem srcmerge_unprimed_adapter_explicit
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W X : C} (x : 𝒮.p.Fiber X) {D : Sheaf (J.over X) (Type (max u v))}
    (cov : D ⟶ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (g : V ⟶ X) (Kf : W ⟶ V) (Lf : U ⟶ W) :
    ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map cov)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).mapComp
            g.op.toLoc Kf.op.toLoc).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (Kf ≫ g) x).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor (Kf ≫ g)).obj x)).hom =
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map cov ≫
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g x).hom) ≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Kf
            (g ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        (Kf ^*[canonicalPullbackChoice 𝒮.p] (g ^*[canonicalPullbackChoice 𝒮.p] x))).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor Lf).map
          ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).inv)).hom := by
  exact srcmerge_unprimed_adapter (𝒮 := 𝒮) hAbelian x (cov := cov) g Kf Lf

private theorem tgtmerge_unprimed_adapter
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W X : C} (x : 𝒮.p.Fiber X) {D : Sheaf (J.over X) (Type (max u v))}
    (cinv : automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x ⟶ D)
    (g : V ⟶ X) (Kf : W ⟶ V) (Lf : U ⟶ W) :
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        ((Kf ≫ g) ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (Kf ≫ g) x).inv) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).mapComp
            g.op.toLoc Kf.op.toLoc).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map cinv)) =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor Lf).map
          ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).inv)).inv ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        (Kf ^*[canonicalPullbackChoice 𝒮.p] (g ^*[canonicalPullbackChoice 𝒮.p] x))).inv ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Kf
            (g ^*[canonicalPullbackChoice 𝒮.p] x)).inv) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g x).inv)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map cinv)) := by
  have w₁ : g.op.toLoc ≫ Kf.op.toLoc = (Kf ≫ g).op.toLoc := by
    simp [← Quiver.Hom.comp_toLoc, ← op_comp]
  simpa only [mapComp'_hom_app_eq_mapComp_adapter, Functor.map_comp, Category.assoc,
    eqToHom_map, op_comp, Quiver.Hom.comp_toLoc, eqToHom_refl, Category.id_comp] using
    (tgtmerge (𝒮 := 𝒮) hAbelian x (cinv := cinv) g Kf Lf w₁)

private theorem srcmerge_cancel_left_cover_adapter
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W X : C} (x : 𝒮.p.Fiber X) {D : Sheaf (J.over X) (Type (max u v))}
    (e : D ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (g : V ⟶ X) (Kf : W ⟶ V) (Lf : U ⟶ W) :
    ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map e.inv)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map e.hom ≫
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g x).hom) ≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Kf
            (g ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        (Kf ^*[canonicalPullbackChoice 𝒮.p] (g ^*[canonicalPullbackChoice 𝒮.p] x))).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor Lf).map
          ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).inv)).hom =
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).mapComp
            g.op.toLoc Kf.op.toLoc).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (Kf ≫ g) x).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
    ((Kf ≫ g) ^*[canonicalPullbackChoice 𝒮.p] x)).hom := by
  rw [← srcmerge_unprimed_adapter (𝒮 := 𝒮) hAbelian x (cov := e.hom) g Kf Lf]
  exact cover_cancel_adapter_tail
    ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor
    ((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor
    ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor
    e _

private theorem srcmerge_cancel_left_cover_adapter_mapped_prefix
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W X : C} (x : 𝒮.p.Fiber X) {D : Sheaf (J.over X) (Type (max u v))}
    (e : D ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (g : V ⟶ X) (Kf : W ⟶ V) (Lf : U ⟶ W)
    {A : Sheaf (J.over W) (Type (max u v))}
    (p : A ⟶
      ((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x))) :
    ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (p ≫
          ((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map e.inv)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map e.hom ≫
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g x).hom) ≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Kf
            (g ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        (Kf ^*[canonicalPullbackChoice 𝒮.p] (g ^*[canonicalPullbackChoice 𝒮.p] x))).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor Lf).map
          ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).inv)).hom =
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map p ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).mapComp
            g.op.toLoc Kf.op.toLoc).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (Kf ≫ g) x).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        ((Kf ≫ g) ^*[canonicalPullbackChoice 𝒮.p] x)).hom := by
  rw [Functor.map_comp]
  simpa only [Category.assoc] using
    congrArg
      (fun f ↦ ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map p ≫ f)
      (srcmerge_cancel_left_cover_adapter (𝒮 := 𝒮) hAbelian x e g Kf Lf)

private theorem srcmerge_cancel_left_cover_adapter_mapped_prefix_split
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W X : C} (x : 𝒮.p.Fiber X) {D : Sheaf (J.over X) (Type (max u v))}
    (e : D ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (g : V ⟶ X) (Kf : W ⟶ V) (Lf : U ⟶ W)
    {A : Sheaf (J.over W) (Type (max u v))}
    (p : A ⟶
      ((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x))) :
    ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (p ≫
          ((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map e.inv)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map e.hom)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g x).hom)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Kf
          (g ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        (Kf ^*[canonicalPullbackChoice 𝒮.p] (g ^*[canonicalPullbackChoice 𝒮.p] x))).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor Lf).map
          ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).inv)).hom =
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map p ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).mapComp
            g.op.toLoc Kf.op.toLoc).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (Kf ≫ g) x).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        ((Kf ≫ g) ^*[canonicalPullbackChoice 𝒮.p] x)).hom := by
  simpa only [Functor.map_comp, Category.assoc] using
    (srcmerge_cancel_left_cover_adapter_mapped_prefix
      (𝒮 := 𝒮) hAbelian x e g Kf Lf p)

private theorem srcmerge_cancel_left_cover_adapter_mapped_prefix_split₂
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W X : C} (x : 𝒮.p.Fiber X) {D : Sheaf (J.over X) (Type (max u v))}
    (e : D ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (g : V ⟶ X) (Kf : W ⟶ V) (Lf : U ⟶ W)
    {A B : Sheaf (J.over W) (Type (max u v))}
    (p : A ⟶ B)
    (q : B ⟶
      ((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x))) :
    ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((p ≫ q) ≫
          ((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map e.inv)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map e.hom)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g x).hom)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Kf
          (g ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        (Kf ^*[canonicalPullbackChoice 𝒮.p] (g ^*[canonicalPullbackChoice 𝒮.p] x))).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor Lf).map
          ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).inv)).hom =
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map (p ≫ q) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).mapComp
            g.op.toLoc Kf.op.toLoc).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (Kf ≫ g) x).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        ((Kf ≫ g) ^*[canonicalPullbackChoice 𝒮.p] x)).hom := by
  simpa only [Category.assoc] using
    (srcmerge_cancel_left_cover_adapter_mapped_prefix_split
      (𝒮 := 𝒮) hAbelian x e g Kf Lf (p ≫ q))

private theorem srcmerge_cancel_left_cover_adapter_mapped_prefix_split₂_tail
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W X : C} (x : 𝒮.p.Fiber X) {D : Sheaf (J.over X) (Type (max u v))}
    (e : D ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (g : V ⟶ X) (Kf : W ⟶ V) (Lf : U ⟶ W)
    {A B : Sheaf (J.over W) (Type (max u v))}
    {T : Sheaf (J.over U) (Type (max u v))}
    (p : A ⟶ B)
    (q : B ⟶
      ((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)))
    (tail : automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (Lf ^*[canonicalPullbackChoice 𝒮.p] ((Kf ≫ g) ^*[canonicalPullbackChoice 𝒮.p] x)) ⟶ T) :
    ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((p ≫ q) ≫
          ((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map e.inv)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map e.hom)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g x).hom)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Kf
          (g ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        (Kf ^*[canonicalPullbackChoice 𝒮.p] (g ^*[canonicalPullbackChoice 𝒮.p] x))).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor Lf).map
          ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).inv)).hom ≫
      tail =
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map (p ≫ q) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).mapComp
            g.op.toLoc Kf.op.toLoc).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (Kf ≫ g) x).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        ((Kf ≫ g) ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
      tail := by
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ tail)
      (srcmerge_cancel_left_cover_adapter_mapped_prefix_split₂
        (𝒮 := 𝒮) hAbelian x e g Kf Lf p q)

private theorem natiso_conj_adapter {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂]
    [Category C₃] {Fa : Functor C₁ C₃} {H : Functor C₁ C₂} {G : Functor C₂ C₃}
    (α : Fa ≅ H ⋙ G) {X Y : C₁} (f : X ⟶ Y) {Z : C₃}
    (rest : Fa.obj Y ⟶ Z) :
    α.hom.app X ≫ (H ⋙ G).map f ≫ α.inv.app Y ≫ rest = Fa.map f ≫ rest := by
  slice_lhs 1 3 => rw [NatIso.naturality_2]

private theorem assemble_mid_adapter {D : Type*} [Category D] {O0 O1 O2 O3 O4 O7 : D}
    {p1 : O0 ⟶ O1} {p2 : O1 ⟶ O2} {M1 : O2 ⟶ O3} {M2 : O3 ⟶ O4}
    {M34 : O4 ⟶ O2} {suf : O2 ⟶ O7} (hmid : M1 ≫ M2 ≫ M34 = 𝟙 O2) :
    p1 ≫ p2 ≫ M1 ≫ M2 ≫ M34 ≫ suf = p1 ≫ p2 ≫ suf := by
  rw [reassoc_of% hmid]

/-- Helper for Lemma 8.11.8: paste a normalized middle block through a fixed prefix and
suffix.  This keeps the target-side `mapComp`/local-isomorphism cancellation from depending on a
particular parenthesization of the surrounding composite. -/
private theorem paste_middle_context_adapter {D : Type*} [Category D]
    {A B E F : D} {pre : A ⟶ B} {mid rhs : B ⟶ E} {post : E ⟶ F}
    (hmid : mid = rhs) :
    pre ≫ mid ≫ post = pre ≫ rhs ≫ post := by
  rw [hmid]

private theorem assemble_hT_adapter {D : Type*} [Category D] {O0 O1 O2 O3 O4 O5 O6 : D}
    {a : O0 ⟶ O1} {b : O1 ⟶ O2} {m : O2 ⟶ O3} {ci : O3 ⟶ O4}
    {ch : O4 ⟶ O5} {ac : O5 ⟶ O6} {cl' : O3 ⟶ O5} {lo : O0 ⟶ O6}
    (hcov : ci ≫ ch = cl') (hfull : a ≫ b ≫ m ≫ cl' ≫ ac = lo) :
    (a ≫ b ≫ m ≫ ci) ≫ ch ≫ ac = lo := by
  rw [← hfull, ← hcov]
  simp only [Category.assoc]

private theorem assemble_right_adapter {D : Type*} [Category D] {O0 O2 O3 O4 O5 O6 : D}
    {a : O0 ⟶ O2} {s : O2 ⟶ O0} {cj : O0 ⟶ O3} {t : O3 ⟶ O4}
    {fl : O4 ⟶ O5} {ci : O5 ⟶ O6} {lo : O3 ⟶ O6}
    (hS : a ≫ s = 𝟙 O0) (hT : t ≫ fl ≫ ci = lo) :
    cj ≫ lo ≫ 𝟙 O6 = a ≫ ((s ≫ cj ≫ t) ≫ fl) ≫ ci := by
  rw [Category.comp_id, ← hT]
  simp only [Category.assoc]
  rw [← Category.assoc a s, hS, Category.id_comp]

private theorem solve_three_iso_bridge_square {D : Type*} [Category D]
    {X X₁ X₂ X₃ Y Y₁ Y₂ Y₃ : D}
    {B₁ : X ≅ X₁} {L₁ : X₂ ≅ X₁} {C₁ : X₃ ≅ X₂}
    {B₂ : Y ≅ Y₁} {L₂ : Y₂ ≅ Y₁} {C₂ : Y₃ ≅ Y₂}
    {t : X ⟶ Y} {d : X₃ ⟶ Y₃}
    (h : t ≫ B₂.hom ≫ L₂.inv ≫ C₂.inv =
         B₁.hom ≫ L₁.inv ≫ C₁.inv ≫ d) :
    L₁.hom ≫ B₁.inv ≫ t =
      C₁.inv ≫ d ≫ C₂.hom ≫ L₂.hom ≫ B₂.inv := by
  calc
    L₁.hom ≫ B₁.inv ≫ t
        = L₁.hom ≫ B₁.inv ≫
            (t ≫ B₂.hom ≫ L₂.inv ≫ C₂.inv) ≫
            C₂.hom ≫ L₂.hom ≫ B₂.inv := by
          simp [Category.assoc]
    _ = L₁.hom ≫ B₁.inv ≫
            (B₁.hom ≫ L₁.inv ≫ C₁.inv ≫ d) ≫
            C₂.hom ≫ L₂.hom ≫ B₂.inv := by
          rw [h]
    _ = C₁.inv ≫ d ≫ C₂.hom ≫ L₂.hom ≫ B₂.inv := by
          simp [Category.assoc]

private theorem solve_three_iso_bridge_square_rev {D : Type*} [Category D]
    {X X₁ X₂ X₃ Y Y₁ Y₂ Y₃ : D}
    {B₁ : X ≅ X₁} {L₁ : X₂ ≅ X₁} {C₁ : X₃ ≅ X₂}
    {B₂ : Y ≅ Y₁} {L₂ : Y₂ ≅ Y₁} {C₂ : Y₃ ≅ Y₂}
    {t : X ⟶ Y} {d : X₃ ⟶ Y₃}
    (h :
      L₁.hom ≫ B₁.inv ≫ t =
        C₁.inv ≫ d ≫ C₂.hom ≫ L₂.hom ≫ B₂.inv) :
    t ≫ B₂.hom ≫ L₂.inv ≫ C₂.inv =
      B₁.hom ≫ L₁.inv ≫ C₁.inv ≫ d := by
  calc
    t ≫ B₂.hom ≫ L₂.inv ≫ C₂.inv
        = B₁.hom ≫ L₁.inv ≫
            (L₁.hom ≫ B₁.inv ≫ t) ≫
            B₂.hom ≫ L₂.inv ≫ C₂.inv := by
          simp [Category.assoc]
    _ = B₁.hom ≫ L₁.inv ≫
            (C₁.inv ≫ d ≫ C₂.hom ≫ L₂.hom ≫ B₂.inv) ≫
            B₂.hom ≫ L₂.inv ≫ C₂.inv := by
          rw [h]
    _ = B₁.hom ≫ L₁.inv ≫ C₁.inv ≫ d := by
          simp [Category.assoc]

/-- Helper for Lemma 8.11.8: paste a right-hand square through a fixed prefix and cancel the
terminal isomorphism.  This keeps the target-side secondary-cover calculation from relying on
fragile occurrence matching in a long composite. -/
private theorem paste_right_tail_adapter {D : Type*} [Category D]
    {A B C D₁ E F G H : D}
    {p : A ⟶ B} {q : B ⟶ C} {r : C ⟶ D₁} {s : D₁ ⟶ E}
    {u : C ⟶ F} {v : F ⟶ G} (e : E ≅ G) {tail : G ⟶ H}
    (h : r ≫ s = u ≫ v ≫ e.inv) :
    p ≫ q ≫ r ≫ s ≫ e.hom ≫ tail =
      p ≫ q ≫ u ≫ v ≫ tail := by
  -- Paste the named square inside the composite, then cancel the exposed isomorphism.
  rw [reassoc_of% h]
  rw [Iso.inv_hom_id_assoc]

/-- Helper for Lemma 8.11.8: cancel two exposed source bridges whose inverses have been grouped
as a prefix of the remaining tail. -/
private theorem cancel_two_iso_prefix {D : Type*} [Category D] {A B C H : D}
    (e₁ : A ≅ B) (e₂ : B ≅ C) {tail : A ⟶ H} :
    e₁.hom ≫ e₂.hom ≫ ((e₂.inv ≫ e₁.inv) ≫ tail) = tail := by
  -- Reassociate until each `hom ≫ inv` pair is adjacent, then cancel both pairs.
  simp [Category.assoc]

/-- Helper for Lemma 8.11.8: solve a left boundary equality with two adjacent isomorphisms,
turning `eA.hom ≫ eB.inv ≫ m = raw` into the transported form
`m = eB.hom ≫ eA.inv ≫ raw`. -/
private theorem solve_two_left_iso {D : Type*} [Category D] {A B C H : D}
    (eA : A ≅ C) (eB : B ≅ C) {m : B ⟶ H} {raw : A ⟶ H}
    (h : eA.hom ≫ eB.inv ≫ m = raw) :
    m = eB.hom ≫ eA.inv ≫ raw := by
  rw [← h]
  simp [Category.assoc]

private theorem pullback_cover_target_secondary_cover_right_component_decompose_adapter
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
      (assembly_local_overlap_target_to_tsdd_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) =
    ((assembly_chosen_to_local_overlap_source_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂) (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
            (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom) ≫
            (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
              ((chosen_local_automorphism_iso
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)))).hom K)).hom L ≫
      (assembly_clai_target_to_tsdd_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv) := by
  have hid : (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) = 𝟙 _ := by
    rw [local_overlap_target_secondary_transition_normalize
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base)
      (K.f ≫ g₁) (K.f ≫ g₂) (q := L.f) (𝟙 L.Y) (𝟙 L.Y)]
    simpa [Cat.Hom.toNatIso] using
      Iso.inv_hom_id_app (Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
          L.f.op.toLoc (𝟙 L.Y).op.toLoc L.f.op.toLoc (by cat_disch)))
        (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₂ := I₂.base) (K.f ≫ g₂))
  rw [hid]
  rw [pullback_cover_target_secondary_cover_right_branch_exposed
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L]
  rw [pullback_cover_target_secondary_cover_middle_component_as_conjugation
    (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂ K L]
  refine assemble_right_adapter ?hS ?hT
  case hS =>
    have w₁ : g₁.op.toLoc ≫ K.f.op.toLoc = (K.f ≫ g₁).op.toLoc := by
      simp [← Quiver.Hom.comp_toLoc, ← op_comp]
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    erw [← srcmerge (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
        (cov := (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).hom)
        g₁ K.f L.f w₁]
    rw [Iso.hom_comp_eq_id]
    rw [mapComp'_inv_app_eq_mapComp_adapter (J.pseudofunctorOver (Type (max u v)))]
    simp only [assembly_chosen_to_local_overlap_source_bridge,
      assembly_clai_source_to_ssdd_bridge, assembly_ssdd_to_local_overlap_source_bridge,
      Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Iso.trans_hom,
      Functor.mapIso_inv, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc, eqToHom_map, op_comp, Quiver.Hom.comp_toLoc,
      eqToHom_refl, Category.comp_id, Iso.inv_hom_id_assoc]
    rfl
  case hT =>
    have w₂ : g₂.op.toLoc ≫ K.f.op.toLoc = (K.f ≫ g₂).op.toLoc := by
      simp [← Quiver.Hom.comp_toLoc, ← op_comp]
    simp only [localizedSheafToCoverDescentEquivalence_functor_map_component,
      Iso.trans_inv, Functor.mapIso_inv]
    erw [← tgtmerge (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (cinv := (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).inv)
        g₂ K.f L.f w₂]
    refine assemble_hT_adapter (cover_cancel_adapter _ _ _
      (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)
      ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)) ?hfull
    rw [mapComp'_hom_app_eq_mapComp_adapter (J.pseudofunctorOver (Type (max u v)))]
    simp only [assembly_clai_target_to_tsdd_bridge, assembly_local_overlap_target_to_tsdd_bridge,
      Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, Iso.trans_hom,
      Functor.mapIso_inv, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc, eqToHom_map, op_comp, Quiver.Hom.comp_toLoc,
      eqToHom_refl, Category.id_comp, Category.comp_id]
    have hinner :
        ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc).hom.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)) ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
                (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                  (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
            ((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc)).app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y))).inv ≫
              ((J.pseudofunctorOver (Type (max u v))).map (g₂.op.toLoc ≫ K.f.op.toLoc)).toFunctor.map
                (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                  (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv = 𝟙 _ := by
      erw [natiso_conj_adapter (Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc))
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
            (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom]
      erw [← Functor.map_comp]
      simp
    have hmid :
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc).hom.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base))) ≫
          ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
                  (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                    (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)) ≫
            ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              (((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc)).app
                  (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                    (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y))).inv ≫
                ((J.pseudofunctorOver (Type (max u v))).map (g₂.op.toLoc ≫ K.f.op.toLoc)).toFunctor.map
                  (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                    (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv) = 𝟙 _ := by
      erw [← Functor.map_comp, ← Functor.map_comp]
      rw [hinner]
      simp
    exact assemble_mid_adapter hmid

/-- RHS bridge for the uncancelled `y` transition: after the chosen-cover RHS has been routed
through the local-overlap source and target assembly bridges, it is exactly the target secondary
boundary of the local-overlap conjugation square. -/
private theorem pullback_cover_y_transition_chosen_middle_rhs_assembly_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((assembly_chosen_to_local_overlap_source_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂) (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
            (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom) ≫
            (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
              ((chosen_local_automorphism_iso
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)))).hom K)).hom L ≫
      (assembly_clai_target_to_tsdd_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv) =
    (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
      (assembly_local_overlap_target_to_tsdd_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) := by
  exact (pullback_cover_target_secondary_cover_right_component_decompose_adapter
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L).symm

/-- Helper for Lemma 8.11.8: on the fixed `(K,L)` component, the source tail
`baseChange(I₁.f, y).hom ≫ chosen_local₁.inv` is functorial through the two local-overlap
refinements. -/
private theorem to_chosen_middle_descent_source_tail_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C}
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    let B₁ :=
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).hom
    let L₁ :=
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
          (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv))
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map (B₁ ≫ L₁)) =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map B₁) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map L₁) := by
  dsimp
  simp only [Functor.map_comp]

private theorem automorphism_overlap_hom_fold_mapped_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch)
    (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow) :
    let E :=
      localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂)
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((E.unitIso.app (local_overlap_source_secondary_sheaf
          (𝒮 := 𝒮) hAbelian S xS f₁)).hom) ≫
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (E.inverse.map
          (secondary_cover_descent_iso_on_local_overlap
            (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom) ≫
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((E.unitIso.app (local_overlap_target_secondary_sheaf
          (𝒮 := 𝒮) hAbelian S xS f₂)).inv) =
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂ hf₁ hf₂) := by
  intro E
  dsimp [E]
  simp only [automorphism_overlap_hom_of_locally_isomorphic_cover,
    Functor.map_comp, Iso.app_hom, Iso.app_inv]
  rfl

/-- Helper for Lemma 8.11.8: expand the target-side bridge on the fixed `(K,L)` component into
the three mapped target normalizations. -/
private theorem to_chosen_middle_descent_KL_left_normalization
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    let E₁ :=
      localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)
    let E₂ :=
      localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))
    let t :=
      ((E₂.functor.map ((E₁.functor.map
        ((((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
            r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L)
    let B₂ :=
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)))
    let L₂ :=
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
            (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
              (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y))))
    let C₂ :=
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)))
    t ≫ (to_chosen_middle_descent_target_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom =
      t ≫ B₂.hom ≫ L₂.inv ≫ C₂.inv := by
  dsimp [to_chosen_middle_descent_target_bridge]
  rfl

private theorem to_chosen_middle_descent_base_component_square
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
          (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
          r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂) =
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).inv ≫
      (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
        (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
        (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
        (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
          (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv := by
  exact to_chosen_middle_descent_base_component_square_api
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂

/-- Component square in the cancellation-friendly orientation.  This is the small interface used
to keep the bridge naturality proof out of the long expanded composite. -/
private theorem to_chosen_middle_descent_component_square
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    let E₁ :=
      localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)
    let E₂ :=
      localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))
    let t :=
      ((E₂.functor.map ((E₁.functor.map
        ((((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
            r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L)
    let d :=
      ((E₂.functor.map ((E₁.functor.map
        ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
          (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
          (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
          (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]))).hom K)).hom L)
    let B₁ :=
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)))
    let L₁ :=
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
            (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
              (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y))))
    let C₁ :=
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian U I₁.base)))
    let B₂ :=
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)))
    let L₂ :=
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
            (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
              (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y))))
    let C₂ :=
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)))
    L₁.hom ≫ B₁.inv ≫ t =
      C₁.inv ≫ d ≫ C₂.hom ≫ L₂.hom ≫ B₂.inv := by
  dsimp only
  have hbase :=
    to_chosen_middle_descent_base_component_square
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂
  simpa only [localizedSheafToCoverDescentEquivalence_functor_map_component,
    Pseudofunctor.DescentData.comp_hom, Functor.map_comp,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, Category.comp_id, Category.id_comp] using
    congrArg
      (fun m ↦
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map m))
      hbase

/-- Core naturality square for the bridge from the abstract pullback-cover middle descent datum
to the chosen-cover middle descent datum, after evaluating at the fixed `(K,L)` component. -/
private theorem to_chosen_middle_descent_bridge_naturality_core
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
              r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L ≫
      (to_chosen_middle_descent_target_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom =
    (to_chosen_middle_descent_source_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom (i₁ := I₁.base)
              (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
              (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
              (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]))).hom K)).hom L)) := by
  let B₁ := (
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y))))
  let L₁ := (
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)))))
  let C₁ := (
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₁.base))))
  let B₂ := (
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y))))
  let L₂ := (
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
            (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)))))
  let C₂ := (
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₂.base))))
  let t := (
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
            (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
              r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L))
  have hq₁ : g₁ ≫ (I₁.f ≫ q) = r ≫ q := by
    rw [← Category.assoc, hg₁]
  have hq₂ : g₂ ≫ (I₂.f ≫ q) = r ≫ q := by
    rw [← Category.assoc, hg₂]
  let d := (
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
            (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
            (_hf₁ := hq₁) (_hf₂ := hq₂))).hom K)).hom L))
  have hcomp :
      L₁.hom ≫ B₁.inv ≫ t =
        C₁.inv ≫ d ≫ C₂.hom ≫ L₂.hom ≫ B₂.inv := by
    simpa [B₁, L₁, C₁, B₂, L₂, C₂, t, d] using
      to_chosen_middle_descent_component_square
        (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L
  have hformal :=
    solve_three_iso_bridge_square_rev
      (B₁ := B₁) (L₁ := L₁) (C₁ := C₁)
      (B₂ := B₂) (L₂ := L₂) (C₂ := C₂)
      (t := t) (d := d) hcomp
  dsimp [t, d, B₁, L₁, C₁, B₂, L₂, C₂] at hformal
  simpa only [to_chosen_middle_descent_source_bridge,
    to_chosen_middle_descent_target_bridge,
    localizedSheafToCoverDescentEquivalence_functor_map_component,
    Pseudofunctor.DescentData.comp_hom, Functor.map_comp,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, Category.comp_id, Category.id_comp] using hformal

/-- Helper for Lemma 8.11.8: component-level naturality of the middle descent comparison after
two local-overlap descent functor components.  This is the noncyclic bridge from the abstract
`toDescentData (fun I => I.f)` transition to the chosen-cover normal form; the surrounding
assembly source/target bridges are deliberately absent from the statement. -/
private theorem to_chosen_middle_descent_component_naturality
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
              (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K)).hom L ≫
      ((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
            (((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
                r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L) =
      (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).inv ≫
          (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
            (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
            (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
            (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
          ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom ≫
    ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
            (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
          (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv)).hom K)).hom L) := by
  have hcore :=
    to_chosen_middle_descent_bridge_naturality_core
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L
  let B₁ := (
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y))))
  let L₁ := (
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)))))
  let C₁ := (
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₁.base))))
  let B₂ := (
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y))))
  let L₂ := (
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
            (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)))))
  let C₂ := (
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₂.base))))
  let t := (
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
            (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
              r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L))
  have hq₁ : g₁ ≫ (I₁.f ≫ q) = r ≫ q := by
    rw [← Category.assoc, hg₁]
  have hq₂ : g₂ ≫ (I₂.f ≫ q) = r ≫ q := by
    rw [← Category.assoc, hg₂]
  let d := (
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
            (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
            (_hf₁ := hq₁) (_hf₂ := hq₂))).hom K)).hom L))
  have hcore' :
      t ≫ B₂.hom ≫ L₂.inv ≫ C₂.inv =
        B₁.hom ≫ L₁.inv ≫ C₁.inv ≫ d := by
    dsimp [t, d, B₁, L₁, C₁, B₂, L₂, C₂]
    simpa only [to_chosen_middle_descent_source_bridge,
      to_chosen_middle_descent_target_bridge,
      localizedSheafToCoverDescentEquivalence_functor_map_component,
      Pseudofunctor.DescentData.comp_hom, Functor.map_comp,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapIso_hom, Functor.mapIso_inv,
      Category.assoc, Category.comp_id, Category.id_comp] using hcore
  have hformal :=
    solve_three_iso_bridge_square
      (B₁ := B₁) (L₁ := L₁) (C₁ := C₁)
      (B₂ := B₂) (L₂ := L₂) (C₂ := C₂)
      (t := t) (d := d) hcore'
  dsimp [t, d, B₁, L₁, C₁, B₂, L₂, C₂] at hformal
  simpa only [localizedSheafToCoverDescentEquivalence_functor_map_component,
    Pseudofunctor.DescentData.comp_hom, Functor.map_comp,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, Category.comp_id, Category.id_comp] using hformal

/-- Fixed-`(K,L)` component bridge for the uncancelled `y` transition.  The abstract
pullback-cover branch is first rewritten through the chosen middle descent bridges; the exposed
source/target bridge isomorphisms then cancel, leaving exactly the mapped raw chosen-cover RHS
component. -/
private theorem pullback_cover_y_transition_chosen_middle_component_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((assembly_clai_source_to_ssdd_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (local_overlap_source_secondary_descent_data
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
          L.f (𝟙 L.Y) (𝟙 L.Y) ≫
        (assembly_clai_target_to_ssdd_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv ≫
        ((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
          (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
            ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
              (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
              (((J.pseudofunctorOver (Type (max u v))).toDescentData
                (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
                  r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L) =
      (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).inv ≫
          (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
            (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
            (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
            (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
          ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom ≫
          ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
            (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
          (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv)).hom K)).hom L) := by
  -- First replace the named source/target assembly boundary by the functorially mapped
  -- chosen-local comparison; the remaining goal is the middle descent naturality square.
  have hsource_boundary :=
    pullback_cover_target_secondary_cover_source_boundary_component
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ K L
  slice_lhs 1 3 => rw [← hsource_boundary]
  exact to_chosen_middle_descent_component_naturality
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L

/-- Helper for Lemma 8.11.8: the chosen-local source comparison is left uncancelled, so after
passing to the local-overlap secondary cover both sides are exactly the naturality square for the
secondary-cover descent isomorphism. -/
private theorem pullback_cover_y_transition_chosen_middle_uncancelled
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
  ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
        (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom ≫
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
      (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ hg₁ hg₂
  =
  ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).inv ≫
    (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
      (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
      (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
      (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
    ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom ≫
    ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom ≫
    (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv := by
  exact to_chosen_middle_descent_base_component_square
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂

/-- Helper for Lemma 8.11.8: normalize the target-side pullback-cover transition for `y`
to the chosen-cover middle form before applying secondary-cover components. -/
private theorem pullback_cover_y_transition_chosen_middle
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
  (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
      (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ hg₁ hg₂
  =
  ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
        (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv ≫
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).inv ≫
    (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
      (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
      (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
      (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
    ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom ≫
    ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom ≫
    (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv := by
  have huncancelled :=
    pullback_cover_y_transition_chosen_middle_uncancelled
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂
  simpa [Category.assoc, ← Functor.map_comp] using
    congrArg
      (fun f ↦
        ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
            (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
              (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv ≫ f)
      huncancelled

/-- Fixed-`(K,L)` varying-base bridge for Lemma 8.11.8: once the abstract
`toDescentData (fun I => I.f)` middle component is transported through the target
`assembly_clai_target_to_ssdd_bridge`, it is the local-overlap conjugation component followed by
the descent-target bridge.  This is the source-faithful omitted compatibility for moving the
canonical automorphism-sheaf comparison across the second local-overlap refinement. -/
private theorem pullback_cover_target_secondary_cover_fixed_bridge_normalization
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
        ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
          (((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
              r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L =
      ((assembly_clai_target_to_ssdd_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (assembly_ssdd_to_local_overlap_source_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
        (assembly_descent_to_local_overlap_target_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv)) := by
  exact pullback_cover_target_secondary_cover_fixed_bridge_normalization_api
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L

/-- Adapter for the remaining target-side secondary-cover assembly in Lemma 8.11.8.

This is the deliberately narrow blocker: it asks for the transport-stable normalization of the
left boundary after the `toDescentData (· .f)` shell has been moved into the named chosen-cover
normal form, and for the resulting fixed-`(K,L)` target component comparison used by Part09. -/
theorem pullback_cover_target_secondary_cover_assembly_adapter
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
          (((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L =
      ((assembly_clai_source_to_ssdd_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (local_overlap_source_secondary_descent_data
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
          L.f (𝟙 L.Y) (𝟙 L.Y) ≫
        (assembly_ssdd_to_local_overlap_source_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
        (assembly_descent_to_local_overlap_target_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv)) ∧
    (((localizedSheafToCoverDescentEquivalence (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
          (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L) =
    (((localizedSheafToCoverDescentEquivalence (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).inv ≫
      (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
        (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
        (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
        (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
          (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv)).hom K)).hom L) := by
  -- Remaining blocker: normalize the transported `toDescentData (· .f)` branch to the named
  -- chosen-cover/local-overlap assembly normal form, then paste the normalized secondary square.
  have hsecondary_square_core_left :
      (((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
            (((J.pseudofunctorOver (Type (max u v))).toDescentData
                (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
                r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L) =
        ((assembly_clai_target_to_ssdd_bridge
            (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
          (assembly_ssdd_to_local_overlap_source_bridge
            (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
          (local_overlap_conjugation_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
          (assembly_descent_to_local_overlap_target_bridge
            (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv))) := by
    exact pullback_cover_target_secondary_cover_fixed_bridge_normalization
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L
  have hsecondary_square_core :
      (((((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
            (((J.pseudofunctorOver (Type (max u v))).toDescentData
                (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
                r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L) =
        ((assembly_clai_target_to_ssdd_bridge
            (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
          (assembly_ssdd_to_local_overlap_source_bridge
            (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
          (local_overlap_conjugation_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
          (assembly_descent_to_local_overlap_target_bridge
            (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv)) ∧
      ((((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).toDescentData
            (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
            r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L) =
      (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).inv ≫
        (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
          (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
          (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
          (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
        ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom ≫
        ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
            (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv)).hom K)).hom L))) := by
    -- Single remaining core: source/target flanks have been named; what is left is the fixed
    -- `(K,L)` pullback-cover secondary square plus its chosen-cover normal form.
    constructor
    · exact hsecondary_square_core_left
    ·
      rw [pullback_cover_target_secondary_cover_left_branch_exposed
        (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L]
      rw [pullback_cover_target_secondary_cover_source_boundary_component
        (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ K L]
      exact pullback_cover_y_transition_chosen_middle_component_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L
  constructor
  · rw [pullback_cover_target_secondary_cover_left_branch_exposed
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L]
    rw [pullback_cover_target_secondary_cover_source_boundary_component
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ K L]
    have hcore :
        ((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
          (((localizedSheafToCoverDescentEquivalence (J := J)
              (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
            ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
              (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
              (((J.pseudofunctorOver (Type (max u v))).toDescentData
                  (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
                  r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L) =
          ((assembly_clai_target_to_ssdd_bridge
              (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
            (assembly_ssdd_to_local_overlap_source_bridge
              (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
            (local_overlap_conjugation_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
            (assembly_descent_to_local_overlap_target_bridge (𝒮 := 𝒮)
              hGerbe hAbelian q y g₁ g₂ K L).inv)) := by
      -- Narrow remaining core: the exposed pullback-cover descent square over the fixed
      -- secondary refinement, after the source/target flanks have been separated.
      exact hsecondary_square_core.1
    rw [hcore]
    exact cancel_two_left_iso
      (assembly_clai_target_to_ssdd_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L)
      ((assembly_ssdd_to_local_overlap_source_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
        (assembly_descent_to_local_overlap_target_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv)
  · exact hsecondary_square_core.2

/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
private theorem pullback_cover_target_secondary_cover_left_component_decompose
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
          (((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L =
      ((assembly_clai_source_to_ssdd_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (local_overlap_source_secondary_descent_data
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
          L.f (𝟙 L.Y) (𝟙 L.Y) ≫
        (assembly_ssdd_to_local_overlap_source_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
        (assembly_descent_to_local_overlap_target_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv) := by
  exact (pullback_cover_target_secondary_cover_assembly_adapter
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L).1
/-- Helper for Lemma 8.11.8: the inverse component of `mapComp'` with an explicit composite name
`c` is the inverse component of the canonical two-argument `mapComp`, transported by the
composite-witness `eqToHom`. Proven by substituting the composite witness so `mapComp'` collapses
to `mapComp` (`Pseudofunctor.mapComp'_eq_mapComp`), avoiding any unfolding of `mapComp'`. -/
theorem mapComp'_inv_app_eq_mapComp {B : Type*} [Bicategory B] [Bicategory.Strict B]
    (F : Pseudofunctor B Cat) {b₀ b₁ b₂ : B} {a : b₀ ⟶ b₁} {b : b₁ ⟶ b₂}
    {c : b₀ ⟶ b₂} {w : a ≫ b = c} {X : (F.obj b₀)} :
    (F.mapComp' a b c w).inv.toNatTrans.app X =
      (F.mapComp a b).inv.toNatTrans.app X ≫ eqToHom (by rw [w]) := by
  subst w
  simp only [Pseudofunctor.mapComp'_eq_mapComp, eqToHom_refl, Category.comp_id]

/-- Helper for Lemma 8.11.8: the hom-side analogue of `mapComp'_inv_app_eq_mapComp`. -/
theorem mapComp'_hom_app_eq_mapComp {B : Type*} [Bicategory B] [Bicategory.Strict B]
    (F : Pseudofunctor B Cat) {b₀ b₁ b₂ : B} {a : b₀ ⟶ b₁} {b : b₁ ⟶ b₂}
    {c : b₀ ⟶ b₂} {w : a ≫ b = c} {X : (F.obj b₀)} :
    (F.mapComp' a b c w).hom.toNatTrans.app X =
      eqToHom (by rw [w]) ≫ (F.mapComp a b).hom.toNatTrans.app X := by
  subst w
  simp only [Pseudofunctor.mapComp'_eq_mapComp, eqToHom_refl, Category.id_comp]

/-- Helper for Lemma 8.11.8: the `cover₂` inverse/hom cancellation through three nested pullback
functors.  Stated and proved over abstract functors so the combine fires reliably; applied at the
target merge through `assemble_hT`, whose `exact`/defeq tolerance bridges the functor-representation
mismatch between the `tgtmerge` and flank sources. -/
private theorem cover_cancel {D1 D2 D3 D4 : Type*} [Category D1] [Category D2] [Category D3]
    [Category D4] (Ga : Functor D1 D2) (Gb : Functor D2 D3) (Gc : Functor D3 D4)
    {a b c : D1} (e : a ≅ b) (z : b ⟶ c) :
    Gc.map (Gb.map (Ga.map e.inv)) ≫ Gc.map (Gb.map (Ga.map e.hom ≫ Ga.map z)) =
      Gc.map (Gb.map (Ga.map z)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Functor.map_id, Category.id_comp]

/-- Helper for Lemma 8.11.8: conjugation of a functor-morphism by a natural isomorphism collapses to
the source functor's map (`NatIso.naturality_2`), with a trailing tail.  This is the `mapComp`
naturality used to cancel the `chosen_local` transport on the target flank. -/
theorem natiso_conj {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    {Fa : Functor C₁ C₃} {H : Functor C₁ C₂} {G : Functor C₂ C₃} (α : Fa ≅ H ⋙ G)
    {X Y : C₁} (f : X ⟶ Y) {Z : C₃} (rest : Fa.obj Y ⟶ Z) :
    α.hom.app X ≫ (H ⋙ G).map f ≫ α.inv.app Y ≫ rest = Fa.map f ≫ rest := by
  slice_lhs 1 3 => rw [NatIso.naturality_2]

/-- Generic abstract-category assembler for the target flank: once the central three-fold composite
`M1 ≫ M2 ≫ M34` is the identity, the whole boundary collapses to the bare prefix/suffix. -/
private theorem assemble_mid {D : Type*} [Category D] {O0 O1 O2 O3 O4 O7 : D}
    {p1 : O0 ⟶ O1} {p2 : O1 ⟶ O2} {M1 : O2 ⟶ O3} {M2 : O3 ⟶ O4} {M34 : O4 ⟶ O2} {suf : O2 ⟶ O7}
    (hmid : M1 ≫ M2 ≫ M34 = 𝟙 O2) :
    p1 ≫ p2 ≫ M1 ≫ M2 ≫ M34 ≫ suf = p1 ≫ p2 ≫ suf := by
  rw [reassoc_of% hmid]

/-- Generic abstract-category assembler for the target merge `hT`: given the cover-cancellation
`hcov` and the reduced target identity `hfull`, glue them (associativity on abstract morphisms). -/
private theorem assemble_hT {D : Type*} [Category D] {O0 O1 O2 O3 O4 O5 O6 : D}
    {a : O0 ⟶ O1} {b : O1 ⟶ O2} {m : O2 ⟶ O3} {ci : O3 ⟶ O4} {ch : O4 ⟶ O5} {ac : O5 ⟶ O6}
    {cl' : O3 ⟶ O5} {lo : O0 ⟶ O6}
    (hcov : ci ≫ ch = cl') (hfull : a ≫ b ≫ m ≫ cl' ≫ ac = lo) :
    (a ≫ b ≫ m ≫ ci) ≫ ch ≫ ac = lo := by
  rw [← hfull, ← hcov]; simp only [Category.assoc]

/-- Generic abstract-category assembler for the right-component decomposition: glue the source
merge `hS` and the target merge `hT` around the central conjugation `cj`, absorbing the trailing
identity, with all associativity handled on abstract morphisms. -/
private theorem assemble_right {D : Type*} [Category D] {O0 O2 O3 O4 O5 O6 : D}
    {a : O0 ⟶ O2} {s : O2 ⟶ O0} {cj : O0 ⟶ O3} {t : O3 ⟶ O4} {fl : O4 ⟶ O5} {ci : O5 ⟶ O6}
    {lo : O3 ⟶ O6}
    (hS : a ≫ s = 𝟙 O0) (hT : t ≫ fl ≫ ci = lo) :
    cj ≫ lo ≫ 𝟙 O6 = a ≫ ((s ≫ cj ≫ t) ≫ fl) ≫ ci := by
  rw [Category.comp_id, ← hT]
  simp only [Category.assoc]
  rw [← Category.assoc a s, hS, Category.id_comp]

/-- Helper for Lemma 8.11.8: on the same fixed secondary-cover refinement `L`, the remaining
target shell of the pullback-cover target square should rewrite directly to the target boundary
term of the normalized local-overlap square. -/
private theorem pullback_cover_target_secondary_cover_right_component_decompose
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
      (assembly_local_overlap_target_to_tsdd_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) =
    ((assembly_chosen_to_local_overlap_source_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂) (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
            (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom) ≫
            (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
              ((chosen_local_automorphism_iso
                (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
              (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)))).hom K)).hom L ≫
      (assembly_clai_target_to_tsdd_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv) := by
  -- (1) The target self-leg `tsdd.hom L.f (𝟙) (𝟙)` is the identity.
  have hid : (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) = 𝟙 _ := by
    rw [local_overlap_target_secondary_transition_normalize
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base)
      (K.f ≫ g₁) (K.f ≫ g₂) (q := L.f) (𝟙 L.Y) (𝟙 L.Y)]
    simpa [Cat.Hom.toNatIso] using
      Iso.inv_hom_id_app (Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
          L.f.op.toLoc (𝟙 L.Y).op.toLoc L.f.op.toLoc (by cat_disch)))
        (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₂ := I₂.base) (K.f ≫ g₂))
  rw [hid]
  -- (2) Expose the chosen-cover middle branch as a conjugation, splitting the right shell.
  rw [pullback_cover_target_secondary_cover_right_branch_exposed
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L]
  rw [pullback_cover_target_secondary_cover_middle_component_as_conjugation
    (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂ K L]
  -- (3) Abstract telescope `cj ≫ lo ≫ 𝟙 = a ≫ ((s ≫ cj ≫ t) ≫ fl) ≫ ci`, closed by the two
  -- base-change-coherence merges `hS` (source flank) and `hT` (target flank).
  refine assemble_right ?hS ?hT
  case hS =>
    -- `A_chosen.hom ≫ Ssh.hom = 𝟙`.  `Ssh.hom` is `srcmerge`'s RHS; replace it by `srcmerge`'s
    -- LHS, then recognise the result as `A_chosen.inv` (`mapComp' → mapComp` via the composite
    -- witness, after which the unit/base-change shells cancel definitionally).
    have w₁ : g₁.op.toLoc ≫ K.f.op.toLoc = (K.f ≫ g₁).op.toLoc := by
      simp [← Quiver.Hom.comp_toLoc, ← op_comp]
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    erw [← srcmerge (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
        (cov := (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).hom)
        g₁ K.f L.f w₁]
    rw [Iso.hom_comp_eq_id]
    rw [mapComp'_inv_app_eq_mapComp (J.pseudofunctorOver (Type (max u v)))]
    simp only [assembly_chosen_to_local_overlap_source_bridge,
      assembly_clai_source_to_ssdd_bridge, assembly_ssdd_to_local_overlap_source_bridge,
      Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Iso.trans_hom,
      Functor.mapIso_inv, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc, eqToHom_map, op_comp, Quiver.Hom.comp_toLoc,
      eqToHom_refl, Category.comp_id, Iso.inv_hom_id_assoc]
    rfl
  case hT =>
    -- `Tsh.inv ≫ flank ≫ A_claitgt.inv = A_lotgt.hom`.  Symmetric target merge via `tgtmerge`;
    -- the `cover₂` inverse/hom pair cancels through `assemble_hT (cover_cancel …)`, after which the
    -- `chosen_local` conjugation collapses by `mapComp` naturality (`natiso_conj`) and the
    -- `chosen_local.hom ≫ .inv` / `mapComp.hom ≫ .inv` pairs vanish, leaving `bc`/`mapId`.
    have w₂ : g₂.op.toLoc ≫ K.f.op.toLoc = (K.f ≫ g₂).op.toLoc := by
      simp [← Quiver.Hom.comp_toLoc, ← op_comp]
    simp only [localizedSheafToCoverDescentEquivalence_functor_map_component,
      Iso.trans_inv, Functor.mapIso_inv]
    erw [← tgtmerge (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (cinv := (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).inv)
        g₂ K.f L.f w₂]
    refine assemble_hT (cover_cancel _ _ _
      (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)
      ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)) ?hfull
    rw [mapComp'_hom_app_eq_mapComp (J.pseudofunctorOver (Type (max u v)))]
    simp only [assembly_clai_target_to_tsdd_bridge, assembly_local_overlap_target_to_tsdd_bridge,
      Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, Iso.trans_hom,
      Functor.mapIso_inv, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc, eqToHom_map, op_comp, Quiver.Hom.comp_toLoc,
      eqToHom_refl, Category.id_comp, Category.comp_id]
    have hinner :
        ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc).hom.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)) ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
                (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                  (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
            ((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc)).app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y))).inv ≫
              ((J.pseudofunctorOver (Type (max u v))).map (g₂.op.toLoc ≫ K.f.op.toLoc)).toFunctor.map
                (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                  (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv = 𝟙 _ := by
      erw [natiso_conj (Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc))
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
            (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom]
      erw [← Functor.map_comp]
      simp
    have hmid :
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc).hom.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base))) ≫
          ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
                  (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                    (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)) ≫
            ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              (((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc)).app
                  (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                    (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y))).inv ≫
                ((J.pseudofunctorOver (Type (max u v))).map (g₂.op.toLoc ≫ K.f.op.toLoc)).toFunctor.map
                  (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                    (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv) = 𝟙 _ := by
      erw [← Functor.map_comp, ← Functor.map_comp]
      rw [hinner]
      simp
    exact assemble_mid hmid
/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
theorem pullback_cover_target_secondary_cover_outer_transport_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
          (((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L =
      ((assembly_clai_source_to_ssdd_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (local_overlap_source_secondary_descent_data
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
          L.f (𝟙 L.Y) (𝟙 L.Y) ≫
        (assembly_ssdd_to_local_overlap_source_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
        (assembly_descent_to_local_overlap_target_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv) ∧
      ((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
        (assembly_local_overlap_target_to_tsdd_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (local_overlap_target_secondary_descent_data
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
          L.f (𝟙 L.Y) (𝟙 L.Y) =
      ((assembly_chosen_to_local_overlap_source_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        ((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂) (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
            (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom) ≫
            (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
              ((chosen_local_automorphism_iso
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)))).hom K)).hom L) ≫
        (assembly_clai_target_to_tsdd_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv)) :=
  ⟨pullback_cover_target_secondary_cover_left_component_decompose
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L,
    pullback_cover_target_secondary_cover_right_component_decompose
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L⟩
end

end CategoryTheory
