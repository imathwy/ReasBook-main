import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_137_14
import stacks_proof.stacks_project.Chap10.Lemma_10_147_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits MorphismProperty
open CommRingCat

universe u₁ u₂ v₁ v₂ w w₁ w₂

namespace RingHom

section

variable {R₁ : Type u₁} {Λ₁ : Type u₁} {R₂ : Type u₂} {Λ₂ : Type u₂}
variable [CommRing R₁] [CommRing Λ₁] [CommRing R₂] [CommRing Λ₂]

/- Domain sampling pass:
* primary domain: filtered colimits of smooth commutative ring maps and their stability under
  products;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfSmooth`, the source-facing owner for PT presentations;
  - `CategoryTheory.MorphismProperty.ind`, the generic owner for filtered-colimit closure of a
    morphism property;
  - `Algebra.smooth_prod_iff`, the product criterion for smooth commutative algebras.
* best owner abstraction: the public owner here is `f.IsFilteredColimitOfSmooth`;
* primitive data: two ring homomorphisms `f₁`, `f₂`;
* derived API: any chosen filtered diagrams, cocones, and smooth stage maps witnessing PT.

Source/core/bridge triage:
* `source-facing`: PT is stable under products of ring maps;
* `core/canonical`: `f.IsFilteredColimitOfSmooth`;
* `bridge/view`: any chosen filtered diagram in `Under (CommRingCat.of _)` presenting the given
  product map.

The Noetherian and regular-map hypotheses from Situation 16.8.1 are mathematically redundant here,
so they should not remain in the public API.
-/

namespace IsFilteredColimitOfSmooth

private instance smoothMorphismPropertyRespectsIso :
    (RingHom.toMorphismProperty RingHom.Smooth).RespectsIso := by
  rw [← RingHom.toMorphismProperty_respectsIso_iff]
  exact RingHom.Smooth.respectsIso

/-- Helper for Lemma 16.8.2: the projection from a product ring to its first factor is smooth. -/
private theorem smooth_fst {A : Type*} {B : Type*} [CommRing A] [CommRing B] :
    (RingHom.fst A B).Smooth := by
  let _ : Algebra (A × B) A := (RingHom.fst A B).toAlgebra
  let _ : Algebra (A × B) B := (RingHom.snd A B).toAlgebra
  -- The identity map on the product is smooth, so each projection is smooth by the product
  -- criterion.
  have hprod : Algebra.Smooth (A × B) (A × B) := by
    simpa [RingHom.smooth_algebraMap] using (RingHom.Smooth.id (A × B))
  have hsplit :
      Algebra.Smooth (A × B) A ∧ Algebra.Smooth (A × B) B :=
    (Algebra.smooth_prod_iff (R := A × B) (S' := A) (S'' := B)).1 hprod
  exact (RingHom.smooth_algebraMap).2 hsplit.1

/-- Helper for Lemma 16.8.2: the projection from a product ring to its second factor is smooth. -/
private theorem smooth_snd {A : Type*} {B : Type*} [CommRing A] [CommRing B] :
    (RingHom.snd A B).Smooth := by
  let _ : Algebra (A × B) A := (RingHom.fst A B).toAlgebra
  let _ : Algebra (A × B) B := (RingHom.snd A B).toAlgebra
  -- The identity map on the product is smooth, so each projection is smooth by the product
  -- criterion.
  have hprod : Algebra.Smooth (A × B) (A × B) := by
    simpa [RingHom.smooth_algebraMap] using (RingHom.Smooth.id (A × B))
  have hsplit :
      Algebra.Smooth (A × B) A ∧ Algebra.Smooth (A × B) B :=
    (Algebra.smooth_prod_iff (R := A × B) (S' := A) (S'' := B)).1 hprod
  exact (RingHom.smooth_algebraMap).2 hsplit.2

/-- Helper for Lemma 16.8.2: products of smooth ring maps are smooth. -/
private theorem smooth_prodMap
    {A₁ : Type*} {B₁ : Type*} {A₂ : Type*} {B₂ : Type*}
    [CommRing A₁] [CommRing B₁] [CommRing A₂] [CommRing B₂]
    {g₁ : A₁ →+* B₁} {g₂ : A₂ →+* B₂}
    (hg₁ : g₁.Smooth) (hg₂ : g₂.Smooth) :
    (g₁.prodMap g₂).Smooth := by
  let _ : Algebra (A₁ × A₂) B₁ := (g₁.comp (RingHom.fst A₁ A₂)).toAlgebra
  let _ : Algebra (A₁ × A₂) A₂ := (RingHom.snd A₁ A₂).toAlgebra
  let _ : Algebra (A₁ × A₂) (B₁ × A₂) := Prod.algebra (A₁ × A₂) B₁ A₂
  -- First replace the left factor by the smooth map `g₁`, keeping the right factor fixed.
  have hleftBase : (g₁.comp (RingHom.fst A₁ A₂)).Smooth := by
    exact RingHom.Smooth.comp smooth_fst hg₁
  have hrightBase : (RingHom.snd A₁ A₂).Smooth := smooth_snd
  have hleftAlg : Algebra.Smooth (A₁ × A₂) (B₁ × A₂) := by
    have hB₁ : Algebra.Smooth (A₁ × A₂) B₁ := (RingHom.smooth_algebraMap).1 hleftBase
    have hA₂ : Algebra.Smooth (A₁ × A₂) A₂ := (RingHom.smooth_algebraMap).1 hrightBase
    exact (Algebra.smooth_prod_iff (R := A₁ × A₂) (S' := B₁) (S'' := A₂)).2 ⟨hB₁, hA₂⟩
  have hleft : (g₁.prodMap (RingHom.id A₂)).Smooth := by
    simpa [RingHom.smooth_algebraMap, RingHom.prodMap_def] using hleftAlg
  let _ : Algebra (B₁ × A₂) B₁ := (RingHom.fst B₁ A₂).toAlgebra
  let _ : Algebra (B₁ × A₂) B₂ := (g₂.comp (RingHom.snd B₁ A₂)).toAlgebra
  let _ : Algebra (B₁ × A₂) (B₁ × B₂) := Prod.algebra (B₁ × A₂) B₁ B₂
  -- Then replace the right factor by the smooth map `g₂`, now over the intermediate product.
  have hleftTop : (RingHom.fst B₁ A₂).Smooth := smooth_fst
  have hrightTop : (g₂.comp (RingHom.snd B₁ A₂)).Smooth := by
    exact RingHom.Smooth.comp smooth_snd hg₂
  have hrightAlg : Algebra.Smooth (B₁ × A₂) (B₁ × B₂) := by
    have hB₁ : Algebra.Smooth (B₁ × A₂) B₁ := (RingHom.smooth_algebraMap).1 hleftTop
    have hB₂ : Algebra.Smooth (B₁ × A₂) B₂ := (RingHom.smooth_algebraMap).1 hrightTop
    exact (Algebra.smooth_prod_iff (R := B₁ × A₂) (S' := B₁) (S'' := B₂)).2 ⟨hB₁, hB₂⟩
  have hright : ((RingHom.id B₁).prodMap g₂).Smooth := by
    simpa [RingHom.smooth_algebraMap, RingHom.prodMap_def] using hrightAlg
  -- The desired map is the composite of these two smooth product steps.
  have hcomp :
      (((RingHom.id B₁).prodMap g₂).comp (g₁.prodMap (RingHom.id A₂))).Smooth :=
    RingHom.Smooth.comp hleft hright
  simpa [RingHom.prodMap_def] using hcomp

/-- Helper for Lemma 16.8.2: the explicit `Type`-valued product cocone on the product index
category. -/
private noncomputable def type_prod_diagram
    {J₁ : Type v₁} [SmallCategory J₁] {J₂ : Type v₂} [SmallCategory J₂]
    {F₁ : J₁ ⥤ Type w₁} {F₂ : J₂ ⥤ Type w₂} :
    J₁ × J₂ ⥤ Type (max w₁ w₂) where
  obj j := F₁.obj j.1 × F₂.obj j.2
  map f x := (F₁.map f.1 x.1, F₂.map f.2 x.2)

/-- Helper for Lemma 16.8.2: the explicit `Type`-valued product cocone on the product index
category. -/
private noncomputable def type_prod_cocone
    {J₁ : Type v₁} [SmallCategory J₁] {J₂ : Type v₂} [SmallCategory J₂]
    {F₁ : J₁ ⥤ Type w₁} {F₂ : J₂ ⥤ Type w₂}
    (c₁ : Cocone F₁) (c₂ : Cocone F₂) :
    Cocone (type_prod_diagram (F₁ := F₁) (F₂ := F₂)) where
  pt := c₁.pt × c₂.pt
  ι :=
    { app := fun j x ↦ (c₁.ι.app j.1 x.1, c₂.ι.app j.2 x.2)
      naturality := by
        intro i j f
        -- The product cocone maps act coordinatewise, so naturality is coordinatewise tautological.
        ext x
        apply Prod.ext
        · simpa using congrFun (c₁.w f.1) x.1
        · simpa using congrFun (c₂.w f.2) x.2 }

/-- Helper for Lemma 16.8.2: a product of filtered colimits in `Type` is the filtered colimit of
the product diagram on the product index category. -/
private noncomputable def type_isColimit_prod_cocone_of_filtered
    {J₁ : Type v₁} [SmallCategory J₁] [IsFiltered J₁]
    {J₂ : Type v₂} [SmallCategory J₂] [IsFiltered J₂]
    {F₁ : J₁ ⥤ Type w₁} {F₂ : J₂ ⥤ Type w₂}
    {c₁ : Cocone F₁} {c₂ : Cocone F₂}
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    IsColimit (type_prod_cocone c₁ c₂) := by
  classical
  refine CategoryTheory.Limits.Types.FilteredColimit.isColimitOf'
    (F := type_prod_diagram (F₁ := F₁) (F₂ := F₂))
    (t := type_prod_cocone c₁ c₂) ?_ ?_
  · intro x
    -- Represent each coordinate at some stage, then use the pair of stages as one product stage.
    obtain ⟨j₁, x₁, hx₁⟩ := Types.jointly_surjective_of_isColimit hc₁ x.1
    obtain ⟨j₂, x₂, hx₂⟩ := Types.jointly_surjective_of_isColimit hc₂ x.2
    refine ⟨(j₁, j₂), (x₁, x₂), ?_⟩
    exact Prod.ext hx₁.symm hx₂.symm
  · intro j x y hxy
    -- Equality in the product cocone is equivalent to equality in each coordinate cocone.
    have h₁ : c₁.ι.app j.1 x.1 = c₁.ι.app j.1 y.1 := congrArg Prod.fst hxy
    have h₂ : c₂.ι.app j.2 x.2 = c₂.ι.app j.2 y.2 := congrArg Prod.snd hxy
    obtain ⟨k₁, f₁, hf₁⟩ :=
      (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'
        (F := F₁) (ht := hc₁) x.1 y.1).mp h₁
    obtain ⟨k₂, f₂, hf₂⟩ :=
      (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'
        (F := F₂) (ht := hc₂) x.2 y.2).mp h₂
    refine ⟨(k₁, k₂), (f₁, f₂), ?_⟩
    -- The product diagram maps coordinatewise, so the equalized coordinates combine directly.
    exact Prod.ext hf₁ hf₂

/-- Helper for Lemma 16.8.2: the filtered product diagram of commutative rings. -/
private noncomputable def commRing_prod_diagram
    {J₁ : Type v₁} [SmallCategory J₁] {J₂ : Type v₂} [SmallCategory J₂]
    (D₁ : J₁ ⥤ CommRingCat.{w}) (D₂ : J₂ ⥤ CommRingCat.{w}) :
    J₁ × J₂ ⥤ CommRingCat.{w} where
  obj j := CommRingCat.of (D₁.obj j.1 × D₂.obj j.2)
  map f := CommRingCat.ofHom ((D₁.map f.1).hom.prodMap (D₂.map f.2).hom)
  map_id _ := by
    -- The product transition map is the identity when both coordinates are identities.
    ext x <;> cases x <;> simp [RingHom.prodMap_def]
  map_comp f g := by
    -- Composition is computed coordinatewise for `RingHom.prodMap`.
    ext x <;> cases x <;> simp [RingHom.prodMap_def]

/-- Helper for Lemma 16.8.2: the product cocone legs satisfy the cocone naturality equation
coordinatewise. -/
private theorem commRing_prod_cocone_naturality
    {J₁ : Type v₁} [SmallCategory J₁] {J₂ : Type v₂} [SmallCategory J₂]
    {D₁ : J₁ ⥤ CommRingCat.{w}} {D₂ : J₂ ⥤ CommRingCat.{w}}
    (c₁ : Cocone D₁) (c₂ : Cocone D₂)
    {i j : J₁ × J₂} (f : i ⟶ j) :
    (commRing_prod_diagram D₁ D₂).map f ≫
        CommRingCat.ofHom
          (RingHom.prodMap (c₁.ι.app j.1).hom (c₂.ι.app j.2).hom) =
      CommRingCat.ofHom
        (RingHom.prodMap (c₁.ι.app i.1).hom (c₂.ι.app i.2).hom) := by
  -- The product cocone is controlled by the two factor cocones, so naturality reduces to the
  -- corresponding coordinatewise cocone equations.
  ext x
  · cases x with
    | mk x₁ x₂ =>
        change (c₁.ι.app j.1).hom ((D₁.map f.1).hom x₁) = (c₁.ι.app i.1).hom x₁
        have h₁ : (c₁.ι.app j.1).hom.comp (D₁.map f.1).hom = (c₁.ι.app i.1).hom := by
          rw [← CommRingCat.hom_comp]
          simpa using congrArg CommRingCat.Hom.hom (c₁.w f.1)
        simpa [RingHom.comp_apply] using congrArg (fun g : D₁.obj i.1 →+* c₁.pt => g x₁) h₁
  · cases x with
    | mk x₁ x₂ =>
        change (c₂.ι.app j.2).hom ((D₂.map f.2).hom x₂) = (c₂.ι.app i.2).hom x₂
        have h₂ : (c₂.ι.app j.2).hom.comp (D₂.map f.2).hom = (c₂.ι.app i.2).hom := by
          rw [← CommRingCat.hom_comp]
          simpa using congrArg CommRingCat.Hom.hom (c₂.w f.2)
        simpa [RingHom.comp_apply] using congrArg (fun g : D₂.obj i.2 →+* c₂.pt => g x₂) h₂

/-- Helper for Lemma 16.8.2: the explicit cocone on the product ring diagram. -/
private noncomputable def commRing_prod_cocone
    {J₁ : Type v₁} [SmallCategory J₁] {J₂ : Type v₂} [SmallCategory J₂]
    {D₁ : J₁ ⥤ CommRingCat.{w}} {D₂ : J₂ ⥤ CommRingCat.{w}}
    (c₁ : Cocone D₁) (c₂ : Cocone D₂) :
    Cocone (commRing_prod_diagram D₁ D₂) where
  pt := CommRingCat.of (c₁.pt × c₂.pt)
  ι :=
    { app := fun j ↦
        CommRingCat.ofHom
          (RingHom.prodMap (c₁.ι.app j.1).hom (c₂.ι.app j.2).hom)
      naturality := by
        intro i j f
        -- The chosen product cocone follows the source route exactly: rewrite each coordinate
        -- using the factor cocone equations and then repackage the pair.
        simpa using commRing_prod_cocone_naturality (c₁ := c₁) (c₂ := c₂) f }

/-- Helper for Lemma 16.8.2: forgetting the explicit `CommRingCat` product cocone yields exactly
the already-defined `Type`-valued product cocone. -/
private theorem forget_mapCocone_commRing_prod_cocone
    {J₁ : Type v₁} [SmallCategory J₁] {J₂ : Type v₂} [SmallCategory J₂]
    {D₁ : J₁ ⥤ CommRingCat.{w}} {D₂ : J₂ ⥤ CommRingCat.{w}}
    (c₁ : Cocone D₁) (c₂ : Cocone D₂) :
    (forget CommRingCat.{w}).mapCocone (commRing_prod_cocone c₁ c₂) =
      type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁) ((forget CommRingCat.{w}).mapCocone c₂) := by
  -- Both cocones have the same point and the same coordinatewise legs after forgetting to
  -- `Type`, so the remaining proof fields are propositionally irrelevant.
  cases c₁
  cases c₂
  rfl

/-- Helper for Lemma 16.8.2: any two points of the product `Type`-colimit come from one common
stage of the product index category. -/
private theorem type_prod_two_points_from_common_stage
    {J₁ : Type v₁} [SmallCategory J₁] [IsFiltered J₁]
    {J₂ : Type v₂} [SmallCategory J₂] [IsFiltered J₂]
    {D₁ : J₁ ⥤ CommRingCat.{w}} {D₂ : J₂ ⥤ CommRingCat.{w}}
    {c₁ : Cocone D₁} {c₂ : Cocone D₂}
    (hcType :
      IsColimit
        (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁) ((forget CommRingCat.{w}).mapCocone c₂)))
    (x y : c₁.pt × c₂.pt) :
    ∃ (j : J₁ × J₂) (a b : D₁.obj j.1 × D₂.obj j.2),
      (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁)
        ((forget CommRingCat.{w}).mapCocone c₂)).ι.app j a = x ∧
        (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁)
          ((forget CommRingCat.{w}).mapCocone c₂)).ι.app j b = y := by
  -- The explicit `Type`-colimit already knows how to place any two points in one filtered stage.
  obtain ⟨j, a, b, ha, hb⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂ hcType x y
  exact ⟨j, a, b, ha, hb⟩

/-- Helper for Lemma 16.8.2: the legs of the explicit product `Type`-cocone are exactly the
coordinatewise factor cocone maps. -/
private theorem type_prod_leg_apply
    {J₁ : Type v₁} [SmallCategory J₁] {J₂ : Type v₂} [SmallCategory J₂]
    {D₁ : J₁ ⥤ CommRingCat.{w}} {D₂ : J₂ ⥤ CommRingCat.{w}}
    (c₁ : Cocone D₁) (c₂ : Cocone D₂)
    (j : J₁ × J₂) (x : D₁.obj j.1 × D₂.obj j.2) :
    (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁)
      ((forget CommRingCat.{w}).mapCocone c₂)).ι.app j x =
      ((c₁.ι.app j.1) x.1, (c₂.ι.app j.2) x.2) :=
  rfl

/-- Helper for Lemma 16.8.2: the descended `Type`-level map out of the product filtered colimit
respects the ring operations, so it lifts to `CommRingCat`. -/
private noncomputable def commRing_prod_desc_fun
    {J₁ : Type v₁} [SmallCategory J₁] [IsFiltered J₁]
    {J₂ : Type v₂} [SmallCategory J₂] [IsFiltered J₂]
    {D₁ : J₁ ⥤ CommRingCat.{w}} {D₂ : J₂ ⥤ CommRingCat.{w}}
    {c₁ : Cocone D₁} {c₂ : Cocone D₂}
    (hcType :
      IsColimit
        (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁) ((forget CommRingCat.{w}).mapCocone c₂)))
    (s : Cocone (commRing_prod_diagram D₁ D₂)) :
    c₁.pt × c₂.pt → s.pt :=
  hcType.desc ((forget CommRingCat.{w}).mapCocone s)

/-- Helper for Lemma 16.8.2: the descended `Type`-level map agrees with each product-stage leg on
that stage. -/
private theorem commRing_prod_desc_fun_fac
    {J₁ : Type v₁} [SmallCategory J₁] [IsFiltered J₁]
    {J₂ : Type v₂} [SmallCategory J₂] [IsFiltered J₂]
    {D₁ : J₁ ⥤ CommRingCat.{w}} {D₂ : J₂ ⥤ CommRingCat.{w}}
    {c₁ : Cocone D₁} {c₂ : Cocone D₂}
    (hcType :
      IsColimit
        (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁) ((forget CommRingCat.{w}).mapCocone c₂)))
    (s : Cocone (commRing_prod_diagram D₁ D₂))
    (j : J₁ × J₂) (x : D₁.obj j.1 × D₂.obj j.2) :
    commRing_prod_desc_fun hcType s
        ((type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁)
          ((forget CommRingCat.{w}).mapCocone c₂)).ι.app j x) =
      (s.ι.app j) x := by
  -- The descended map is characterized by the colimit factorization property on each stage leg.
  exact congrFun (hcType.fac ((forget CommRingCat.{w}).mapCocone s) j) x

/-- Helper for Lemma 16.8.2: the descended `Type`-level map preserves zero. -/
private theorem commRing_prod_desc_fun_map_zero
    {J₁ : Type v₁} [SmallCategory J₁] [IsFiltered J₁]
    {J₂ : Type v₂} [SmallCategory J₂] [IsFiltered J₂]
    {D₁ : J₁ ⥤ CommRingCat.{w}} {D₂ : J₂ ⥤ CommRingCat.{w}}
    {c₁ : Cocone D₁} {c₂ : Cocone D₂}
    (hcType :
      IsColimit
        (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁) ((forget CommRingCat.{w}).mapCocone c₂)))
    (s : Cocone (commRing_prod_diagram D₁ D₂)) :
    commRing_prod_desc_fun hcType s 0 = 0 := by
  classical
  let j₀ : J₁ × J₂ := Classical.choice (CategoryTheory.IsFiltered.nonempty (C := J₁ × J₂))
  have hzero :
      (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁)
        ((forget CommRingCat.{w}).mapCocone c₂)).ι.app j₀ (0 : D₁.obj j₀.1 × D₂.obj j₀.2) =
        (0 : c₁.pt × c₂.pt) := by
    exact Prod.ext
      ((c₁.ι.app j₀.1).hom.map_zero)
      ((c₂.ι.app j₀.2).hom.map_zero)
  -- Any filtered stage contributes zero to the colimit, and the cocone leg is a ring hom.
  calc
    commRing_prod_desc_fun hcType s 0
        =
          commRing_prod_desc_fun hcType s
            ((type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁)
                ((forget CommRingCat.{w}).mapCocone c₂)).ι.app j₀
              (0 : D₁.obj j₀.1 × D₂.obj j₀.2)) := by
          rw [← hzero]
    _ = (s.ι.app j₀) (0 : D₁.obj j₀.1 × D₂.obj j₀.2) :=
      commRing_prod_desc_fun_fac hcType s j₀ (0 : D₁.obj j₀.1 × D₂.obj j₀.2)
    _ = 0 := by simpa using (s.ι.app j₀).hom.map_zero

/-- Helper for Lemma 16.8.2: the descended `Type`-level map preserves one. -/
private theorem commRing_prod_desc_fun_map_one
    {J₁ : Type v₁} [SmallCategory J₁] [IsFiltered J₁]
    {J₂ : Type v₂} [SmallCategory J₂] [IsFiltered J₂]
    {D₁ : J₁ ⥤ CommRingCat.{w}} {D₂ : J₂ ⥤ CommRingCat.{w}}
    {c₁ : Cocone D₁} {c₂ : Cocone D₂}
    (hcType :
      IsColimit
        (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁) ((forget CommRingCat.{w}).mapCocone c₂)))
    (s : Cocone (commRing_prod_diagram D₁ D₂)) :
    commRing_prod_desc_fun hcType s 1 = 1 := by
  classical
  let j₀ : J₁ × J₂ := Classical.choice (CategoryTheory.IsFiltered.nonempty (C := J₁ × J₂))
  have hone :
      (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁)
        ((forget CommRingCat.{w}).mapCocone c₂)).ι.app j₀ (1 : D₁.obj j₀.1 × D₂.obj j₀.2) =
        (1 : c₁.pt × c₂.pt) := by
    exact Prod.ext
      ((c₁.ι.app j₀.1).hom.map_one)
      ((c₂.ι.app j₀.2).hom.map_one)
  -- The same stagewise factorization argument works for the unit element.
  calc
    commRing_prod_desc_fun hcType s 1
        =
          commRing_prod_desc_fun hcType s
            ((type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁)
                ((forget CommRingCat.{w}).mapCocone c₂)).ι.app j₀
              (1 : D₁.obj j₀.1 × D₂.obj j₀.2)) := by
          rw [← hone]
    _ = (s.ι.app j₀) (1 : D₁.obj j₀.1 × D₂.obj j₀.2) :=
      commRing_prod_desc_fun_fac hcType s j₀ (1 : D₁.obj j₀.1 × D₂.obj j₀.2)
    _ = 1 := by simpa using (s.ι.app j₀).hom.map_one

/-- Helper for Lemma 16.8.2: the descended `Type`-level map preserves addition. -/
private theorem commRing_prod_desc_fun_map_add
    {J₁ : Type v₁} [SmallCategory J₁] [IsFiltered J₁]
    {J₂ : Type v₂} [SmallCategory J₂] [IsFiltered J₂]
    {D₁ : J₁ ⥤ CommRingCat.{w}} {D₂ : J₂ ⥤ CommRingCat.{w}}
    {c₁ : Cocone D₁} {c₂ : Cocone D₂}
    (hcType :
      IsColimit
        (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁) ((forget CommRingCat.{w}).mapCocone c₂)))
    (s : Cocone (commRing_prod_diagram D₁ D₂))
    (x y : c₁.pt × c₂.pt) :
    commRing_prod_desc_fun hcType s (x + y) =
      commRing_prod_desc_fun hcType s x + commRing_prod_desc_fun hcType s y := by
  -- Move both inputs to one filtered stage so the stage ring-hom laws control the colimit map.
  obtain ⟨j, a, b, ha, hb⟩ := type_prod_two_points_from_common_stage hcType x y
  have hax :
      commRing_prod_desc_fun hcType s x = (s.ι.app j) a := by
    simpa [ha] using commRing_prod_desc_fun_fac hcType s j a
  have hby :
      commRing_prod_desc_fun hcType s y = (s.ι.app j) b := by
    simpa [hb] using commRing_prod_desc_fun_fac hcType s j b
  have hxy :
      (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁)
        ((forget CommRingCat.{w}).mapCocone c₂)).ι.app j (a + b) =
        x + y := by
    rcases a with ⟨a₁, a₂⟩
    rcases b with ⟨b₁, b₂⟩
    -- Re-express the two colimit points with their chosen stage representatives coordinatewise.
    rw [← ha, ← hb]
    exact Prod.ext
      ((c₁.ι.app j.1).hom.map_add a₁ b₁)
      ((c₂.ι.app j.2).hom.map_add a₂ b₂)
  -- After rewriting the colimit points back to the chosen stage representatives, addition is
  -- stagewise.
  rw [← hxy]
  rw [commRing_prod_desc_fun_fac]
  have hmap : (s.ι.app j).hom (a + b) = (s.ι.app j).hom a + (s.ι.app j).hom b :=
    (s.ι.app j).hom.map_add a b
  simpa [hax, hby] using hmap

/-- Helper for Lemma 16.8.2: the descended `Type`-level map preserves multiplication. -/
private theorem commRing_prod_desc_fun_map_mul
    {J₁ : Type v₁} [SmallCategory J₁] [IsFiltered J₁]
    {J₂ : Type v₂} [SmallCategory J₂] [IsFiltered J₂]
    {D₁ : J₁ ⥤ CommRingCat.{w}} {D₂ : J₂ ⥤ CommRingCat.{w}}
    {c₁ : Cocone D₁} {c₂ : Cocone D₂}
    (hcType :
      IsColimit
        (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁) ((forget CommRingCat.{w}).mapCocone c₂)))
    (s : Cocone (commRing_prod_diagram D₁ D₂))
    (x y : c₁.pt × c₂.pt) :
    commRing_prod_desc_fun hcType s (x * y) =
      commRing_prod_desc_fun hcType s x * commRing_prod_desc_fun hcType s y := by
  -- As for addition, move to a common filtered stage and use multiplicativity there.
  obtain ⟨j, a, b, ha, hb⟩ := type_prod_two_points_from_common_stage hcType x y
  have hax :
      commRing_prod_desc_fun hcType s x = (s.ι.app j) a := by
    simpa [ha] using commRing_prod_desc_fun_fac hcType s j a
  have hby :
      commRing_prod_desc_fun hcType s y = (s.ι.app j) b := by
    simpa [hb] using commRing_prod_desc_fun_fac hcType s j b
  have hxy :
      (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁)
        ((forget CommRingCat.{w}).mapCocone c₂)).ι.app j (a * b) =
        x * y := by
    rcases a with ⟨a₁, a₂⟩
    rcases b with ⟨b₁, b₂⟩
    -- The multiplicative case uses the same coordinatewise representative rewrite.
    rw [← ha, ← hb]
    exact Prod.ext
      ((c₁.ι.app j.1).hom.map_mul a₁ b₁)
      ((c₂.ι.app j.2).hom.map_mul a₂ b₂)
  -- The descended function inherits multiplicativity from the stage ring hom.
  rw [← hxy]
  rw [commRing_prod_desc_fun_fac]
  have hmap : (s.ι.app j).hom (a * b) = (s.ι.app j).hom a * (s.ι.app j).hom b :=
    (s.ι.app j).hom.map_mul a b
  simpa [hax, hby] using hmap

/-- Helper for Lemma 16.8.2: the descended `Type`-level map is a ring hom. -/
private noncomputable def commRing_prod_desc_hom
    {J₁ : Type v₁} [SmallCategory J₁] [IsFiltered J₁]
    {J₂ : Type v₂} [SmallCategory J₂] [IsFiltered J₂]
    {D₁ : J₁ ⥤ CommRingCat.{w}} {D₂ : J₂ ⥤ CommRingCat.{w}}
    {c₁ : Cocone D₁} {c₂ : Cocone D₂}
    (hcType :
      IsColimit
        (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁) ((forget CommRingCat.{w}).mapCocone c₂)))
    (s : Cocone (commRing_prod_diagram D₁ D₂)) :
    (c₁.pt × c₂.pt) →+* s.pt :=
  { toFun := commRing_prod_desc_fun hcType s
    map_zero' := commRing_prod_desc_fun_map_zero hcType s
    map_one' := commRing_prod_desc_fun_map_one hcType s
    map_add' := commRing_prod_desc_fun_map_add hcType s
    map_mul' := commRing_prod_desc_fun_map_mul hcType s }

/-- Helper for Lemma 16.8.2: the descended `Type`-level map out of the product filtered colimit
respects the ring operations, so it lifts to `CommRingCat`. -/
private noncomputable def commRing_prod_desc_lift
    {J₁ : Type v₁} [SmallCategory J₁] [IsFiltered J₁]
    {J₂ : Type v₂} [SmallCategory J₂] [IsFiltered J₂]
    {D₁ : J₁ ⥤ CommRingCat.{w}} {D₂ : J₂ ⥤ CommRingCat.{w}}
    {c₁ : Cocone D₁} {c₂ : Cocone D₂}
    (hcType :
      IsColimit
        (type_prod_cocone ((forget CommRingCat.{w}).mapCocone c₁) ((forget CommRingCat.{w}).mapCocone c₂)))
    (s : Cocone (commRing_prod_diagram D₁ D₂)) :
    CommRingCat.of.{w} (c₁.pt × c₂.pt) ⟶ s.pt :=
  CommRingCat.ofHom (commRing_prod_desc_hom hcType s)

/-- Helper for Chap16 Lemma 16 8 2: the forgetful functor from commutative rings to types sends
filtered colimit cocones to colimit cocones. -/
private noncomputable def forget_mapCocone_isColimit_of_filtered
    {J : Type v₁} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ CommRingCat.{w}} {c : Cocone D}
    (hc : IsColimit c) :
    IsColimit ((forget CommRingCat.{w}).mapCocone c) := by
  -- TODO: replan the universe bookkeeping for `forget CommRingCat`: the generic helper should
  -- obtain the required `PreservesColimit` instance from filtered-colimit preservation without
  -- over-specializing the index universe.
  sorry

/-- Helper for Lemma 16.8.2: the explicit product cocone in `CommRingCat` is colimiting because
filtered colimits of commutative rings are created by the underlying `Type` diagram. -/
private noncomputable def commRing_isColimit_prod_cocone_of_filtered
    {J₁ : Type v₁} [SmallCategory J₁] [IsFiltered J₁]
    {J₂ : Type v₂} [SmallCategory J₂] [IsFiltered J₂]
    {D₁ : J₁ ⥤ CommRingCat.{w}} {D₂ : J₂ ⥤ CommRingCat.{w}}
    {c₁ : Cocone D₁} {c₂ : Cocone D₂}
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    IsColimit (commRing_prod_cocone c₁ c₂) := by
  -- TODO: replan the faithful-descent comparison between the descended ring hom and the forgotten
  -- `Type`-level colimit desc map once the universe-polymorphic forgetful-preservation bridge is
  -- stabilized.
  sorry

/-- Helper for Lemma 16.8.2: the lifted product ring is canonically equivalent to the product of
the lifted factors. -/
private noncomputable def ulift_prod_ringEquiv
    {A : Type u₁} {B : Type u₂} [CommRing A] [CommRing B] :
    ULift.{max u₁ u₂} (A × B) ≃+* (ULift.{max u₁ u₂} A × ULift.{max u₁ u₂} B) :=
  (ULift.ringEquiv : ULift.{max u₁ u₂} (A × B) ≃+* (A × B)).trans
    (RingEquiv.prodCongr
      (ULift.ringEquiv.symm : A ≃+* ULift.{max u₁ u₂} A)
      (ULift.ringEquiv.symm : B ≃+* ULift.{max u₁ u₂} B))

/-- Helper for Lemma 16.8.2: a ring map induces the canonical map on the corresponding `ULift`s. -/
private noncomputable def uliftMap₁
    {A : Type u₁} {B : Type u₁} [CommRing A] [CommRing B] (g : A →+* B) :
    ULift.{max u₁ u₂} A →+* ULift.{max u₁ u₂} B :=
  ((ULift.ringEquiv.symm : B ≃+* ULift.{max u₁ u₂} B).toRingHom).comp
    (g.comp ((ULift.ringEquiv : ULift.{max u₁ u₂} A ≃+* A).toRingHom))

/-- Helper for Lemma 16.8.2: the second factor uses the same common lift universe as the first. -/
private noncomputable def uliftMap₂
    {A : Type u₂} {B : Type u₂} [CommRing A] [CommRing B] (g : A →+* B) :
    ULift.{max u₁ u₂} A →+* ULift.{max u₁ u₂} B :=
  ((ULift.ringEquiv.symm : B ≃+* ULift.{max u₁ u₂} B).toRingHom).comp
    (g.comp ((ULift.ringEquiv : ULift.{max u₁ u₂} A ≃+* A).toRingHom))

/-- Helper for Lemma 16.8.2: the product map also has a canonical common-universe lift. -/
private noncomputable def uliftProdMap
    {A₁ : Type u₁} {B₁ : Type u₁} {A₂ : Type u₂} {B₂ : Type u₂}
    [CommRing A₁] [CommRing B₁] [CommRing A₂] [CommRing B₂]
    (g₁ : A₁ →+* B₁) (g₂ : A₂ →+* B₂) :
    ULift.{max u₁ u₂} (A₁ × A₂) →+* ULift.{max u₁ u₂} (B₁ × B₂) :=
  ((ULift.ringEquiv.symm : (B₁ × B₂) ≃+* ULift.{max u₁ u₂} (B₁ × B₂)).toRingHom).comp
    ((g₁.prodMap g₂).comp ((ULift.ringEquiv : ULift.{max u₁ u₂} (A₁ × A₂) ≃+* (A₁ × A₂)).toRingHom))

/-- Helper for Lemma 16.8.2: the factorwise lifted maps combine to a product map in the common
lift universe. -/
private noncomputable def uliftFactorProdMap
    {A₁ : Type u₁} {B₁ : Type u₁} {A₂ : Type u₂} {B₂ : Type u₂}
    [CommRing A₁] [CommRing B₁] [CommRing A₂] [CommRing B₂]
    (g₁ : A₁ →+* B₁) (g₂ : A₂ →+* B₂) :
    (ULift.{max u₁ u₂} A₁ × ULift.{max u₁ u₂} A₂) →+*
      (ULift.{max u₁ u₂} B₁ × ULift.{max u₁ u₂} B₂) :=
  (uliftMap₁ g₁).prodMap (uliftMap₂ g₂)

/-- Helper for Lemma 16.8.2: the canonical `ULift`-product equivalences identify the lifted
product map with the product of the lifted factor maps. -/
private theorem ulift_prod_ringEquiv_comp_uliftMap
    {A₁ : Type u₁} {B₁ : Type u₁} {A₂ : Type u₂} {B₂ : Type u₂}
    [CommRing A₁] [CommRing B₁] [CommRing A₂] [CommRing B₂]
    (g₁ : A₁ →+* B₁) (g₂ : A₂ →+* B₂) :
    (ulift_prod_ringEquiv (A := B₁) (B := B₂)).toRingHom.comp
        (uliftProdMap g₁ g₂) =
      (uliftFactorProdMap g₁ g₂).comp
        (ulift_prod_ringEquiv (A := A₁) (B := A₂)).toRingHom := by
  -- Both sides are the canonical map sending a lifted pair to the pair of lifted images.
  exact RingHom.ext fun x ↦ rfl

/-- Helper for Lemma 16.8.2: the wrapper `IsFilteredColimitOfSmooth` uses `uliftMap` for the
hidden `ULift` arrow after unfolding the chosen algebra structure. -/
private theorem uliftMap₁_eq_algebraMap
    {A : Type u₁} {B : Type u₁} [CommRing A] [CommRing B] (g : A →+* B) :
    let _ : Algebra A B := g.toAlgebra
    let _ : Algebra A (ULift.{max u₁ u₂} B) := ULift.algebra
    let _ : Algebra (ULift.{max u₁ u₂} A) (ULift.{max u₁ u₂} B) :=
      ULift.algebra' A (ULift.{max u₁ u₂} B)
    algebraMap (ULift.{max u₁ u₂} A) (ULift.{max u₁ u₂} B) = uliftMap₁ g := by
  rfl

/-- Helper for Lemma 16.8.2: the second factor satisfies the same `algebraMap = uliftMap`
identity. -/
private theorem uliftMap₂_eq_algebraMap
    {A : Type u₂} {B : Type u₂} [CommRing A] [CommRing B] (g : A →+* B) :
    let _ : Algebra A B := g.toAlgebra
    let _ : Algebra A (ULift.{max u₁ u₂} B) := ULift.algebra
    let _ : Algebra (ULift.{max u₁ u₂} A) (ULift.{max u₁ u₂} B) :=
      ULift.algebra' A (ULift.{max u₁ u₂} B)
    algebraMap (ULift.{max u₁ u₂} A) (ULift.{max u₁ u₂} B) = uliftMap₂ g := by
  rfl

/-- Helper for Lemma 16.8.2: the product owner also unfolds to the common-universe lifted product
map. -/
private theorem uliftProdMap_eq_algebraMap
    {A₁ : Type u₁} {B₁ : Type u₁} {A₂ : Type u₂} {B₂ : Type u₂}
    [CommRing A₁] [CommRing B₁] [CommRing A₂] [CommRing B₂]
    (g₁ : A₁ →+* B₁) (g₂ : A₂ →+* B₂) :
    let _ : Algebra (A₁ × A₂) (B₁ × B₂) := (g₁.prodMap g₂).toAlgebra
    let _ : Algebra (A₁ × A₂) (ULift.{max u₁ u₂} (B₁ × B₂)) := ULift.algebra
    let _ : Algebra (ULift.{max u₁ u₂} (A₁ × A₂)) (ULift.{max u₁ u₂} (B₁ × B₂)) :=
      ULift.algebra' (A₁ × A₂) (ULift.{max u₁ u₂} (B₁ × B₂))
    algebraMap (ULift.{max u₁ u₂} (A₁ × A₂)) (ULift.{max u₁ u₂} (B₁ × B₂)) =
      uliftProdMap g₁ g₂ := by
  rfl

/-- Helper for Lemma 16.8.2: the hidden `ULift` arrow for a product ring map is isomorphic to the
product of the two hidden factor arrows. -/
private noncomputable def ulift_prod_arrow_iso
    (g₁ : R₁ →+* Λ₁) (g₂ : R₂ →+* Λ₂) :
    CategoryTheory.Arrow.mk
        (CommRingCat.ofHom (uliftProdMap g₁ g₂)) ≅
      CategoryTheory.Arrow.mk
        (CommRingCat.ofHom (uliftFactorProdMap g₁ g₂)) :=
  CategoryTheory.Arrow.isoMk
    (RingEquiv.toCommRingCatIso (ulift_prod_ringEquiv (A := R₁) (B := R₂)))
    (RingEquiv.toCommRingCatIso (ulift_prod_ringEquiv (A := Λ₁) (B := Λ₂)))
    (by
      -- This packages the transport as a single arrow isomorphism so the main theorem can rewrite
      -- the target owner in one step instead of performing inline universe-sensitive coercions.
      simpa using congrArg CommRingCat.ofHom
        (ulift_prod_ringEquiv_comp_uliftMap g₁ g₂))

/-- Helper for Lemma 16.8.2: the small `ULift` of a `u₁`-sized ring identifies with the common
lift universe used in the product proof. -/
private noncomputable def ulift₁ToCommonRingEquiv
    {A : Type u₁} [CommRing A] :
    ULift.{u₁} A ≃+* ULift.{max u₁ u₂} A :=
  (ULift.ringEquiv : ULift.{u₁} A ≃+* A).trans
    (ULift.ringEquiv.symm : A ≃+* ULift.{max u₁ u₂} A)

/-- Helper for Lemma 16.8.2: the small `ULift` of a `u₂`-sized ring identifies with the same
common lift universe. -/
private noncomputable def ulift₂ToCommonRingEquiv
    {A : Type u₂} [CommRing A] :
    ULift.{u₂} A ≃+* ULift.{max u₁ u₂} A :=
  (ULift.ringEquiv : ULift.{u₂} A ≃+* A).trans
    (ULift.ringEquiv.symm : A ≃+* ULift.{max u₁ u₂} A)

/-- Helper for Lemma 16.8.2: transporting the first-factor hidden `ULift` arrow to the common
universe commutes with the canonical lifted map. -/
private theorem uliftMap₁_commonUniverse_commutes
    {A : Type u₁} {B : Type u₁} [CommRing A] [CommRing B] (g : A →+* B) :
    let _ : Algebra A B := g.toAlgebra
    let _ : Algebra A (ULift.{u₁} B) := ULift.algebra
    let _ : Algebra (ULift.{u₁} A) (ULift.{u₁} B) := ULift.algebra' A (ULift.{u₁} B)
    CommRingCat.ofHom (ulift₁ToCommonRingEquiv (A := A)).toRingHom ≫
        CommRingCat.ofHom (uliftMap₁ g) =
      CommRingCat.ofHom (algebraMap (ULift.{u₁} A) (ULift.{u₁} B)) ≫
        CommRingCat.ofHom (ulift₁ToCommonRingEquiv (A := B)).toRingHom := by
  -- Both composites send a lifted element to the same lifted image under `g`.
  dsimp [uliftMap₁, ulift₁ToCommonRingEquiv]
  rfl

/-- Helper for Lemma 16.8.2: the second-factor hidden `ULift` arrow satisfies the same common
universe compatibility square. -/
private theorem uliftMap₂_commonUniverse_commutes
    {A : Type u₂} {B : Type u₂} [CommRing A] [CommRing B] (g : A →+* B) :
    let _ : Algebra A B := g.toAlgebra
    let _ : Algebra A (ULift.{u₂} B) := ULift.algebra
    let _ : Algebra (ULift.{u₂} A) (ULift.{u₂} B) := ULift.algebra' A (ULift.{u₂} B)
    CommRingCat.ofHom (ulift₂ToCommonRingEquiv (A := A)).toRingHom ≫
        CommRingCat.ofHom (uliftMap₂ g) =
      CommRingCat.ofHom (algebraMap (ULift.{u₂} A) (ULift.{u₂} B)) ≫
        CommRingCat.ofHom (ulift₂ToCommonRingEquiv (A := B)).toRingHom := by
  -- The second factor uses the identical coordinatewise transport argument.
  dsimp [uliftMap₂, ulift₂ToCommonRingEquiv]
  rfl

/-- Helper for Lemma 16.8.2: smooth ring maps are invariant under isomorphisms of source and
target. -/
private theorem smooth_respectsIso :
    RingHom.RespectsIso @RingHom.Smooth := by
  refine RingHom.StableUnderComposition.respectsIso RingHom.Smooth.stableUnderComposition ?_
  intro A B _ _ e
  exact RingHom.Smooth.of_bijective e.bijective

/-- Helper for Lemma 16.8.2: the source `ULift` presentation of the first factor is canonically
identified with the common-universe lifted arrow used in the product proof. -/
private noncomputable def uliftMap₁ArrowIsoCommonUniverse
    {A : Type u₁} {B : Type u₁} [CommRing A] [CommRing B] (g : A →+* B) :
    let _ : Algebra A B := g.toAlgebra
    let _ : Algebra A (ULift.{u₁} B) := ULift.algebra
    let _ : Algebra (ULift.{u₁} A) (ULift.{u₁} B) := ULift.algebra' A (ULift.{u₁} B)
    let _ : Algebra A (ULift.{max u₁ u₂} B) := ULift.algebra
    let _ : Algebra (ULift.{max u₁ u₂} A) (ULift.{max u₁ u₂} B) :=
      ULift.algebra' A (ULift.{max u₁ u₂} B)
    CategoryTheory.Arrow.mk
        (CommRingCat.ofHom (algebraMap (ULift.{u₁} A) (ULift.{u₁} B))) ≅
      CategoryTheory.Arrow.mk
        (CommRingCat.ofHom (uliftMap₁ g)) :=
  CategoryTheory.Arrow.isoMk
    (RingEquiv.toCommRingCatIso (ulift₁ToCommonRingEquiv (A := A)))
    (RingEquiv.toCommRingCatIso (ulift₁ToCommonRingEquiv (A := B)))
    (uliftMap₁_commonUniverse_commutes (g := g))

/-- Helper for Lemma 16.8.2: the second factor has the same common-universe arrow isomorphism as
the first. -/
private noncomputable def uliftMap₂ArrowIsoCommonUniverse
    {A : Type u₂} {B : Type u₂} [CommRing A] [CommRing B] (g : A →+* B) :
    let _ : Algebra A B := g.toAlgebra
    let _ : Algebra A (ULift.{u₂} B) := ULift.algebra
    let _ : Algebra (ULift.{u₂} A) (ULift.{u₂} B) := ULift.algebra' A (ULift.{u₂} B)
    let _ : Algebra A (ULift.{max u₁ u₂} B) := ULift.algebra
    let _ : Algebra (ULift.{max u₁ u₂} A) (ULift.{max u₁ u₂} B) :=
      ULift.algebra' A (ULift.{max u₁ u₂} B)
    CategoryTheory.Arrow.mk
        (CommRingCat.ofHom (algebraMap (ULift.{u₂} A) (ULift.{u₂} B))) ≅
      CategoryTheory.Arrow.mk
        (CommRingCat.ofHom (uliftMap₂ g)) :=
  CategoryTheory.Arrow.isoMk
    (RingEquiv.toCommRingCatIso (ulift₂ToCommonRingEquiv (A := A)))
    (RingEquiv.toCommRingCatIso (ulift₂ToCommonRingEquiv (A := B)))
    (uliftMap₂_commonUniverse_commutes (g := g))

/-- Helper for Lemma 16.8.2: the first factor PT witness transports to the common `ULift`
universe used for the product construction. -/
private theorem isFilteredColimitOfSmooth_uliftMap₁
    {A : Type u₁} {B : Type u₁} [CommRing A] [CommRing B] (g : A →+* B)
    (hg : g.IsFilteredColimitOfSmooth) :
    CategoryTheory.MorphismProperty.ind.{u₁, max u₁ u₂, (max u₁ u₂) + 1}
      (RingHom.toMorphismProperty RingHom.Smooth)
      (CommRingCat.ofHom (uliftMap₁.{u₁, u₂} g)) := by
  -- TODO: replan the first-factor universe transport. The stable next step is to extract the
  -- small-universe `ind` witness from `hg`, then rebuild it in the common universe by an explicit
  -- reindexed diagram/cocone transport, rather than trying to coerce the source arrow directly.
  sorry

/-- Helper for Lemma 16.8.2: the second factor PT witness transports to the same common `ULift`
universe as the first. -/
private theorem isFilteredColimitOfSmooth_uliftMap₂
    {A : Type u₂} {B : Type u₂} [CommRing A] [CommRing B] (g : A →+* B)
    (hg : g.IsFilteredColimitOfSmooth) :
    CategoryTheory.MorphismProperty.ind.{u₂, max u₁ u₂, (max u₁ u₂) + 1}
      (RingHom.toMorphismProperty RingHom.Smooth)
      (CommRingCat.ofHom (uliftMap₂.{u₁, u₂} g)) := by
  -- TODO: replan the second-factor universe transport with the same explicit witness-rebuild
  -- pattern needed for `isFilteredColimitOfSmooth_uliftMap₁`.
  sorry

/-- Helper for Chap16 Lemma 16 8 2: product presentations of the two lifted factors assemble into
one presentation of the lifted product map. -/
private theorem isFilteredColimitOfSmooth_uliftFactorProdMap
    {A₁ : Type u₁} {B₁ : Type u₁} {A₂ : Type u₂} {B₂ : Type u₂}
    [CommRing A₁] [CommRing B₁] [CommRing A₂] [CommRing B₂]
    (g₁ : A₁ →+* B₁) (g₂ : A₂ →+* B₂)
    (hg₁ :
      CategoryTheory.MorphismProperty.ind.{u₁, max u₁ u₂, (max u₁ u₂) + 1}
        (RingHom.toMorphismProperty RingHom.Smooth)
        (CommRingCat.ofHom (uliftMap₁.{u₁, u₂} g₁)))
    (hg₂ :
      CategoryTheory.MorphismProperty.ind.{u₂, max u₁ u₂, (max u₁ u₂) + 1}
        (RingHom.toMorphismProperty RingHom.Smooth)
        (CommRingCat.ofHom (uliftMap₂.{u₁, u₂} g₂))) :
    CategoryTheory.MorphismProperty.ind.{max u₁ u₂, max u₁ u₂, (max u₁ u₂) + 1}
      (RingHom.toMorphismProperty RingHom.Smooth)
      (CommRingCat.ofHom (uliftFactorProdMap.{u₁, u₂} g₁ g₂)) := by
  rcases hg₁ with ⟨J₁, _, _, D₁, t₁, s₁, hs₁, hstage₁⟩
  rcases hg₂ with ⟨J₂, _, _, D₂, t₂, s₂, hs₂, hstage₂⟩
  let c₁ : Cocone D₁ := Cocone.mk _ s₁
  let c₂ : Cocone D₂ := Cocone.mk _ s₂
  refine ⟨J₁ × J₂, inferInstance, inferInstance, commRing_prod_diagram D₁ D₂, ?_, ?_, ?_, ?_⟩
  · refine
      { app := fun j ↦
          CommRingCat.ofHom
            (RingHom.prodMap (t₁.app j.1).hom (t₂.app j.2).hom)
        naturality := by
          intro i j f
          -- Proof comment: the source legs commute with the transition maps coordinatewise.
          ext x
          cases x with
          | mk x₁ x₂ =>
              apply Prod.ext
              · have h₁ :
                    (t₁.app j.1).hom = (D₁.map f.1).hom.comp (t₁.app i.1).hom := by
                  simpa [CommRingCat.hom_comp] using congrArg CommRingCat.Hom.hom
                    (t₁.naturality f.1)
                simpa [RingHom.comp_apply, RingHom.prodMap_def] using congrArg
                  (fun h : ULift.{max u₁ u₂} A₁ →+* D₁.obj j.1 => h x₁) h₁
              · have h₂ :
                    (t₂.app j.2).hom = (D₂.map f.2).hom.comp (t₂.app i.2).hom := by
                  simpa [CommRingCat.hom_comp] using congrArg CommRingCat.Hom.hom
                    (t₂.naturality f.2)
                simpa [RingHom.comp_apply, RingHom.prodMap_def] using congrArg
                  (fun h : ULift.{max u₁ u₂} A₂ →+* D₂.obj j.2 => h x₂) h₂ }
  · exact (commRing_prod_cocone c₁ c₂).ι
  · -- Proof comment: the product cocone is colimiting because filtered colimits in
    -- `CommRingCat` are created by the forgetful functor to `Type`.
    simpa [c₁, c₂] using commRing_isColimit_prod_cocone_of_filtered hs₁ hs₂
  · intro j
    refine ⟨?_, ?_⟩
    · -- Proof comment: each product stage map is smooth because both factor stage maps are
      -- smooth and smoothness is preserved under finite products.
      have hsmooth₁ : ((t₁.app j.1).hom).Smooth := by
        simpa [RingHom.toMorphismProperty] using (hstage₁ j.1).1
      have hsmooth₂ : ((t₂.app j.2).hom).Smooth := by
        simpa [RingHom.toMorphismProperty] using (hstage₂ j.2).1
      simpa [uliftFactorProdMap] using smooth_prodMap hsmooth₁ hsmooth₂
    · -- Proof comment: the product factorization is obtained by combining the coordinatewise
      -- factorization equations from the two input presentations.
      ext x
      cases x with
      | mk x₁ x₂ =>
          apply Prod.ext
          · have hfac₁ :
                (s₁.app j.1).hom.comp (t₁.app j.1).hom = uliftMap₁ g₁ := by
              rw [← CommRingCat.hom_comp]
              simpa using congrArg CommRingCat.Hom.hom (hstage₁ j.1).2
            simpa [uliftFactorProdMap, RingHom.prodMap_def, RingHom.comp_apply] using congrArg
              (fun h : ULift.{max u₁ u₂} A₁ →+* ULift.{max u₁ u₂} B₁ => h x₁) hfac₁
          · have hfac₂ :
                (s₂.app j.2).hom.comp (t₂.app j.2).hom = uliftMap₂ g₂ := by
              rw [← CommRingCat.hom_comp]
              simpa using congrArg CommRingCat.Hom.hom (hstage₂ j.2).2
            simpa [uliftFactorProdMap, RingHom.prodMap_def, RingHom.comp_apply] using congrArg
              (fun h : ULift.{max u₁ u₂} A₂ →+* ULift.{max u₁ u₂} B₂ => h x₂) hfac₂

-- Proof sketch: choose filtered diagrams of smooth algebras presenting `f₁` and `f₂`. Their
-- product diagram is again filtered, each stage map to the product is smooth because smoothness is
-- preserved by finite products, and the product cocone presents `f₁.prodMap f₂` as the
-- corresponding filtered colimit.
/-- Lemma 16.8.2: if two ring maps satisfy PT, i.e. each is a filtered colimit of smooth algebras
over its source, then their product map also satisfies PT. -/
-- TODO: the factor `ULift` transports and the product-cocone descent are now available; the
-- remaining work is to extract the two factor presentations and assemble the explicit product
-- filtered colimit witness.
theorem prodMap
    {f₁ : R₁ →+* Λ₁} {f₂ : R₂ →+* Λ₂}
    (hf₁ : f₁.IsFilteredColimitOfSmooth)
    (hf₂ : f₂.IsFilteredColimitOfSmooth) :
    (f₁.prodMap f₂).IsFilteredColimitOfSmooth := by
  -- Route correction: the direct `ind_iff_exists` projection plan does not apply to product ring
  -- maps, because a finitely presentable test map into the product source does not canonically
  -- project to test maps out of each factor source. The stable route is still to combine the two
  -- raw `ind` witnesses after transporting them to a common `ULift` universe.
  let P :=
    CategoryTheory.MorphismProperty.ind.{max u₁ u₂, max u₁ u₂, (max u₁ u₂) + 1}
      (RingHom.toMorphismProperty RingHom.Smooth)
  have h₁ := isFilteredColimitOfSmooth_uliftMap₁ (g := f₁) hf₁
  have h₂ := isFilteredColimitOfSmooth_uliftMap₂ (g := f₂) hf₂
  have hfactor :
      P (CommRingCat.ofHom (uliftFactorProdMap.{u₁, u₂} f₁ f₂)) :=
    isFilteredColimitOfSmooth_uliftFactorProdMap f₁ f₂ h₁ h₂
  have hprod :
      P (CommRingCat.ofHom (uliftProdMap.{u₁, u₂} f₁ f₂)) := by
    -- Proof comment: after building the product witness for the factorwise lift, descend along
    -- the canonical arrow isomorphism identifying it with the lifted product map.
    exact (P.arrow_mk_iso_iff (ulift_prod_arrow_iso f₁ f₂)).mpr hfactor
  -- Proof comment: fold the hidden owner back into the source-facing wrapper.
  simpa [RingHom.IsFilteredColimitOfSmooth, uliftProdMap_eq_algebraMap] using hprod

end IsFilteredColimitOfSmooth

end

end RingHom
