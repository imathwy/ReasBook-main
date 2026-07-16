import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_proof.stacks_project.Chap07.Lemma_7_26_4.Index
import stacks_proof.stacks_project.Chap07.Lemma_7_26_6
import stacks_proof.stacks_project.Chap08.Lemma_8_3_7
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Definition_8_11_1
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part06

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
attribute [local irreducible] Pseudofunctor.mapComp'

/-- On one secondary-cover refinement, the local-overlap component comparison satisfies the
descent square with the source and target secondary descent data. -/
theorem local_overlap_secondary_descent_square_at_refinement
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map (𝟙 L.Y).op.toLoc).toFunctor.map
        ((local_overlap_secondary_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ L).hom) ≫
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom L.f (𝟙 L.Y) (𝟙 L.Y) =
    (local_overlap_source_secondary_descent_data
      (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom L.f (𝟙 L.Y) (𝟙 L.Y) ≫
      ((J.pseudofunctorOver (Type (max u v))).map (𝟙 L.Y).op.toLoc).toFunctor.map
        ((local_overlap_secondary_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ L).hom) := by
  exact (secondary_cover_descent_iso_on_local_overlap
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom.comm L.f (𝟙 L.Y) (𝟙 L.Y)
    (Category.id_comp _) (Category.id_comp _)

private theorem srccore'
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W X : C} (g : V ⟶ X) (Kf : W ⟶ V) (Lf : U ⟶ W)
    (x : 𝒮.p.Fiber X) :
    ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).symm.hom).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        ((Kf ≫ g) ^*[canonicalPullbackChoice 𝒮.p] x)).hom =
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        (Kf ^*[canonicalPullbackChoice 𝒮.p] (g ^*[canonicalPullbackChoice 𝒮.p] x))).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor Lf).map
          ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).inv)).hom := by
  rw [automorphismUnderlyingSheafConj_pullbackFunctor_map (𝒮 := 𝒮) hAbelian Lf
    ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).symm.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  congr 2

-- TGTCORE: the inverse-side mirror of SRCCORE, obtained by inverting the source iso square.
private theorem tgtcore'
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W X : C} (g : V ⟶ X) (Kf : W ⟶ V) (Lf : U ⟶ W)
    (x : 𝒮.p.Fiber X) :
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        ((Kf ≫ g) ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).symm.hom).inv) =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor Lf).map
          ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).inv)).inv ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        (Kf ^*[canonicalPullbackChoice 𝒮.p] (g ^*[canonicalPullbackChoice 𝒮.p] x))).inv := by
  have h :
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).symm.hom) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
          ((Kf ≫ g) ^*[canonicalPullbackChoice 𝒮.p] x) =
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
          (Kf ^*[canonicalPullbackChoice 𝒮.p] (g ^*[canonicalPullbackChoice 𝒮.p] x)) ≪≫
        automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor Lf).map
            ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).inv) := by
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    exact srccore' (𝒮 := 𝒮) hAbelian g Kf Lf x
  have h2 := congrArg Iso.inv h
  simpa only [Iso.trans_inv, Functor.mapIso_inv] using h2

-- SRCMERGE: the source-side three-fold base-change merge.
theorem srcmerge
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W X : C} (x : 𝒮.p.Fiber X) {D : Sheaf (J.over X) (Type (max u v))}
    (cov : D ⟶ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (g : V ⟶ X) (Kf : W ⟶ V) (Lf : U ⟶ W)
    (w₁ : g.op.toLoc ≫ Kf.op.toLoc = (Kf ≫ g).op.toLoc) :
    ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map cov)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            g.op.toLoc Kf.op.toLoc (Kf ≫ g).op.toLoc w₁).inv.toNatTrans.app
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
  have hmerge1 := automorphismUnderlyingSheafBaseChangeIso_comp_conj_hom
    (𝒮 := 𝒮) hAbelian g Kf (Kf ≫ g) x w₁
    ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x)
    (by
      simpa using fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv
        (hc := canonicalPullbackChoice 𝒮.p) g Kf x)
  have hinner :
      (((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map cov) ≫
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
            g.op.toLoc Kf.op.toLoc (Kf ≫ g).op.toLoc w₁).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (Kf ≫ g) x).hom =
      ((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map cov ≫
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g x).hom) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Kf
          (g ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).symm.hom).hom := by
    rw [Category.assoc]
    erw [← hmerge1, ← Functor.map_comp_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  rw [hinner]
  erw [((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map_comp,
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map_comp]
  simp only [Category.assoc]
  erw [srccore' (𝒮 := 𝒮) hAbelian g Kf Lf x]
  erw [← ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map_comp_assoc]

-- TGTMERGE: the target-side three-fold base-change merge (inverse side).
theorem tgtmerge
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W X : C} (x : 𝒮.p.Fiber X) {D : Sheaf (J.over X) (Type (max u v))}
    (cinv : automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x ⟶ D)
    (g : V ⟶ X) (Kf : W ⟶ V) (Lf : U ⟶ W)
    (w₁ : g.op.toLoc ≫ Kf.op.toLoc = (Kf ≫ g).op.toLoc) :
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Lf
        ((Kf ≫ g) ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (Kf ≫ g) x).inv) ≫
      ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            g.op.toLoc Kf.op.toLoc (Kf ≫ g).op.toLoc w₁).hom.toNatTrans.app
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
            (g ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
          ((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g x).inv ≫
              ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map cinv)) := by
  have hmerge2 := automorphismUnderlyingSheafBaseChangeIso_comp_conj_inv
    (𝒮 := 𝒮) hAbelian g Kf (Kf ≫ g) x w₁
    ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x)
    (by
      simpa using fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom
        (hc := canonicalPullbackChoice 𝒮.p) g Kf x)
  have hinner :
      ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (Kf ≫ g) x).inv ≫
          ((J.pseudofunctorOver (Type (max u v))).mapComp'
              g.op.toLoc Kf.op.toLoc (Kf ≫ g).op.toLoc w₁).hom.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
        ((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map cinv) =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g Kf x).symm.hom).inv ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Kf
          (g ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g x).inv ≫
            ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map cinv) := by
    rw [← hmerge2]
    erw [Category.assoc,
      ← ((J.pseudofunctorOver (Type (max u v))).map Kf.op.toLoc).toFunctor.map_comp]
  rw [← Functor.map_comp_assoc]
  erw [← ((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map_comp]
  erw [hinner]
  erw [((J.pseudofunctorOver (Type (max u v))).map Lf.op.toLoc).toFunctor.map_comp]
  erw [reassoc_of% tgtcore' (𝒮 := 𝒮) hAbelian g Kf Lf x]
  exact Category.assoc _ _ _


private theorem H1prime
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} (r : Z ⟶ U)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hf₁ : g₁ ≫ I₁.f = r) (hf₂ : g₂ ≫ I₂.f = r)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁) (I₂ := I₂) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁) (I₂ := I₂) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((secondary_cover_descent_iso_on_local_overlap (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁) (I₂ := I₂) g₁ g₂).hom.hom K) =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            g₁.op.toLoc K.f.op.toLoc (K.f ≫ g₁).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))) ≫
      ((secondary_cover_descent_iso_on_local_overlap (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁) (I₂ := I₂) (K.f ≫ g₁) (K.f ≫ g₂)).hom.hom L) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            g₂.op.toLoc K.f.op.toLoc (K.f ≫ g₂).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))) := by
  rw [← automorphism_overlap_hom_secondary_cover_component
        (𝒮 := 𝒮) hGerbe hAbelian (S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (xS := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (q := r)
        (I₁ := I₁) (I₂ := I₂) (f₁ := g₁) (f₂ := g₂) (hf₁ := hf₁) (hf₂ := hf₂) (K := K)]
  rw [map_eq_pullHom
        (φ := automorphism_overlap_hom_of_locally_isomorphic_cover (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          r (I₁ := I₁) (I₂ := I₂) g₁ g₂ hf₁ hf₂)
        (g := K.f) (gf₁ := K.f ≫ g₁) (gf₂ := K.f ≫ g₂) (hgf₁ := rfl) (hgf₂ := rfl)]
  erw [Functor.map_comp, Functor.map_comp]
  rw [map_eq_pullHom
        (φ := pullHom (automorphism_overlap_hom_of_locally_isomorphic_cover (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          r (I₁ := I₁) (I₂ := I₂) g₁ g₂ hf₁ hf₂) K.f (K.f ≫ g₁) (K.f ≫ g₂) rfl rfl)
        (g := L.f) (gf₁ := L.f ≫ (K.f ≫ g₁)) (gf₂ := L.f ≫ (K.f ≫ g₂)) (hgf₁ := rfl) (hgf₂ := rfl)]
  rw [pullHom_pullHom]
  rw [automorphism_overlap_hom_pull_common_owner_shell_eq_local_overlap_conjugation
        (𝒮 := 𝒮) hGerbe hAbelian (S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (xS := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (g := K.f) (q := r)
        (I₁ := I₁) (I₂ := I₂) (f₁ := g₁) (f₂ := g₂) (hf₁ := hf₁) (hf₂ := hf₂)
        (gf₁ := K.f ≫ g₁) (gf₂ := K.f ≫ g₂) (hgf₁ := rfl) (hgf₂ := rfl) (K := L)]
  rfl


/-- Generic abstract-category assembly: glue the source-merge and target-merge identities around
the central conjugation, with all associativity handled on abstract morphisms. -/
private theorem assemble_p07 {D : Type*} [Category D]
    {O0 O1 O2 O3 O4 O5 O6 O7 O8 O9 : D}
    {a : O0 ⟶ O1} {b : O1 ⟶ O2} {c : O2 ⟶ O3} {d : O3 ⟶ O4}
    (m : O4 ⟶ O5)
    {e : O5 ⟶ O6} {f : O6 ⟶ O7} {gg : O7 ⟶ O8} {h : O8 ⟶ O9}
    {P : O0 ⟶ O4} {Q : O5 ⟶ O9}
    (hS : a ≫ b ≫ c ≫ d = P) (hT : e ≫ f ≫ gg ≫ h = Q) :
    a ≫ ((b ≫ ((c ≫ d ≫ m ≫ e ≫ f) ≫ gg)) ≫ h) = P ≫ m ≫ Q := by
  rw [← hS, ← hT]; simp only [Category.assoc]

theorem pullback_cover_target_secondary_cover_middle_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
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
      (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base)).hom)).hom K)).hom L) ≫ (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map (automorphism_overlap_hom_of_locally_isomorphic_cover (𝒮 := 𝒮) hGerbe hAbelian (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (r ≫ q) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂ (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]))).hom K)).hom L) ≫ (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map ((((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)).inv)).hom K)).hom L) =
      ((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g₁ (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f (g₁ ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base))) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f (K.f ^*[canonicalPullbackChoice 𝒮.p] (g₁ ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base))) ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g₁ K.f (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)).inv))).hom ≫ (local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫ ((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g₂ (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f (g₂ ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base))) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f (K.f ^*[canonicalPullbackChoice 𝒮.p] (g₂ ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base))) ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g₂ K.f (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)).inv))).inv := by
  have hf₁ : g₁ ≫ I₁.base.f = r ≫ q := by
    change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]
  have hf₂ : g₂ ≫ I₂.base.f = r ≫ q := by
    change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]
  have w₁ : g₁.op.toLoc ≫ K.f.op.toLoc = (K.f ≫ g₁).op.toLoc := by
    simp [← Quiver.Hom.comp_toLoc, ← op_comp]
  have w₂ : g₂.op.toLoc ≫ K.f.op.toLoc = (K.f ≫ g₂).op.toLoc := by
    simp [← Quiver.Hom.comp_toLoc, ← op_comp]
  simp only [localizedSheafToCoverDescentEquivalence_functor_map_component]
  have hcomp := automorphism_overlap_hom_secondary_cover_component
        (𝒮 := 𝒮) hGerbe hAbelian (S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (xS := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (q := r ≫ q)
        (I₁ := I₁.base) (I₂ := I₂.base) (f₁ := g₁) (f₂ := g₂)
        (hf₁ := hf₁) (hf₂ := hf₂) (K := K)
  rw [hcomp]
  erw [H1prime (𝒮 := 𝒮) hGerbe hAbelian (r ≫ q) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂ hf₁ hf₂ K L]
  rw [secondary_cover_descent_iso_on_local_overlap_hom_component_explicit
        (𝒮 := 𝒮) hGerbe hAbelian (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base)
        (K.f ≫ g₁) (K.f ≫ g₂) L]
  exact assemble_p07 _
    (srcmerge (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
        (cov := (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).hom)
        g₁ K.f L.f w₁)
    (tgtmerge (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (cinv := (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).inv)
        g₂ K.f L.f w₂)

end


/-- Helper for Lemma 8.11.8: an explicit name for the chosen-cover overlap descent datum, equal by
proof irrelevance to the internal datum used to build `chosen_cover_underlying_automorphism_sheaf`.
Naming it lets us apply the descent-data `Hom.comm` compatibility of the counit comparison. -/
private noncomputable def chosen_cover_overlap_descent_datum
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) (U : C) :
    (J.pseudofunctorOver (Type (max u v))).DescentData
      (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f) :=
  automorphism_cover_descent_datum (𝒮 := 𝒮) hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
    (fun {_Y} _q {_I₁ _I₂} f₁ f₂ ↦
      let S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U
      let xS := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U
      let E :=
        localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂)
      (E.unitIso.app (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)).hom ≫
        E.inverse.map
          (secondary_cover_descent_iso_on_local_overlap
            (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom ≫
        (E.unitIso.app (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)).inv)
    (automorphism_cover_overlap_pull (𝒮 := 𝒮) hGerbe hAbelian (U := U))
    (fun {_Y} q {_I} g hg ↦
      automorphism_cover_overlap_self (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q g hg)
    (automorphism_cover_overlap_comp (𝒮 := 𝒮) hGerbe hAbelian)

/-- The counit comparison of the chosen-cover overlap descent datum, packaged so its
descent-data `Hom.comm` compatibility can be evaluated on overlaps. -/
private noncomputable def chosen_cover_overlap_descent_datum_counitIso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) (U : C) :
    ((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).obj
      (chosen_cover_underlying_automorphism_sheaf (𝒮 := 𝒮) hGerbe hAbelian U) ≅
      chosen_cover_overlap_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U :=
  localizedSheafFromCoverDescentData_counitIso (J := J)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_cover_overlap_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U)

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

/-- Helper for Lemma 8.11.8: on one overlap of the fixed chosen gerbe cover of `U`, the descended
chosen-cover transition is still compared to the explicit overlap morphism by the counit
components on the two branches. This isolates the datum-side middle branch before it is pulled to
the secondary cover. -/
private theorem chosen_cover_descent_datum_overlap_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} (q : Z ⟶ U)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = q := by cat_disch) (hg₂ : g₂ ≫ I₂.f = q := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₁)).hom ≫
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q g₁ g₂) =
    (chosen_cover_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian U).hom q g₁ g₂ ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₂)).hom := by
  exact (chosen_cover_overlap_descent_datum_counitIso
    (𝒮 := 𝒮) hGerbe hAbelian U).hom.comm q g₁ g₂ hg₁ hg₂
/-- Helper for Lemma 8.11.8: the middle morphism of `chosen_cover_descent_datum` can be exposed as
the explicit chosen-cover overlap morphism, with only the pulled counit component isomorphisms on
the two sides. This is the raw source-faithful exposure step needed before secondary-cover
normalization. -/
private theorem chosen_cover_descent_datum_overlap_raw
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} (q : Z ⟶ U)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = q := by cat_disch) (hg₂ : g₂ ≫ I₂.f = q := by cat_disch) :
    (chosen_cover_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian U).hom q g₁ g₂ =
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₁)).hom ≫
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q g₁ g₂) ≫
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₂)).inv := by
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv _).mpr
    (chosen_cover_descent_datum_overlap_component
      (𝒮 := 𝒮) hGerbe hAbelian q g₁ g₂ hg₁ hg₂).symm
/-- Helper for Lemma 8.11.8: after applying the explicit local-overlap descent equivalence to the
raw chosen-cover overlap comparison, one secondary-cover component displays exactly three visible
factors: the left counit flank, the explicit overlap middle morphism, and the right counit flank.
This freezes the transport-heavy normal form used in the blocked secondary-cover reduction. -/
theorem pullback_cover_target_secondary_cover_mapped_raw_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₂).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₂)).functor.map
      ((chosen_cover_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian U).hom q f₁ f₂)).hom K =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.mapIso
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian U I₁)).hom)).hom K) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₂)).functor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)).hom K) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₂)).functor.map
            ((((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.mapIso
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian U I₂)).inv)).hom K) := by
  rw [chosen_cover_descent_datum_overlap_raw
    (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ hf₁ hf₂]
  simp only [localizedSheafToCoverDescentEquivalence_functor_map_component, Functor.map_comp,
    Category.assoc]
  rfl
/-- Helper for Lemma 8.11.8: on one chosen-local cover arrow attached to a pullback-cover
component, the transported local-object comparison is sent back to the original chosen-local
descent component. This removes the remaining target-side transport shell before the pullback-cover
coherence square is reduced to the normalized chosen-local square. -/
theorem pullback_cover_target_component_to_chosen_local_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow)
    (L : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
          (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) =
      (chosen_local_automorphism_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
        (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.hom L := by
  refine (localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y))
    (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom L).symm.trans ?_
  exact chosen_local_automorphism_iso_functor_map_component (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
    (I.f ^*[canonicalPullbackChoice 𝒮.p] y) L
/-- Helper for Lemma 8.11.8: on one fixed secondary-cover arrow above a pullback-cover branch,
the transported chosen-local comparison component is already the common-owner conjugation shell on
that same owner `K.f`. This is the source-faithful component bridge needed before passing to a
common refinement of the two pullback-cover branches. -/
private theorem pullback_cover_target_secondary_component_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow)
    (K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
          (I.f ^*[canonicalPullbackChoice 𝒮.p] y))).functor.map
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
        (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom).hom K =
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe K.f (K := K) (g := 𝟙 K.Y)
            (by simp)).hom).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv := by
  rw [chosen_local_automorphism_iso_functor_map_eq_chosen_local_conjugation_component
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
    (I.f ^*[canonicalPullbackChoice 𝒮.p] y) K,
    automorphismUnderlyingSheafConj_eq_of_parallel hAbelian
      (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
        (I.f ^*[canonicalPullbackChoice 𝒮.p] y) K).hom
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe K.f (K := K) (g := 𝟙 K.Y) (by simp)).hom]
/-- Helper for Lemma 8.11.8: pure conjugation-shell rewrite.  Conjugation by a morphism `m`
equals conjugation by `m` framed on both sides by the boundary isomorphisms `a` and `b`, since
`automorphismUnderlyingSheafConj` is functorial and kills the inner cancellation `a.symm ≫ a`.
This is the abstract algebra behind reframing a pulled chosen-local conjugation over a refined
common owner. -/
private theorem conj_refine
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {A₁ A₂ B₁ B₂ : 𝒮.p.Fiber U} (a : A₁ ≅ A₂) (b : B₁ ≅ B₂) (m : A₂ ⟶ B₂) :
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian m).hom =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian a.symm.hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (a.hom ≫ m ≫ b.symm.hom)).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian b.symm.hom).inv := by
  have key : a.symm.hom ≫ (a.hom ≫ m ≫ b.symm.hom) = m ≫ b.symm.hom := by
    rw [← Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.id_comp]
  symm
  calc
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian a.symm.hom).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (a.hom ≫ m ≫ b.symm.hom)).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian b.symm.hom).inv
        = ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian a.symm.hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (a.hom ≫ m ≫ b.symm.hom)).hom) ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian b.symm.hom).inv := by
          rw [Category.assoc]
      _ = (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (a.symm.hom ≫ (a.hom ≫ m ≫ b.symm.hom))).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian b.symm.hom).inv := by
          rw [automorphismUnderlyingSheafConj_comp (𝒮 := 𝒮) hAbelian a.symm.hom
            (a.hom ≫ m ≫ b.symm.hom)]; rfl
      _ = (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (m ≫ b.symm.hom)).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian b.symm.hom).inv := by
          rw [key]
      _ = ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian m).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian b.symm.hom).hom) ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian b.symm.hom).inv := by
          rw [automorphismUnderlyingSheafConj_comp (𝒮 := 𝒮) hAbelian m b.symm.hom]; rfl
      _ = (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian m).hom := by
          rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Generic associativity bridge: the two parenthesizations produced by the refinement reduction
agree.  Phrased in an abstract category so `simp [Category.assoc]` applies; used by `exact` against
the concrete (bundled-instance) goal, where `simp [Category.assoc]` fails to fire syntactically. -/
private theorem assoc_bridge {D : Type*} [Category D] {O0 O1 O2 O3 O4 O5 O6 O7 : D}
    (t1 : O0 ⟶ O1) (t2 : O1 ⟶ O2) (t3 : O2 ⟶ O3) (t4 : O3 ⟶ O4)
    (t5 : O4 ⟶ O5) (t6 : O5 ⟶ O6) (t7 : O6 ⟶ O7) :
    t1 ≫ (t2 ≫ (t3 ≫ t4 ≫ t5) ≫ t6) ≫ t7 =
      (t1 ≫ t2 ≫ t3) ≫ t4 ≫ (t5 ≫ t6) ≫ t7 := by
  simp only [Category.assoc]

/-- Helper for Lemma 8.11.8: after one further owner refinement `s : Z ⟶ K.Y`, the pulled
`K`-component of the transported chosen-local comparison is exactly the common-owner conjugation
shell over the refined owner `s ≫ K.f`. This is the missing refinement-level bridge needed by the
source-faithful secondary-cover reduction. -/
theorem pullback_cover_target_secondary_component_bridge_on_refinement
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y Z : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow)
    (K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow)
    (s : Z ⟶ K.Y) :
    ((J.pseudofunctorOver (Type (max u v))).map s.op.toLoc).toFunctor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
              (I.f ^*[canonicalPullbackChoice 𝒮.p] y))).functor.map
          (chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
            (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom).hom K) =
      (((J.pseudofunctorOver (Type (max u v))).map s.op.toLoc).toFunctor.mapIso (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)) ≪≫ (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian s (K.f ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base))) ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (chosen_local_common_owner_source_iso (𝒮 := 𝒮) hGerbe (s ≫ K.f) (K := K) (g := s) (by simp [Category.assoc])).symm.hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (chosen_local_common_owner_isomorphism (𝒮 := 𝒮) hGerbe (s ≫ K.f) (K := K) (g := s) (by simp [Category.assoc])).hom).hom ≫
        (((J.pseudofunctorOver (Type (max u v))).map s.op.toLoc).toFunctor.mapIso (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f (I.f ^*[canonicalPullbackChoice 𝒮.p] y)) ≪≫ (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian s (K.f ^*[canonicalPullbackChoice 𝒮.p] (I.f ^*[canonicalPullbackChoice 𝒮.p] y))) ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (chosen_local_common_owner_target_iso (𝒮 := 𝒮) hGerbe (s ≫ K.f) (K := K) (g := s) (by simp [Category.assoc])).symm.hom).inv := by
  rw [chosen_local_automorphism_iso_functor_map_eq_chosen_local_conjugation_component
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
    (I.f ^*[canonicalPullbackChoice 𝒮.p] y) K]
  erw [Functor.map_comp, Functor.map_comp]
  erw [automorphismUnderlyingSheafConj_pullbackFunctor_map (𝒮 := 𝒮) hAbelian s
    (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y) K).hom]
  simp only [Functor.mapIso_hom, asIso_hom]
  erw [conj_refine (𝒮 := 𝒮) hAbelian
    (chosen_local_common_owner_source_iso (𝒮 := 𝒮) hGerbe (s ≫ K.f) (K := K) (g := s)
      (by simp [Category.assoc]))
    (chosen_local_common_owner_target_iso (𝒮 := 𝒮) hGerbe (s ≫ K.f) (K := K) (g := s)
      (by simp [Category.assoc]))
    (((canonicalPullbackChoice 𝒮.p).pullbackFunctor s).map
      (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
        (I.f ^*[canonicalPullbackChoice 𝒮.p] y) K).hom)]
  simp only [chosen_local_common_owner_isomorphism, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv]
  simp [Category.assoc]
  exact assoc_bridge _ _ _ _ _ _ _
/-- Helper for Lemma 8.11.8: after refining one chosen-local branch by `s : Z ⟶ K.Y`, the pulled
`hom` counit component of the chosen-cover comparison becomes exactly the source boundary shell on
the common owner `s ≫ K.f`. This is the left-flank transport rewrite needed by the blocked
secondary-cover reduction. -/
theorem chosen_cover_secondary_cover_source_counit_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y Z : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow)
    (K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow)
    (s : Z ⟶ K.Y) :
    ((J.pseudofunctorOver (Type (max u v))).map s.op.toLoc).toFunctor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
              (I.f ^*[canonicalPullbackChoice 𝒮.p] y))).functor.map
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I.base).hom).hom K) =
      (((J.pseudofunctorOver (Type (max u v))).map s.op.toLoc).toFunctor.mapIso (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I.base) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian s (K.f ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base))).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (chosen_local_common_owner_source_iso (𝒮 := 𝒮) hGerbe (s ≫ K.f) (g := s) (by simp [Category.assoc])).inv).hom ≫
      (((J.pseudofunctorOver (Type (max u v))).map s.op.toLoc).toFunctor.mapIso (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian s (K.f ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)) ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (chosen_local_common_owner_source_iso (𝒮 := 𝒮) hGerbe (s ≫ K.f) (g := s) (by simp [Category.assoc])).symm.hom).inv := by
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_trans, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.symm_hom, Category.assoc]
  erw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
    Iso.hom_inv_id, Functor.map_id, Category.comp_id]
  rfl
/-- Helper for Lemma 8.11.8: after the same refinement `s : Z ⟶ K.Y`, the pulled `inv` counit
component of the chosen-cover comparison is exactly the target boundary shell on the common owner
`s ≫ K.f`. This is the right-flank transport rewrite needed by the blocked secondary-cover
reduction. -/
theorem chosen_cover_secondary_cover_target_counit_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y Z : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow)
    (K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow)
    (s : Z ⟶ K.Y) :
    ((J.pseudofunctorOver (Type (max u v))).map s.op.toLoc).toFunctor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
              (I.f ^*[canonicalPullbackChoice 𝒮.p] y))).functor.map
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I.base).inv).hom K) =
      (((J.pseudofunctorOver (Type (max u v))).map s.op.toLoc).toFunctor.mapIso (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian s (K.f ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)) ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (chosen_local_common_owner_source_iso (𝒮 := 𝒮) hGerbe (s ≫ K.f) (g := s) (by simp [Category.assoc])).symm.hom).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (chosen_local_common_owner_source_iso (𝒮 := 𝒮) hGerbe (s ≫ K.f) (g := s) (by simp [Category.assoc])).inv).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).map s.op.toLoc).toFunctor.mapIso (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I.base) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian s (K.f ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base))).inv := by
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_trans, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.symm_hom, Category.assoc]
  erw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, ← Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id, Functor.map_id, Category.id_comp]
  rfl
/-- Helper for Lemma 8.11.8: once the pullback-cover owner is rewritten to `r ≫ q`, the
`K`-component of the chosen-cover middle morphism already has the source-faithful three-factor
shape "left counit flank, explicit overlap comparison, right counit flank" on the common
secondary cover. -/
private theorem pullback_cover_target_secondary_cover_middle_component_raw
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
      ((chosen_cover_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian U).hom (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂) (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]))).hom K =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian U I₁.base)).hom)).hom K) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (r ≫ q) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂ (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]))).hom K) ≫
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
            ((((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)).inv)).hom K) := by
  rw [chosen_cover_descent_datum_overlap_raw (𝒮 := 𝒮) hGerbe hAbelian
    (I₁ := I₁.base) (I₂ := I₂.base) (r ≫ q) g₁ g₂
    (by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
    (by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂])]
  simp only [localizedSheafToCoverDescentEquivalence_functor_map_component, Functor.map_comp,
    Category.assoc]
  rfl
/-- Helper for Lemma 8.11.8: after descending once more to the secondary cover over `K.Y`, the
raw fixed-`K` overlap equality can be read componentwise at a fixed refinement arrow `L`. This is
the exact middle-branch rewrite needed in the nested secondary-cover normalization step. -/
theorem pullback_cover_target_secondary_cover_middle_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
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
        ((chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian U).hom (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂) (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]))).hom K)).hom L =
      (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base)).hom)).hom K)).hom L) ≫
      (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map (automorphism_overlap_hom_of_locally_isomorphic_cover (𝒮 := 𝒮) hGerbe hAbelian (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (r ≫ q) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂ (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]))).hom K)).hom L) ≫
      (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map ((((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)).inv)).hom K)).hom L) := by
  rw [pullback_cover_target_secondary_cover_middle_component_raw
    (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂ K]
  simp only [Pseudofunctor.DescentData.comp_hom,
    localizedSheafToCoverDescentEquivalence_functor_map_component, Functor.map_comp, Category.assoc]
  rfl
/-- Helper for Lemma 8.11.8: after passing to the fixed secondary-cover refinement `L`, the
chosen-cover middle branch from `pullback_cover_target_secondary_cover_right_branch_exposed`
already collapses to the common-owner conjugation component. This isolates the reusable part of
the right-branch normalization from the remaining target-boundary transport. -/
theorem pullback_cover_target_secondary_cover_middle_component_as_conjugation
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
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
      ((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂) (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]))).hom K)).hom L =
      ((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g₁ (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f (g₁ ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base))) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f (K.f ^*[canonicalPullbackChoice 𝒮.p] (g₁ ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base))) ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g₁ K.f (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)).inv))).hom ≫ (local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫ ((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g₂ (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f (g₂ ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base))) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f (K.f ^*[canonicalPullbackChoice 𝒮.p] (g₂ ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base))) ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g₂ K.f (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)).inv))).inv := by
  exact (pullback_cover_target_secondary_cover_middle_component
      (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂ K L).trans
    (pullback_cover_target_secondary_cover_middle_normalized
      (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂ K L)
/-- Helper for Lemma 8.11.8: evaluating the already-normalized chosen-cover middle branch on one
owner leg `S : Over L.Y` gives the local-overlap conjugation component directly. This keeps the
later fixed-component proofs at the section level and avoids reopening `Sheaf.hom_ext`. -/
theorem pullback_cover_target_secondary_cover_middle_component_as_conjugation_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
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
      (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂) (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]))).hom K)).hom L).1.app S =
      (((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g₁ (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f (g₁ ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base))) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f (K.f ^*[canonicalPullbackChoice 𝒮.p] (g₁ ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base))) ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g₁ K.f (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)).inv))).hom ≫ (local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫ ((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g₂ (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f (g₂ ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base))) ≪≫ automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f (K.f ^*[canonicalPullbackChoice 𝒮.p] (g₂ ^*[canonicalPullbackChoice 𝒮.p] (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base))) ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso g₂ K.f (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)).inv))).inv).1.app S := by
  rw [pullback_cover_target_secondary_cover_middle_component_as_conjugation
    (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂ K L]
/-- Helper for Lemma 8.11.8: after fixing one secondary-cover arrow `L` and one owner leg
`T : Over L.Y`, pull back the same secondary cover along `T.unop.hom`. The resulting base-site
cover and its slice-site avatar are the source-faithful refinement cover used to compare
sections on `C / L.Y`. -/
private theorem local_overlap_secondary_cover_on_slice
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow)
    (T : (Over L.Y)ᵒᵖ) :
    ∃ B : J.Cover T.unop.left,
      ∃ R : (J.over L.Y).Cover T.unop,
        (R : Sieve T.unop) = (Sieve.overEquiv T.unop).symm (B : Sieve T.unop.left) := by
  refine ⟨⊤, ⊤, ?_⟩
  show (⊤ : Sieve T.unop) = (Sieve.overEquiv T.unop).symm (⊤ : Sieve T.unop.left)
  rw [Sieve.overEquiv_symm_top]
/-- Helper for Lemma 8.11.8: on one refinement member of the pulled secondary cover over a fixed
owner leg `T : Over L.Y`, the identity leg on `I.Y.left` and the base arrow of the induced
secondary-cover member `Ī.base` determine the same common owner `qI := I.Y.hom ≫ L.f`. This is
the arrow witness needed before any app-level owner transport. -/
private theorem local_overlap_secondary_refinement_member_identity_leg_eq
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow)
    (T : (Over L.Y)ᵒᵖ)
    {R : (J.over L.Y).Cover T.unop}
    (I : R.Arrow)
    (hmem : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂) (I.f.left ≫ (T.unop.hom ≫ L.f))) :
    let qI : I.Y.left ⟶ Y := I.Y.hom ≫ L.f
    let LI :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow :=
      (⟨I.Y.left, I.f.left, hmem⟩ : ((local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).pullback (T.unop.hom ≫ L.f)).Arrow).base
    (𝟙 I.Y.left) ≫ LI.f = qI := by
  intro qI LI
  show 𝟙 I.Y.left ≫ LI.f = I.Y.hom ≫ L.f
  rw [Category.id_comp]
  exact Over.w_assoc I.f L.f
/-- Helper for Lemma 8.11.8: after moving the previous common-owner witness to the opposite slice
owner, the object obtained by applying `Over.map LI.f` to the identity owner of `I.Y.left` is
exactly `I.Y`. This packages the object-level cast needed for owner-transport rewrites on the
pulled secondary cover. -/
private theorem local_overlap_secondary_refinement_member_owner_obj_eq_op
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow)
    (T : (Over L.Y)ᵒᵖ)
    {R : (J.over L.Y).Cover T.unop}
    (I : R.Arrow)
    (hmem : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂) (I.f.left ≫ (T.unop.hom ≫ L.f))) :
    let qI : I.Y.left ⟶ Y := I.Y.hom ≫ L.f
    let LI :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow :=
      (⟨I.Y.left, I.f.left, hmem⟩ : ((local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).pullback (T.unop.hom ≫ L.f)).Arrow).base
    op ((Over.map LI.f).obj (Over.mk (𝟙 I.Y.left))) = op ((Over.map L.f).obj I.Y) := by
  intro qI LI
  apply congrArg op
  refine Comma.ext rfl rfl (heq_of_eq ?_)
  simp only [Over.map_obj_hom, Over.mk_hom]
  show 𝟙 I.Y.left ≫ LI.f = I.Y.hom ≫ L.f
  rw [Category.id_comp]
  exact Over.w_assoc I.f L.f
/-- Helper for Lemma 8.11.8: after peeling off the pullback-cover source shell, the remaining
target-side branch is best compared only after passing to the chosen local-overlap secondary
cover. On each fixed secondary-cover arrow `K`, the mapped pullback-cover target square should
rewrite to the normalized common-owner square from
`local_overlap_secondary_descent_square_normalized`. -/
theorem pullback_cover_target_secondary_cover_left_branch_exposed
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
      ((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base) (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)) ≫ (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫ (((J.pseudofunctorOver (Type (max u v))).toDescentData (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L =
      (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base) (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)))).hom K)).hom L) ≫
      (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫ (((J.pseudofunctorOver (Type (max u v))).toDescentData (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L) := by
  simp only [Pseudofunctor.DescentData.comp_hom,
    localizedSheafToCoverDescentEquivalence_functor_map_component, Functor.map_comp]
  rfl
/-- Helper for Lemma 8.11.8: on a fixed secondary-cover refinement `L`, the target-side branch of
the pullback-cover target square factors into the mapped chosen-cover middle component followed by
the mapped target-shell component. This is the transport-stable normal form used before the
target boundary is rewritten by the secondary-cover counit comparison. -/
theorem pullback_cover_target_secondary_cover_right_branch_exposed
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
      ((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂) (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫ (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom) ≫ (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base) (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)))).hom K)).hom L =
      (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂) (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]))).hom K)).hom L) ≫
      (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map (((localizedSheafToCoverDescentEquivalence (J := J) (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map ((((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom) ≫ (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base) (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)))).hom K)).hom L) := by
  simp only [Pseudofunctor.DescentData.comp_hom,
    localizedSheafToCoverDescentEquivalence_functor_map_component, Functor.map_comp]
  rfl
end

end CategoryTheory
