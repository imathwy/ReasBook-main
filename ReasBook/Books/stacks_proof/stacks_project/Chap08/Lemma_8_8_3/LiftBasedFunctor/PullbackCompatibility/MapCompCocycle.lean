import StacksProject_2024.Chap08.Lemma_8_8_3.Prelude

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]

/-- Naturality of the two-leg pseudofunctor composition comparison, solved for the iterated
pullback of a morphism. -/
theorem mapCompAppIso_inv_comp_map_map_hom
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {x y : p.Fiber U} (e : x ⟶ y) :
    ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map
        (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map e) =
      (mapCompAppIso p f g (g ≫ f)
        (FibredCategoryMor.comp_toLoc_eq f g (g ≫ f) rfl) x).inv ≫
        ((canonicalFiberPseudofunctor p).map (g ≫ f).op.toLoc).toFunctor.map e ≫
        (mapCompAppIso p f g (g ≫ f)
          (FibredCategoryMor.comp_toLoc_eq f g (g ≫ f) rfl) y).hom := by
  let Fp := canonicalFiberPseudofunctor p
  let hfg := FibredCategoryMor.comp_toLoc_eq f g (g ≫ f) rfl
  let κ := Fp.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc hfg
  have hnat := κ.hom.toNatTrans.naturality e
  dsimp only [mapCompAppIso]
  change
    (Fp.map f.op.toLoc ≫ Fp.map g.op.toLoc).toFunctor.map e =
      κ.inv.toNatTrans.app x ≫
        (Fp.map (g ≫ f).op.toLoc).toFunctor.map e ≫
        κ.hom.toNatTrans.app y
  rw [hnat]
  rw [← Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
  simp only [Category.id_comp]

/-- The three-leg pseudofunctor composition comparison in the orientation used by the
stackification-lift pullback cocycle.

Pulling the `f,g` comparison back along `i`, after first expanding the `g,i` comparison, is the
same as passing through the direct `(i ≫ g) ≫ f` comparison and then expanding the `gf,i`
comparison. -/
theorem mapCompAppIso_hom_comp_map_inv
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {U V W Y : C} (f : V ⟶ U) (g : W ⟶ V) (i : Y ⟶ W)
    (gf : W ⟶ U) (hgf : g ≫ f = gf) (y : p.Fiber U) :
    (mapCompAppIso p g i (i ≫ g)
        (FibredCategoryMor.comp_toLoc_eq g i (i ≫ g) rfl)
        (f ^*[canonicalPullbackChoice p] y)).hom ≫
      ((canonicalFiberPseudofunctor p).map i.op.toLoc).toFunctor.map
        (mapCompAppIso p f g gf
          (FibredCategoryMor.comp_toLoc_eq f g gf hgf) y).inv =
    (mapCompAppIso p f (i ≫ g) (i ≫ gf)
        (FibredCategoryMor.comp_toLoc_eq f (i ≫ g) (i ≫ gf) (by
          simp [Category.assoc, hgf]))
        y).inv ≫
      (mapCompAppIso p gf i (i ≫ gf)
        (FibredCategoryMor.comp_toLoc_eq gf i (i ≫ gf) rfl) y).hom := by
  subst gf
  let Fp := canonicalFiberPseudofunctor p
  let h₀₂ := FibredCategoryMor.comp_toLoc_eq f g (g ≫ f) rfl
  let h₁₃ := FibredCategoryMor.comp_toLoc_eq g i (i ≫ g) rfl
  let hf := FibredCategoryMor.comp_toLoc_eq (g ≫ f) i (i ≫ g ≫ f) rfl
  let h₀₃ := FibredCategoryMor.comp_toLoc_eq f (i ≫ g) (i ≫ g ≫ f)
    (Category.assoc i g f)
  have h :=
    Pseudofunctor.mapComp'₀₂₃_hom_app
      (F := Fp)
      (f₀₁ := f.op.toLoc) (f₁₂ := g.op.toLoc) (f₂₃ := i.op.toLoc)
      (f₀₂ := (g ≫ f).op.toLoc) (f₁₃ := (i ≫ g).op.toLoc)
      (f := (i ≫ g ≫ f).op.toLoc)
      (h₀₂ := h₀₂) (h₁₃ := h₁₃) (hf := hf) y
  have h' :
      (Fp.mapComp' (g ≫ f).op.toLoc i.op.toLoc
          (i ≫ g ≫ f).op.toLoc hf).hom.toNatTrans.app y =
        (Fp.mapComp' f.op.toLoc (i ≫ g).op.toLoc
            (i ≫ g ≫ f).op.toLoc h₀₃).hom.toNatTrans.app y ≫
          (Fp.mapComp' g.op.toLoc i.op.toLoc
              (i ≫ g).op.toLoc h₁₃).hom.toNatTrans.app
            (((Fp.map f.op.toLoc).toFunctor.obj y)) ≫
          (Fp.map i.op.toLoc).toFunctor.map
            ((Fp.mapComp' f.op.toLoc g.op.toLoc
              (g ≫ f).op.toLoc h₀₂).inv.toNatTrans.app y) := by
    simpa [Fp, h₀₂, h₁₃, hf, h₀₃] using h
  dsimp only [mapCompAppIso]
  change
    (Fp.mapComp' g.op.toLoc i.op.toLoc
        (i ≫ g).op.toLoc h₁₃).hom.toNatTrans.app
          (((Fp.map f.op.toLoc).toFunctor.obj y)) ≫
        (Fp.map i.op.toLoc).toFunctor.map
          ((Fp.mapComp' f.op.toLoc g.op.toLoc
            (g ≫ f).op.toLoc h₀₂).inv.toNatTrans.app y) =
      (Fp.mapComp' f.op.toLoc (i ≫ g).op.toLoc
          (i ≫ g ≫ f).op.toLoc h₀₃).inv.toNatTrans.app y ≫
        (Fp.mapComp' (g ≫ f).op.toLoc i.op.toLoc
          (i ≫ g ≫ f).op.toLoc hf).hom.toNatTrans.app y
  symm
  rw [h']
  let C₁ := (Fp.mapComp' g.op.toLoc i.op.toLoc
    (i ≫ g).op.toLoc h₁₃).hom.toNatTrans.app
      ((Fp.map f.op.toLoc).toFunctor.obj y)
  let D₁ := (Fp.map i.op.toLoc).toFunctor.map
    ((Fp.mapComp' f.op.toLoc g.op.toLoc
      (g ≫ f).op.toLoc h₀₂).inv.toNatTrans.app y)
  have hcancel :
      (Fp.mapComp' f.op.toLoc (i ≫ g).op.toLoc
          (i ≫ g ≫ f).op.toLoc h₀₃).inv.toNatTrans.app y ≫
        (Fp.mapComp' f.op.toLoc (i ≫ g).op.toLoc
          (i ≫ g ≫ f).op.toLoc h₀₃).hom.toNatTrans.app y =
      𝟙 _ :=
    Cat.Hom.inv_hom_id_toNatTrans_app
      (Fp.mapComp' f.op.toLoc (i ≫ g).op.toLoc
        (i ≫ g ≫ f).op.toLoc h₀₃) y
  calc
    (Fp.mapComp' f.op.toLoc (i ≫ g).op.toLoc
        (i ≫ g ≫ f).op.toLoc h₀₃).inv.toNatTrans.app y ≫
        (Fp.mapComp' f.op.toLoc (i ≫ g).op.toLoc
          (i ≫ g ≫ f).op.toLoc h₀₃).hom.toNatTrans.app y ≫
          C₁ ≫ D₁ =
        ((Fp.mapComp' f.op.toLoc (i ≫ g).op.toLoc
            (i ≫ g ≫ f).op.toLoc h₀₃).inv.toNatTrans.app y ≫
          (Fp.mapComp' f.op.toLoc (i ≫ g).op.toLoc
            (i ≫ g ≫ f).op.toLoc h₀₃).hom.toNatTrans.app y) ≫
            C₁ ≫ D₁ := by
          simp only [Category.assoc]
    _ = 𝟙 _ ≫ C₁ ≫ D₁ := by
          exact congrArg (fun t => t ≫ C₁ ≫ D₁) hcancel
    _ = C₁ ≫ D₁ := by
          simp only [Category.id_comp]

end

end CategoryTheory
