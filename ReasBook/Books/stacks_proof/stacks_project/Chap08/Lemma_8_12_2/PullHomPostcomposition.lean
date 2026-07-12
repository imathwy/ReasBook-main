import StacksProject_2024.Chap08.Lemma_8_12_2.TargetRestrictionNaturality

open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Cover

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Chap08 Lemma 8 12 2: applying `u` to a morphism in `Over U` preserves the
displayed triangle equation used by the target Hom-presheaf restriction. -/
theorem overPost_map_left_comp_hom
    {U : C} {T₁ T₂ : Over U} (g : T₂ ⟶ T₁) :
    u.map g.left ≫ u.map T₁.hom = u.map T₂.hom := by
  -- Map the slice equation and rewrite functoriality to expose the target-side triangle.
  have hg : g.left ≫ T₁.hom = T₂.hom := by simpa using g.w
  rw [← u.map_comp]
  rw [hg]
  rfl

/-- Helper for Chap08 Lemma 8 12 2: the source slice triangle gives the `toLoc` composite
used by the source `mapComp'` shell. -/
theorem over_left_comp_hom_toLoc
    {U : C} {T₁ T₂ : Over U} (g : T₂ ⟶ T₁) :
    T₁.hom.op.toLoc ≫ g.left.op.toLoc = T₂.hom.op.toLoc := by
  -- Feed the over-category triangle into the canonical locally-discrete-op normalizer.
  exact
    FibredCategoryMor.comp_toLoc_eq T₁.hom g.left T₂.hom
      (by simpa using g.w)

/-- Helper for Chap08 Lemma 8 12 2: after applying `u`, the slice triangle gives the target
`toLoc` composite used by the target `mapComp'` shell. -/
theorem overPost_map_left_comp_hom_toLoc
    {U : C} {T₁ T₂ : Over U} (g : T₂ ⟶ T₁) :
    (u.map T₁.hom).op.toLoc ≫ (u.map g.left).op.toLoc =
      (u.map T₂.hom).op.toLoc := by
  -- The target-side equality is the image of the slice triangle, then translated to `toLoc`.
  exact
    FibredCategoryMor.comp_toLoc_eq (u.map T₁.hom) (u.map g.left) (u.map T₂.hom)
      (overPost_map_left_comp_hom u g)

/-- Helper for Chap08 Lemma 8 12 2: a canonical-fiber restriction map and the corresponding
`pullHom` have the same postcomposition after exposing the left `mapComp'` boundary. -/
theorem canonicalFiberPseudofunctor_pullHom_postcomp_map
    (p : S ⥤ D) [p.IsFibered]
    {X₁ X₂ Y Y' : D} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (g : Y' ⟶ Y)
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    {M₁ : p.Fiber X₁} {M₂ : p.Fiber X₂}
    (φ : ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj M₂) :
    (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ).1 ≫
      (canonicalPullbackChoice p).map g
        (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj M₂) ≫
      (canonicalPullbackChoice p).map f₂ M₂ =
    (((canonicalFiberPseudofunctor p).mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f₁ g gf₁ hgf₁)).inv.toNatTrans.app M₁).1 ≫
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂).1 ≫
      (canonicalPullbackChoice p).map gf₂ M₂ := by
  -- Split the pseudofunctorial restriction map through the public `pullHom` normal form.
  have hmap := congrArg Functor.Fiber.fiberInclusion.map
    (Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor p) φ g gf₁ gf₂ hgf₁ hgf₂)
  have hmapSplit :
      Functor.Fiber.fiberInclusion.map
          (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ) =
        Functor.Fiber.fiberInclusion.map
            (((canonicalFiberPseudofunctor p).mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq f₁ g gf₁ hgf₁)).inv.toNatTrans.app M₁) ≫
          Functor.Fiber.fiberInclusion.map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂) ≫
          Functor.Fiber.fiberInclusion.map
            (((canonicalFiberPseudofunctor p).mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq f₂ g gf₂ hgf₂)).hom.toNatTrans.app M₂) := by
    change
      Functor.Fiber.fiberInclusion.map
          (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ) =
        Functor.Fiber.fiberInclusion.map
          ((((canonicalFiberPseudofunctor p).mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq f₁ g gf₁ hgf₁)).inv.toNatTrans.app M₁) ≫
            Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫
            (((canonicalFiberPseudofunctor p).mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq f₂ g gf₂ hgf₂)).hom.toNatTrans.app M₂))
    exact hmap
  -- Postcompose the split equality and collapse the right `mapComp'` boundary by its owner API.
  calc
    Functor.Fiber.fiberInclusion.map
        (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ) ≫
      (canonicalPullbackChoice p).map g
        (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj M₂) ≫
      (canonicalPullbackChoice p).map f₂ M₂ =
        (Functor.Fiber.fiberInclusion.map
            (((canonicalFiberPseudofunctor p).mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq f₁ g gf₁ hgf₁)).inv.toNatTrans.app M₁) ≫
          Functor.Fiber.fiberInclusion.map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂) ≫
          Functor.Fiber.fiberInclusion.map
            (((canonicalFiberPseudofunctor p).mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq f₂ g gf₂ hgf₂)).hom.toNatTrans.app M₂)) ≫
          (canonicalPullbackChoice p).map g
            (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj M₂) ≫
          (canonicalPullbackChoice p).map f₂ M₂ := by
            exact
              congrArg
                (fun k ↦ k ≫
                  (canonicalPullbackChoice p).map g
                    (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj M₂) ≫
                  (canonicalPullbackChoice p).map f₂ M₂)
                hmapSplit
    _ = Functor.Fiber.fiberInclusion.map
          (((canonicalFiberPseudofunctor p).mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f₁ g gf₁ hgf₁)).inv.toNatTrans.app M₁) ≫
        Functor.Fiber.fiberInclusion.map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂) ≫
        (canonicalPullbackChoice p).map gf₂ M₂ := by
          have hfac :=
            FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac p f₂ g gf₂ hgf₂ M₂
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                (Functor.Fiber.fiberInclusion.map
                    (((canonicalFiberPseudofunctor p).mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
                      (FibredCategoryMor.comp_toLoc_eq f₁ g gf₁ hgf₁)).inv.toNatTrans.app M₁) ≫
                  Functor.Fiber.fiberInclusion.map
                    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂)) ≫ k)
              hfac

end

end CategoryTheory
