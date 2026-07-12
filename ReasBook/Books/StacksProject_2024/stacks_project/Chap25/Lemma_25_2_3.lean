import StacksProject_2024.Chap25.Definition_25_3_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search note: `lean_leansearch` was unavailable in this runner, so the owner/API choice
-- was verified directly against the local Chapter 25 files and small `#check` probes.

universe w v u

namespace CategoryTheory

open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

namespace SemiRepresentableFamily
namespace Over

/-- The source-facing functor `SR(C, X) ⥤ PSh(C) / h_X`, obtained from the augmentation via the
canonical `Functor.toOver` construction. -/
noncomputable abbrev toOverPresheaf (X : C) :
    SR(C, X) ⥤ CategoryTheory.Over (uliftYoneda.obj X) :=
  (forget ⋙ toPresheaf).toOver (uliftYoneda.obj X)
    (fun K ↦ augmentation K)
    (by
      intro Y Z g
      simpa using augmentation_naturality g)

/-- Forgetting the structure morphism from `toOverPresheaf X` recovers the canonical coproduct
presheaf functor on fixed-target semi-representable families. -/
@[simp] theorem toOverPresheaf_comp_forget (X : C) :
    toOverPresheaf X ⋙ CategoryTheory.Over.forget (uliftYoneda.obj X) =
      forget ⋙ toPresheaf := by
  simpa [toOverPresheaf] using
    (Functor.toOver_comp_forget
      (forget ⋙ toPresheaf)
      (uliftYoneda.obj X)
      (fun K ↦ augmentation K)
      (fun φ ↦ by simpa using augmentation_naturality φ))

/-- The left presheaf of `toOverPresheaf X` is the canonical coproduct presheaf. -/
@[simp] theorem toOverPresheaf_obj_left {X : C} (K : SR(C, X)) :
    ((toOverPresheaf X).obj K).left =
      toPresheaf.obj (forget.obj K) :=
  rfl

/-- The structure map of `toOverPresheaf X` is the augmentation to `h_X`. -/
@[simp] theorem toOverPresheaf_obj_hom {X : C} (K : SR(C, X)) :
    ((toOverPresheaf X).obj K).hom = augmentation K :=
  rfl

/-- On morphisms, `toOverPresheaf X` acts by the underlying presheaf map. -/
@[simp] theorem toOverPresheaf_map_left {X : C} {K L : SR(C, X)} (φ : K ⟶ L) :
    ((toOverPresheaf X).map φ).left = toPresheaf.map (forget.map φ) :=
  rfl

/-- The image of a morphism under `toOverPresheaf X` satisfies the defining commutative triangle
in `PSh(C) / h_X`. -/
@[reassoc, simp] theorem toOverPresheaf_map_w {X : C} {K L : SR(C, X)} (φ : K ⟶ L) :
    ((toOverPresheaf X).map φ).left ≫ ((toOverPresheaf X).obj L).hom =
      ((toOverPresheaf X).obj K).hom := by
  simpa using augmentation_naturality φ

end Over

/-- Lemma 25.2.3 (1): the category `SR(C)` has coproducts. -/
@[stacks 01G2]
instance semiRepresentableFamily_hasCoproducts :
    HasCoproducts.{w} (SR(C)) := by
  simpa using (inferInstance : HasCoproducts.{w} (FormalCoproduct.{w} C))

/-- Lemma 25.2.3 (2): the functor `F : SR(C) ⥤ PSh(C)` commutes with coproducts. -/
@[stacks 01G2]
instance semiRepresentableFamily_toPresheaf_preservesCoproductsOfShape (J : Type w) :
    PreservesColimitsOfShape (Discrete J)
      (SemiRepresentableFamily.toPresheaf : SR(C) ⥤ (Cᵒᵖ ⥤ Type (max w v))) := by
  simpa using
    (inferInstance :
      PreservesColimitsOfShape (Discrete J)
        (FormalCoproduct.toPresheaf : FormalCoproduct.{w} C ⥤ (Cᵒᵖ ⥤ Type (max w v))))

/-- Lemma 25.2.3 (3): the functor `F : SR(C) ⥤ PSh(C)` commutes with limits. -/
@[stacks 01G2]
instance semiRepresentableFamily_toPresheaf_preservesLimits :
    PreservesLimits
      (SemiRepresentableFamily.toPresheaf : SR(C) ⥤ (Cᵒᵖ ⥤ Type (max w v))) := by
  simpa using
    (inferInstance :
      PreservesLimits
        (FormalCoproduct.toPresheaf : FormalCoproduct.{w} C ⥤ (Cᵒᵖ ⥤ Type (max w v))))

/-- Lemma 25.2.3 (4): if `C` has fibre products, then `SR(C)` has fibre products. -/
@[stacks 01G2]
instance semiRepresentableFamily_hasPullbacks [HasPullbacks C] :
    HasPullbacks (SR(C)) := by
  simpa using (inferInstance : HasPullbacks (FormalCoproduct.{w} C))

/-- Lemma 25.2.3 (5): if `C` has products of pairs, then `SR(C)` has products of pairs. -/
@[stacks 01G2]
instance semiRepresentableFamily_hasBinaryProducts [HasBinaryProducts C] :
    HasBinaryProducts (SR(C)) := by
  simpa using (inferInstance : HasBinaryProducts (FormalCoproduct.{w} C))

/-- Lemma 25.2.3 (6): if `C` has equalizers, then `SR(C)` has equalizers. -/
@[stacks 01G2]
instance semiRepresentableFamily_hasEqualizers [HasEqualizers C] :
    HasEqualizers (SR(C)) := by
  simpa using (inferInstance : HasEqualizers (FormalCoproduct.{w} C))

/-- Lemma 25.2.3 (7): if `C` has a final object, then `SR(C)` has a final object. -/
@[stacks 01G2]
instance semiRepresentableFamily_hasTerminal [HasTerminal C] :
    HasTerminal (SR(C)) := by
  simpa using (inferInstance : HasTerminal (FormalCoproduct.{w} C))

/-- Lemma 25.2.3 (8): for `X : C`, the category `SR(C, X)` has coproducts. -/
@[stacks 01G2]
instance semiRepresentableFamilyOver_hasCoproducts (X : C) :
    HasCoproducts.{w} (SR(C, X)) := by
  simpa using
    (inferInstance : HasCoproducts.{w} (FormalCoproduct.{w} (CategoryTheory.Over X)))

/-- Lemma 25.2.3 (9): for `X : C`, the functor `F : SR(C, X) ⥤ PSh(C) / h_X` commutes with
coproducts. -/
@[stacks 01G2]
instance semiRepresentableFamilyOver_toOverPresheaf_preservesCoproductsOfShape
    (X : C) (J : Type w) :
    PreservesColimitsOfShape (Discrete J) (Over.toOverPresheaf X) := by
  let _ :
      PreservesColimitsOfShape (Discrete J)
        (SemiRepresentableFamily.Over.forget ⋙ SemiRepresentableFamily.toPresheaf) := by
    simpa using
      (inferInstance :
        PreservesColimitsOfShape (Discrete J)
          (SemiRepresentableFamily.map (CategoryTheory.Over.forget X) ⋙
            SemiRepresentableFamily.toPresheaf))
  dsimp [Over.toOverPresheaf]
  infer_instance

/-- Lemma 25.2.3 (10): if `C` has fibre products, then `SR(C, X)` has finite limits. -/
@[stacks 01G2]
instance semiRepresentableFamilyOver_hasFiniteLimits (X : C) [HasPullbacks C] :
    HasFiniteLimits (SR(C, X)) := by
  simpa using
    (inferInstance : HasFiniteLimits (FormalCoproduct.{w} (CategoryTheory.Over X)))

/-- Lemma 25.2.3 (11): if `C` has fibre products, then the functor
`F : SR(C, X) ⥤ PSh(C) / h_X` commutes with finite limits. -/
@[stacks 01G2]
instance semiRepresentableFamilyOver_toOverPresheaf_preservesFiniteLimits
    (X : C) [HasPullbacks C] :
    PreservesFiniteLimits (Over.toOverPresheaf X) := by
  let _ :
      PreservesFiniteLimits
        (SemiRepresentableFamily.Over.forget ⋙ SemiRepresentableFamily.toPresheaf) := by
    simpa using
      (inferInstance :
        PreservesFiniteLimits
          (SemiRepresentableFamily.map (CategoryTheory.Over.forget X) ⋙
            SemiRepresentableFamily.toPresheaf))
  dsimp [Over.toOverPresheaf]
  infer_instance

end SemiRepresentableFamily

end CategoryTheory
