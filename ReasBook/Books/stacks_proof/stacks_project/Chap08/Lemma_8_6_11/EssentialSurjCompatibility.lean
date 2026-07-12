import StacksProject_2024.Chap08.Lemma_8_6_11.SliceLocalClasses

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- Helper for Chap08 Lemma 8 6 11: the fixed-cover descent functor induced by a stack morphism
spells each overlap map as conjugation by the two pullback-comparison isomorphisms. -/
theorem coverDescentDataFunctor_hom_eq_pullbackComparison
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered]
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : S.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch)
    (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((cover_descent_data_functor_of_stack_morphism (J := J) H S).obj D).hom
        q f₁ f₂ hf₁ hf₂ =
      (FibredCategoryMor.pullbackComparison H f₁ (D.obj I₁)).hom ≫
        (FibredCategoryMor.fiberFunctor H V).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
          (FibredCategoryMor.pullbackComparison H f₂ (D.obj I₂)).inv := by
  -- Open the owner abbreviation once, in a fresh declaration budget, so target proofs can rewrite
  -- through this stable normal form without unfolding the descent functor locally.
  change
    cover_descent_data_functor_hom_of_stack_morphism (J := J) H S D q f₁ f₂ hf₁ hf₂ =
      (FibredCategoryMor.pullbackComparison H f₁ (D.obj I₁)).hom ≫
        (FibredCategoryMor.fiberFunctor H V).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
          (FibredCategoryMor.pullbackComparison H f₂ (D.obj I₂)).inv
  simp only [cover_descent_data_functor_hom_of_stack_morphism]

end

end CategoryTheory
