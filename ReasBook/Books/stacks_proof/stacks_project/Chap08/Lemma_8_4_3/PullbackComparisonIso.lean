import stacks_proof.stacks_project.Chap04.CanonicalFiberPseudofunctor
import stacks_proof.stacks_project.Chap08.Lemma_8_2_3.PullbackComparisonNaturality
import stacks_proof.stacks_project.Chap08.Lemma_8_4_3.PullbackComparisonBase

open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C)
variable (P : ObjectProperty X)
variable [p.IsFibered]

section RestrictedFibered

variable [(P.ι ⋙ p).IsFibered]

/-- Helper for Lemma 8.4.3: the restricted canonical pullback of an object in the full
subcategory matches the ambient canonical pullback of its underlying inverse-image fiber object in
the ambient fiber. -/
noncomputable def restricted_pullback_vs_ambient_pullback_comparison
    (J : GrothendieckTopology C)
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U V : C} (f : V ⟶ U) (x : (P.ι ⋙ p).Fiber U) :
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) V).obj
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f.op.toLoc).toFunctor.obj x)).obj ≅
      (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj) := by
  let H := fullSubcategory_inclusion_fibredMor (J := J) (p := p) (P := P) hpullback
  -- Route correction: compare the two underlying ambient fiber objects first, without trying to
  -- package the ambient pullback target back into the strict inverse-image full subcategory.
  simpa [H] using (FibredCategoryMor.pullbackComparison H f x).symm

end RestrictedFibered

end
