import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.PullHom

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor
namespace DescentCompletionObject

/-- Source stage 3.13 transition-level restriction law for
`rho_(ai)(bj)`.  This is the owner-coherence statement still needed after the local-refinement
and same-outer pullback lemmas have been isolated. -/
def projectionDescentTotalCoverTransitionComponentPullHomLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) : Prop :=
  ∀ ⦃Y' Y : C⦄ (g : Y' ⟶ Y)
    ⦃A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow⦄
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f)
    (ga : Y' ⟶ A.Y) (gb : Y' ⟶ B.Y)
    (hga : g ≫ a = ga) (hgb : g ≫ b = gb),
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (projectionDescentTotalCoverTransitionComponent (J := J) hSheaf D A B a b h)
          g ga gb hga hgb =
        projectionDescentTotalCoverTransitionComponent (J := J) hSheaf D A B ga gb
          (by
            calc
              ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
              _ = g ≫ b ≫ B.f := by
                simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
              _ = gb ≫ B.f := by rw [← hgb]; simp [Category.assoc])

/-- Source stage 3.13 transition-level cocycle law for `rho_(ai)(bj)`.  The later proof should
expand this into the outer descent cocycle for `Theta` plus the inner gluing compatibilities. -/
def projectionDescentTotalCoverTransitionComponentHomCompLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) : Prop :=
  ∀ ⦃Y : C⦄
    ⦃A B K : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow⦄
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y) (k : Y ⟶ K.Y)
    (hab : a ≫ A.f = b ≫ B.f) (hbk : b ≫ B.f = k ≫ K.f),
      projectionDescentTotalCoverTransitionComponent (J := J) hSheaf D A B a b hab ≫
          projectionDescentTotalCoverTransitionComponent (J := J) hSheaf D B K b k hbk =
        projectionDescentTotalCoverTransitionComponent (J := J) hSheaf D A K a k
          (hab.trans hbk)

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
