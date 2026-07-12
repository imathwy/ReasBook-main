import Mathlib
import StacksProject_2024.Chap14.Lemma_14_8_2
import StacksProject_2024.Chap25.25_9_1_2

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory
open Opposite
open SSet (ι₀ ι₁)
open scoped MonoidalCategory Simplicial

noncomputable section

namespace CategoryTheory

-- Semantic search note: `lean_leansearch` recalled the simplicial-set subcomplex/range API and
-- the canonical pushout-pullback universal-property owner. The source-facing statement here keeps
-- the explicit simplicial maps from diagram `25.9.1.2`, reusing the owner file
-- `stacks_project/Chap25/25_9_1_2.lean`, and uses the canonical pushout owner for
-- the source simplicial subset `U`.

/-- The chosen pushout owner of the span in diagram `25.9.1.2`. This is the project-facing
replacement for the source's simplicial subset `U ⊆ Δ[1] × Δ[n + 1]`. -/
noncomputable abbrev hypercoveringEquationPushout (n : ℕ) : SSet :=
  pushout
    (hypercoveringEquationBoundaryCoprodToFullCoprod n)
    (hypercoveringEquationBoundaryCoprodToBoundaryCylinder n)

/-- The canonical map from the chosen pushout owner of diagram `25.9.1.2` into the ambient
cylinder `Δ[n + 1] ⊗ Δ[1]`. -/
noncomputable abbrev hypercoveringEquationPushoutToCylinder (n : ℕ) :
    hypercoveringEquationPushout n ⟶ hypercoveringEquationCylinder n :=
  pushout.desc
    (hypercoveringEquationFullCoprodToCylinder n)
    (hypercoveringEquationBoundaryCylinderToCylinder n)
    (hypercoveringEquationPushoutCocone_condition n)

/-- Lemma 25.9.1: the simplicial subset `U ⊆ Δ[1] × Δ[n + 1]` from the source is represented here
by the chosen pushout of diagram `25.9.1.2`. This is the exact pushout input used to identify the
fibre product in the source proof via the Chapter 14 pushout/pullback comparison. -/
noncomputable abbrev hypercoveringEquationPushoutIsColimit (n : ℕ) :
    IsColimit
      (pushout.cocone
        (hypercoveringEquationBoundaryCoprodToFullCoprod n)
        (hypercoveringEquationBoundaryCoprodToBoundaryCylinder n)) :=
  pushout.isColimit
    (hypercoveringEquationBoundaryCoprodToFullCoprod n)
    (hypercoveringEquationBoundaryCoprodToBoundaryCylinder n)

/-- The colimit structure `hypercoveringEquationPushoutIsColimit` computes the universal morphism
to any cocone over the pushout diagram as the canonical `pushout.desc`. -/
theorem hypercoveringEquationPushoutIsColimit_desc
    (n : ℕ)
    (s :
      PushoutCocone
        (hypercoveringEquationBoundaryCoprodToFullCoprod n)
        (hypercoveringEquationBoundaryCoprodToBoundaryCylinder n)) :
    (hypercoveringEquationPushoutIsColimit n).desc s =
      pushout.desc s.inl s.inr s.condition := sorry

/-- Maps from the pushout owner of diagram `25.9.1.2` into a simplicial set form the pullback of
the two restriction maps from the two source pieces. This is the simplicial-set universal-property
bridge behind the source's object-level identification of the fibre product with `Hom(U, L)_0`. -/
noncomputable abbrev hypercoveringEquationPushoutHomEquiv
    (n : ℕ) (L : SSet) :
    (hypercoveringEquationPushout n ⟶ L) ≃
      Types.PullbackObj
        (fun f : hypercoveringEquationFullCoprod n ⟶ L ↦
          hypercoveringEquationBoundaryCoprodToFullCoprod n ≫ f)
        (fun g : hypercoveringEquationBoundaryCylinder n ⟶ L ↦
          hypercoveringEquationBoundaryCoprodToBoundaryCylinder n ≫ g) :=
  PullbackCone.IsLimit.equivPullbackObj
    ((pushout.cocone
        (hypercoveringEquationBoundaryCoprodToFullCoprod n)
        (hypercoveringEquationBoundaryCoprodToBoundaryCylinder n)).isColimitYonedaEquiv.toFun
      (hypercoveringEquationPushoutIsColimit n) L)

end CategoryTheory
