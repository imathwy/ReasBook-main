import Mathlib.AlgebraicGeometry.ValuativeCriterion

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

section

variable {X₀ S : Scheme.{u}} (f : X₀ ⟶ S)

/- 32.15.2.2: for the diagonal morphism `Δ : X₀ ⟶ X₀ ×[S] X₀`, the displayed solid diagram
`Spec(K) ⟶ X₀`
over
`Spec(A) ⟶ X₀ ×[S] X₀`
is the canonical valuative square `AlgebraicGeometry.ValuativeCommSq (pullback.diagonal f)`. -/
#check ValuativeCommSq (pullback.diagonal f)

namespace ValuativeCommSq

variable {f}
variable (sq : ValuativeCommSq (pullback.diagonal f))

/- Companion check: a chosen dotted arrow in the valuative square for the diagonal is a
`LiftStruct` for the underlying commutative square. -/
#check sq.commSq.LiftStruct

/-- A chosen lift of the valuative square for the diagonal composes with the first pullback
projection to the dotted arrow. -/
theorem diagonalLift_comp_fst (l : sq.commSq.LiftStruct) :
    sq.i₂ ≫ pullback.fst f f = l.l := by
  calc
    sq.i₂ ≫ pullback.fst f f = (l.l ≫ pullback.diagonal f) ≫ pullback.fst f f := by
      rw [l.fac_right]
    _ = l.l := by simp [Category.assoc]

/-- A chosen lift of the valuative square for the diagonal composes with the second pullback
projection to the dotted arrow. -/
theorem diagonalLift_comp_snd (l : sq.commSq.LiftStruct) :
    sq.i₂ ≫ pullback.snd f f = l.l := by
  calc
    sq.i₂ ≫ pullback.snd f f = (l.l ≫ pullback.diagonal f) ≫ pullback.snd f f := by
      rw [l.fac_right]
    _ = l.l := by simp [Category.assoc]

end ValuativeCommSq

end
