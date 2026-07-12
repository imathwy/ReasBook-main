import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.CommSq

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory
open SSet (ι₀ ι₁)
open scoped MonoidalCategory Simplicial

noncomputable section

universe u

namespace CategoryTheory

section

variable (n : ℕ)

-- This file is the source-facing owner for the simplicial-set square `25.9.1.2`; downstream
-- files should import it rather than redeclare the same four objects and four structure maps.

/-- The boundary coproduct object in the simplicial-set square `25.9.1.2`. -/
abbrev hypercoveringEquationBoundaryCoprod : SSet :=
  (∂Δ[n + 1] : SSet.{u}) ⨿ (∂Δ[n + 1] : SSet.{u})

/-- The full coproduct object in the simplicial-set square `25.9.1.2`. -/
abbrev hypercoveringEquationFullCoprod : SSet :=
  (Δ[n + 1] : SSet.{u}) ⨿ (Δ[n + 1] : SSet.{u})

/-- The boundary cylinder object in the simplicial-set square `25.9.1.2`, realized by the
cartesian product `(∂Δ[n + 1]) ⊗ Δ[1]`, i.e. the simplicial cylinder on
`∂Δ[n + 1]`. -/
abbrev hypercoveringEquationBoundaryCylinder : SSet :=
  (∂Δ[n + 1] : SSet.{u}) ⊗ Δ[1]

/-- The ambient cylinder object in the simplicial-set square `25.9.1.2`, realized by the
cartesian product `Δ[n + 1] ⊗ Δ[1]`, i.e. the simplicial cylinder on
`Δ[n + 1]`. -/
abbrev hypercoveringEquationCylinder : SSet :=
  (Δ[n + 1] : SSet.{u}) ⊗ Δ[1]

/-- The coproduct of the two boundary inclusions in the simplicial-set square `25.9.1.2`. -/
abbrev hypercoveringEquationBoundaryCoprodToFullCoprod :
    hypercoveringEquationBoundaryCoprod n ⟶ hypercoveringEquationFullCoprod n :=
  coprod.map ((∂Δ[n + 1]).ι) ((∂Δ[n + 1]).ι)

/-- The map from the boundary coproduct into the boundary cylinder given by the two endpoint inclusions. -/
abbrev hypercoveringEquationBoundaryCoprodToBoundaryCylinder :
    hypercoveringEquationBoundaryCoprod n ⟶ hypercoveringEquationBoundaryCylinder n :=
  coprod.desc
    (ι₀ : (∂Δ[n + 1] : SSet.{u}) ⟶ (∂Δ[n + 1] : SSet.{u}) ⊗ Δ[1])
    (ι₁ : (∂Δ[n + 1] : SSet.{u}) ⟶ (∂Δ[n + 1] : SSet.{u}) ⊗ Δ[1])

/-- The map from the full coproduct into the ambient cylinder given by the two endpoint inclusions. -/
abbrev hypercoveringEquationFullCoprodToCylinder :
    hypercoveringEquationFullCoprod n ⟶ hypercoveringEquationCylinder n :=
  coprod.desc
    (ι₀ : (Δ[n + 1] : SSet.{u}) ⟶ (Δ[n + 1] : SSet.{u}) ⊗ Δ[1])
    (ι₁ : (Δ[n + 1] : SSet.{u}) ⟶ (Δ[n + 1] : SSet.{u}) ⊗ Δ[1])

/-- The cylinder map induced by the boundary inclusion in the simplicial-set square `25.9.1.2`. -/
abbrev hypercoveringEquationBoundaryCylinderToCylinder :
    hypercoveringEquationBoundaryCylinder n ⟶ hypercoveringEquationCylinder n :=
  (∂Δ[n + 1]).ι ▷ (Δ[1] : SSet.{u})

/-- 25.9.1.2: the simplicial-set square displayed in the source, expressed as a `CommSq`,
commutes. -/
@[stacks 01GR]
theorem hypercoveringEquationDiagram :
    CommSq
      (hypercoveringEquationBoundaryCoprodToFullCoprod n)
      (hypercoveringEquationBoundaryCoprodToBoundaryCylinder n)
      (hypercoveringEquationFullCoprodToCylinder n)
      (hypercoveringEquationBoundaryCylinderToCylinder n) := by
  refine CommSq.mk ?_
  apply coprod.hom_ext <;>
    simp [hypercoveringEquationBoundaryCoprodToFullCoprod,
      hypercoveringEquationBoundaryCoprodToBoundaryCylinder,
      hypercoveringEquationFullCoprodToCylinder,
      hypercoveringEquationBoundaryCylinderToCylinder]

/-- The ambient cylinder maps in diagram `25.9.1.2` satisfy the cocone condition over the
displayed span. -/
@[stacks 01GR]
theorem hypercoveringEquationPushoutCocone_condition :
    hypercoveringEquationBoundaryCoprodToFullCoprod n ≫
        hypercoveringEquationFullCoprodToCylinder n =
      hypercoveringEquationBoundaryCoprodToBoundaryCylinder n ≫
        hypercoveringEquationBoundaryCylinderToCylinder n :=
  (hypercoveringEquationDiagram n).w

end

end CategoryTheory
