import StacksProject_2024.stacks_project.Chap29.Definition_29_48_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_57_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

-- Semantic recall: local Chapter 29 precedent already fixes the source-facing owners
-- `IsFiniteLocallyFreeOfRank` for finite locally free degree,
-- `Scheme.Hom.degreesOfFibresBoundedBy` for fibrewise degree bounds, and
-- `Scheme.Hom.universallyBoundedFibres` for the existential reformulation.

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)

/-- Lemma 29.57.3: if `f` is a finite locally free morphism of degree `d`, then `d` bounds the
degree of the fibres of `f`. -/
@[stacks 0CC2]
theorem degreesOfFibresBoundedBy_of_isFiniteLocallyFreeOfRank
    [IsFiniteLocallyFreeOfRank f d] :
    degreesOfFibresBoundedBy f d := sorry

/-- For a finite locally free morphism of degree `d`, every fibre over a point of the base is
finite over the residue field of that point. -/
theorem isFinite_fiberToSpecResidueField_of_isFiniteLocallyFreeOfRank
    [IsFiniteLocallyFreeOfRank f d] (y : Y) :
    IsFinite (f.fiberToSpecResidueField y) :=
  (degreesOfFibresBoundedBy_of_isFiniteLocallyFreeOfRank f d).isFinite y

/-- For a finite locally free morphism of degree `d`, the degree of each fibre is at most `d`. -/
theorem fiberDegree_le_of_isFiniteLocallyFreeOfRank
    [IsFiniteLocallyFreeOfRank f d] (y : Y) :
    f.fiberDegree y ≤ d :=
  (degreesOfFibresBoundedBy_of_isFiniteLocallyFreeOfRank f d).fiberDegree_le y

/-- A finite locally free morphism of degree `d` has universally bounded fibres. -/
theorem universallyBoundedFibres_of_isFiniteLocallyFreeOfRank
    [IsFiniteLocallyFreeOfRank f d] :
    universallyBoundedFibres f :=
  ⟨d, degreesOfFibresBoundedBy_of_isFiniteLocallyFreeOfRank f d⟩

end Scheme.Hom
end AlgebraicGeometry
