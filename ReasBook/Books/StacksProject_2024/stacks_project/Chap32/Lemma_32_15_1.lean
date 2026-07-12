import Mathlib
import StacksProject_2024.Chap29.Definition_29_15_1
import StacksProject_2024.Chap29.Definition_29_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `LocallyOfFiniteType`,
-- `Scheme.residueField`, and `ValuativeCommSq`; nearby Chapter 32 uses `CommSq`,
-- `Scheme.fromSpecResidueField`, and `genericPointsOfIrreducibleComponents` for the
-- DVR-valuative generic-point statements.

/-- Lemma 32.15.1: let `f : X ⟶ Y` be of finite type, with `Y` locally Noetherian.
If `y` lies in the closure of the image of `f`, then there is a discrete valuation ring `A`
whose fraction field is the residue field of a generic point `η` of an irreducible component of
`X`, and a commutative valuative square
`Spec(κ(η)) ⟶ X` over `Spec(A) ⟶ Y`; the closed point of `Spec(A)` maps to `y`. -/
@[stacks 0CM2]
theorem exists_dvr_diagram_of_mem_closure_image
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Scheme.Hom.FiniteType f] [IsLocallyNoetherian Y]
    {y : Y} (hy : y ∈ closure (Set.range f.base)) :
    ∃ (η : genericPointsOfIrreducibleComponents X),
      ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
        (_ : Algebra A (X.residueField (η : X)))
        (_ : IsFractionRing A (X.residueField (η : X)))
        (toY : Spec (CommRingCat.of A) ⟶ Y),
          CommSq (X.fromSpecResidueField (η : X))
            (Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField (η : X))))) f toY ∧
          toY (IsLocalRing.closedPoint A) = y := sorry

end AlgebraicGeometry
