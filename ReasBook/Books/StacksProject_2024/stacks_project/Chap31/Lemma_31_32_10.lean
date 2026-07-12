import Mathlib
import StacksProject_2024.Chap29.Definition_29_50_1
import StacksProject_2024.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical topological owners `genericPoints`
-- and `genericPoints.ofComponent`; local Chapter 29/31 precedent uses the source-facing set
-- `genericPointsOfIrreducibleComponents` and records blowups by the morphism class `IsBlowup`.

/-- Lemma 31.32.10: let `X` be a scheme, let `I` define a closed subscheme `Z ⊆ X`, and let
`b : X' ⟶ X` be the blowing up of `X` along `Z`. Then `b` induces a bijection from the generic
points of irreducible components of `X'` to the generic points of irreducible components of `X`
which are not in `Z`, represented here by the complement of `I.support`. -/
@[stacks 0BFM]
theorem bijOn_genericPointsOfIrreducibleComponents_compl_support_of_isBlowup
    {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] :
    Set.BijOn b
      (genericPointsOfIrreducibleComponents X')
      (genericPointsOfIrreducibleComponents X ∩ (I.support : Set X)ᶜ) := sorry

end AlgebraicGeometry
