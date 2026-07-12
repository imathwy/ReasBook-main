import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

noncomputable section

-- Semantic recall / local precedent check:
-- `lean_leansearch` surfaced `topologicalKrullDim`, `Scheme.functionField`, `IsDominant`,
-- `LocallyOfFiniteType`, and the closed-map API. Nearby dimension-formula files in this chapter
-- use `Cardinal.toNat (Algebra.trdeg Y.functionField X.functionField)` for the function-field
-- transcendence degree.

/-- Lemma 29.52.4 (1): let `f : X ⟶ Y` be a dominant morphism of integral schemes, with `Y`
locally Noetherian and `f` locally of finite type. Then
`dim(X) ≤ dim(Y) + trdeg_{R(Y)} R(X)`. -/
@[stacks 02JX]
theorem topologicalKrullDim_le_topologicalKrullDim_target_add_functionFieldTrdeg
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [Algebra Y.functionField X.functionField] :
    topologicalKrullDim X ≤
      topologicalKrullDim Y +
        (Cardinal.toNat (Algebra.trdeg Y.functionField X.functionField) : WithBot ℕ∞) := sorry

/-- Lemma 29.52.4 (2): under the hypotheses of the first part, if `f` is closed as a map of
topological spaces, then `dim(X) = dim(Y) + trdeg_{R(Y)} R(X)`. -/
@[stacks 02JX]
theorem topologicalKrullDim_eq_topologicalKrullDim_target_add_functionFieldTrdeg_of_isClosedMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [Algebra Y.functionField X.functionField]
    (hclosed : IsClosedMap f.base) :
    topologicalKrullDim X =
      topologicalKrullDim Y +
        (Cardinal.toNat (Algebra.trdeg Y.functionField X.functionField) : WithBot ℕ∞) := sorry

end

end AlgebraicGeometry
