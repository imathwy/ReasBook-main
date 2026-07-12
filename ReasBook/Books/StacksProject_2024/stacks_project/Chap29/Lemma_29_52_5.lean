import Mathlib
import StacksProject_2024.Chap28.Lemma_28_10_2
import StacksProject_2024.Chap29.Lemma_29_52_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

noncomputable section

-- Semantic recall / local precedent check:
-- `lean_leansearch` did not surface a canonical scheme-dimension inequality for this exact Stacks
-- statement, but it did confirm the Noetherian finiteness surrounding irreducible components.
-- The source-facing owner here is therefore the global scheme dimension `topologicalKrullDim`,
-- with the generic-component transcendence-degree bound encoded by an explicit `sSup`.

/-- Lemma 29.52.5: let `f : X ⟶ Y` be a morphism of schemes. Assume `Y` is locally Noetherian and
`f` is locally of finite type. If `E` is the supremum of
`trdeg_{κ(f(ξ))}(κ(ξ))` as `ξ` ranges over the generic points of the irreducible components of
`X`, then `dim(X) ≤ dim(Y) + E`. -/
@[stacks 0BAG]
theorem topologicalKrullDim_le_topologicalKrullDim_target_add_sSup_genericComponentTrdeg
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y] (E : ℕ)
    (hE :
      sSup
          { n : ℕ |
              ∃ Z : irreducibleComponents X,
                n =
                  Cardinal.toNat
                    (Algebra.trdeg
                      (Y.residueField (f (genericPoints.ofComponent Z)))
                      (X.residueField (genericPoints.ofComponent Z))) } =
        E) :
    topologicalKrullDim X ≤ topologicalKrullDim Y + E := sorry

end

end AlgebraicGeometry
