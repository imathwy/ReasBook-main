import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

noncomputable section

-- Semantic recall / local precedent check:
-- `lean_leansearch` surfaced the topological generic-point owners `irreducibleComponents`,
-- `genericPoints`, and `genericPoints.ofComponent`.
-- The nearby precursor `29_52_2_1` fixes the source's maximum-over-components parameter `E`
-- through an `IsGreatest` hypothesis, and the source-facing statement below keeps that shape
-- while preserving the scheme-level locally Noetherian assumption.

/-- Lemma 29.52.2: let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of finite
type, let `x : X`, and let `E` be the maximum of the transcendence degrees
`trdeg_{κ(f(ξ))} κ(ξ)` as `ξ` ranges over the generic points of the irreducible components of `X`
containing `x`. Then
`dim (𝒪_{X, x}) + trdeg_{κ(f(x))} κ(x) ≤ dim (𝒪_{S, f(x)}) + E`.
This is the additive form equivalent to the displayed source inequality
`dim (𝒪_{X, x}) ≤ dim (𝒪_{S, f(x)}) + E - trdeg_{κ(f(x))} κ(x)`, which is the natural
formalization in the current `ringKrullDim` API. -/
@[stacks 0BAE]
theorem ringKrullDim_stalk_add_residueFieldTrdeg_le_ringKrullDim_stalk_image_add_maxGenericComponentTrdeg
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S]
    (x : X) (E : ℕ)
    (hE :
      IsGreatest
        { n : ℕ |
            ∃ Z : irreducibleComponents X,
              x ∈ (Z : Set X) ∧
                n =
                  Cardinal.toNat
                    (Algebra.trdeg
                      (S.residueField (f (genericPoints.ofComponent Z)))
                      (X.residueField (genericPoints.ofComponent Z))) }
        E) :
    ringKrullDim (X.presheaf.stalk x) +
        Cardinal.toNat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) ≤
      ringKrullDim (S.presheaf.stalk (f x)) + E := sorry

end
end AlgebraicGeometry
