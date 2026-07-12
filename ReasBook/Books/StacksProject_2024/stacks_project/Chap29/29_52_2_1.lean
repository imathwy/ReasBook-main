import StacksProject_2024.Chap29.Lemma_29_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

-- Semantic recall / source-core-bridge triage:
-- `29.52.2.1` is not a second owner; it is exactly the source-facing Chapter 29 theorem already
-- recorded as
-- `ringKrullDim_stalk_add_residueFieldTrdeg_le_ringKrullDim_stalk_image_add_maxGenericComponentTrdeg`
-- in `Lemma_29_52_2.lean`. The current workspace rebuilds that owner import from source, so this
-- file keeps the cheaper non-owner recall shape by checking the exact source-facing proposition
-- directly rather than duplicating a local theorem.

/- 29.52.2.1: if `f : X ⟶ S` is locally of finite type, `S` is locally Noetherian, `x : X` has
image `s = f x`, and `E` is the maximum of the transcendence degrees
`trdeg_{κ(f ξ)} κ(ξ)` over the generic points `ξ` of the irreducible components of `X`
containing `x`, then
`dim (𝒪_{X, x}) + trdeg_{κ(s)} κ(x) ≤ dim (𝒪_{S, s}) + E`, equivalently
`dim (𝒪_{X, x}) ≤ dim (𝒪_{S, s}) + E - trdeg_{κ(s)} κ(x)`. -/
#check ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S]
    (x : X) (E : ℕ),
    IsGreatest
        {n : ℕ |
          ∃ Z : irreducibleComponents X,
            x ∈ (Z : Set X) ∧
              n =
                Cardinal.toNat
                  (Algebra.trdeg
                    (S.residueField (f (genericPoints.ofComponent Z)))
                    (X.residueField (genericPoints.ofComponent Z)))} E →
      ringKrullDim (X.presheaf.stalk x) +
          Cardinal.toNat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) ≤
        ringKrullDim (S.presheaf.stalk (f x)) + E
