import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_16_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the affine-open owner `IsAffineOpen`, and local
-- precedent in `Chap29/Lemma_29_11_12.lean` records “`X` has affine diagonal” as the instance
-- `[IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]`. This item keeps the `Lemma 31.16.6` conclusion and
-- source-faithfully weakens the ambient hypothesis from separatedness to affine diagonal.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]

/-- Lemma 31.16.7: let `X` be a Noetherian scheme with affine diagonal and let `U ⊆ X` be a
dense affine open. If `\mathcal O_{X, x}` is a unique factorization domain for every
`x ∈ X \ U`, then there exists an effective Cartier divisor `D ⊆ X` whose open complement is
exactly `U`. -/
@[stacks 0EGJ]
theorem exists_effectiveCartierDivisor_of_dense_isAffineOpen_of_affineDiagonal_of_stalks_uniqueFactorizationMonoid
    {U : X.Opens} (hU : IsAffineOpen U) (hU_dense : Dense (U : Set X))
    (hUFD : ∀ x : X, x ∉ (U : Set X) → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ D : X.IdealSheafData,
      D.IsEffectiveCartierDivisor ∧
        U = ⟨(((D.support : Closeds X) : Set X)ᶜ), D.support.2.isOpen_compl⟩ := sorry

end AlgebraicGeometry.Scheme
