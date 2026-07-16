import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_15_7
import StacksProject_2024.stacks_project.Chap31.Lemma_31_16_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.support` as the canonical
-- closed-set owner for the support of an ideal-sheaf datum. Local Chapter 31 precedent already
-- uses `IsAffineOpen U`, `Dense (U : Set X)`, `X.IdealSheafData`, and the open complement
-- `⟨(((D.support : Closeds X) : Set X)ᶜ), D.support.2.isOpen_compl⟩` as the source-facing API.

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [X.IsSeparated]

/-- Lemma 31.16.6: let `X` be a Noetherian separated scheme and let `U ⊆ X` be a dense affine
open. If `\mathcal O_{X, x}` is a unique factorization domain for every `x ∈ X \ U`, then there
exists an effective Cartier divisor `D ⊆ X` whose open complement is exactly `U`. -/
@[stacks 0BCW]
theorem exists_effectiveCartierDivisor_of_dense_isAffineOpen_of_stalks_uniqueFactorizationMonoid
    {U : X.Opens} (hU : IsAffineOpen U) (hU_dense : Dense (U : Set X))
    (hUFD : ∀ x : X, x ∉ (U : Set X) → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ D : X.IdealSheafData,
      D.IsEffectiveCartierDivisor ∧
        U = ⟨(((D.support : Closeds X) : Set X)ᶜ), D.support.2.isOpen_compl⟩ := sorry

end AlgebraicGeometry.Scheme
