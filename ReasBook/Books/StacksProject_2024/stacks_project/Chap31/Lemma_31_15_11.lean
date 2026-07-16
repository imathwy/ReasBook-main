import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_9_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_15_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Set TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.IdealSheafData

-- Semantic recall: `lean_leansearch` surfaced only ambient scheme/subscheme API here, while the
-- local Chapter 31 owner for sums of effective Cartier divisors is
-- `effectiveCartierDivisorWeightedSum` from `Lemma 31.15.8`. The source addendum “`X` regular”
-- uses the project owner `Scheme.Regular` from Chapter 28.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable {ι : Type v}

/-- Lemma 31.15.11 (1): let `X` be a Noetherian scheme and let `D ⊆ X` be an effective Cartier
divisor. If `D` is set-theoretically contained in the union of integral effective Cartier
divisors `Dᵢ`, then `D` is a finite weighted sum `\sum aᵢ Dᵢ`, expressed in the local owner by
`effectiveCartierDivisorWeightedSum`. -/
@[stacks 0BCP]
theorem eq_effectiveCartierDivisorWeightedSum_of_support_subset_iUnion
    [DecidableEq ι] (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (Dᵢ : ι → X.IdealSheafData) (hCartier : ∀ i, IsEffectiveCartierDivisor (Dᵢ i))
    (hIntegral : ∀ i, IsIntegral (Dᵢ i).subscheme)
    (hcover : (D.support : Set X) ⊆ ⋃ i, ((Dᵢ i).support : Set X)) :
    ∃ a : ι →₀ ℕ, D = effectiveCartierDivisorWeightedSum a Dᵢ := sorry

/-- Lemma 31.15.11 (2): in the situation of Lemma 31.15.11 (1), the existence of a family of
integral effective Cartier divisors whose union contains `D` set-theoretically is guaranteed if
every local ring `\mathcal O_{X,x}` for `x ∈ D` is a unique factorization domain. -/
@[stacks 0BCP]
theorem exists_family_integral_effectiveCartierDivisors_covering_support_of_stalks_uniqueFactorizationMonoid
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (hUFD : ∀ x : X, x ∈ D.support → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ ι : Type v,
      ∃ Dᵢ : ι → {E : X.IdealSheafData // IsEffectiveCartierDivisor E ∧ IsIntegral E.subscheme},
        (D.support : Set X) ⊆ ⋃ i, (((Dᵢ i).1).support : Set X) := sorry

/-- Lemma 31.15.11 (3): in the situation of Lemma 31.15.11 (1), the existence of a family of
integral effective Cartier divisors whose union contains `D` set-theoretically is guaranteed if
`X` is a regular scheme. -/
@[stacks 0BCP]
theorem exists_family_integral_effectiveCartierDivisors_covering_support_of_regular
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] [Regular X] :
    ∃ ι : Type v,
      ∃ Dᵢ : ι → {E : X.IdealSheafData // IsEffectiveCartierDivisor E ∧ IsIntegral E.subscheme},
        (D.support : Set X) ⊆ ⋃ i, (((Dᵢ i).1).support : Set X) := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
