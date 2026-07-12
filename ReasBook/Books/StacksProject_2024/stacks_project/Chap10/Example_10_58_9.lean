import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_58_1
import StacksProject_2024.Chap10.Proposition_10_58_7

-- Declarations for this item will be appended below by the statement pipeline.

open HomogeneousIdeal
open scoped DirectSum

noncomputable section

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

/- Definition 10.58.3: the notion of a numerical polynomial used in Example 10.58.9 is the
canonical project definition `IsNumericalPolynomial`. -/
recall IsNumericalPolynomial {A : Type u} [AddCommGroup A] (f : ℤ → A) : Prop

/-- The standard nonnegative grading on `k[X₁, …, X_d]` shifts an integer grading on a graded
module by addition. -/
local instance : AddAction ℕ ℤ where
  vadd n d := (n : ℤ) + d
  zero_vadd := by
    intro d
    change ((0 : ℕ) : ℤ) + d = d
    simp
  add_vadd := by
    intro m n d
    change (((m + n : ℕ) : ℤ) + d) = ((m : ℤ) + ((n : ℤ) + d))
    simp [Nat.cast_add, add_assoc]

section

variable {k : Type u} [Field k] {d : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (MvPolynomial (Fin d) k) M]
variable [Module k M] [IsScalarTower k (MvPolynomial (Fin d) k) M]
variable (ℳ : ℤ → Submodule (MvPolynomial (Fin d) k) M)
variable [DirectSum.Decomposition ℳ]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin d) k) ℳ]
variable [Module.Finite (MvPolynomial (Fin d) k) M]

local notation "S" => MvPolynomial (Fin d) k
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin d) k

-- Proof sketch: convert the standard generated-in-degree-one hypothesis for `k[X₁, …, X_d]` to
-- `Ideal.span (S₁) = S₊` via Lemma `10.58.1`, apply Proposition `10.58.7` to the owner-valued
-- function `n ↦ [Mₙ] ∈ K'_0(S₀)`, and then compose with the canonical length map
-- `K'_0(S₀) → ℤ`. For the standard grading, this length map is exactly
-- `n ↦ dim_k(M_n)`.
/-- Example 10.58.9: a finitely generated graded module over the standard graded polynomial ring
`k[X₁, …, X_d]`, represented by `MvPolynomial (Fin d) k`, has a Hilbert function
`n ↦ dim_k(M_n)` which is a numerical polynomial. -/
theorem graded_mvPolynomial_module_dimension_isNumericalPolynomial :
    IsNumericalPolynomial (fun n ↦ (Module.finrank k (ℳ n) : ℤ)) := by
  have hgenerated : Algebra.adjoin (𝒜 0) (𝒜 1 : Set S) = ⊤ := by
    sorry
  have hspan : Ideal.span (𝒜 1 : Set S) = 𝒜₊.toIdeal :=
    (homogeneous_adjoin_eq_top_iff_span_eq_irrelevant 𝒜 (𝒜 1 : Set S)
      (fun _ hx ↦ ⟨1, by simp, hx⟩)).1 hgenerated
  have howner :
      IsNumericalPolynomial (gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ) := by
    exact
      gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_span_degreeOne_eq_irrelevant
        𝒜 ℳ hspan
  -- Identify the owner-valued Hilbert function `n ↦ [Mₙ] ∈ K'_0(S₀)` with the usual
  -- dimension function `n ↦ dim_k(M_n)` by passing to the canonical degree-zero comparison map.
  sorry

end
