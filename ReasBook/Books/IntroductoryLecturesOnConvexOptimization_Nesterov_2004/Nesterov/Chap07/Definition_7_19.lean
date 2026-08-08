import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Nesterov.Chap05.Definition_5_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open RealSymmetricMatrixSpace
open scoped BigOperators RealSymmetricMatrixSpace

variable {n : ℕ}

/-- Definition 7.19: `spectral_eigenvalue_l1_unit_ball n` is the set `Q₂` of real symmetric
`n × n` matrices whose ordered eigenvalues satisfy `∑ i, |λ_i(X)| ≤ 1`. -/
def spectral_eigenvalue_l1_unit_ball (n : ℕ) : Set (𝕊^n) :=
  {X | ∑ i : Fin n, |eigenvalues X i| ≤ (1 : ℝ)}

-- Proof sketch: unfold `spectral_eigenvalue_l1_unit_ball`; membership is exactly the displayed
-- eigenvalue `ℓ₁`-bound from the definition of `Q₂`.
/-- Membership in `spectral_eigenvalue_l1_unit_ball n` means that the sum of the absolute values
of the ordered eigenvalues of `X` is at most `1`. -/
theorem mem_spectral_eigenvalue_l1_unit_ball_iff
    (X : 𝕊^n) :
    X ∈ spectral_eigenvalue_l1_unit_ball n ↔
      ∑ i : Fin n, |eigenvalues X i| ≤ (1 : ℝ) :=
  Iff.rfl
