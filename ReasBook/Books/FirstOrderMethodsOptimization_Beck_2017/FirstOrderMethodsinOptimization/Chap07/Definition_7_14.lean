import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap07.Definition_7_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {n : ℕ}

local notation "𝕊" => symmetricMatrices n

/- Definition 7.14 is `source-facing`: it defines a class of subsets of the symmetric-matrix space
by requiring their indicator functions to factor through the ordered eigenvalue map via the
indicator of a permutation symmetric set in `ℝ^n`. The owner abstractions already present in the
project for this are `extendedIndicator`, `IsPermutationSymmetricFunction`, and
`symmetricEigenvalues`. -/

/-- A set `C ⊆ ℝ^n` is associated to a set `T ⊆ 𝕊^n` when the indicator of `T` is the indicator of
`C` composed with the ordered eigenvalue map, and the indicator of `C` is permutation symmetric. -/
def IsAssociatedSymmetricSpectralSet (T : Set 𝕊) (C : Set (Fin n → ℝ)) : Prop :=
  IsPermutationSymmetricFunction (extendedIndicator C) ∧
    extendedIndicator T = extendedIndicator C ∘ symmetricEigenvalues

/-- Definition 7.14: a set `T ⊆ 𝕊^n` is symmetric spectral when its indicator function is the
indicator of a permutation symmetric set in `ℝ^n` composed with the ordered eigenvalue map; such
a set `C` is an associated set. -/
def IsSymmetricSpectralSet (T : Set 𝕊) : Prop :=
  ∃ C : Set (Fin n → ℝ), IsAssociatedSymmetricSpectralSet T C

-- Proof sketch: unfold `IsSymmetricSpectralSet`; the statement is exactly the existential
-- packaging of the associated-set relation introduced just above.
/-- A set in `𝕊^n` is symmetric spectral exactly when it admits an associated set in eigenvalue
coordinates. -/
theorem isSymmetricSpectralSet_iff_exists_associatedSet (T : Set 𝕊) :
    IsSymmetricSpectralSet T ↔ ∃ C : Set (Fin n → ℝ), IsAssociatedSymmetricSpectralSet T C := by
  -- The theorem just unpacks the existential content of `IsSymmetricSpectralSet`.
  rfl

end
