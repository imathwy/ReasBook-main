module

public import Book.Ch1.Remark_1_2_2.Reconstruction

public section

noncomputable section

namespace Tikhonov

universe u v

variable {m : Type u} {n : Type v}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]

/-- The discrepancy functional `D(α) = ‖K f_α - d‖` for Tikhonov reconstruction. -/
def discrepancy (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ) : ℝ :=
  ‖K.toEuclideanLin (reconstruction K α d) - d‖

/-- The defining formula for `Tikhonov.discrepancy`. -/
theorem discrepancy_eq (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ) :
    discrepancy K d α = ‖K.toEuclideanLin (reconstruction K α d) - d‖ := by
  simp [discrepancy]

/-- The discrepancy-principle parameter chosen from the unique nonnegative
solution of `discrepancy K d α = δ`. -/
def discrepancyParam (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (δ : ℝ)
    (h_existsUnique : ∃! α : ℝ, α ∈ Set.Ici 0 ∧ discrepancy K d α = δ) : ℝ :=
  Classical.choose h_existsUnique

/-- The chosen discrepancy parameter is nonnegative and satisfies the
discrepancy equation. -/
theorem discrepancyParam_spec (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (δ : ℝ)
    (h_existsUnique : ∃! α : ℝ, α ∈ Set.Ici 0 ∧ discrepancy K d α = δ) :
    discrepancyParam K d δ h_existsUnique ∈ Set.Ici 0 ∧
      discrepancy K d (discrepancyParam K d δ h_existsUnique) = δ := by
  simpa [discrepancyParam] using (Classical.choose_spec h_existsUnique).1

end Tikhonov
