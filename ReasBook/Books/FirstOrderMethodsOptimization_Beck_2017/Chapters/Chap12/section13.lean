import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_13 (from Chap12) -/
open scoped BigOperators

noncomputable section

section

open Matrix

variable {rows cols : ℕ}

local notation "Mmn" => Matrix (Fin rows) (Fin cols) ℝ
local notation "PixelIndex" => Fin rows × Fin cols

/- Definition 12.13 is `source-facing`: it introduces the two concrete matrix regularizers
`TV_I` and `TV_l1` used in two-dimensional total-variation denoising.

For this item, the public owner is the matrix-side total-variation functional itself, written as a
finite sum of site contributions with the textbook boundary convention absorbed into the site term.
The boundary extensions below are only internal bookkeeping for those site formulas, while the
derived API records the explicit textbook interior/boundary expansions used downstream by
Definitions 12.21 and 12.22. -/

private def rightBoundaryExtension
    (x : Mmn) (i : Fin rows) (j : Fin cols) : ℝ :=
  if h : j.1 + 1 < cols then x i ⟨j.1 + 1, h⟩ else x i j

private def downBoundaryExtension
    (x : Mmn) (i : Fin rows) (j : Fin cols) : ℝ :=
  if h : i.1 + 1 < rows then x ⟨i.1 + 1, h⟩ j else x i j

/-- Helper for Definition 12.13: on an interior column, the right boundary extension advances to
the next column. -/
@[simp] private theorem rightBoundaryExtension_castSucc
    (x : Matrix (Fin rows) (Fin (cols + 1)) ℝ) (i : Fin rows) (j : Fin cols) :
    rightBoundaryExtension x i (Fin.castSucc j) = x i j.succ := by
  -- The interior branch of the boundary extension is active on every `castSucc` column.
  dsimp [rightBoundaryExtension]
  split_ifs with h
  · congr 1
  · exfalso
    exact h j.succ.is_lt

/-- Helper for Definition 12.13: on the last column, the right boundary extension fixes the
current entry. -/
@[simp] private theorem rightBoundaryExtension_last
    (x : Matrix (Fin rows) (Fin (cols + 1)) ℝ) (i : Fin rows) :
    rightBoundaryExtension x i (Fin.last cols) = x i (Fin.last cols) := by
  -- The last column falls into the boundary branch, so no forward step is taken.
  simp [rightBoundaryExtension]

/-- Helper for Definition 12.13: on an interior row, the downward boundary extension advances to
the next row. -/
@[simp] private theorem downBoundaryExtension_castSucc
    (x : Matrix (Fin (rows + 1)) (Fin cols) ℝ) (i : Fin rows) (j : Fin cols) :
    downBoundaryExtension x (Fin.castSucc i) j = x i.succ j := by
  -- The interior branch of the boundary extension is active on every `castSucc` row.
  dsimp [downBoundaryExtension]
  split_ifs with h
  · congr 1
  · exfalso
    exact h i.succ.is_lt

/-- Helper for Definition 12.13: on the last row, the downward boundary extension fixes the
current entry. -/
@[simp] private theorem downBoundaryExtension_last
    (x : Matrix (Fin (rows + 1)) (Fin cols) ℝ) (j : Fin cols) :
    downBoundaryExtension x (Fin.last rows) j = x (Fin.last rows) j := by
  -- The last row falls into the boundary branch, so no downward step is taken.
  simp [downBoundaryExtension]

/-- The isotropic site contribution
`sqrt ((x_(i,j) - x_(i,j+1))^2 + (x_(i,j) - x_(i+1,j))^2)` with the boundary conventions encoded
by the total-variation boundary extensions. -/
def isotropic_two_dimensional_total_variation_site_term
    (x : Mmn) (ij : PixelIndex) : ℝ :=
  let i := ij.1
  let j := ij.2
  let xij := x i j
  let right := rightBoundaryExtension x i j
  let down := downBoundaryExtension x i j
  Real.sqrt ((xij - right) ^ (2 : ℕ) + (xij - down) ^ (2 : ℕ))

/-- The anisotropic `ℓ¹` site contribution
`|x_(i,j) - x_(i,j+1)| + |x_(i,j) - x_(i+1,j)|` with the boundary conventions encoded by the
total-variation boundary extensions. -/
def anisotropic_two_dimensional_total_variation_site_term
    (x : Mmn) (ij : PixelIndex) : ℝ :=
  let i := ij.1
  let j := ij.2
  let xij := x i j
  let right := rightBoundaryExtension x i j
  let down := downBoundaryExtension x i j
  |xij - right| + |xij - down|

/-- Helper for Definition 12.13: at an interior site, the isotropic site term is the Euclidean
norm of the horizontal and vertical forward differences. -/
@[simp] private theorem isotropic_site_term_castSucc_castSucc
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) (i : Fin rows) (j : Fin cols) :
    isotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, Fin.castSucc j) =
      Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^ (2 : ℕ) +
        (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^ (2 : ℕ)) := by
  -- Both boundary extensions move to the adjacent interior entries.
  simp [isotropic_two_dimensional_total_variation_site_term]

/-- Helper for Definition 12.13: on the last row, the isotropic site term collapses to the
horizontal absolute difference. -/
@[simp] private theorem isotropic_site_term_last_row
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) (j : Fin cols) :
    isotropic_two_dimensional_total_variation_site_term x (Fin.last rows, Fin.castSucc j) =
      |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| := by
  -- The vertical difference vanishes on the last row, leaving a one-dimensional boundary term.
  calc
    isotropic_two_dimensional_total_variation_site_term x (Fin.last rows, Fin.castSucc j) =
        Real.sqrt ((x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ) ^ (2 : ℕ)) := by
      simp [isotropic_two_dimensional_total_variation_site_term]
    _ = |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| := by
      simpa using
        Real.sqrt_sq_eq_abs (x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ)

/-- Helper for Definition 12.13: on the last column, the isotropic site term collapses to the
vertical absolute difference. -/
@[simp] private theorem isotropic_site_term_last_col
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) (i : Fin rows) :
    isotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, Fin.last cols) =
      |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
  -- The horizontal difference vanishes on the last column, leaving a one-dimensional boundary
  -- term.
  calc
    isotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, Fin.last cols) =
        Real.sqrt ((x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)) ^ (2 : ℕ)) := by
      simp [isotropic_two_dimensional_total_variation_site_term]
    _ = |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
      simpa using
        Real.sqrt_sq_eq_abs (x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols))

/-- Helper for Definition 12.13: the isotropic site term at the bottom-right corner is zero. -/
@[simp] private theorem isotropic_site_term_last_last
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) :
    isotropic_two_dimensional_total_variation_site_term x (Fin.last rows, Fin.last cols) = 0 := by
  -- Both boundary extensions fix the corner entry, so both forward differences vanish.
  simp [isotropic_two_dimensional_total_variation_site_term]

/-- Helper for Definition 12.13: at an interior site, the anisotropic site term is the sum of the
absolute horizontal and vertical forward differences. -/
@[simp] private theorem anisotropic_site_term_castSucc_castSucc
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) (i : Fin rows) (j : Fin cols) :
    anisotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, Fin.castSucc j) =
      (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
        |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|) := by
  -- Both boundary extensions move to the adjacent interior entries.
  simp [anisotropic_two_dimensional_total_variation_site_term]

/-- Helper for Definition 12.13: on the last row, the anisotropic site term keeps only the
horizontal absolute difference. -/
@[simp] private theorem anisotropic_site_term_last_row
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) (j : Fin cols) :
    anisotropic_two_dimensional_total_variation_site_term x (Fin.last rows, Fin.castSucc j) =
      |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| := by
  -- The downward boundary extension fixes the last-row entry, so the vertical part is zero.
  simp [anisotropic_two_dimensional_total_variation_site_term]

/-- Helper for Definition 12.13: on the last column, the anisotropic site term keeps only the
vertical absolute difference. -/
@[simp] private theorem anisotropic_site_term_last_col
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) (i : Fin rows) :
    anisotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, Fin.last cols) =
      |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
  -- The rightward boundary extension fixes the last-column entry, so the horizontal part is zero.
  simp [anisotropic_two_dimensional_total_variation_site_term]

/-- Helper for Definition 12.13: the anisotropic site term at the bottom-right corner is zero. -/
@[simp] private theorem anisotropic_site_term_last_last
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) :
    anisotropic_two_dimensional_total_variation_site_term x (Fin.last rows, Fin.last cols) = 0 := by
  -- Both forward differences vanish at the corner.
  simp [anisotropic_two_dimensional_total_variation_site_term]

/-- Definition 12.13 (1): the isotropic two-dimensional total variation of a real matrix is the
finite sum of the isotropic site contributions over all pixels. -/
def isotropic_two_dimensional_total_variation (x : Mmn) : ℝ :=
  ∑ ij : PixelIndex, isotropic_two_dimensional_total_variation_site_term x ij

notation "TV_I" => isotropic_two_dimensional_total_variation

-- Proof sketch: unfold `TV_I`; it is definitionally the finite sum of the isotropic site terms.
/-- Evaluating `TV_I` rewrites it as the finite sum of the isotropic site contributions. -/
@[simp] theorem isotropic_two_dimensional_total_variation_apply
    (x : Mmn) :
    TV_I x =
      ∑ ij : PixelIndex, isotropic_two_dimensional_total_variation_site_term x ij := rfl

-- Proof sketch: when there are no rows, the index type is empty, so the isotropic site sum
-- vanishes.
/-- Evaluating `TV_I` on a matrix with no rows gives `0`. -/
@[simp] theorem isotropic_two_dimensional_total_variation_zero_rows
    (x : Matrix (Fin 0) (Fin cols) ℝ) :
    TV_I x = 0 := by
  -- With no rows, the site index set is empty.
  simp [isotropic_two_dimensional_total_variation]

-- Proof sketch: when there are no columns, the index type is empty, so the isotropic site sum
-- vanishes.
/-- Evaluating `TV_I` on a matrix with no columns gives `0`. -/
@[simp] theorem isotropic_two_dimensional_total_variation_zero_cols
    (x : Matrix (Fin rows) (Fin 0) ℝ) :
    TV_I x = 0 := by
  -- With no columns, the site index set is empty.
  simp [isotropic_two_dimensional_total_variation]

/-- Helper for Definition 12.13: on a nonempty matrix, the sum of isotropic site terms equals the
textbook interior-plus-boundary formula. -/
private theorem isotropic_two_dimensional_total_variation_site_sum_nonempty_expansion
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) :
    (∑ ij : Fin (rows + 1) × Fin (cols + 1),
        isotropic_two_dimensional_total_variation_site_term x ij) =
      ∑ i : Fin rows, ∑ j : Fin cols,
        Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^ (2 : ℕ) +
          (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^ (2 : ℕ)) +
      ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| +
      ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
  have h_interior_rows :
      ∑ i : Fin rows, ∑ j : Fin (cols + 1),
        isotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, j) =
      (∑ i : Fin rows, ∑ j : Fin cols,
        Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^
            (2 : ℕ) +
          (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^ (2 : ℕ))) +
        ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
    -- Split each interior row into its interior columns and its last-column boundary site.
    calc
      ∑ i : Fin rows, ∑ j : Fin (cols + 1),
          isotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, j) =
        ∑ i : Fin rows,
          ((∑ j : Fin cols,
              Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^
                  (2 : ℕ) +
                (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^
                  (2 : ℕ))) +
            |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)|) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Fin.sum_univ_castSucc]
          simp
      _ =
          (∑ i : Fin rows, ∑ j : Fin cols,
            Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^
                (2 : ℕ) +
              (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^ (2 : ℕ))) +
            ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
          rw [Finset.sum_add_distrib]
  have h_last_row :
      ∑ j : Fin (cols + 1),
        isotropic_two_dimensional_total_variation_site_term x (Fin.last rows, j) =
      ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| := by
    -- Split the last row into its interior columns and the vanishing bottom-right corner.
    rw [Fin.sum_univ_castSucc]
    simp
  -- Split the product index set into interior rows and the last row, then split columns inside
  -- the interior rows.
  rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  calc
    (∑ i : Fin rows, ∑ j : Fin (cols + 1),
        isotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, j)) +
      ∑ j : Fin (cols + 1),
        isotropic_two_dimensional_total_variation_site_term x (Fin.last rows, j) =
      ((∑ i : Fin rows, ∑ j : Fin cols,
          Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^
              (2 : ℕ) +
            (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^ (2 : ℕ))) +
          ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)|) +
        ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| := by
          rw [h_interior_rows, h_last_row]
    _ =
        ∑ i : Fin rows, ∑ j : Fin cols,
          Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^ (2 : ℕ) +
            (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^ (2 : ℕ)) +
        ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| +
        ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
          simp [add_left_comm, add_comm]

-- Proof sketch: unfold `TV_I`; it is exactly the sum over the isotropic site terms.
/-- The isotropic total variation is the finite sum of the isotropic site terms over all matrix
entries, with the boundary conventions absorbed into the site term itself. -/
theorem isotropic_two_dimensional_total_variation_eq_sum_site_terms
    (x : Mmn) :
    TV_I x =
      ∑ ij : Fin rows × Fin cols, isotropic_two_dimensional_total_variation_site_term x ij := rfl

-- Proof sketch: unfold `TV_I` and then split the site sum into interior, last-row, and
-- last-column contributions.
/-- Expanding `TV_I` on a nonempty `(rows + 1) × (cols + 1)` matrix yields the textbook isotropic
two-dimensional total-variation formula in full. -/
theorem isotropic_two_dimensional_total_variation_formula
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) :
    TV_I x =
      ∑ i : Fin rows, ∑ j : Fin cols,
        Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^ (2 : ℕ) +
          (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^ (2 : ℕ)) +
      ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| +
      ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
  -- The public formula is exactly the nonempty expansion of the isotropic site sum.
  simpa [isotropic_two_dimensional_total_variation] using
    isotropic_two_dimensional_total_variation_site_sum_nonempty_expansion x

/-- Definition 12.13 (2): the anisotropic `ℓ¹`-based two-dimensional total variation of a real
matrix is the finite sum of the anisotropic site contributions over all pixels. -/
def anisotropic_two_dimensional_total_variation (x : Mmn) : ℝ :=
  ∑ ij : PixelIndex, anisotropic_two_dimensional_total_variation_site_term x ij

notation "TV_l1" => anisotropic_two_dimensional_total_variation

-- Proof sketch: unfold `TV_l1`; it is definitionally the finite sum of the anisotropic site
-- terms.
/-- Evaluating `TV_l1` rewrites it as the finite sum of the anisotropic site contributions. -/
@[simp] theorem anisotropic_two_dimensional_total_variation_apply
    (x : Mmn) :
    TV_l1 x =
      ∑ ij : PixelIndex, anisotropic_two_dimensional_total_variation_site_term x ij := rfl

-- Proof sketch: when there are no rows, the index type is empty, so the anisotropic site sum
-- vanishes.
/-- Evaluating `TV_l1` on a matrix with no rows gives `0`. -/
@[simp] theorem anisotropic_two_dimensional_total_variation_zero_rows
    (x : Matrix (Fin 0) (Fin cols) ℝ) :
    TV_l1 x = 0 := by
  -- With no rows, the site index set is empty.
  simp [anisotropic_two_dimensional_total_variation]

-- Proof sketch: when there are no columns, the index type is empty, so the anisotropic site sum
-- vanishes.
/-- Evaluating `TV_l1` on a matrix with no columns gives `0`. -/
@[simp] theorem anisotropic_two_dimensional_total_variation_zero_cols
    (x : Matrix (Fin rows) (Fin 0) ℝ) :
    TV_l1 x = 0 := by
  -- With no columns, the site index set is empty.
  simp [anisotropic_two_dimensional_total_variation]

/-- Helper for Definition 12.13: on a nonempty matrix, the sum of anisotropic site terms equals
the textbook interior-plus-boundary formula. -/
private theorem anisotropic_two_dimensional_total_variation_site_sum_nonempty_expansion
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) :
    (∑ ij : Fin (rows + 1) × Fin (cols + 1),
        anisotropic_two_dimensional_total_variation_site_term x ij) =
      ∑ i : Fin rows, ∑ j : Fin cols,
        (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
          |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|) +
      ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| +
      ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
  have h_interior_rows :
      ∑ i : Fin rows, ∑ j : Fin (cols + 1),
        anisotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, j) =
      (∑ i : Fin rows, ∑ j : Fin cols,
        (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
          |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|)) +
        ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
    -- Split each interior row into its interior columns and its last-column boundary site.
    calc
      ∑ i : Fin rows, ∑ j : Fin (cols + 1),
          anisotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, j) =
        ∑ i : Fin rows,
          ((∑ j : Fin cols,
              (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
                |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|)) +
            |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)|) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Fin.sum_univ_castSucc]
          simp
      _ =
          (∑ i : Fin rows, ∑ j : Fin cols,
            (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
              |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|)) +
            ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
          rw [Finset.sum_add_distrib]
  have h_last_row :
      ∑ j : Fin (cols + 1),
        anisotropic_two_dimensional_total_variation_site_term x (Fin.last rows, j) =
      ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| := by
    -- Split the last row into its interior columns and the vanishing bottom-right corner.
    rw [Fin.sum_univ_castSucc]
    simp
  -- Split the product index set into interior rows and the last row, then split columns inside
  -- the interior rows.
  rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  calc
    (∑ i : Fin rows, ∑ j : Fin (cols + 1),
        anisotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, j)) +
      ∑ j : Fin (cols + 1),
        anisotropic_two_dimensional_total_variation_site_term x (Fin.last rows, j) =
      ((∑ i : Fin rows, ∑ j : Fin cols,
          (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
            |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|)) +
          ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)|) +
        ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| := by
          rw [h_interior_rows, h_last_row]
    _ =
        ∑ i : Fin rows, ∑ j : Fin cols,
          (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
            |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|) +
        ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| +
        ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
          simp [add_assoc, add_comm]

-- Proof sketch: unfold `TV_l1`; it is exactly the sum over the anisotropic site terms.
/-- The anisotropic total variation is the finite sum of the anisotropic site terms over all
matrix entries, with the boundary conventions absorbed into the site term itself. -/
theorem anisotropic_two_dimensional_total_variation_eq_sum_site_terms
    (x : Mmn) :
    TV_l1 x =
      ∑ ij : Fin rows × Fin cols,
        anisotropic_two_dimensional_total_variation_site_term x ij := rfl

-- Proof sketch: unfold `TV_l1` and then split the site sum into interior, last-row, and
-- last-column contributions.
/-- Expanding `TV_l1` on a nonempty `(rows + 1) × (cols + 1)` matrix yields the textbook
anisotropic `ℓ¹`-based two-dimensional total-variation formula in full. -/
theorem anisotropic_two_dimensional_total_variation_formula
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) :
    TV_l1 x =
      ∑ i : Fin rows, ∑ j : Fin cols,
        (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
          |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|) +
      ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| +
      ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
  -- The public formula is exactly the nonempty expansion of the anisotropic site sum.
  simpa [anisotropic_two_dimensional_total_variation] using
    anisotropic_two_dimensional_total_variation_site_sum_nonempty_expansion x

end

/-! ### Proposition_12_13 (from Chap12) -/
noncomputable section

open scoped InnerProduct

section

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/- Proposition 12.13 is `source-facing` in the Chapter 6 proximal-norm-composition API.

Domain sampling against Definition 6.1, Example 6.19, Lemma 6.68, and the Euclidean-space
adjoint API shows the following owner split.

- `source-facing`: the fixed three-point-star difference matrix and the resulting inactive/active
  proximal branch formulas from Proposition 12.13.
- `core/canonical`: `prox[...]`, `norm_penalty`, the adjoint notation `†`, and the Gram operator
  `A ∘L A†`.
- `bridge/view`: the concrete Euclidean matrix realization
  `three_point_star_difference_matrix.toEuclideanLin.toContinuousLinearMap`.

The generic shifted-Gram root existence/uniqueness and proximal singleton formulas already live in
`Lemma_6_68`. This file therefore keeps only the fixed matrix/operator data and the proposition's
branch-local specialization of those Chapter 6 owner theorems, instead of duplicating a parallel
local chosen-root API. -/

/-- The fixed matrix `A = !![1, -1, 0; 1, 0, -1]` appearing in Proposition 12.13. -/
def three_point_star_difference_matrix : Matrix (Fin 2) (Fin 3) ℝ :=
  !![(1 : ℝ), -1, 0;
      1, 0, -1]

/-- The continuous linear map `x ↦ A x` attached to the fixed matrix of Proposition 12.13. -/
def three_point_star_difference_operator : E3 →L[ℝ] E2 :=
  three_point_star_difference_matrix.toEuclideanLin.toContinuousLinearMap

local notation "A" => three_point_star_difference_operator

/-- The Gram operator `A A†` attached to the fixed three-point-star difference map. -/
def three_point_star_difference_gram : E2 →L[ℝ] E2 :=
  A ∘L A†

local notation "G" => three_point_star_difference_gram

/-- The penalty `h(z) = ‖A z‖₂` attached to the fixed matrix in Proposition 12.13. -/
def three_point_star_difference_penalty : E3 → EReal :=
  norm_penalty 1 ∘ A

/-- Evaluating the penalty gives the textbook formula `h(z) = ‖A z‖₂`. -/
@[simp] theorem three_point_star_difference_penalty_eq (z : E3) :
    three_point_star_difference_penalty z = ((‖A z‖ : ℝ) : EReal) := by
  simp [three_point_star_difference_penalty, norm_penalty_apply]

/-- Helper for Proposition 12.13: the adjoint of the fixed operator is the transpose-matrix action
on `E2`. -/
lemma three_point_star_difference_operator_adjoint_eq_transpose :
    A† = three_point_star_difference_matrix.transpose.toEuclideanLin.toContinuousLinearMap := by
  -- Identify the Hilbert-space adjoint with the transpose matrix on Euclidean coordinates.
  calc
    A† =
        LinearMap.toContinuousLinearMap
          ((Matrix.toEuclideanLin three_point_star_difference_matrix).adjoint) := by
      simpa [three_point_star_difference_operator] using
        (LinearMap.adjoint_toContinuousLinearMap
          (Matrix.toEuclideanLin three_point_star_difference_matrix)).symm
    _ = three_point_star_difference_matrix.transpose.toEuclideanLin.toContinuousLinearMap := by
      simpa using
        congrArg LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin_conjTranspose_eq_adjoint
            three_point_star_difference_matrix).symm

/-- Helper for Proposition 12.13: the Gram operator `A A†` is the Euclidean action of the concrete
matrix `AAᵀ = !![2, 1; 1, 2]`. -/
lemma three_point_star_difference_gram_eq_concrete_matrix_operator :
    G =
      ((!![(2 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin.toContinuousLinearMap) := by
  -- Route correction: rewrite the abstract Gram operator into the concrete textbook matrix `AAᵀ`.
  have hgram :
      three_point_star_difference_matrix * three_point_star_difference_matrix.transpose =
        (!![(2 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) := by
    -- The fixed `2 × 3` matrix gives the displayed `2 × 2` Gram matrix by coordinate calculation.
    ext i j
    fin_cases i <;> fin_cases j
    · simp [three_point_star_difference_matrix, Matrix.mul_apply, Fin.sum_univ_three]
      norm_num
    · simp [three_point_star_difference_matrix, Matrix.mul_apply, Fin.sum_univ_three]
    · simp [three_point_star_difference_matrix, Matrix.mul_apply, Fin.sum_univ_three]
    · simp [three_point_star_difference_matrix, Matrix.mul_apply, Fin.sum_univ_three]
      norm_num
  -- Push the matrix identity through `Matrix.toEuclideanLin`.
  calc
    G =
        LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin
            (three_point_star_difference_matrix *
              three_point_star_difference_matrix.transpose)) := by
          rw [three_point_star_difference_gram,
            three_point_star_difference_operator_adjoint_eq_transpose]
          ext v i
          simp [three_point_star_difference_operator, Matrix.mulVec_mulVec]
    _ =
        LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin
            (!![(2 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ)) := by
          simp [hgram]

/-- Helper for Proposition 12.13: the concrete Gram matrix `!![2, 1; 1, 2]` has inverse
`(1 / 3) • !![2, -1; -1, 2]`. -/
lemma three_point_star_difference_gram_matrix_inverse_formula :
    (((!![(2 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) *
        ((1 / 3 : ℝ) • (!![(2 : ℝ), -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℝ))) = 1) ∧
      ((((1 / 3 : ℝ) • (!![(2 : ℝ), -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℝ)) *
        (!![(2 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ)) = 1) := by
  constructor
  · -- Verify the left inverse entrywise.
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · -- Verify the right inverse entrywise.
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Helper for Proposition 12.13: the concrete Gram operator is the Euclidean action of the matrix
`!![2, 1; 1, 2]`. -/
def three_point_star_difference_concrete_gram_operator : E2 →L[ℝ] E2 :=
  ((!![(2 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin.toContinuousLinearMap)

/-- Helper for Proposition 12.13: the explicit inverse candidate is the Euclidean action of
`(1 / 3) • !![2, -1; -1, 2]`. -/
def three_point_star_difference_concrete_gram_inverse_operator : E2 →L[ℝ] E2 :=
  LinearMap.toContinuousLinearMap <|
    Matrix.toEuclideanLin
      (((1 / 3 : ℝ) • (!![(2 : ℝ), -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℝ)))

/-- Helper for Proposition 12.13: the explicit inverse candidate is a left inverse of the concrete
Gram operator. -/
lemma three_point_star_difference_concrete_gram_left_inverse :
    three_point_star_difference_concrete_gram_operator ∘L
        three_point_star_difference_concrete_gram_inverse_operator =
      1 := by
  -- Evaluate the two coordinates directly and simplify the resulting linear expressions.
  ext v i
  fin_cases i
  · simp [three_point_star_difference_concrete_gram_operator,
      three_point_star_difference_concrete_gram_inverse_operator]
    ring_nf
    simp [Matrix.vecHead]
  · simp [three_point_star_difference_concrete_gram_operator,
      three_point_star_difference_concrete_gram_inverse_operator]
    ring_nf
    simp [Matrix.vecHead, Matrix.vecTail]

/-- Helper for Proposition 12.13: the explicit inverse candidate is also a right inverse of the
concrete Gram operator. -/
lemma three_point_star_difference_concrete_gram_right_inverse :
    three_point_star_difference_concrete_gram_inverse_operator ∘L
        three_point_star_difference_concrete_gram_operator =
      1 := by
  -- The reverse composition has the same coordinate verification.
  ext v i
  fin_cases i
  · simp [three_point_star_difference_concrete_gram_operator,
      three_point_star_difference_concrete_gram_inverse_operator]
    ring_nf
    simp [Matrix.vecHead]
  · simp [three_point_star_difference_concrete_gram_operator,
      three_point_star_difference_concrete_gram_inverse_operator]
    ring_nf
    simp [Matrix.vecHead, Matrix.vecTail]

/-- The Gram operator `A A†` of the fixed three-point-star difference map is invertible. -/
theorem three_point_star_difference_gram_isInvertible :
    three_point_star_difference_gram.IsInvertible := by
  let u : Units (E2 →L[ℝ] E2) :=
    { val := three_point_star_difference_concrete_gram_operator
      inv := three_point_star_difference_concrete_gram_inverse_operator
      val_inv := three_point_star_difference_concrete_gram_left_inverse
      inv_val := three_point_star_difference_concrete_gram_right_inverse }
  -- Repackage the explicit unit as a continuous linear equivalence for the Gram operator.
  rw [three_point_star_difference_gram_eq_concrete_matrix_operator]
  exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ E2 u, rfl⟩

/-- Scaling the fixed penalty by `λ` recovers the Chapter 6 owner `norm_penalty lam ∘ A`. -/
theorem scaled_three_point_star_difference_penalty_eq_norm_penalty_comp (lam : ℝ) :
    (fun z : E3 ↦ ((lam : EReal) * three_point_star_difference_penalty z)) =
      norm_penalty lam ∘ A := by
  funext z
  simp [three_point_star_difference_penalty, norm_penalty_apply]

/-- The active-branch scalar residual from Proposition 12.13,
`g(α) = ‖(A A† + α I)⁻¹ (A x)‖₂² - λ²`. -/
def three_point_star_difference_shift_residual (x : E3) (lam : ℝ) (α : ℝ) : ℝ :=
  ‖(G + α • 1).inverse (A x)‖ ^ 2 - lam ^ 2

/-- Expanding the active-branch scalar residual gives the textbook formula
`g(α) = ‖(A A† + α I)⁻¹ (A x)‖₂² - λ²`. -/
@[simp] theorem three_point_star_difference_shift_residual_eq
    (x : E3) (lam α : ℝ) :
    three_point_star_difference_shift_residual x lam α =
      ‖(G + α • 1).inverse (A x)‖ ^ 2 - lam ^ 2 :=
  rfl

/-- On the active branch, the scalar residual `g(α)` from Proposition 12.13 is strictly
decreasing on `[0, ∞)`. -/
theorem three_point_star_difference_shift_residual_strictAntiOn_nonneg
    (x : E3) (lam : ℝ) (hx : A x ≠ 0) :
    StrictAntiOn (three_point_star_difference_shift_residual x lam) (Set.Ici 0) := by
  intro α hα β hβ hlt
  dsimp [three_point_star_difference_shift_residual]
  exact sub_lt_sub_right
    ((gram_shift_inverse_norm_sq_strictAntiOn_nonneg
      A three_point_star_difference_gram_isInvertible x hx) hα hβ hlt) _

/-- Active-branch root equation used in Proposition 12.13: when
`λ < ‖(A A†)⁻¹ (A x)‖₂`, the decreasing residual
`g(α) = ‖(A A† + α I)⁻¹ (A x)‖₂² - λ²` has a unique positive root. -/
theorem existsUnique_three_point_star_difference_shift_residual_root
    (x : E3) (lam : ℝ) (hlam : 0 < lam)
    (hlarge : lam < ‖(G).inverse (A x)‖) :
    ∃! α : ℝ,
      0 < α ∧ three_point_star_difference_shift_residual x lam α = 0 := by
  rcases
      existsUnique_linear_image_norm_prox_shift
        A three_point_star_difference_gram_isInvertible lam hlam x hlarge with
    ⟨α, hα, hαuniq⟩
  refine ⟨α, ?_, ?_⟩
  · refine ⟨hα.1, ?_⟩
    have hsq :
        ‖(G + α • 1).inverse (A x)‖ ^ 2 = lam ^ 2 :=
      by
        simpa [three_point_star_difference_gram] using
          (gram_shift_inverse_norm_eq_iff_sq_eq A lam hlam x α).1 hα.2
    dsimp [three_point_star_difference_shift_residual]
    linarith
  · intro β hβ
    have hsq : ‖(G + β • 1).inverse (A x)‖ ^ 2 = lam ^ 2 := by
      have hzero := hβ.2
      dsimp [three_point_star_difference_shift_residual] at hzero
      linarith
    have hβnorm :
        ‖(A ∘L A† + β • 1).inverse (A x)‖ = lam := by
      exact (gram_shift_inverse_norm_eq_iff_sq_eq A lam hlam x β).2 <| by
        simpa [three_point_star_difference_gram] using hsq
    exact hαuniq β ⟨hβ.1, hβnorm⟩

/-- The unique positive root `α*` of the active-branch scalar residual from Proposition 12.13. -/
noncomputable def three_point_star_difference_active_shift
    (x : E3) (lam : ℝ) (hlam : 0 < lam)
    (hlarge : lam < ‖(G).inverse (A x)‖) : ℝ :=
  (existsUnique_three_point_star_difference_shift_residual_root x lam hlam hlarge).choose

/-- The active-branch root `α*` is the unique positive zero of the residual `g`. -/
theorem three_point_star_difference_active_shift_spec
    (x : E3) (lam : ℝ) (hlam : 0 < lam)
    (hlarge : lam < ‖(G).inverse (A x)‖) :
    0 < three_point_star_difference_active_shift x lam hlam hlarge ∧
      three_point_star_difference_shift_residual x lam
        (three_point_star_difference_active_shift x lam hlam hlarge) = 0 := by
  let hroot :=
    existsUnique_three_point_star_difference_shift_residual_root x lam hlam hlarge
  exact hroot.choose_spec.1

/-- The active-branch root `α*` from Proposition 12.13 is positive. -/
theorem three_point_star_difference_active_shift_pos
    (x : E3) (lam : ℝ) (hlam : 0 < lam)
    (hlarge : lam < ‖(G).inverse (A x)‖) :
    0 < three_point_star_difference_active_shift x lam hlam hlarge := by
  exact (three_point_star_difference_active_shift_spec x lam hlam hlarge).1

/-- The active-branch root `α*` solves the residual equation `g(α*) = 0`. -/
theorem three_point_star_difference_shift_residual_active_shift_eq_zero
    (x : E3) (lam : ℝ) (hlam : 0 < lam)
    (hlarge : lam < ‖(G).inverse (A x)‖) :
    three_point_star_difference_shift_residual x lam
      (three_point_star_difference_active_shift x lam hlam hlarge) = 0 := by
  exact (three_point_star_difference_active_shift_spec x lam hlam hlarge).2

/-- The active-branch root `α*` satisfies the textbook norm equation
`‖(A A† + α* I)⁻¹ (A x)‖₂ = λ`. -/
theorem three_point_star_difference_active_shift_norm_eq
    (x : E3) (lam : ℝ) (hlam : 0 < lam)
    (hlarge : lam < ‖(G).inverse (A x)‖) :
    ‖(G + three_point_star_difference_active_shift x lam hlam hlarge • 1).inverse (A x)‖ = lam := by
  have hzero :=
    three_point_star_difference_shift_residual_active_shift_eq_zero x lam hlam hlarge
  have hsq :
      ‖(G + three_point_star_difference_active_shift x lam hlam hlarge • 1).inverse (A x)‖ ^ 2 =
        lam ^ 2 := by
    dsimp [three_point_star_difference_shift_residual] at hzero
    linarith
  exact
    (gram_shift_inverse_norm_eq_iff_sq_eq
      A lam hlam x (three_point_star_difference_active_shift x lam hlam hlarge)).2 hsq

/-- Inactive branch of Proposition 12.13: if `‖(A A†)⁻¹ (A x)‖₂ ≤ λ`, then the proximal mapping of
`λ h` with `h(z) = ‖A z‖₂` is the singleton `{x - A† (A A†)⁻¹ A x}`. -/
theorem prox_three_point_star_difference_penalty_eq_inactive_singleton
    (x : E3) (lam : ℝ)
    (hsmall : ‖(G).inverse (A x)‖ ≤ lam) :
    prox[fun z : E3 ↦ ((lam : EReal) * three_point_star_difference_penalty z)] x =
      {x - (A†) ((G).inverse (A x))} := by
  rw [scaled_three_point_star_difference_penalty_eq_norm_penalty_comp]
  simpa [three_point_star_difference_gram] using
    prox_linear_image_norm_eq_singleton_of_le
      A three_point_star_difference_gram_isInvertible lam x hsmall

/-- Active branch of Proposition 12.13: if `λ < ‖(A A†)⁻¹ (A x)‖₂`, then the proximal mapping of
`λ h` with `h(z) = ‖A z‖₂` is the singleton
`{x - A† (A A† + α* I)⁻¹ A x}`, where `α*` is the unique positive root of the residual
equation from `existsUnique_three_point_star_difference_shift_residual_root`. -/
theorem prox_three_point_star_difference_penalty_eq_active_singleton
    (x : E3) (lam : ℝ) (hlam : 0 < lam)
    (hlarge : lam < ‖(G).inverse (A x)‖) :
    prox[fun z : E3 ↦ ((lam : EReal) * three_point_star_difference_penalty z)] x =
      {x - (A†) ((G + three_point_star_difference_active_shift x lam hlam hlarge • 1).inverse
        (A x))} := by
  rw [scaled_three_point_star_difference_penalty_eq_norm_penalty_comp]
  simpa [three_point_star_difference_gram] using
    prox_linear_image_norm_eq_singleton_of_shift
      A lam x
      (three_point_star_difference_active_shift x lam hlam hlarge)
      (three_point_star_difference_active_shift_pos x lam hlam hlarge)
      (three_point_star_difference_active_shift_norm_eq x lam hlam hlarge)

/-- Proposition 12.13: for the fixed three-point-star matrix `A`, the proximal mapping of the
scaled penalty `λ h` with `h(z) = ‖A z‖₂` is the singleton
`{x - A† (A A†)⁻¹ A x}` on the branch `‖(A A†)⁻¹ A x‖₂ ≤ λ`. On the complementary branch
`λ < ‖(A A†)⁻¹ A x‖₂`, the active-branch shift is the unique positive root `α*` of the
decreasing scalar residual `g(α) = ‖(A A† + α I)⁻¹ (A x)‖₂² - λ²`, and the proximal mapping is
the singleton `{x - A† (A A† + α* I)⁻¹ A x}`. In this Euclidean model, `A†` is the transpose
action `Aᵀ`. -/
theorem prox_three_point_star_difference_penalty_eq_piecewise
    (x : E3) (lam : ℝ) (hlam : 0 < lam) :
    (‖(G).inverse (A x)‖ ≤ lam →
      prox[fun z : E3 ↦ ((lam : EReal) * three_point_star_difference_penalty z)] x =
        {x - (A†) ((G).inverse (A x))}) ∧
    (∀ hlarge : lam < ‖(G).inverse (A x)‖,
      prox[fun z : E3 ↦ ((lam : EReal) * three_point_star_difference_penalty z)] x =
        {x - (A†) ((G + three_point_star_difference_active_shift x lam hlam hlarge • 1).inverse
          (A x))}) := by
  refine ⟨?_, ?_⟩
  · intro hsmall
    exact prox_three_point_star_difference_penalty_eq_inactive_singleton x lam hsmall
  · intro hlarge
    exact prox_three_point_star_difference_penalty_eq_active_singleton x lam hlam hlarge

end
