import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Theorem_6_24

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Matrix Matrix.Norms.Frobenius

noncomputable section

section

variable {n : ℕ}

local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ

/- Proposition 7.4 is `source-facing`: the textbook projects a symmetric matrix onto the spectral
set associated with a vector-side set `C`. In this item file the ambient matrix space is expressed
directly as `Mₙ` with the Frobenius norm, while the chapter-level projection owner is the
set-valued map `Proj[...]`. The public statement below therefore records the spectral projection
formula as an image equality of projection sets, which specializes to the textbook singleton
formula under the closed-convex uniqueness assumptions. -/

/-- A real symmetric matrix is Hermitian. -/
-- Proof sketch: over `ℝ`, the conjugate transpose is the ordinary transpose, so `IsHermitian`
-- reduces to `IsSymm`.
theorem Matrix.IsSymm.isHermitian_of_real_raw {X : Mₙ} (hX : X.IsSymm) :
    X.IsHermitian := sorry

/-- The ordered eigenvalue map on real symmetric matrices, using the Hermitian eigenvalue list of
the underlying symmetric matrix. -/
noncomputable def symmetricEigenvaluesRaw (X : Mₙ) (hX : X.IsSymm) : Fin n → ℝ :=
  hX.isHermitian_of_real_raw.eigenvalues

-- Proof sketch: unfold `symmetricEigenvalues`; by definition it is the Hermitian eigenvalue list
-- attached to the symmetric matrix `X`.
/-- Evaluating `symmetricEigenvalues X hX` returns the ordered Hermitian eigenvalue list of `X`. -/
theorem symmetricEigenvaluesRaw_def (X : Mₙ) (hX : X.IsSymm) :
    symmetricEigenvaluesRaw X hX = hX.isHermitian_of_real_raw.eigenvalues := sorry

/-- The symmetric spectral set associated with `C`, consisting of the real symmetric matrices whose
ordered eigenvalue lists belong to `C`. -/
def symmetricSpectralSet (C : Set (Fin n → ℝ)) : Set Mₙ :=
  {X | ∃ hX : X.IsSymm, symmetricEigenvaluesRaw X hX ∈ C}

-- Proof sketch: unfold `symmetricSpectralSet`; membership is exactly the conjunction that `X` is
-- symmetric and that its ordered eigenvalue list belongs to `C`.
/-- A matrix lies in `symmetricSpectralSet C` exactly when it is symmetric and its ordered
eigenvalue list belongs to `C`. -/
theorem mem_symmetricSpectralSet_iff {C : Set (Fin n → ℝ)} {X : Mₙ} :
    X ∈ symmetricSpectralSet C ↔ ∃ hX : X.IsSymm, symmetricEigenvaluesRaw X hX ∈ C := sorry

/-- The orthogonal conjugate of a diagonal matrix with diagonal `x`. -/
noncomputable def orthogonalDiagonalMapRaw (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    (Fin n → ℝ) → Mₙ :=
  fun x ↦ (U : Mₙ) * Matrix.diagonal x * (U : Mₙ)ᵀ

-- Proof sketch: the diagonal matrix is symmetric, and conjugation by an orthogonal matrix
-- preserves symmetry under transpose.
/-- The matrix `orthogonalDiagonalMap U x` is symmetric. -/
theorem orthogonalDiagonalMapRaw_isSymm (U : Matrix.orthogonalGroup (Fin n) ℝ) (x : Fin n → ℝ) :
    (orthogonalDiagonalMapRaw U x).IsSymm := sorry

-- Proof sketch: write any competitor `Y` in the spectral set as an orthogonal conjugate of a
-- diagonal matrix whose diagonal lies in `C`, use orthogonal invariance of the Frobenius norm and
-- Fan's trace inequality to reduce the matrix minimization problem to the vector minimization
-- problem on `C`, and then conjugate the projected eigenvalue vector back by the fixed
-- diagonalizer `U`.
/-- Proposition 7.4: if `C` is nonempty, closed, and convex, then the projection set of a real
symmetric matrix `X` onto the associated symmetric spectral set is obtained by conjugating the
projection set of the ordered eigenvalue vector `λ(X)` by the same orthogonal diagonalizer `U`.
Under the closed-convex hypotheses, this is the set-valued form of equation `(7.6)`. -/
theorem projection_mapping_symmetricSpectralSet_eq_image_projection_mapping_eigenvalues
    (C : Set (Fin n → ℝ)) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (X : Mₙ) (hX : X.IsSymm)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (hdiag : X = orthogonalDiagonalMapRaw U (symmetricEigenvaluesRaw X hX)) :
    Proj[symmetricSpectralSet C] X =
      orthogonalDiagonalMapRaw U '' Proj[C] (symmetricEigenvaluesRaw X hX) := sorry

end
