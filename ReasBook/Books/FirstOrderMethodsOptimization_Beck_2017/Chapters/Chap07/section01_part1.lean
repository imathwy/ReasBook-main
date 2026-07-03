import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_1 (from Chap07) -/
universe u

section

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/- Definition 7.1 is `source-facing`: it records invariance of a proper extended-real-valued
function under a chosen family of orthogonal symmetries of `ℝ^ι`. The `core/canonical` owner for
those symmetries in mathlib and this project is `Matrix.orthogonalGroup ι ℝ`, and the action on
`ι → ℝ` is the inherited matrix action. Primitive data are therefore just properness together with
invariance under every matrix in the chosen family. -/

/-- Definition 7.1: a proper extended-real-valued function on `ι → ℝ` is symmetric with respect to
a family `𝒜` of orthogonal matrices if it is invariant under the action of every element of `𝒜`. -/
class IsSymmetricFunction (𝒜 : Set (Matrix.orthogonalGroup ι ℝ))
    (f : (ι → ℝ) → EReal) : Prop extends IsProperExtendedRealFunction f where
  map_smul (A : Matrix.orthogonalGroup ι ℝ) (hA : A ∈ 𝒜) (x : ι → ℝ) :
    f (A • x) = f x

/-- The constant zero extended-real-valued function is symmetric with respect to any family of
orthogonal matrices. -/
instance (𝒜 : Set (Matrix.orthogonalGroup ι ℝ)) :
    IsSymmetricFunction 𝒜 (fun _ : ι → ℝ ↦ (0 : EReal)) := by
  refine
    { toIsProperExtendedRealFunction := ?_
      map_smul := ?_ }
  · refine
      { ne_bot := ?_
        effective_domain_nonempty := ?_ }
    · -- The constant zero function never attains `-∞`, so the first properness field is immediate.
      intro x
      simp
    · -- The zero vector lies in the effective domain because the function value there is finite.
      refine ⟨0, ?_⟩
      simp [effective_domain]
  · -- Symmetry follows because the function is constant, so both sides reduce to the same value.
    intro A hA x
    simp

end

/-! ### Proposition_7_1 (from Chap07) -/
open Matrix

noncomputable section

section

variable {n : ℕ}

/-- A real symmetric matrix is Hermitian. -/
-- Proof sketch: over `ℝ`, the conjugate transpose is the ordinary transpose, so `IsHermitian`
-- reduces to `IsSymm`.
theorem Matrix.IsSymm.isHermitian_of_real {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsSymm) :
    X.IsHermitian := by
  -- Over `ℝ`, Hermitian matrices are exactly symmetric matrices because conjugation is trivial.
  simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hX

/-- Proposition 7.1: every real symmetric matrix admits an orthogonal diagonalization whose
diagonal entries are the eigenvalues of the matrix. -/
-- Proof sketch: apply mathlib's Hermitian matrix spectral theorem to
-- `hX.isHermitian_of_real`, choose the orthogonal matrix
-- `hX.isHermitian_of_real.eigenvectorUnitary`, and rewrite the conjugate transpose over `ℝ` as the
-- ordinary transpose.
theorem symmetric_matrix_exists_orthogonal_diagonalization
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsSymm) :
    ∃ U : Matrix.orthogonalGroup (Fin n) ℝ,
      X = (U : Matrix (Fin n) (Fin n) ℝ) * diagonal (hX.isHermitian_of_real.eigenvalues) *
        (U : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
  let hH : X.IsHermitian := hX.isHermitian_of_real
  refine ⟨hH.eigenvectorUnitary, ?_⟩
  -- Route correction: use the Hermitian spectral theorem as the main skeleton, then rewrite the
  -- real conjugate-transpose expression into the orthogonal `U * diagonal * Uᵀ` form.
  simpa [hH, Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_eq_transpose_of_trivial,
    Function.comp_apply, mul_assoc] using hH.spectral_theorem

end
