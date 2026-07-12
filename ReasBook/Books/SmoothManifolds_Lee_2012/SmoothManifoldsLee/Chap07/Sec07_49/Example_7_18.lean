import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic.Recall
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Maps.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MatrixGroups
open Matrix

noncomputable section

-- Domain sampling:
-- * primary domain: matrix Lie groups and subgroup embeddings inside `GL` and `ℂˣ`;
-- * core owners: `GL(n, ℝ)⁺`, `Circle.toUnits`, and `Matrix.SpecialLinearGroup.toGL`;
-- * genuinely local primitive data: only the complex-to-real block matrix construction below.
-- The redundant local `OpenSubgroup` packaging of `GL(n, ℝ)⁺` and the unused circle-range alias
-- are therefore removed in favor of the canonical owners.

/-- The `2 × 2` real block associated to a complex number `a + ib`. -/
def complex_entry_block (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![z.re, -z.im; z.im, z.re]

/-- The block matrix obtained by replacing each complex entry of `A` by its associated real
`2 × 2` block. The target uses the canonically equivalent indexing type `Fin n × Fin 2` for
`2n` coordinates. -/
def complex_matrix_to_real_block (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
  fun p q ↦ complex_entry_block (A p.1 q.1) p.2 q.2

/-- Helper for Example 7.18: the block matrix construction sends the identity matrix to the
identity matrix. -/
lemma complex_matrix_to_real_block_map_one (n : ℕ) :
    complex_matrix_to_real_block n (1 : Matrix (Fin n) (Fin n) ℂ) =
      (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) := by
  -- Reduce the identity claim to the four entries in each `2 × 2` block.
  ext p q
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  by_cases hij : i = j
  · subst hij
    fin_cases a <;> fin_cases b <;> simp [complex_matrix_to_real_block, complex_entry_block]
  · fin_cases a <;> fin_cases b <;>
      simp [complex_matrix_to_real_block, complex_entry_block, hij]

/-- Helper for Example 7.18: the block matrix construction respects matrix multiplication. -/
lemma complex_matrix_to_real_block_map_mul (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    complex_matrix_to_real_block n (A * B) =
      complex_matrix_to_real_block n A * complex_matrix_to_real_block n B := by
  -- Check each block coordinate and expand the inner `Fin 2` sum explicitly.
  ext p q
  rcases p with ⟨i, a⟩
  rcases q with ⟨k, c⟩
  rw [complex_matrix_to_real_block, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  fin_cases a
  · fin_cases c
    · simp [complex_matrix_to_real_block, complex_entry_block, Complex.mul_re, Complex.mul_im,
        Fin.sum_univ_two, sub_eq_add_neg]
    · suffices h :
          -∑ x, ((A i x).re * (B x k).im + (A i x).im * (B x k).re) =
            ∑ x, (-((A i x).re * (B x k).im) + -((A i x).im * (B x k).re)) by
        simpa [complex_matrix_to_real_block, complex_entry_block, Complex.mul_re, Complex.mul_im,
          Fin.sum_univ_two, sub_eq_add_neg] using h
      calc
        -∑ x, ((A i x).re * (B x k).im + (A i x).im * (B x k).re) =
            ∑ x, -(((A i x).re * (B x k).im + (A i x).im * (B x k).re)) := by
              rw [← Finset.sum_neg_distrib]
        _ = ∑ x, (-((A i x).re * (B x k).im) + -((A i x).im * (B x k).re)) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
  · fin_cases c
    · suffices h :
          ∑ x, ((A i x).re * (B x k).im + (A i x).im * (B x k).re) =
            ∑ x, ((A i x).im * (B x k).re + (A i x).re * (B x k).im) by
        simpa [complex_matrix_to_real_block, complex_entry_block, Complex.mul_re, Complex.mul_im,
          Fin.sum_univ_two, sub_eq_add_neg] using h
      refine Finset.sum_congr rfl ?_
      intro x hx
      ring
    · suffices h :
          ∑ x, ((A i x).re * (B x k).re + -((A i x).im * (B x k).im)) =
            ∑ x, (-((A i x).im * (B x k).im) + (A i x).re * (B x k).re) by
        simpa [complex_matrix_to_real_block, complex_entry_block, Complex.mul_re, Complex.mul_im,
          Fin.sum_univ_two, sub_eq_add_neg] using h
      refine Finset.sum_congr rfl ?_
      intro x hx
      ring

/-- The entrywise complex-to-real block map is multiplicative. -/
def complex_matrix_to_real_block_hom (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ where
  toFun := complex_matrix_to_real_block n
  map_one' := complex_matrix_to_real_block_map_one n
  map_mul' := complex_matrix_to_real_block_map_mul n

/-- The block map on matrices sends invertible complex matrices to invertible real block matrices.
-/
def complex_generalLinear_to_real_generalLinear (n : ℕ) :
    GL (Fin n) ℂ →* GL (Fin n × Fin 2) ℝ :=
  Units.map (complex_matrix_to_real_block_hom n)

/-- Applying `complex_generalLinear_to_real_generalLinear` and forgetting invertibility recovers the
explicit real block matrix. -/
theorem complex_generalLinear_to_real_generalLinear_apply_val (n : ℕ) (A : GL (Fin n) ℂ) :
    (complex_generalLinear_to_real_generalLinear n A :
      Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) =
      complex_matrix_to_real_block n (A : Matrix (Fin n) (Fin n) ℂ) := rfl

/-- Part (1) of Example 7.18: `GL(n, ℝ)⁺` is an open subgroup of `GL(n, ℝ)`. -/
theorem real_generalLinear_pos_isOpenSubgroup (n : ℕ) :
    IsOpen (GL(n, ℝ)⁺ : Set (GL (Fin n) ℝ)) := by
  -- `GL(n, ℝ)⁺` is the determinant preimage of the open half-line `(0, ∞)`.
  let s : Set ℝˣ := {u | 0 < (u : ℝ)}
  have hs : IsOpen s := by
    simpa [s] using isOpen_Ioi.preimage Units.continuous_val
  simpa [Matrix.mem_glpos, s] using
    Matrix.GeneralLinearGroup.continuous_det.isOpen_preimage s hs

/-- Part (2) of Example 7.18: the canonical inclusion `S¹ ↪ ℂˣ`,
realized as `Circle.toUnits`, is a closed embedding. -/
theorem circle_toUnits_isClosedEmbedding :
    Topology.IsClosedEmbedding Circle.toUnits := by
  have hcont : Continuous Circle.toUnits := by
    -- Continuity follows from continuity of the value and inverse coordinates in `ℂ`.
    refine Units.continuous_iff.mpr ?_
    constructor
    · simpa [Circle.toUnits_apply] using
        (continuous_subtype_val : Continuous fun z : Circle ↦ (z : ℂ))
    · simpa [Circle.toUnits_apply] using
        (continuous_subtype_val.comp continuous_inv :
          Continuous fun z : Circle ↦ ((z⁻¹ : Circle) : ℂ))
  -- A continuous injective map from compact `S¹` into Hausdorff `ℂˣ` is a closed embedding.
  refine hcont.isClosedEmbedding ?_
  simpa [Circle.toUnits] using (unitSphereToUnits_injective (𝕜 := ℂ))

/- Example 7.18 (3): `SL(n, ℝ)` is the kernel of the determinant map on `GL(n, ℝ)`, expressed as
the range of `Matrix.SpecialLinearGroup.toGL`. -/
recall Matrix.SpecialLinearGroup.range_toGL

/-- Part (4) of Example 7.18: for positive `n`, the determinant map on `GL(n, ℝ)` is surjective. -/
theorem real_generalLinear_det_surjective (n : ℕ) [Fact (0 < n)] :
    Function.Surjective (Matrix.GeneralLinearGroup.det : GL (Fin n) ℝ → ℝˣ) := by
  let i0 : Fin n := ⟨0, Fact.out⟩
  intro u
  let d : Fin n → ℝ := fun i ↦ if i = i0 then (u : ℝ) else 1
  have hdet : Matrix.det (Matrix.diagonal d) = u := by
    rw [Matrix.det_diagonal, Fintype.prod_eq_single i0]
    · simp [d]
    · intro i hi
      simp [d, hi]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) ?_, ?_⟩
  · rw [hdet]
    exact Units.ne_zero u
  · ext
    exact hdet

/-- Helper for Example 7.18: over a field and in positive size, `det : GL (Fin n) 𝕜 → 𝕜ˣ` is
surjective. -/
lemma generalLinear_det_surjective_of_pos {𝕜 : Type*} [Field 𝕜]
    (n : ℕ) [Fact (0 < n)] :
    Function.Surjective (Matrix.GeneralLinearGroup.det : GL (Fin n) 𝕜 → 𝕜ˣ) := by
  let i0 : Fin n := ⟨0, Fact.out⟩
  intro u
  let d : Fin n → 𝕜 := fun i ↦ if i = i0 then (u : 𝕜) else 1
  have hdet : Matrix.det (Matrix.diagonal d) = u := by
    -- The determinant is the product of the diagonal entries, with only the `0`-entry nontrivial.
    rw [Matrix.det_diagonal, Fintype.prod_eq_single i0]
    · simp [d]
    · intro i hi
      simp [d, hi]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) ?_, ?_⟩
  · rw [hdet]
    exact Units.ne_zero u
  · -- Forget to the underlying determinant to identify the chosen witness.
    ext
    exact hdet

/-- Helper for Example 7.18: recover a complex matrix from the `(0,0)` and `(1,0)` entries of each
real `2 × 2` block. -/
def recoverComplexMatrix (n : ℕ) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ → Matrix (Fin n) (Fin n) ℂ :=
  fun A i j ↦ (A (i, 0) (j, 0) : ℂ) + (A (i, 1) (j, 0) : ℂ) * Complex.I

/-- Helper for Example 7.18: the recovery map is a left inverse to the block construction. -/
lemma recoverComplexMatrix_leftInverse (n : ℕ) :
    Function.LeftInverse (recoverComplexMatrix n) (complex_matrix_to_real_block n) := by
  intro A
  -- Recover the real and imaginary parts from the first column of each `2 × 2` block.
  ext i j
  apply Complex.ext <;>
    simp [recoverComplexMatrix, complex_matrix_to_real_block, complex_entry_block]

/-- Helper for Example 7.18: the ambient complex-to-real block map is a closed embedding. -/
lemma complex_matrix_to_real_block_isClosedEmbedding (n : ℕ) :
    Topology.IsClosedEmbedding (complex_matrix_to_real_block n) := by
  have hleft := recoverComplexMatrix_leftInverse n
  have hforward : Continuous (complex_matrix_to_real_block n) := by
    -- The block map is coordinatewise in real and imaginary parts.
    refine continuous_matrix fun p q ↦ ?_
    rcases p with ⟨i, a⟩
    rcases q with ⟨j, b⟩
    have happly : Continuous fun A : Matrix (Fin n) (Fin n) ℂ ↦ A i j := by
      fun_prop
    fin_cases a <;> fin_cases b
    · simpa [complex_matrix_to_real_block, complex_entry_block] using
        Complex.continuous_re.comp happly
    · simpa [complex_matrix_to_real_block, complex_entry_block] using
        (Complex.continuous_im.comp happly).neg
    · simpa [complex_matrix_to_real_block, complex_entry_block] using
        Complex.continuous_im.comp happly
    · simpa [complex_matrix_to_real_block, complex_entry_block] using
        Complex.continuous_re.comp happly
  have hbackward : Continuous (recoverComplexMatrix n) := by
    -- The recovery map reads finitely many coordinates and recombines them linearly.
    refine continuous_matrix fun i j ↦ ?_
    have h00 : Continuous fun A : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ ↦ A (i, 0) (j, 0) := by
      fun_prop
    have h10 : Continuous fun A : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ ↦ A (i, 1) (j, 0) := by
      fun_prop
    simpa [recoverComplexMatrix] using
      (Complex.continuous_ofReal.comp h00).add
        ((Complex.continuous_ofReal.comp h10).mul continuous_const)
  exact hleft.isClosedEmbedding hbackward hforward

/- Example 7.18 (5): the inclusion `SL(n, ℝ) ↪ GL(n, ℝ)` is a closed embedding. -/
recall Matrix.SpecialLinearGroup.isClosedEmbedding_toGL

/-- Part (6) of Example 7.18: the complex-to-real block map
`β : GL(n, ℂ) → GL(2n, ℝ)`, represented using the canonically
equivalent index type `Fin n × Fin 2`, is injective. -/
theorem complex_generalLinear_to_real_generalLinear_injective (n : ℕ) :
    Function.Injective (complex_generalLinear_to_real_generalLinear n) := by
  intro A B hAB
  apply Matrix.GeneralLinearGroup.ext
  have hval :
      complex_matrix_to_real_block n (A : Matrix (Fin n) (Fin n) ℂ) =
        complex_matrix_to_real_block n (B : Matrix (Fin n) (Fin n) ℂ) := by
    -- Forgetting the unit structure reduces injectivity to the ambient matrix map.
    exact congrArg
      (fun g : GL (Fin n × Fin 2) ℝ => (g : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) hAB
  have hrecover := congrArg (recoverComplexMatrix n) hval
  have hmatrix : (A : Matrix (Fin n) (Fin n) ℂ) = (B : Matrix (Fin n) (Fin n) ℂ) := by
    calc
      (A : Matrix (Fin n) (Fin n) ℂ) =
          recoverComplexMatrix n
            (complex_matrix_to_real_block n (A : Matrix (Fin n) (Fin n) ℂ)) := by
            symm
            exact recoverComplexMatrix_leftInverse n (A : Matrix (Fin n) (Fin n) ℂ)
      _ =
          recoverComplexMatrix n
            (complex_matrix_to_real_block n (B : Matrix (Fin n) (Fin n) ℂ)) := by
            exact hrecover
      _ = (B : Matrix (Fin n) (Fin n) ℂ) := by
            exact recoverComplexMatrix_leftInverse n (B : Matrix (Fin n) (Fin n) ℂ)
  intro i j
  simpa using congrArg (fun M : Matrix (Fin n) (Fin n) ℂ ↦ M i j) hmatrix

/-- Example 7.18 (7): the block map `β` is a closed embedding into the ambient real general linear
group. -/
theorem complex_generalLinear_to_real_generalLinear_isClosedEmbedding (n : ℕ) :
    Topology.IsClosedEmbedding (complex_generalLinear_to_real_generalLinear n) := by
  -- First prove the ambient matrix map is a closed embedding, then lift it to units.
  simpa [complex_generalLinear_to_real_generalLinear] using
    (Topology.IsClosedEmbedding.units_map (f := complex_matrix_to_real_block_hom n)
      (complex_matrix_to_real_block_isClosedEmbedding n))

/- Example 7.18 (8): `SL(n, ℂ)` is the kernel of the determinant map on `GL(n, ℂ)`, expressed as
the range of `Matrix.SpecialLinearGroup.toGL`. -/
recall Matrix.SpecialLinearGroup.range_toGL

/-- Part (9) of Example 7.18: for positive `n`, the determinant map on `GL(n, ℂ)` is surjective. -/
theorem complex_generalLinear_det_surjective (n : ℕ) [Fact (0 < n)] :
    Function.Surjective (Matrix.GeneralLinearGroup.det : GL (Fin n) ℂ → ℂˣ) := by
  -- The same diagonal witness works over `ℂ`.
  simpa using (generalLinear_det_surjective_of_pos (𝕜 := ℂ) n)

/- Example 7.18 (10): the inclusion `SL(n, ℂ) ↪ GL(n, ℂ)` is a closed embedding. -/
recall Matrix.SpecialLinearGroup.isClosedEmbedding_toGL
