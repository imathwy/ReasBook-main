import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Compactness.Compact

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: the primary owner abstractions here are mathlib's matrix-group carriers
-- `GL`, `SL`, `Matrix.unitaryGroup`, and `Matrix.specialUnitaryGroup`. The relevant upstream
-- declarations inspected before refinement were `Matrix.GeneralLinearGroup.mkOfDetNeZero`,
-- `Matrix.det_transvection_of_ne`, `Matrix.mem_unitaryGroup_iff'`, and
-- `Matrix.mem_specialUnitaryGroup_iff`. Primitive data are explicit matrices and membership in
-- those canonical owners; compactness and noncompactness are derived theorems.

open scoped Matrix.Norms.Elementwise MatrixGroups

local notation "U(" n ")" => Matrix.unitaryGroup (Fin n) ℂ
local notation "SU(" n ")" => Matrix.specialUnitaryGroup (Fin n) ℂ

/-- Helper for Problem 7-17: every matrix entry is bounded by the ambient matrix norm. -/
lemma norm_entry_le_matrixNorm {n : ℕ} {𝕜 : Type*} [NormedRing 𝕜]
    (A : Matrix (Fin n) (Fin n) 𝕜) (i j : Fin n) : ‖A i j‖ ≤ ‖A‖ := by
  -- First control the chosen entry by its row norm, then control that row by the matrix norm.
  exact (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

/-- Helper for Problem 7-17: the matrix image of `GL(Fin n, 𝕜)` is unbounded when `n > 0`. -/
lemma glMatrixRange_unbounded {n : ℕ} {𝕜 : Type*} [RCLike 𝕜] (hn : 0 < n) :
    ¬ Bornology.IsBounded (Set.range ((↑) : GL (Fin n) 𝕜 → Matrix (Fin n) (Fin n) 𝕜)) := by
  intro hbounded
  obtain ⟨C, hC⟩ := hbounded.subset_closedBall (0 : Matrix (Fin n) (Fin n) 𝕜)
  let i0 : Fin n := ⟨0, hn⟩
  let t : ℝ := ‖C‖ + 1
  have ht : C < t := lt_of_le_of_lt (le_abs_self C) (lt_add_of_pos_right ‖C‖ zero_lt_one)
  have ht0 : 0 < t := by
    positivity
  let u : 𝕜ˣ := Units.mk0 (t : 𝕜) (by
    exact_mod_cast (ne_of_gt ht0))
  let A : GL (Fin n) 𝕜 := Matrix.GeneralLinearGroup.scalar (Fin n) u
  have hA : ‖(A : Matrix (Fin n) (Fin n) 𝕜)‖ ≤ C := by
    -- Boundedness puts the whole range inside a closed ball centered at the origin.
    simpa [Metric.mem_closedBall, dist_eq_norm] using hC (Set.mem_range_self A)
  have hdiag : t ≤ ‖(A : Matrix (Fin n) (Fin n) 𝕜)‖ := by
    -- The chosen diagonal entry of the scalar matrix has norm `t`.
    have hentry := norm_entry_le_matrixNorm (A := (A : Matrix (Fin n) (Fin n) 𝕜)) i0 i0
    have hdiag' : ‖(t : 𝕜)‖ ≤ ‖(A : Matrix (Fin n) (Fin n) 𝕜)‖ := by
      simpa [A, u, t, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply] using hentry
    have hnorm : ‖(t : 𝕜)‖ = t := by
      simpa [RCLike.norm_ofReal, Real.norm_eq_abs] using abs_of_nonneg (le_of_lt ht0)
    exact hnorm.ge.trans hdiag'
  exact (not_le_of_gt ht) (hdiag.trans hA)

/-- Helper for Problem 7-17: the determinant-one matrices in `Matrix (Fin n) (Fin n) 𝕜`
are unbounded when `n > 1`. -/
lemma slMatrixRange_unbounded {n : ℕ} {𝕜 : Type*} [RCLike 𝕜] (hn : 1 < n) :
    ¬ Bornology.IsBounded ({A : Matrix (Fin n) (Fin n) 𝕜 | Matrix.det A = 1}) := by
  intro hbounded
  obtain ⟨C, hC⟩ := hbounded.subset_closedBall (0 : Matrix (Fin n) (Fin n) 𝕜)
  let i0 : Fin n := ⟨0, lt_trans Nat.zero_lt_one hn⟩
  let i1 : Fin n := ⟨1, hn⟩
  have hij : i0 ≠ i1 := by
    simp [i0, i1]
  let r : ℝ := ‖C‖ + 1
  have hr : C < r := lt_of_le_of_lt (le_abs_self C) (lt_add_of_pos_right ‖C‖ zero_lt_one)
  have hr0 : 0 < r := by
    positivity
  let t : 𝕜 := r
  let A : SL(n, 𝕜) :=
    ⟨Matrix.transvection i0 i1 t, by
      simpa [t] using Matrix.det_transvection_of_ne i0 i1 hij t⟩
  have hA : ‖(A : Matrix (Fin n) (Fin n) 𝕜)‖ ≤ C := by
    -- The transvection witness lies in the determinant-one carrier set.
    simpa [Metric.mem_closedBall, dist_eq_norm] using hC A.2
  have hentry : r ≤ ‖(A : Matrix (Fin n) (Fin n) 𝕜)‖ := by
    -- The chosen off-diagonal entry of the transvection matrix has norm `r`.
    have h := norm_entry_le_matrixNorm (A := (A : Matrix (Fin n) (Fin n) 𝕜)) i0 i1
    have h' : ‖(r : 𝕜)‖ ≤ ‖(A : Matrix (Fin n) (Fin n) 𝕜)‖ := by
      simpa [A, r, t, Matrix.transvection, hij] using h
    have hnorm : ‖(r : 𝕜)‖ = r := by
      simpa [RCLike.norm_ofReal, Real.norm_eq_abs] using abs_of_nonneg (le_of_lt hr0)
    exact hnorm.ge.trans h'
  exact (not_le_of_gt hr) (hentry.trans hA)

/-- Helper for Problem 7-17: every entry of a unitary matrix has norm at most `1`. -/
lemma norm_entry_le_one_of_mem_unitaryGroup {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (i j : Fin n) : ‖A i j‖ ≤ 1 := by
  -- Mathlib already packages the diagonal-entry argument for unitary matrices.
  simpa using entry_norm_bound_of_unitary hA i j

/-- Helper for Problem 7-17: the carrier of `U(n)` is closed in matrix space. -/
lemma isClosed_unitaryGroupCarrier (n : ℕ) :
    IsClosed (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  let f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun A ↦ star A * A
  have hf : Continuous f := by
    simpa [f] using continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  -- A matrix is unitary exactly when `star A * A = 1`.
  rw [show (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) = f ⁻¹' ({1} : Set _)
      by
        ext A
        simp [f, Matrix.mem_unitaryGroup_iff']]
  exact IsClosed.preimage hf isClosed_singleton

/-- Helper for Problem 7-17: the carrier of `SU(n)` is closed in matrix space. -/
lemma isClosed_specialUnitaryGroupCarrier (n : ℕ) :
    IsClosed (Matrix.specialUnitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hdet :
      IsClosed ((fun A : Matrix (Fin n) (Fin n) ℂ ↦ Matrix.det A) ⁻¹' ({1} : Set ℂ)) := by
    -- Determinant is continuous, so the determinant-one locus is closed.
    exact IsClosed.preimage continuous_id.matrix_det isClosed_singleton
  -- `SU(n)` is the intersection of the unitary condition with the determinant-one condition.
  rw [show (Matrix.specialUnitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
      (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩
        (fun A : Matrix (Fin n) (Fin n) ℂ ↦ Matrix.det A) ⁻¹' ({1} : Set ℂ) by
        ext A
        simp [Matrix.mem_specialUnitaryGroup_iff]]
  exact (isClosed_unitaryGroupCarrier n).inter hdet

/- Problem 7-17: the six declarations below classify the listed classical matrix Lie groups into
their compact and noncompact cases. -/

/-- Helper for Problem 7-17: `GL(n, ℝ)` is not compact for positive `n`. -/
lemma gl_real_not_compact {n : ℕ} (hn : 0 < n) :
    ¬ CompactSpace (GL (Fin n) ℝ) := by
  intro hcompact
  letI := hcompact
  -- A compact domain has compact, hence bounded, image in matrix space.
  have hbounded :
      Bornology.IsBounded
        (Set.range ((↑) : GL (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)) := by
    let f : GL (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ :=
      ((↑) : GL (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
    have hf : Continuous f := Units.continuous_val
    simpa [f] using (isCompact_range hf).isBounded
  exact glMatrixRange_unbounded (𝕜 := ℝ) hn hbounded

/-- Helper for Problem 7-17: `SL(n, ℝ)` is not compact for `n > 1`. -/
lemma sl_real_not_compact {n : ℕ} (hn : 1 < n) :
    ¬ CompactSpace (SL(n, ℝ)) := by
  intro hcompact
  letI := hcompact
  -- The same compact-image argument reduces the claim to an unbounded explicit family.
  have hbounded :
      Bornology.IsBounded
        ({A : Matrix (Fin n) (Fin n) ℝ | Matrix.det A = 1}) := by
    let f : SL(n, ℝ) → Matrix (Fin n) (Fin n) ℝ :=
      ((↑) : SL(n, ℝ) → Matrix (Fin n) (Fin n) ℝ)
    have hf : Continuous f := continuous_subtype_val
    have hrange : Set.range f = {A : Matrix (Fin n) (Fin n) ℝ | Matrix.det A = 1} := by
      ext A
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hA
        exact ⟨⟨A, hA⟩, rfl⟩
    rw [← hrange]
    exact (isCompact_range hf).isBounded
  exact slMatrixRange_unbounded (𝕜 := ℝ) hn hbounded

/-- Helper for Problem 7-17: `GL(n, ℂ)` is not compact for positive `n`. -/
lemma gl_complex_not_compact {n : ℕ} (hn : 0 < n) :
    ¬ CompactSpace (GL (Fin n) ℂ) := by
  intro hcompact
  letI := hcompact
  -- A compact domain has compact, hence bounded, image in matrix space.
  have hbounded :
      Bornology.IsBounded
        (Set.range ((↑) : GL (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)) := by
    let f : GL (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
      ((↑) : GL (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
    have hf : Continuous f := Units.continuous_val
    simpa [f] using (isCompact_range hf).isBounded
  exact glMatrixRange_unbounded (𝕜 := ℂ) hn hbounded

/-- Helper for Problem 7-17: `SL(n, ℂ)` is not compact for `n > 1`. -/
lemma sl_complex_not_compact {n : ℕ} (hn : 1 < n) :
    ¬ CompactSpace (SL(n, ℂ)) := by
  intro hcompact
  letI := hcompact
  -- The same compact-image argument reduces the claim to an unbounded explicit family.
  have hbounded :
      Bornology.IsBounded
        ({A : Matrix (Fin n) (Fin n) ℂ | Matrix.det A = 1}) := by
    let f : SL(n, ℂ) → Matrix (Fin n) (Fin n) ℂ :=
      ((↑) : SL(n, ℂ) → Matrix (Fin n) (Fin n) ℂ)
    have hf : Continuous f := continuous_subtype_val
    have hrange : Set.range f = {A : Matrix (Fin n) (Fin n) ℂ | Matrix.det A = 1} := by
      ext A
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hA
        exact ⟨⟨A, hA⟩, rfl⟩
    rw [← hrange]
    exact (isCompact_range hf).isBounded
  exact slMatrixRange_unbounded (𝕜 := ℂ) hn hbounded

/-- Helper for Problem 7-17: `U(n)` is compact. -/
lemma unitary_compact (n : ℕ) :
    CompactSpace (U(n)) := by
  let K : Set (Matrix (Fin n) (Fin n) ℂ) := (Metric.closedBall (0 : ℂ) 1).matrix
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).matrix
  have hsub : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ⊆ K := by
    -- Every entry of a unitary matrix lies in the closed unit ball.
    intro A hA
    simpa [K, Set.mem_matrix, Metric.mem_closedBall, dist_eq_norm] using
      (fun i j ↦ norm_entry_le_one_of_mem_unitaryGroup hA i j)
  have hcompactCarrier :
      IsCompact (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) :=
    hK.of_isClosed_subset (isClosed_unitaryGroupCarrier n) hsub
  -- Transfer compactness of the carrier set to the subtype `U(n)`.
  simpa using (isCompact_iff_compactSpace.mp hcompactCarrier)

/-- Helper for Problem 7-17: `SU(n)` is compact. -/
lemma special_unitary_compact (n : ℕ) :
    CompactSpace (SU(n)) := by
  let K : Set (Matrix (Fin n) (Fin n) ℂ) := (Metric.closedBall (0 : ℂ) 1).matrix
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).matrix
  have hsub :
      (Matrix.specialUnitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ⊆ K := by
    -- Special unitary matrices are unitary, so they satisfy the same entrywise bound.
    intro A hA
    simpa [K, Set.mem_matrix, Metric.mem_closedBall, dist_eq_norm] using
      (fun i j ↦
        norm_entry_le_one_of_mem_unitaryGroup
          (Matrix.specialUnitaryGroup_le_unitaryGroup hA) i j)
  have hcompactCarrier :
      IsCompact (Matrix.specialUnitaryGroup (Fin n) ℂ :
        Set (Matrix (Fin n) (Fin n) ℂ)) :=
    hK.of_isClosed_subset (isClosed_specialUnitaryGroupCarrier n) hsub
  -- Transfer compactness of the carrier set to the subtype `SU(n)`.
  simpa using (isCompact_iff_compactSpace.mp hcompactCarrier)

/-- Problem 7-17: `GL(n, ℝ)` and `GL(n, ℂ)` are noncompact for `n > 0`, `SL(n, ℝ)` and
`SL(n, ℂ)` are noncompact for `n > 1`, while `U(n)` and `SU(n)` are compact for every `n`. -/
theorem problem_7_17 :
    (∀ {n : ℕ}, 0 < n → ¬ CompactSpace (GL (Fin n) ℝ)) ∧
    (∀ {n : ℕ}, 1 < n → ¬ CompactSpace (SL(n, ℝ))) ∧
    (∀ {n : ℕ}, 0 < n → ¬ CompactSpace (GL (Fin n) ℂ)) ∧
    (∀ {n : ℕ}, 1 < n → ¬ CompactSpace (SL(n, ℂ))) ∧
    (∀ n : ℕ, CompactSpace (U(n))) ∧
    ∀ n : ℕ, CompactSpace (SU(n)) := by
  -- Package the six classification components into the single textbook summary entry.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact gl_real_not_compact hn
  · intro n hn
    exact sl_real_not_compact hn
  · intro n hn
    exact gl_complex_not_compact hn
  · intro n hn
    exact sl_complex_not_compact hn
  · intro n
    exact unitary_compact n
  · intro n
    exact special_unitary_compact n
