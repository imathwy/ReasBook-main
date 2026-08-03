import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.UnitaryGroup
import BauschkeLean.Chap02.Fact_2_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Matrix
open WithLp
open scoped BigOperators Matrix.Norms.Frobenius InnerProductSpace

noncomputable section

-- Mathlib recall: `Matrix.IsHermitian.eigenvalues` is the canonical decreasing eigenvalue list,
-- and `Matrix.IsHermitian.spectral_theorem` provides the diagonalization surface used here.
-- Semantic search also surfaced `Matrix.frobenius_norm_def`; the source-facing statement below
-- keeps the spectral vector on the Euclidean side via `EuclideanSpace.equiv`.

namespace Matrix

/-- Over a trivial star ring such as `ℝ`, a symmetric matrix is Hermitian. This lets
source-facing symmetric statements reuse the canonical Hermitian spectral API. -/
theorem IsSymm.isHermitian [Star α] [TrivialStar α] {n : Type*} {A : Matrix n n α}
    (hA : A.IsSymm) : A.IsHermitian := by
  simpa [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using hA

end Matrix

/-- Helper for Fact 24.59: an antitone finite real vector is already its own nonincreasing
rearrangement. -/
private theorem nonincreasingRearrangement_eq_self_of_antitone
    {N : ℕ} {x : Fin N → ℝ} (hx : Antitone x) :
    nonincreasingRearrangement x = x := by
  -- Both sides are antitone permutations of the same finite tuple, so uniqueness of the sorted
  -- antitone permutation identifies them.
  simpa [nonincreasingRearrangement, Function.comp] using
    (Tuple.unique_antitone
      (f := x)
      (σ := Tuple.sort (OrderDual.toDual ∘ x))
      (τ := Equiv.refl (Fin N))
      (by
        simpa [nonincreasingRearrangement, Function.comp_assoc] using
          (antitone_nonincreasingRearrangement (x := x)))
      (by simpa [Function.comp] using hx))

/-- Helper for Fact 24.59: permuting an antitone vector does not change its canonical
nonincreasing rearrangement. -/
private theorem nonincreasingRearrangement_comp_perm_eq_of_antitone
    {N : ℕ} {x : Fin N → ℝ} (hx : Antitone x) (σ : Equiv.Perm (Fin N)) :
    nonincreasingRearrangement (x ∘ σ) = x := by
  -- The rearrangement of `x ∘ σ` is the unique antitone permutation of that tuple, and `x`
  -- itself is obtained back by composing with `σ.symm`.
  simpa [nonincreasingRearrangement, Function.comp_assoc] using
    (Tuple.unique_antitone
      (f := x ∘ σ)
      (σ := Tuple.sort (OrderDual.toDual ∘ (x ∘ σ)))
      (τ := σ.symm)
      (by
        simpa [nonincreasingRearrangement, Function.comp_assoc] using
          (antitone_nonincreasingRearrangement (x := x ∘ σ)))
      (by simpa [Function.comp_assoc] using hx))

/-- Helper for Fact 24.59: an orthogonal matrix satisfies `U * Uᵀ = 1`. -/
private theorem orthogonal_mul_transpose_eq_one
    {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℝ}
    (hU : U ∈ Matrix.orthogonalGroup n ℝ) :
    U * Uᵀ = 1 :=
  (Matrix.mem_orthogonalGroup_iff (A := U)).mp hU

/-- Helper for Fact 24.59: an orthogonal matrix satisfies `Uᵀ * U = 1`. -/
private theorem orthogonal_transpose_mul_eq_one
    {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℝ}
    (hU : U ∈ Matrix.orthogonalGroup n ℝ) :
    Uᵀ * U = 1 :=
  (Matrix.mem_orthogonalGroup_iff' (A := U)).mp hU

/-- Helper for Fact 24.59: equality in a rearrangement term yields a correction permutation that
preserves the strict-drop decomposition of the first antitone vector. -/
private theorem equality_term_has_prefix_preserving_correction
    {N : ℕ} {a b : Fin N → ℝ}
    (ha : Antitone a) (hb : Antitone b) (σ : Equiv.Perm (Fin N))
    (hEq : dotProduct a (b ∘ σ) = dotProduct a b) :
    ∃ ρ : Equiv.Perm (Fin N), a ∘ ρ = a ∧ b ∘ σ ∘ ρ = b := by
  have hEq' :
      dotProduct a (b ∘ σ) =
        dotProduct (nonincreasingRearrangement a) (nonincreasingRearrangement (b ∘ σ)) := by
    -- Rewrite both canonical rearrangements back to the already ordered vectors `a` and `b`.
    simpa [nonincreasingRearrangement_eq_self_of_antitone ha,
      nonincreasingRearrangement_comp_perm_eq_of_antitone hb σ] using hEq
  rcases (hardy_littlewood_polya_inequality_eq_iff
      (x := a) (y := b ∘ σ)).mp hEq' with ⟨ρ, hρa, hρb⟩
  refine ⟨ρ, ?_, ?_⟩
  · simpa [nonincreasingRearrangement_eq_self_of_antitone ha] using hρa.symm
  · simpa [Function.comp_assoc, nonincreasingRearrangement_comp_perm_eq_of_antitone hb σ] using
      hρb.symm

/-- Helper for Fact 24.59: if a permutation preserves the values of an antitone vector, then every
strict-drop prefix is invariant under that permutation. -/
private theorem strict_drop_prefix_invariant_of_value_preserving_perm
    {N : ℕ} {a : Fin N → ℝ} (ha : Antitone a) {ρ : Equiv.Perm (Fin N)}
    (hρ : a ∘ ρ = a) {r : Fin N} (hrN : r.1 + 1 < N)
    (hr : a r > a ⟨r.1 + 1, hrN⟩) :
    ∀ i : Fin N, i ≤ r ↔ ρ i ≤ r := by
  let rs : Fin N := ⟨r.1 + 1, hrN⟩
  have hρsymm : a ∘ ρ.symm = a := by
    funext i
    -- Evaluate `a ∘ ρ = a` at `ρ.symm i` to recover the inverse preservation law.
    have hρi : a (ρ (ρ.symm i)) = a (ρ.symm i) := by
      simpa [Function.comp] using congrArg (fun f : Fin N → ℝ ↦ f (ρ.symm i)) hρ
    simpa [Function.comp] using hρi.symm
  have hforward :
      ∀ {τ : Equiv.Perm (Fin N)},
        a ∘ τ = a →
          ∀ i : Fin N, i ≤ r → τ i ≤ r := by
    intro τ hτ i hi
    by_contra hnot
    have hs : rs ≤ τ i := by
      apply Fin.le_iff_val_le_val.mpr
      have hlt : r < τ i := lt_of_not_ge hnot
      exact Nat.succ_le_of_lt (Fin.lt_def.mp hlt)
    have hprefix : a r ≤ a i := ha hi
    have hτi : a (τ i) = a i := by
      simpa [Function.comp] using congrArg (fun f : Fin N → ℝ ↦ f i) hτ
    have htail : a (τ i) ≤ a rs := ha hs
    have hle : a r ≤ a rs := by
      calc
        a r ≤ a i := hprefix
        _ = a (τ i) := hτi.symm
        _ ≤ a rs := htail
    exact (not_le_of_gt hr) hle
  intro i
  constructor
  · exact hforward hρ i
  · intro hi
    -- Apply the same forward implication to `ρ.symm`, then rewrite back using `ρ.symm (ρ i) = i`.
    have hback : ρ.symm (ρ i) ≤ r := hforward hρsymm (ρ i) hi
    simpa using hback

/-- Helper for Fact 24.59: the coordinate mask for the first `r + 1` indices. -/
private def prefixMask {N : ℕ} (r : Fin N) : Fin N → ℝ :=
  fun i ↦ if i ≤ r then 1 else 0

/-- Helper for Fact 24.59: the diagonal projection onto the first `r + 1` coordinates. -/
private def prefixProj {N : ℕ} (r : Fin N) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (prefixMask r)

/-- Helper for Fact 24.59: the prefix projection is symmetric. -/
private theorem prefixProj_isSymm
    {N : ℕ} (r : Fin N) :
    (prefixProj r).IsSymm := by
  -- A diagonal matrix is symmetric, so the prefix mask defines an orthogonal projection surface.
  simpa [prefixProj] using Matrix.isSymm_diagonal (prefixMask r)

/-- Helper for Fact 24.59: the prefix projection is idempotent. -/
private theorem prefixProj_mul_self
    {N : ℕ} (r : Fin N) :
    prefixProj r * prefixProj r = prefixProj r := by
  have hmask :
      (fun i : Fin N ↦ prefixMask r i * prefixMask r i) = prefixMask r := by
    funext i
    by_cases hi : i ≤ r
    · simp [prefixMask, hi]
    · simp [prefixMask, hi]
  -- The diagonal `0/1` mask squares to itself coordinatewise.
  simpa [prefixProj, hmask] using Matrix.diagonal_mul_diagonal (prefixMask r) (prefixMask r)

/-- Helper for Fact 24.59: the prefix projections form a nested chain under multiplication. -/
private theorem prefixProj_mul_of_le
    {N : ℕ} {r s : Fin N} (hrs : r ≤ s) :
    prefixProj r * prefixProj s = prefixProj r ∧
      prefixProj s * prefixProj r = prefixProj r := by
  constructor
  · have hmask :
        (fun i : Fin N ↦ prefixMask r i * prefixMask s i) = prefixMask r := by
      funext i
      by_cases hi : i ≤ r
      · have his : i ≤ s := le_trans hi hrs
        simp [prefixMask, hi, his]
      · simp [prefixMask, hi]
    -- A smaller prefix followed by a larger one keeps the smaller cutoff unchanged.
    simpa [prefixProj, hmask] using Matrix.diagonal_mul_diagonal (prefixMask r) (prefixMask s)
  · have hmask :
        (fun i : Fin N ↦ prefixMask s i * prefixMask r i) = prefixMask r := by
      funext i
      by_cases hi : i ≤ r
      · have his : i ≤ s := le_trans hi hrs
        simp [prefixMask, hi, his]
      · simp [prefixMask, hi]
    -- The same nested-prefix identity also holds with the factors reversed.
    simpa [prefixProj, hmask] using Matrix.diagonal_mul_diagonal (prefixMask s) (prefixMask r)

/-- Helper for Fact 24.59: the trace of the prefix projection is the size of the first
`r + 1` block, written in source prefix-sum form. -/
private theorem trace_prefixProj_eq_sum_prefix
    {N : ℕ} (r : Fin N) :
    Matrix.trace (prefixProj r) = ∑ i, if i ≤ r then (1 : ℝ) else 0 := by
  -- Tracing the prefix projector just reads off the `1`s on its diagonal.
  simp [Matrix.trace, prefixProj, prefixMask]

/-- Helper for Fact 24.59: after correcting an equality permutation inside the value blocks of
`a`, every strict-drop prefix sum of `b ∘ σ` agrees with the corresponding prefix sum of `b`. -/
private theorem supported_perm_prefix_sum_eq_of_strict_drop
    {N : ℕ} {a b : Fin N → ℝ}
    (ha : Antitone a) {σ : Equiv.Perm (Fin N)}
    {r : Fin N} (hrN : r.1 + 1 < N)
    (hr : a r > a ⟨r.1 + 1, hrN⟩)
    (hcorr : ∃ ρ : Equiv.Perm (Fin N), a ∘ ρ = a ∧ b ∘ σ ∘ ρ = b) :
    (∑ i, if i ≤ r then (b ∘ σ) i else 0) =
      ∑ i, if i ≤ r then b i else 0 := by
  rcases hcorr with ⟨ρ, hρa, hρb⟩
  have hprefix :=
    strict_drop_prefix_invariant_of_value_preserving_perm ha hρa hrN hr
  have hρb_eval : ∀ i : Fin N, (b ∘ σ) (ρ i) = b i := by
    intro i
    -- Evaluate the corrected permutation identity at each coordinate.
    simpa [Function.comp_assoc, Function.comp] using
      congrArg (fun f : Fin N → ℝ ↦ f i) hρb
  -- Reindex the prefix sum along the correcting permutation, which preserves the strict-drop cut.
  calc
    (∑ i, if i ≤ r then (b ∘ σ) i else 0)
        = ∑ i, if ρ i ≤ r then (b ∘ σ) (ρ i) else 0 := by
            simpa using
              (Equiv.sum_comp ρ (fun i : Fin N ↦ if i ≤ r then (b ∘ σ) i else 0)).symm
    _ = ∑ i, if i ≤ r then b i else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hi' : i ≤ r
          · have hρi : ρ i ≤ r := (hprefix i).1 hi'
            rw [if_pos hρi, if_pos hi']
            exact hρb_eval i
          · have hρi : ¬ ρ i ≤ r := by
              simpa [hprefix i] using hi'
            rw [if_neg hρi, if_neg hi']

/-- Helper for Fact 24.59: if a real matrix has orthonormal rows and columns, then the matrix of
squared entries is doubly stochastic. -/
private theorem sq_entry_matrix_mem_doublyStochastic
    {n : Type u} [Fintype n] [DecidableEq n] {W : Matrix n n ℝ}
    (hWWt : W * Wᵀ = 1) (hWtW : Wᵀ * W = 1) :
    (fun i j ↦ (W i j) ^ 2) ∈ doublyStochastic ℝ n := by
  -- Read the row and column sums off the diagonal of the orthogonality relations.
  let M : Matrix n n ℝ := fun i j ↦ (W i j) ^ 2
  change M ∈ doublyStochastic ℝ n
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact sq_nonneg (W i j)
  · intro i
    have hdiag := congrArg (fun N : Matrix n n ℝ ↦ N i i) hWWt
    simp [Matrix.mul_apply] at hdiag
    simpa [M, pow_two] using hdiag
  · intro j
    have hdiag := congrArg (fun N : Matrix n n ℝ ↦ N j j) hWtW
    simp [Matrix.mul_apply] at hdiag
    simpa [M, pow_two] using hdiag

/-- Helper for Fact 24.59: the diagonal of an orthogonal conjugate of a diagonal matrix is the
action of the squared-entry matrix on the diagonal vector. -/
private theorem diag_orthogonal_conj_diagonal_eq_sq_entry_mulVec
    {n : Type u} [Fintype n] [DecidableEq n] (W : Matrix n n ℝ) (d : n → ℝ) :
    Matrix.diag (W * Matrix.diagonal d * Wᵀ) = (fun i j ↦ (W i j) ^ 2) *ᵥ d := by
  -- Expand the diagonal entry and collapse the diagonal matrix to a single sum.
  ext i
  rw [Matrix.diag_apply, Matrix.mul_apply]
  simp [Matrix.mulVec, dotProduct, pow_two, mul_left_comm, mul_comm]

/-- Helper for Fact 24.59: multiplying on the left by a diagonal matrix weights the diagonal by the
same coefficient vector, so the trace becomes the corresponding dot product. -/
private theorem trace_diagonal_mul_eq_dotProduct_diag
    {n : Type u} [Fintype n] [DecidableEq n] (a : n → ℝ) (X : Matrix n n ℝ) :
    Matrix.trace (Matrix.diagonal a * X) = dotProduct a (Matrix.diag X) := by
  -- Expand the trace on the diagonal and use the diagonal-left-multiplication rule entrywise.
  simp [Matrix.trace, dotProduct]

/-- Helper for Fact 24.59: the prefix mask keeps exactly the first `r + 1` coordinates in a
finite dot product. -/
private theorem dotProduct_prefixMask_eq_sum_prefix
    {N : ℕ} (r : Fin N) (x : Fin N → ℝ) :
    dotProduct (prefixMask r) x =
      ∑ i, if i ≤ r then x i else 0 := by
  -- Expand the dot product and use the `0/1` mask to discard the tail coordinates.
  unfold dotProduct prefixMask
  simp_rw [ite_mul, one_mul, zero_mul]

/-- Helper for Fact 24.59: tracing against the prefix projection reads off the sum of the diagonal
entries in the leading coordinate block. -/
private theorem trace_prefixProj_mul_eq_sum_diag_prefix
    {N : ℕ} (r : Fin N) (X : Matrix (Fin N) (Fin N) ℝ) :
    Matrix.trace (prefixProj r * X) =
      ∑ i, if i ≤ r then X i i else 0 := by
  -- First convert the trace to the dot product of the prefix mask with the diagonal of `X`.
  rw [prefixProj, trace_diagonal_mul_eq_dotProduct_diag]
  -- Then rewrite the masked dot product as the prefix diagonal sum.
  simpa using dotProduct_prefixMask_eq_sum_prefix r (Matrix.diag X)

/-- Helper for Fact 24.59: if a strict-drop prefix trace equality is known for `C`, then the same
equality can be rewritten in the diagonal basis of an orthogonal conjugate of `C`. -/
private theorem trace_conjugated_prefixProj_mul_diagonal_eq_of_trace_prefixProj
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℝ}
    {U : Matrix.orthogonalGroup (Fin N) ℝ} {c : Fin N → ℝ}
    (hCdiag : C = (((U : Matrix _ _ ℝ) * Matrix.diagonal c) * (U : Matrix _ _ ℝ)ᵀ))
    {r : Fin N}
    (htrace : Matrix.trace (prefixProj r * C) = ∑ i, if i ≤ r then c i else 0) :
    Matrix.trace
        ((((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ)) * Matrix.diagonal c) =
      ∑ i, if i ≤ r then c i else 0 := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  have hrewrite :
      Matrix.trace (prefixProj r * C) =
        Matrix.trace (((UMᵀ * prefixProj r * UM) * Matrix.diagonal c) : Matrix (Fin N) (Fin N) ℝ) := by
    -- Route correction: cycle the trace so the strict-drop projector is expressed in the already
    -- diagonal `U`-basis, which is the source-faithful surface for the equality case.
    rw [hCdiag]
    calc
      Matrix.trace (prefixProj r * ((UM * Matrix.diagonal c) * UMᵀ))
          = Matrix.trace (((prefixProj r * UM) * Matrix.diagonal c) * UMᵀ) := by
              simp [Matrix.mul_assoc]
      _ = Matrix.trace (UMᵀ * ((prefixProj r * UM) * Matrix.diagonal c)) := by
            simpa [Matrix.mul_assoc] using
              (Matrix.trace_mul_cycle (prefixProj r * UM) (Matrix.diagonal c) UMᵀ)
      _ = Matrix.trace (((UMᵀ * prefixProj r * UM) * Matrix.diagonal c) :
            Matrix (Fin N) (Fin N) ℝ) := by
            simp [Matrix.mul_assoc]
  -- Replace the original strict-drop trace equality by its diagonal-basis form.
  calc
    Matrix.trace ((((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ)) * Matrix.diagonal c)
        = Matrix.trace (((UMᵀ * prefixProj r * UM) * Matrix.diagonal c) :
            Matrix (Fin N) (Fin N) ℝ) := by
            simp [UM, Matrix.mul_assoc]
    _ = Matrix.trace (prefixProj r * C) := hrewrite.symm
    _ = ∑ i, if i ≤ r then c i else 0 := htrace

/-- Helper for Fact 24.59: orthogonal conjugation preserves symmetry of the prefix projection. -/
private theorem conjugated_prefixProj_isSymm
    {N : ℕ} {U : Matrix.orthogonalGroup (Fin N) ℝ} (r : Fin N) :
    ((((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ)) :
      Matrix (Fin N) (Fin N) ℝ).IsSymm := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  -- Transposing the orthogonal conjugate just returns the same matrix because `prefixProj r`
  -- is symmetric.
  rw [Matrix.IsSymm]
  calc
    ((((UMᵀ * prefixProj r) * UM) : Matrix (Fin N) (Fin N) ℝ)ᵀ)
        = UMᵀ * (prefixProj r)ᵀ * UM := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (UMᵀ * prefixProj r) * UM := by
          simp [(prefixProj_isSymm r).eq, Matrix.mul_assoc]

/-- Helper for Fact 24.59: orthogonal conjugation preserves idempotence of the prefix
projection. -/
private theorem conjugated_prefixProj_mul_self
    {N : ℕ} {U : Matrix.orthogonalGroup (Fin N) ℝ} (r : Fin N) :
    let P : Matrix (Fin N) (Fin N) ℝ :=
      (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
    P * P = P := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  have hUUt : UM * UMᵀ = 1 := orthogonal_mul_transpose_eq_one U.prop
  -- Collapse the middle orthogonal factor and reduce to the idempotence of `prefixProj r`.
  change (((UMᵀ * prefixProj r) * UM) * ((UMᵀ * prefixProj r) * UM) :
      Matrix (Fin N) (Fin N) ℝ) = ((UMᵀ * prefixProj r) * UM)
  calc
    (((UMᵀ * prefixProj r) * UM) * ((UMᵀ * prefixProj r) * UM) :
        Matrix (Fin N) (Fin N) ℝ)
        = (((UMᵀ * prefixProj r) * (UM * UMᵀ)) * prefixProj r) * UM := by
            simp [Matrix.mul_assoc]
    _ = (((UMᵀ * prefixProj r) * (1 : Matrix (Fin N) (Fin N) ℝ)) * prefixProj r) * UM := by
          rw [hUUt]
    _ = ((UMᵀ * prefixProj r * prefixProj r) : Matrix (Fin N) (Fin N) ℝ) * UM := by
          simp [Matrix.mul_assoc]
    _ = ((UMᵀ * prefixProj r) * UM) := by
          simp [Matrix.mul_assoc, prefixProj_mul_self]

/-- Helper for Fact 24.59: orthogonal conjugation preserves the trace of the prefix projection. -/
private theorem trace_conjugated_prefixProj_eq_sum_prefix
    {N : ℕ} {U : Matrix.orthogonalGroup (Fin N) ℝ} (r : Fin N) :
    Matrix.trace ((((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ)) :
      Matrix (Fin N) (Fin N) ℝ) =
      ∑ i, if i ≤ r then (1 : ℝ) else 0 := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  have hUUt : UM * UMᵀ = 1 := orthogonal_mul_transpose_eq_one U.prop
  -- Cycle the trace once so the orthogonal factors collapse against each other.
  calc
    Matrix.trace ((((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ)) :
        Matrix (Fin N) (Fin N) ℝ)
        = Matrix.trace ((UM * UMᵀ) * prefixProj r : Matrix (Fin N) (Fin N) ℝ) := by
            simpa [UM, Matrix.mul_assoc] using
              (Matrix.trace_mul_cycle UMᵀ (prefixProj r) UM)
    _ = Matrix.trace (prefixProj r) := by simp [hUUt]
    _ = ∑ i, if i ≤ r then (1 : ℝ) else 0 := trace_prefixProj_eq_sum_prefix r

/-- Helper for Fact 24.59: the orthogonally transported prefix projectors still form the same
nested symmetric idempotent trace chain. -/
private theorem conjugated_prefix_projection_chain
    {N : ℕ} {U : Matrix.orthogonalGroup (Fin N) ℝ} {r s : Fin N} (hrs : r ≤ s) :
    let Pr : Matrix (Fin N) (Fin N) ℝ :=
      (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
    let Ps : Matrix (Fin N) (Fin N) ℝ :=
      (((U : Matrix _ _ ℝ)ᵀ * prefixProj s) * (U : Matrix _ _ ℝ))
    Pr.IsSymm ∧
      Pr * Pr = Pr ∧
      Matrix.trace Pr = (∑ i, if i ≤ r then (1 : ℝ) else 0) ∧
      Pr * Ps = Pr ∧
      Ps * Pr = Pr := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  have hUUt : UM * UMᵀ = 1 := orthogonal_mul_transpose_eq_one U.prop
  have hprefix_mul : prefixProj r * prefixProj s = prefixProj r :=
    (prefixProj_mul_of_le hrs).1
  have hprefix_mul_rev : prefixProj s * prefixProj r = prefixProj r :=
    (prefixProj_mul_of_le hrs).2
  refine ⟨conjugated_prefixProj_isSymm (U := U) r, ?_, ?_, ?_, ?_⟩
  · -- The transported prefix projector remains idempotent under orthogonal conjugation.
    simpa using (conjugated_prefixProj_mul_self (U := U) r)
  · -- Orthogonal conjugation preserves the trace/rank of the prefix projector.
    exact trace_conjugated_prefixProj_eq_sum_prefix (U := U) r
  · -- The transported chain remains nested in the same order `r ≤ s`.
    change (((UMᵀ * prefixProj r) * UM) * ((UMᵀ * prefixProj s) * UM) :
        Matrix (Fin N) (Fin N) ℝ) = ((UMᵀ * prefixProj r) * UM)
    calc
      (((UMᵀ * prefixProj r) * UM) * ((UMᵀ * prefixProj s) * UM) :
          Matrix (Fin N) (Fin N) ℝ)
          = (((UMᵀ * prefixProj r) * (UM * UMᵀ)) * prefixProj s) * UM := by
              simp [Matrix.mul_assoc]
      _ = (((UMᵀ * prefixProj r) * (1 : Matrix (Fin N) (Fin N) ℝ)) * prefixProj s) * UM := by
            rw [hUUt]
      _ = ((UMᵀ * (prefixProj r * prefixProj s)) : Matrix (Fin N) (Fin N) ℝ) * UM := by
            simp [Matrix.mul_assoc]
      _ = ((UMᵀ * prefixProj r) * UM) := by
            rw [hprefix_mul]
  · -- Reversing the factors gives the same smaller projector by the nested prefix identity.
    change (((UMᵀ * prefixProj s) * UM) * ((UMᵀ * prefixProj r) * UM) :
        Matrix (Fin N) (Fin N) ℝ) = ((UMᵀ * prefixProj r) * UM)
    calc
      (((UMᵀ * prefixProj s) * UM) * ((UMᵀ * prefixProj r) * UM) :
          Matrix (Fin N) (Fin N) ℝ)
          = (((UMᵀ * prefixProj s) * (UM * UMᵀ)) * prefixProj r) * UM := by
              simp [Matrix.mul_assoc]
      _ = (((UMᵀ * prefixProj s) * (1 : Matrix (Fin N) (Fin N) ℝ)) * prefixProj r) * UM := by
            rw [hUUt]
      _ = ((UMᵀ * (prefixProj s * prefixProj r)) : Matrix (Fin N) (Fin N) ℝ) * UM := by
            simp [Matrix.mul_assoc]
      _ = ((UMᵀ * prefixProj r) * UM) := by
            rw [hprefix_mul_rev]

/-- Helper for Fact 24.59: reading idempotence on one diagonal entry of a symmetric matrix turns
that entry into the sum of squares along the corresponding row. -/
private theorem diag_eq_sum_sq_of_symmetric_idempotent
    {N : ℕ} {P : Matrix (Fin N) (Fin N) ℝ}
    (hPsymm : P.IsSymm) (hPidem : P * P = P) (i : Fin N) :
    P i i = ∑ j, (P i j) ^ 2 := by
  -- Read the `(i,i)` entry of `P * P = P` and rewrite the symmetry relation into squares.
  have hdiag := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ ↦ M i i) hPidem
  simpa [Matrix.mul_apply, hPsymm.apply, pow_two] using hdiag.symm

/-- Helper for Fact 24.59: every diagonal entry of a symmetric idempotent matrix lies in the unit
interval. -/
private theorem diag_mem_unit_interval_of_symmetric_idempotent
    {N : ℕ} {P : Matrix (Fin N) (Fin N) ℝ}
    (hPsymm : P.IsSymm) (hPidem : P * P = P) :
    ∀ i, 0 ≤ P i i ∧ P i i ≤ 1 := by
  intro i
  have hdiag := diag_eq_sum_sq_of_symmetric_idempotent hPsymm hPidem i
  have hnonneg : 0 ≤ P i i := by
    rw [hdiag]
    exact Finset.sum_nonneg fun j _ ↦ sq_nonneg (P i j)
  have hsq_le : (P i i) ^ 2 ≤ P i i := by
    calc
      (P i i) ^ 2 ≤ ∑ j, (P i j) ^ 2 := by
        exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (P i j)) (Finset.mem_univ i)
      _ = P i i := hdiag.symm
  have hone : P i i ≤ 1 := by
    nlinarith
  exact ⟨hnonneg, hone⟩

/-- Helper for Fact 24.59: if a diagonal entry of a symmetric idempotent matrix is `0`, then the
corresponding row vanishes. -/
private theorem row_eq_zero_of_symmetric_idempotent_diag_eq_zero
    {N : ℕ} {P : Matrix (Fin N) (Fin N) ℝ}
    (hPsymm : P.IsSymm) (hPidem : P * P = P) {i : Fin N}
    (hii : P i i = 0) :
    ∀ j, P i j = 0 := by
  have hsum :
      ∑ j, (P i j) ^ 2 = 0 := by
    simpa [hii] using (diag_eq_sum_sq_of_symmetric_idempotent hPsymm hPidem i).symm
  have hentry_sq :
      ∀ j, (P i j) ^ 2 = 0 := by
    intro j
    exact
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ sq_nonneg (P i k))).1 hsum j
        (Finset.mem_univ j)
  intro j
  exact sq_eq_zero_iff.mp (hentry_sq j)

/-- Helper for Fact 24.59: if a diagonal entry of a symmetric idempotent matrix is `1`, then the
corresponding row is the matching identity row. -/
private theorem row_eq_identity_of_symmetric_idempotent_diag_eq_one
    {N : ℕ} {P : Matrix (Fin N) (Fin N) ℝ}
    (hPsymm : P.IsSymm) (hPidem : P * P = P) {i : Fin N}
    (hii : P i i = 1) :
    ∀ j, P i j = if i = j then 1 else 0 := by
  have hsum :
      ∑ j, (P i j) ^ 2 = 1 := by
    simpa [hii] using (diag_eq_sum_sq_of_symmetric_idempotent hPsymm hPidem i).symm
  have hsplit :
      (P i i) ^ 2 + Finset.sum (Finset.univ.erase i) (fun j : Fin N ↦ (P i j) ^ 2) =
        ∑ j, (P i j) ^ 2 := by
    simpa [add_comm] using
      (Finset.univ.sum_erase_add (fun j : Fin N ↦ (P i j) ^ 2) (Finset.mem_univ i))
  let s : ℝ := Finset.sum (Finset.univ.erase i) (fun j : Fin N ↦ (P i j) ^ 2)
  have hoffsum :
      s = 0 := by
    have hsplit' :
        (1 : ℝ) + s = 1 := by
      calc
        (1 : ℝ) + s = (P i i) ^ 2 + s := by
            simp [s, hii]
        _ = ∑ j, (P i j) ^ 2 := by
              simpa [s] using hsplit
        _ = 1 := hsum
    nlinarith
  have hoff_sq :
      ∀ j ∈ Finset.univ.erase i, (P i j) ^ 2 = 0 := by
    simpa [s] using
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (P i j))).1 hoffsum
  intro j
  by_cases hij : i = j
  · subst hij
    simp [hii]
  · have hjmem : j ∈ Finset.univ.erase i := by
      simp [hij, eq_comm]
    have hjzero : (P i j) ^ 2 = 0 := hoff_sq j hjmem
    have hj : P i j = 0 := sq_eq_zero_iff.mp hjzero
    simp [hij, hj]

/-- Helper for Fact 24.59: diagonal extremality of a symmetric idempotent projector upgrades from
the scalar diagonal entry to actual fixed/killed basis rows and columns. -/
private theorem basis_vector_action_of_projector_diagonal_extreme
    {N : ℕ} {P : Matrix (Fin N) (Fin N) ℝ}
    (hPsymm : P.IsSymm) (hPidem : P * P = P) (i : Fin N) :
    (P i i = 0 → (∀ j, P i j = 0) ∧ ∀ j, P j i = 0) ∧
      (P i i = 1 →
        (∀ j, P i j = if i = j then 1 else 0) ∧
          ∀ j, P j i = if j = i then 1 else 0) := by
  constructor
  · intro hii
    have hrow : ∀ j, P i j = 0 :=
      row_eq_zero_of_symmetric_idempotent_diag_eq_zero hPsymm hPidem hii
    refine ⟨hrow, ?_⟩
    intro j
    -- Symmetry turns the vanishing row into the matching vanishing column.
    simpa [hPsymm.apply] using hrow j
  · intro hii
    have hrow : ∀ j, P i j = if i = j then 1 else 0 :=
      row_eq_identity_of_symmetric_idempotent_diag_eq_one hPsymm hPidem hii
    refine ⟨hrow, ?_⟩
    intro j
    -- Symmetry likewise transports the identity row to the identity column.
    simpa [hPsymm.apply, eq_comm] using hrow j

/-- Helper for Fact 24.59: a rank/trace equality at the cutoff index rewrites to the centered
nonnegative sum used in the source equality case. -/
private theorem centered_cutoff_trace_identity_of_trace_equality
    {N : ℕ} {b : Fin N → ℝ} {P : Matrix (Fin N) (Fin N) ℝ} {r : Fin N}
    (htraceP : Matrix.trace P = ∑ i, if i ≤ r then (1 : ℝ) else 0)
    (htracePD : Matrix.trace (P * Matrix.diagonal b) = ∑ i, if i ≤ r then b i else 0) :
    (∑ i, if i ≤ r then (1 - P i i) * (b i - b r) else P i i * (b r - b i)) = 0 := by
  have htraceP' : ∑ i, P i i = ∑ i, if i ≤ r then (1 : ℝ) else 0 := by
    -- Rewrite the trace equality as an equality of the diagonal sums of `P`.
    simpa [Matrix.trace] using htraceP
  have htracePD' : ∑ i, P i i * b i = ∑ i, if i ≤ r then b i else 0 := by
    -- Rewrite the weighted trace equality as the corresponding diagonal weighted sum.
    simpa [Matrix.trace, Matrix.mul_diagonal] using htracePD
  calc
    (∑ i, if i ≤ r then (1 - P i i) * (b i - b r) else P i i * (b r - b i))
        = ∑ i,
            ((if i ≤ r then b i else 0) - P i i * b i -
              b r * ((if i ≤ r then (1 : ℝ) else 0) - P i i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hir : i ≤ r
              · simp [hir]
                ring
              · simp [hir]
                ring
    _ = (∑ i, if i ≤ r then b i else 0) - ∑ i, P i i * b i -
          ∑ i, b r * ((if i ≤ r then (1 : ℝ) else 0) - P i i) := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = (∑ i, if i ≤ r then b i else 0) - ∑ i, P i i * b i -
          b r * ((∑ i, if i ≤ r then (1 : ℝ) else 0) - ∑ i, P i i) := by
            rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    _ = 0 := by
          rw [← htracePD', ← htraceP']
          ring

/-- Helper for Fact 24.59: the centered cutoff identity forces strict-above diagonal entries to be
`1` and strict-below diagonal entries to be `0`. -/
private theorem strict_side_diag_of_centered_cutoff
    {N : ℕ} {b : Fin N → ℝ} (hb : Antitone b)
    {P : Matrix (Fin N) (Fin N) ℝ} (hPsymm : P.IsSymm) (hPidem : P * P = P) {r : Fin N}
    (htraceP : Matrix.trace P = ∑ i, if i ≤ r then (1 : ℝ) else 0)
    (htracePD : Matrix.trace (P * Matrix.diagonal b) = ∑ i, if i ≤ r then b i else 0) :
    (∀ i, b i > b r → P i i = 1) ∧ (∀ i, b i < b r → P i i = 0) := by
  have hdiag := diag_mem_unit_interval_of_symmetric_idempotent hPsymm hPidem
  have hcenter :
      (∑ i, if i ≤ r then (1 - P i i) * (b i - b r) else P i i * (b r - b i)) = 0 :=
    centered_cutoff_trace_identity_of_trace_equality htraceP htracePD
  have hterm_nonneg :
      ∀ i ∈ Finset.univ,
        0 ≤ if i ≤ r then (1 - P i i) * (b i - b r) else P i i * (b r - b i) := by
    intro i hi
    by_cases hir : i ≤ r
    · -- On the prefix side, both factors are nonnegative.
      have hfactor₁ : 0 ≤ 1 - P i i := sub_nonneg.mpr (hdiag i).2
      have hfactor₂ : 0 ≤ b i - b r := sub_nonneg.mpr (hb hir)
      simp [hir, mul_nonneg hfactor₁ hfactor₂]
    · -- Off the prefix side, antitonicity reverses the centered difference.
      have hfactor₁ : 0 ≤ P i i := (hdiag i).1
      have hfactor₂ : 0 ≤ b r - b i := sub_nonneg.mpr (hb (le_of_not_ge hir))
      simp [hir, mul_nonneg hfactor₁ hfactor₂]
  have hterm_zero :
      ∀ i, (if i ≤ r then (1 - P i i) * (b i - b r) else P i i * (b r - b i)) = 0 := by
    intro i
    exact
      (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).1 hcenter i (Finset.mem_univ i)
  constructor
  · intro i hi_gt
    have hir : i ≤ r := by
      by_contra hir
      have hle : b i ≤ b r := hb (le_of_not_ge hir)
      exact not_lt_of_ge hle hi_gt
    have hzero : (1 - P i i) * (b i - b r) = 0 := by
      simpa [hir] using hterm_zero i
    have hpos : 0 < b i - b r := sub_pos.mpr hi_gt
    have hone : 1 - P i i = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hpos)
    nlinarith
  · intro i hi_lt
    have hir : ¬ i ≤ r := by
      intro hir
      have hle : b r ≤ b i := hb hir
      exact not_lt_of_ge hle hi_lt
    have hzero : P i i * (b r - b i) = 0 := by
      simpa [hir] using hterm_zero i
    have hpos : 0 < b r - b i := sub_pos.mpr hi_lt
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hpos)

/-- Helper for Fact 24.59: once the centered cutoff identity has forced diagonal `0/1` values,
the projector already fixes or kills the corresponding standard basis vectors. -/
private theorem strict_side_basis_action_of_centered_cutoff
    {N : ℕ} {b : Fin N → ℝ} (hb : Antitone b)
    {P : Matrix (Fin N) (Fin N) ℝ} (hPsymm : P.IsSymm) (hPidem : P * P = P) {r : Fin N}
    (htraceP : Matrix.trace P = ∑ i, if i ≤ r then (1 : ℝ) else 0)
    (htracePD : Matrix.trace (P * Matrix.diagonal b) = ∑ i, if i ≤ r then b i else 0) :
    (∀ i, b i > b r →
      (∀ j, P i j = if i = j then 1 else 0) ∧
        ∀ j, P j i = if j = i then 1 else 0) ∧
      (∀ i, b i < b r → (∀ j, P i j = 0) ∧ ∀ j, P j i = 0) := by
  rcases strict_side_diag_of_centered_cutoff hb hPsymm hPidem htraceP htracePD with
    ⟨habove, hbelow⟩
  constructor
  · intro i hi
    -- On the strict-above side, diagonal `1` upgrades to the identity basis action.
    exact (basis_vector_action_of_projector_diagonal_extreme hPsymm hPidem i).2 (habove i hi)
  · intro i hi
    -- On the strict-below side, diagonal `0` upgrades to the zero basis action.
    exact (basis_vector_action_of_projector_diagonal_extreme hPsymm hPidem i).1 (hbelow i hi)

/-- Helper for Fact 24.59: once a strict-drop projector already fixes the strict-above basis
vectors and kills the strict-below ones, it commutes with the diagonal matrix whose entries define
that cutoff. -/
private theorem mul_diagonal_apply
    {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ) (c : Fin N → ℝ) (i j : Fin N) :
    (P * Matrix.diagonal c) i j = P i j * c j := by
  -- This is exactly mathlib's right-diagonal multiplication rule.
  simpa using Matrix.mul_diagonal c P i j

/-- Helper for Fact 24.59: left multiplication by a diagonal matrix scales the matching row. -/
private theorem diagonal_mul_apply
    {N : ℕ} (c : Fin N → ℝ) (P : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    (Matrix.diagonal c * P) i j = c i * P i j := by
  -- This is exactly mathlib's left-diagonal multiplication rule.
  simpa using Matrix.diagonal_mul c P i j

/-- Helper for Fact 24.59: once a strict-drop projector already fixes the strict-above basis
vectors and kills the strict-below ones, it commutes with the diagonal matrix whose entries define
that cutoff. -/
private theorem commute_diagonal_of_strict_side_basis_action
    {N : ℕ} {c : Fin N → ℝ} {P : Matrix (Fin N) (Fin N) ℝ} {r : Fin N}
    (hside :
      (∀ i, c i > c r →
        (∀ j, P i j = if i = j then 1 else 0) ∧
          ∀ j, P j i = if j = i then 1 else 0) ∧
        ∀ i, c i < c r → (∀ j, P i j = 0) ∧ ∀ j, P j i = 0) :
    Commute P (Matrix.diagonal c) := by
  change P * Matrix.diagonal c = Matrix.diagonal c * P
  ext i j
  -- Compare the two products entrywise and split by the position of `c i` and `c j`
  -- relative to the cutoff value `c r`.
  rw [mul_diagonal_apply, diagonal_mul_apply]
  rcases lt_trichotomy (c i) (c r) with hilt | hieq | higt
  · rcases lt_trichotomy (c j) (c r) with hjlt | hjeq | hjgt
    · have hPij : P i j = 0 := (hside.2 i hilt).1 j
      simp [hPij]
    · have hPij : P i j = 0 := (hside.2 i hilt).1 j
      simp [hPij, hjeq]
    · have hPij : P i j = 0 := (hside.2 i hilt).1 j
      simp [hPij]
  · rcases lt_trichotomy (c j) (c r) with hjlt | hjeq | hjgt
    · have hPij : P i j = 0 := (hside.2 j hjlt).2 i
      simp [hPij, hieq]
    · simpa [hieq, hjeq, mul_comm]
    · have hneq : i ≠ j := by
        intro hij
        subst hij
        linarith
      have hPij : P i j = 0 := by
        simpa [hneq] using (hside.1 j hjgt).2 i
      simp [hPij, hieq]
  · rcases lt_trichotomy (c j) (c r) with hjlt | hjeq | hjgt
    · have hPij : P i j = 0 := by
        have hneq : i ≠ j := by
          intro hij
          subst hij
          linarith
        simpa [hneq] using (hside.1 i higt).1 j
      simp [hPij]
    · have hPij : P i j = 0 := by
        have hneq : i ≠ j := by
          intro hij
          subst hij
          linarith
        simpa [hneq] using (hside.1 i higt).1 j
      simp [hPij, hjeq]
    · have hPij : P i j = if i = j then 1 else 0 := (hside.1 i higt).1 j
      by_cases hij : i = j
      · subst hij
        simpa [hPij, mul_comm]
      · simp [hPij, hij]

/-- Helper for Fact 24.59: commutation in an orthogonal diagonal basis conjugates back to
commutation before the basis change. -/
private theorem commute_of_orthogonal_conjugate_commute
    {N : ℕ} {U : Matrix.orthogonalGroup (Fin N) ℝ}
    {P D : Matrix (Fin N) (Fin N) ℝ}
    (hcomm :
      Commute ((((U : Matrix _ _ ℝ)ᵀ * P) * (U : Matrix _ _ ℝ)) : Matrix (Fin N) (Fin N) ℝ) D) :
    Commute P (((U : Matrix _ _ ℝ) * D) * (U : Matrix _ _ ℝ)ᵀ) := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  have hUtU : UMᵀ * UM = 1 := orthogonal_transpose_mul_eq_one U.prop
  have hUUt : UM * UMᵀ = 1 := orthogonal_mul_transpose_eq_one U.prop
  change P * ((UM * D) * UMᵀ) = ((UM * D) * UMᵀ) * P
  -- Conjugate the commuting core back out by `U` and collapse the orthogonal factors.
  calc
    P * ((UM * D) * UMᵀ)
        = (UM * ((((UMᵀ * P) * UM) * D))) * UMᵀ := by
            calc
              P * ((UM * D) * UMᵀ)
                  = ((UM * UMᵀ) * P) * ((UM * D) * UMᵀ) := by simp [hUUt]
              _ = (UM * ((((UMᵀ * P) * UM) * D))) * UMᵀ := by
                    simp [Matrix.mul_assoc]
    _ = (UM * (D * (((UMᵀ * P) * UM)))) * UMᵀ := by
          rw [hcomm.eq]
    _ = ((UM * D) * UMᵀ) * P := by
          simp [Matrix.mul_assoc, hUtU, hUUt]

/-- Helper for Fact 24.59: if an antitone finite vector drops between two indices, then one of its
adjacent steps strictly drops somewhere between those indices. -/
private theorem exists_strict_drop_between_of_antitone_gt
    {N : ℕ} {a : Fin N → ℝ} (ha : Antitone a)
    {i j : Fin N} (hij : i < j) (hgt : a i > a j) :
    ∃ (r : Fin N) (hrN : r.1 + 1 < N),
      i ≤ r ∧ r < j ∧ a r > a ⟨r.1 + 1, hrN⟩ := by
  let P : ℕ → Prop := fun k ↦
    i.1 < k ∧ k ≤ j.1 ∧ ∃ hkN : k < N, a ⟨k, hkN⟩ < a i
  have hexists : ∃ k : ℕ, P k := by
    -- The target index `j` already witnesses the first place where the value has dropped below
    -- `a i`.
    refine ⟨j.1, hij, le_rfl, ?_⟩
    exact ⟨j.2, by simpa using hgt⟩
  let k : ℕ := Nat.find hexists
  have hk_spec : P k := Nat.find_spec hexists
  have hk_gt : i.1 < k := hk_spec.1
  have hk_le_j : k ≤ j.1 := hk_spec.2.1
  rcases hk_spec.2.2 with ⟨hkN, hk_drop⟩
  have hk_pos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hk_gt
  let r : Fin N := ⟨k - 1, by omega⟩
  have hrN : r.1 + 1 < N := by
    -- The predecessor of the minimal drop index still lies strictly before `N`.
    dsimp [r]
    omega
  have hir : i ≤ r := by
    -- Since `k > i`, its predecessor is still at or beyond `i`.
    apply Fin.le_iff_val_le_val.mpr
    dsimp [r]
    omega
  have hrj : r < j := by
    -- Because `k ≤ j`, the predecessor of `k` lies strictly before `j`.
    apply Fin.lt_def.mpr
    dsimp [r]
    omega
  have har_eq : a r = a i := by
    have hri_le : a r ≤ a i := ha hir
    have hnot_lt : ¬ a r < a i := by
      intro hlt
      rcases lt_or_eq_of_le hir with hir_lt | hir_eq
      ·
        have hprop : P r.1 := by
          -- If `a r` were already below `a i`, then `r = k - 1` would contradict the minimality
          -- of `k`.
          refine ⟨?_, ?_, ?_⟩
          · exact hir_lt
          · exact le_of_lt hrj
          · exact ⟨r.2, by simpa using hlt⟩
        have hk_min : k ≤ r.1 := Nat.find_min' hexists hprop
        dsimp [r] at hk_min
        omega
      · exact (lt_irrefl (a i)) (by simpa [hir_eq] using hlt)
    exact le_antisymm hri_le (le_of_not_gt hnot_lt)
  refine ⟨r, hrN, hir, hrj, ?_⟩
  -- The minimality argument shows `a r = a i`, while the defining property of `k = r + 1`
  -- gives the strict drop at the next index.
  calc
    a r = a i := har_eq
    _ > a ⟨k, hkN⟩ := hk_drop
    _ = a ⟨r.1 + 1, hrN⟩ := by
          have hk_eq : (⟨k, hkN⟩ : Fin N) = ⟨r.1 + 1, hrN⟩ := by
            apply Fin.ext
            dsimp [r]
            omega
          simpa using congrArg a hk_eq

/-- Helper for Fact 24.59: left multiplication by a prefix projection keeps exactly the rows whose
indices lie in the prefix. -/
private theorem prefixProj_mul_apply
    {N : ℕ} (r : Fin N) (C : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    (prefixProj r * C) i j = if i ≤ r then C i j else 0 := by
  -- Unfold the prefix projector and collapse the diagonal `0/1` mask on the left.
  rw [prefixProj, diagonal_mul_apply]
  by_cases hi : i ≤ r
  · simp [prefixMask, hi]
  · simp [prefixMask, hi]

/-- Helper for Fact 24.59: right multiplication by a prefix projection keeps exactly the columns
whose indices lie in the prefix. -/
private theorem mul_prefixProj_apply
    {N : ℕ} (C : Matrix (Fin N) (Fin N) ℝ) (r : Fin N) (i j : Fin N) :
    (C * prefixProj r) i j = if j ≤ r then C i j else 0 := by
  -- Unfold the prefix projector and collapse the diagonal `0/1` mask on the right.
  rw [prefixProj, mul_diagonal_apply]
  by_cases hj : j ≤ r
  · simp [prefixMask, hj]
  · simp [prefixMask, hj]

/-- Helper for Fact 24.59: if every strict-drop prefix projector of an antitone diagonal commutes
with a matrix, then the matrix has no entries connecting distinct value plateaus of that diagonal.
-/
private theorem cross_block_entry_eq_zero_of_distinct_a_values
    {N : ℕ} {a : Fin N → ℝ} (ha : Antitone a)
    {C : Matrix (Fin N) (Fin N) ℝ}
    (hcomm :
      ∀ {r : Fin N} (hrN : r.1 + 1 < N),
        a r > a ⟨r.1 + 1, hrN⟩ → Commute (prefixProj r) C)
    {i j : Fin N} (hij : a i ≠ a j) :
    C i j = 0 := by
  rcases lt_trichotomy i j with hij_lt | rfl | hij_gt
  · have hgt : a i > a j := by
      -- Distinct antitone values can only decrease as the index increases.
      exact lt_of_le_of_ne (ha (le_of_lt hij_lt)) (by simpa [eq_comm] using hij)
    rcases exists_strict_drop_between_of_antitone_gt ha hij_lt hgt with
      ⟨r, hrN, hir, hrj, hdrop⟩
    have hij_entry :
        (prefixProj r * C) i j = (C * prefixProj r) i j := by
      -- Evaluate the commuting strict-drop prefix identity at the cross-block entry `(i,j)`.
      exact congrArg (fun M : Matrix (Fin N) (Fin N) ℝ ↦ M i j) (hcomm hrN hdrop).eq
    have hj_not_le : ¬ j ≤ r := not_le_of_gt hrj
    -- The separator puts row `i` inside the prefix and column `j` outside it, so the commuting
    -- identity reads `C i j = 0`.
    simpa [prefixProj_mul_apply, mul_prefixProj_apply, hir, hj_not_le] using hij_entry
  · exact (hij rfl).elim
  · have hgt : a j > a i := by
      -- The reverse index order yields the symmetric strict drop after swapping `i` and `j`.
      exact lt_of_le_of_ne (ha (le_of_lt hij_gt)) (by simpa [eq_comm] using hij.symm)
    rcases exists_strict_drop_between_of_antitone_gt ha hij_gt hgt with
      ⟨r, hrN, hjr, hri, hdrop⟩
    have hij_entry :
        (prefixProj r * C) i j = (C * prefixProj r) i j := by
      -- Again evaluate the commuting prefix identity, now with the separator between `j` and `i`.
      exact congrArg (fun M : Matrix (Fin N) (Fin N) ℝ ↦ M i j) (hcomm hrN hdrop).eq
    have hi_not_le : ¬ i ≤ r := not_le_of_gt hri
    -- This time column `j` lies inside the prefix while row `i` lies outside, so the equality is
    -- `0 = C i j`.
    simpa [prefixProj_mul_apply, mul_prefixProj_apply, hi_not_le, hjr] using hij_entry.symm

/-- Helper for Fact 24.59: once a matrix vanishes off the equal-value plateaus of an antitone
diagonal, the diagonal matrix commutes with it. -/
private theorem diagonal_commutes_of_cross_block_zero
    {N : ℕ} {a : Fin N → ℝ} {C : Matrix (Fin N) (Fin N) ℝ}
    (hzero : ∀ {i j : Fin N}, a i ≠ a j → C i j = 0) :
    Commute (Matrix.diagonal a) C := by
  change Matrix.diagonal a * C = C * Matrix.diagonal a
  ext i j
  -- Reduce both sides entrywise and split according to whether the two diagonal weights agree.
  rw [diagonal_mul_apply, mul_diagonal_apply]
  by_cases hij : a i = a j
  · rw [hij]
    simpa [mul_comm]
  · have hCij : C i j = 0 := hzero hij
    simp [hCij]

/-- Helper for Fact 24.59: if a matrix commutes with `Matrix.diagonal a`, then it has no entries
connecting two distinct value plateaus of `a`. -/
private theorem cross_block_entry_eq_zero_of_diagonal_commute
    {N : ℕ} {a : Fin N → ℝ} {C : Matrix (Fin N) (Fin N) ℝ}
    (hcomm : Commute (Matrix.diagonal a) C)
    {i j : Fin N} (hij : a i ≠ a j) :
    C i j = 0 := by
  have hij_entry :
      (Matrix.diagonal a * C) i j = (C * Matrix.diagonal a) i j := by
    -- Evaluate the diagonal commutation identity at the single entry `(i,j)`.
    exact congrArg (fun M : Matrix (Fin N) (Fin N) ℝ ↦ M i j) hcomm.eq
  have hfactor : (a i - a j) * C i j = 0 := by
    -- After expanding the diagonal actions, the scalar factor `a i - a j` annihilates `C i j`.
    have hij_entry' : a i * C i j = C i j * a j := by
      simpa [diagonal_mul_apply, mul_diagonal_apply] using hij_entry
    nlinarith [hij_entry']
  have hneq : a i - a j ≠ 0 := sub_ne_zero.mpr hij
  exact (mul_eq_zero.mp hfactor).resolve_left hneq

/-- Helper for Fact 24.59: once `Matrix.diagonal a` commutes with `C`, every strict-drop prefix
projector of the antitone diagonal `a` also commutes with `C`. -/
private theorem strict_drop_prefix_commutes_of_diagonal_commute
    {N : ℕ} {a : Fin N → ℝ} (ha : Antitone a)
    {C : Matrix (Fin N) (Fin N) ℝ}
    (hcomm : Commute (Matrix.diagonal a) C)
    {r : Fin N} (hrN : r.1 + 1 < N)
    (hr : a r > a ⟨r.1 + 1, hrN⟩) :
    Commute (prefixProj r) C := by
  change prefixProj r * C = C * prefixProj r
  ext i j
  -- Compare the two prefix-projected entries and split by whether the row and column lie in the
  -- strict-drop prefix cut.
  rw [prefixProj_mul_apply, mul_prefixProj_apply]
  by_cases hir : i ≤ r <;> by_cases hjr : j ≤ r
  · simp [hir, hjr]
  · have hsj : a j ≤ a ⟨r.1 + 1, hrN⟩ := by
      -- Indices strictly after `r` lie on the weakly smaller side of the strict drop.
      have hsuccj : ⟨r.1 + 1, hrN⟩ ≤ j := by
        apply Fin.le_iff_val_le_val.mpr
        exact Nat.succ_le_of_lt (lt_of_not_ge hjr)
      exact ha hsuccj
    have hri : a r ≤ a i := ha hir
    have hij_ne : a i ≠ a j := by
      -- The strict drop separates every prefix value from every tail value.
      symm
      have hsep : a j < a i := by
        calc
          a j ≤ a ⟨r.1 + 1, hrN⟩ := hsj
          _ < a r := hr
          _ ≤ a i := hri
      exact ne_of_lt hsep
    have hCij : C i j = 0 :=
      cross_block_entry_eq_zero_of_diagonal_commute hcomm hij_ne
    simp [hir, hjr, hCij]
  · have hsi : a i ≤ a ⟨r.1 + 1, hrN⟩ := by
      -- The symmetric argument handles rows strictly after `r`.
      have hsucci : ⟨r.1 + 1, hrN⟩ ≤ i := by
        apply Fin.le_iff_val_le_val.mpr
        exact Nat.succ_le_of_lt (lt_of_not_ge hir)
      exact ha hsucci
    have hrj : a r ≤ a j := ha hjr
    have hij_ne : a i ≠ a j := by
      have hsep : a i < a j := by
        calc
          a i ≤ a ⟨r.1 + 1, hrN⟩ := hsi
          _ < a r := hr
          _ ≤ a j := hrj
      exact ne_of_lt hsep
    have hCij : C i j = 0 :=
      cross_block_entry_eq_zero_of_diagonal_commute hcomm hij_ne
    simp [hir, hjr, hCij]
  · simp [hir, hjr]

/-- Helper for Fact 24.59: if every supported permutation term in the Birkhoff expansion of the
orthostochastic overlap matrix admits a strict-drop correction, then each strict-drop prefix
projection already attains the corresponding trace equality against `C`. -/
private theorem strict_drop_prefix_trace_eq_of_hsupport_correction
    {N : ℕ} {a b : Fin N → ℝ}
    (ha : Antitone a)
    {C : Matrix (Fin N) (Fin N) ℝ}
    {U : Matrix.orthogonalGroup (Fin N) ℝ}
    (hCdiag : C = (((U : Matrix _ _ ℝ) * Matrix.diagonal b) * (U : Matrix _ _ ℝ)ᵀ))
    (w : Equiv.Perm (Fin N) → ℝ)
    (hw_sum : ∑ σ, w σ = 1)
    (hwM :
      ((fun i j ↦ (((U : Matrix (Fin N) (Fin N) ℝ) i j) ^ 2)) :
        Matrix (Fin N) (Fin N) ℝ) = ∑ σ, w σ • σ.permMatrix ℝ)
    (hsupport_correction :
      ∀ σ : Equiv.Perm (Fin N), w σ ≠ 0 →
        ∃ ρ : Equiv.Perm (Fin N), a ∘ ρ = a ∧ b ∘ σ ∘ ρ = b)
    {r : Fin N} (hrN : r.1 + 1 < N)
    (hr : a r > a ⟨r.1 + 1, hrN⟩) :
    Matrix.trace (prefixProj r * C) = ∑ i, if i ≤ r then b i else 0 := by
  let M : Matrix (Fin N) (Fin N) ℝ := fun i j ↦ (((U : Matrix (Fin N) (Fin N) ℝ) i j) ^ 2)
  have hdiagC : Matrix.diag C = M *ᵥ b := by
    -- Diagonalizing `C` in the `U`-basis exposes the orthostochastic overlap matrix `M`.
    rw [hCdiag]
    simpa [M] using
      diag_orthogonal_conj_diagonal_eq_sq_entry_mulVec
        ((U : Matrix (Fin N) (Fin N) ℝ)) b
  calc
    Matrix.trace (prefixProj r * C) = dotProduct (prefixMask r) (Matrix.diag C) := by
      rw [prefixProj, trace_diagonal_mul_eq_dotProduct_diag]
    _ = dotProduct (prefixMask r) (M *ᵥ b) := by
          rw [hdiagC]
    _ = dotProduct (prefixMask r)
          ((((∑ σ, w σ • σ.permMatrix ℝ) : Matrix (Fin N) (Fin N) ℝ)) *ᵥ b) := by
            simpa [M] using
              congrArg
                (fun X : Matrix (Fin N) (Fin N) ℝ ↦ dotProduct (prefixMask r) (X *ᵥ b))
                hwM
    _ = dotProduct (prefixMask r) (∑ σ, w σ • (b ∘ σ)) := by
          congr 1
          calc
            ((((∑ σ, w σ • σ.permMatrix ℝ) : Matrix (Fin N) (Fin N) ℝ)) *ᵥ b)
                = ∑ σ, ((w σ • σ.permMatrix ℝ : Matrix (Fin N) (Fin N) ℝ) *ᵥ b) := by
                    simpa using
                      (Matrix.sum_mulVec Finset.univ
                        (fun σ : Equiv.Perm (Fin N) ↦
                          (w σ • σ.permMatrix ℝ : Matrix (Fin N) (Fin N) ℝ))
                        b)
            _ = ∑ σ, w σ • (b ∘ σ) := by
                  refine Finset.sum_congr rfl ?_
                  intro σ hσ
                  rw [smul_mulVec, Matrix.permMatrix_mulVec]
    _ = ∑ σ, dotProduct (prefixMask r) (w σ • (b ∘ σ)) := by
          simpa using
            (dotProduct_sum (prefixMask r) Finset.univ
              (fun σ : Equiv.Perm (Fin N) ↦ w σ • (b ∘ σ)))
    _ = ∑ σ, w σ * dotProduct (prefixMask r) (b ∘ σ) := by
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          rw [dotProduct_smul]
          simp [smul_eq_mul]
    _ = ∑ σ, w σ * (∑ i, if i ≤ r then b i else 0) := by
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          by_cases hwσ : w σ = 0
          · simp [hwσ]
          · rw [dotProduct_prefixMask_eq_sum_prefix]
            rw [supported_perm_prefix_sum_eq_of_strict_drop ha hrN hr
              (hsupport_correction σ hwσ)]
    _ = (∑ σ, w σ) * (∑ i, if i ≤ r then b i else 0) := by
          rw [Finset.sum_mul]
    _ = ∑ i, if i ≤ r then b i else 0 := by
          simp [hw_sum]

/-- Helper for Fact 24.59: if both factors use the same orthogonal basis, the trace pairing of
their diagonal conjugates is the dot product of the two diagonal vectors. -/
private theorem trace_orthogonal_conj_diagonal_mul_eq_dotProduct
    {n : Type u} [Fintype n] [DecidableEq n]
    (U : Matrix.orthogonalGroup n ℝ) (a b : n → ℝ) :
    Matrix.trace
        (((((U : Matrix n n ℝ) * Matrix.diagonal a) * (U : Matrix n n ℝ)ᵀ) *
            (((U : Matrix n n ℝ) * Matrix.diagonal b) * (U : Matrix n n ℝ)ᵀ)) :
          Matrix n n ℝ) =
      dotProduct a b := by
  let UM : Matrix n n ℝ := U
  have hUtU : UMᵀ * UM = 1 := orthogonal_transpose_mul_eq_one U.prop
  -- Move the common orthogonal basis through the trace until only the diagonal core remains.
  calc
    Matrix.trace
        (((((U : Matrix n n ℝ) * Matrix.diagonal a) * (U : Matrix n n ℝ)ᵀ) *
            (((U : Matrix n n ℝ) * Matrix.diagonal b) * (U : Matrix n n ℝ)ᵀ)) :
          Matrix n n ℝ)
        = Matrix.trace ((UM * (Matrix.diagonal a * (UMᵀ * UM) * Matrix.diagonal b)) * UMᵀ) := by
            simp [UM, Matrix.mul_assoc]
    _ = Matrix.trace ((UM * (Matrix.diagonal a * Matrix.diagonal b)) * UMᵀ) := by
          simp [hUtU, Matrix.mul_assoc]
    _ = Matrix.trace ((Matrix.diagonal a) * (Matrix.diagonal b)) := by
          calc
            Matrix.trace ((UM * (Matrix.diagonal a * Matrix.diagonal b)) * UMᵀ)
                = Matrix.trace (UMᵀ * (UM * (Matrix.diagonal a * Matrix.diagonal b))) := by
                    simpa [Matrix.mul_assoc] using
                      (Matrix.trace_mul_cycle UM (Matrix.diagonal a * Matrix.diagonal b) UMᵀ)
            _ = Matrix.trace ((Matrix.diagonal a) * (Matrix.diagonal b)) := by
                  rw [show UMᵀ * (UM * (Matrix.diagonal a * Matrix.diagonal b)) =
                      (UMᵀ * UM) * (Matrix.diagonal a * Matrix.diagonal b) by
                        simp [Matrix.mul_assoc]]
                  simp [hUtU]
    _ = dotProduct a b := by
          simp [Matrix.trace, Matrix.mul_apply, dotProduct]

/-- Helper for Fact 24.59: after diagonalizing two Hermitian matrices in orthogonal coordinates,
their trace pairing depends only on the overlap matrix of squared coordinates. -/
private theorem trace_orthogonal_conj_diagonal_mul_eq_dotProduct_sq_entry_mulVec_fin
    {N : ℕ} (U V : Matrix.orthogonalGroup (Fin N) ℝ) (a b : Fin N → ℝ) :
    let W : Matrix (Fin N) (Fin N) ℝ :=
      (U : Matrix (Fin N) (Fin N) ℝ)ᵀ * (V : Matrix (Fin N) (Fin N) ℝ)
    Matrix.trace
        (((((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
              (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) *
            (((V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal b) *
              (V : Matrix (Fin N) (Fin N) ℝ)ᵀ)) : Matrix (Fin N) (Fin N) ℝ) =
      dotProduct a (((fun i j ↦ (W i j) ^ 2) : Matrix (Fin N) (Fin N) ℝ) *ᵥ b) := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  let VM : Matrix (Fin N) (Fin N) ℝ := V
  let W : Matrix (Fin N) (Fin N) ℝ := UMᵀ * VM
  have htrace :
      Matrix.trace
          (((((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
                (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) *
              (((V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal b) *
                (V : Matrix (Fin N) (Fin N) ℝ)ᵀ)) : Matrix (Fin N) (Fin N) ℝ) =
        Matrix.trace ((Matrix.diagonal a) * (W * Matrix.diagonal b * Wᵀ)) := by
    -- Cycle the trace until the common `U`-basis exposes the overlap matrix `W = UᵀV`.
    calc
      Matrix.trace
          (((((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
                (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) *
              (((V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal b) *
                (V : Matrix (Fin N) (Fin N) ℝ)ᵀ)) : Matrix (Fin N) (Fin N) ℝ)
          =
            Matrix.trace
              ((((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
                  ((U : Matrix (Fin N) (Fin N) ℝ)ᵀ *
                    (((V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal b) *
                      (V : Matrix (Fin N) (Fin N) ℝ)ᵀ))) :
                Matrix (Fin N) (Fin N) ℝ) := by
              simp [Matrix.mul_assoc]
      _ =
            Matrix.trace
              ((((U : Matrix (Fin N) (Fin N) ℝ)ᵀ *
                    (((V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal b) *
                      (V : Matrix (Fin N) (Fin N) ℝ)ᵀ)) *
                  ((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a)) :
                Matrix (Fin N) (Fin N) ℝ) := by
              exact Matrix.trace_mul_comm _ _
      _ =
            Matrix.trace
              (((((U : Matrix (Fin N) (Fin N) ℝ)ᵀ *
                      (((V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal b) *
                        (V : Matrix (Fin N) (Fin N) ℝ)ᵀ)) *
                    (U : Matrix (Fin N) (Fin N) ℝ)) *
                  Matrix.diagonal a) :
                Matrix (Fin N) (Fin N) ℝ) := by
              simp [Matrix.mul_assoc]
      _ = Matrix.trace (((W * Matrix.diagonal b * Wᵀ) * Matrix.diagonal a) :
            Matrix (Fin N) (Fin N) ℝ) := by
            simp [W, UM, VM, Matrix.mul_assoc, Matrix.transpose_mul]
      _ = Matrix.trace ((Matrix.diagonal a) * (W * Matrix.diagonal b * Wᵀ)) := by
            exact Matrix.trace_mul_comm _ _
  calc
    Matrix.trace
        (((((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
              (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) *
            (((V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal b) *
              (V : Matrix (Fin N) (Fin N) ℝ)ᵀ)) : Matrix (Fin N) (Fin N) ℝ)
        = Matrix.trace ((Matrix.diagonal a) * (W * Matrix.diagonal b * Wᵀ)) := htrace
    _ = dotProduct a (Matrix.diag (W * Matrix.diagonal b * Wᵀ)) := by
          rw [trace_diagonal_mul_eq_dotProduct_diag]
    _ = dotProduct a (((fun i j ↦ (W i j) ^ 2) : Matrix (Fin N) (Fin N) ℝ) *ᵥ b) := by
          simpa [W] using
            congrArg (fun x : Fin N → ℝ ↦ dotProduct a x)
              (diag_orthogonal_conj_diagonal_eq_sq_entry_mulVec W b)

/-- Helper for Fact 24.59: once the squared-entry overlap matrix is written as a Birkhoff sum,
its action on a vector is the corresponding convex combination of permuted vectors. -/
private theorem birkhoff_sum_permMatrix_mulVec_eq_sum_smul_comp_perm_fin
    {N : ℕ} (b : Fin N → ℝ) (w : Equiv.Perm (Fin N) → ℝ) :
    ((((∑ σ, w σ • σ.permMatrix ℝ) : Matrix (Fin N) (Fin N) ℝ)) *ᵥ b) =
      ∑ σ, w σ • (b ∘ σ) := by
  classical
  -- Push the matrix sum through `mulVec`, then evaluate each permutation matrix on `b`.
  calc
    ((((∑ σ, w σ • σ.permMatrix ℝ) : Matrix (Fin N) (Fin N) ℝ)) *ᵥ b)
        = ∑ σ, ((w σ • σ.permMatrix ℝ : Matrix (Fin N) (Fin N) ℝ) *ᵥ b) := by
            simpa using
              (Matrix.sum_mulVec Finset.univ
                (fun σ : Equiv.Perm (Fin N) ↦
                  (w σ • σ.permMatrix ℝ : Matrix (Fin N) (Fin N) ℝ))
                b)
    _ = ∑ σ, w σ • (b ∘ σ) := by
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          rw [smul_mulVec, Matrix.permMatrix_mulVec]

/-- Helper for Fact 24.59: pairing the Birkhoff sum action with a fixed vector turns the matrix
rewrite into the corresponding convex combination of rearrangement terms. -/
private theorem dotProduct_birkhoff_sum_permMatrix_mulVec_eq_sum_mul_dotProduct_comp_perm_fin
    {N : ℕ} (a b : Fin N → ℝ) (w : Equiv.Perm (Fin N) → ℝ) :
    dotProduct a ((((∑ σ, w σ • σ.permMatrix ℝ) : Matrix (Fin N) (Fin N) ℝ)) *ᵥ b) =
      ∑ σ, w σ * dotProduct a (b ∘ σ) := by
  classical
  -- First normalize the `mulVec`, then distribute the dot product over the resulting finite sum.
  calc
    dotProduct a ((((∑ σ, w σ • σ.permMatrix ℝ) : Matrix (Fin N) (Fin N) ℝ)) *ᵥ b)
        = dotProduct a (∑ σ, w σ • (b ∘ σ)) := by
            rw [birkhoff_sum_permMatrix_mulVec_eq_sum_smul_comp_perm_fin]
    _ = ∑ σ, dotProduct a (w σ • (b ∘ σ)) := by
          simpa using
            (dotProduct_sum a Finset.univ
              (fun σ : Equiv.Perm (Fin N) ↦ w σ • (b ∘ σ)))
    _ = ∑ σ, w σ * dotProduct a (b ∘ σ) := by
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          rw [dotProduct_smul]
          simp [smul_eq_mul]

/-- Helper for Fact 24.59: the rearrangement inequality is stable under convex combinations of the
permuted second factor. -/
private theorem convex_sum_dotProduct_comp_perm_le_dotProduct_fin
    {N : ℕ} (a b : Fin N → ℝ) (w : Equiv.Perm (Fin N) → ℝ)
    (hw_nonneg : ∀ σ, 0 ≤ w σ) (hw_sum : ∑ σ, w σ = 1) (hmono : Monovary a b) :
    ∑ σ, w σ * dotProduct a (b ∘ σ) ≤ dotProduct a b := by
  have hterm :
      ∀ σ : Equiv.Perm (Fin N), dotProduct a (b ∘ σ) ≤ dotProduct a b := by
    intro σ
    -- Each permutation term is bounded by the rearrangement inequality for the same monovary pair.
    simpa [dotProduct] using hmono.sum_mul_comp_perm_le_sum_mul (σ := σ)
  calc
    ∑ σ, w σ * dotProduct a (b ∘ σ) ≤ ∑ σ, w σ * dotProduct a b := by
      refine Finset.sum_le_sum ?_
      intro σ hσ
      exact mul_le_mul_of_nonneg_left (hterm σ) (hw_nonneg σ)
    _ = (∑ σ, w σ) * dotProduct a b := by
          rw [Finset.sum_mul]
    _ = dotProduct a b := by
          simp [hw_sum]

/-- Helper for Fact 24.59: on `Fin N`, the common reindex from `eigenvalues₀` to `eigenvalues`
does not change their dot product. -/
private theorem dotProduct_eigenvalues_eq_dotProduct_eigenvalues₀_fin {N : ℕ}
    {H K : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    dotProduct hH.eigenvalues hK.eigenvalues = dotProduct hH.eigenvalues₀ hK.eigenvalues₀ := by
  let e : Fin N ≃ Fin (Fintype.card (Fin N)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N)))).symm
  -- Both `eigenvalues` lists are the same simultaneous permutation of the `eigenvalues₀` lists.
  unfold Matrix.IsHermitian.eigenvalues
  simpa [dotProduct, e] using
    (Equiv.sum_comp e (fun i : Fin (Fintype.card (Fin N)) ↦ hH.eigenvalues₀ i * hK.eigenvalues₀ i))

/-- Helper for Fact 24.59: transporting a dot product along the canonical card-preserving cast
between `Fin N` and `Fin (card (Fin N))` does not change its value. -/
private theorem dotProduct_cast_card_fin_eq {N : ℕ}
    (a b : Fin (Fintype.card (Fin N)) → ℝ) :
    dotProduct a b =
      dotProduct (fun i : Fin N ↦ a ((finCongr (Fintype.card_fin N).symm) i))
        (fun i : Fin N ↦ b ((finCongr (Fintype.card_fin N).symm) i)) := by
  let e : Fin N ≃ Fin (Fintype.card (Fin N)) :=
    finCongr (Fintype.card_fin N).symm
  -- This is a pure reindexing of the same finite sum.
  unfold dotProduct
  simpa [e] using
    (Equiv.sum_comp e (fun i : Fin (Fintype.card (Fin N)) ↦ a i * b i)).symm

/-- Helper for Fact 24.59: reindexing a Hermitian matrix to `Fin (Fintype.card ι)` preserves its
canonical ordered spectrum `eigenvalues₀`. -/
private theorem reindexFin_eigenvalues₀_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.IsHermitian) :
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let hHfin : (Matrix.reindex e e H).IsHermitian := hH.reindex e
    List.ofFn hHfin.eigenvalues₀ = List.ofFn hH.eigenvalues₀ := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let hHfin : (Matrix.reindex e e H).IsHermitian := hH.reindex e
  -- Both canonical spectra are the same sorted real roots of the common characteristic polynomial.
  calc
    List.ofFn hHfin.eigenvalues₀
        = ((Matrix.reindex e e H).charpoly.roots.map RCLike.re).sort (· ≥ ·) := by
            simpa [hHfin] using hHfin.sort_roots_charpoly_eq_eigenvalues₀.symm
    _ = (H.charpoly.roots.map RCLike.re).sort (· ≥ ·) := by
          rw [Matrix.charpoly_reindex]
    _ = List.ofFn hH.eigenvalues₀ := by
          simpa using hH.sort_roots_charpoly_eq_eigenvalues₀

/-- Helper for Fact 24.59: transporting a diagonalization back along a reindex equivalence moves
both the orthogonal factor and the diagonal entries by the same equivalence. -/
private theorem reindex_symm_diagonalization_eq
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (U : Matrix m m ℝ) (d : m → ℝ) :
    Matrix.reindex e.symm e.symm (((U * Matrix.diagonal d) * Uᵀ) : Matrix m m ℝ) =
      (((Matrix.reindex e.symm e.symm U) * Matrix.diagonal (d ∘ e)) *
        (Matrix.reindex e.symm e.symm U)ᵀ : Matrix n n ℝ) := by
  have hmul :
      Matrix.reindex e.symm e.symm (U * Matrix.diagonal d) =
        (Matrix.reindex e.symm e.symm U) * Matrix.reindex e.symm e.symm (Matrix.diagonal d) := by
    -- Reindexing is multiplicative on square matrices once all three indices are transported by
    -- the same equivalence.
    simpa using
      (Matrix.submatrix_mul_equiv U (Matrix.diagonal d) e e e).symm
  -- Reindex the two multiplication steps separately, then rewrite the diagonal surface through `e`.
  calc
    Matrix.reindex e.symm e.symm (((U * Matrix.diagonal d) * Uᵀ) : Matrix m m ℝ)
        = (Matrix.reindex e.symm e.symm (U * Matrix.diagonal d) *
            Matrix.reindex e.symm e.symm Uᵀ : Matrix n n ℝ) := by
            simpa using
              (Matrix.submatrix_mul_equiv (U * Matrix.diagonal d) Uᵀ e e id)
    _ = (((Matrix.reindex e.symm e.symm U) * Matrix.reindex e.symm e.symm (Matrix.diagonal d)) *
            Matrix.reindex e.symm e.symm Uᵀ : Matrix n n ℝ) := by
          rw [hmul]
    _ = (((Matrix.reindex e.symm e.symm U) * Matrix.diagonal (d ∘ e)) *
            (Matrix.reindex e.symm e.symm U)ᵀ : Matrix n n ℝ) := by
          simp [Matrix.mul_assoc, Matrix.reindex_apply]

/-- Helper for Fact 24.59: reindexing a square matrix along an equivalence preserves its trace. -/
private theorem trace_reindex_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : Matrix ι ι ℝ) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  -- Reindexing only permutes the diagonal summands in the trace.
  unfold Matrix.trace
  simpa [Matrix.diag_apply, Matrix.reindex_apply] using
    (Equiv.sum_comp e.symm (fun i : ι ↦ M i i))

/-- Helper for Fact 24.59: for real Hermitian matrices on `Fin N`, the trace pairing is bounded by
the dot product of the decreasing eigenvalue lists. -/
private theorem trace_le_eigenvalues_dotProduct_local {N : ℕ}
    {H K : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    Matrix.trace (H * K) ≤ dotProduct hH.eigenvalues hK.eigenvalues := by
  classical
  let U : Matrix.orthogonalGroup (Fin N) ℝ :=
    ⟨hH.eigenvectorUnitary, by
      simpa using hH.eigenvectorUnitary.prop⟩
  let V : Matrix.orthogonalGroup (Fin N) ℝ :=
    ⟨hK.eigenvectorUnitary, by
      simpa using hK.eigenvectorUnitary.prop⟩
  let W : Matrix (Fin N) (Fin N) ℝ :=
    (U : Matrix (Fin N) (Fin N) ℝ)ᵀ * (V : Matrix (Fin N) (Fin N) ℝ)
  have hHdiag :
      H =
        (((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal hH.eigenvalues) *
          (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) := by
    -- Put `H` in its canonical orthogonal eigenbasis before invoking the Birkhoff route.
    simpa [U, Matrix.conjTranspose_eq_transpose_of_trivial, Unitary.conjStarAlgAut_apply,
      Matrix.mul_assoc] using hH.spectral_theorem
  have hKdiag :
      K =
        (((V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal hK.eigenvalues) *
          (V : Matrix (Fin N) (Fin N) ℝ)ᵀ) := by
    -- The same canonical orthogonal diagonalization is used for `K`.
    simpa [V, Matrix.conjTranspose_eq_transpose_of_trivial, Unitary.conjStarAlgAut_apply,
      Matrix.mul_assoc] using hK.spectral_theorem
  have hWWt : W * Wᵀ = 1 := by
    have hVorth :
        ((V : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)ᵀ) = 1 :=
      orthogonal_mul_transpose_eq_one V.prop
    have hUorth :
        ((U : Matrix (Fin N) (Fin N) ℝ)ᵀ * (U : Matrix (Fin N) (Fin N) ℝ)) = 1 :=
      orthogonal_transpose_mul_eq_one U.prop
    -- The overlap matrix `W = Uᵀ V` is again orthogonal.
    calc
      W * Wᵀ
          = (((U : Matrix (Fin N) (Fin N) ℝ)ᵀ * (V : Matrix (Fin N) (Fin N) ℝ)) *
              (((U : Matrix (Fin N) (Fin N) ℝ)ᵀ * (V : Matrix (Fin N) (Fin N) ℝ))ᵀ)) := by
              rfl
      _ = (((U : Matrix (Fin N) (Fin N) ℝ)ᵀ * (V : Matrix (Fin N) (Fin N) ℝ)) *
            ((V : Matrix (Fin N) (Fin N) ℝ)ᵀ * (U : Matrix (Fin N) (Fin N) ℝ))) := by
            simp [Matrix.transpose_mul]
      _ = (U : Matrix (Fin N) (Fin N) ℝ)ᵀ *
            (((V : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)ᵀ) *
              (U : Matrix (Fin N) (Fin N) ℝ)) := by
            simp [Matrix.mul_assoc]
      _ = (U : Matrix (Fin N) (Fin N) ℝ)ᵀ * (U : Matrix (Fin N) (Fin N) ℝ) := by
            simp [hVorth]
      _ = 1 := hUorth
  have hWtW : Wᵀ * W = 1 := by
    have hUorth :
        ((U : Matrix (Fin N) (Fin N) ℝ) * (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) = 1 :=
      orthogonal_mul_transpose_eq_one U.prop
    have hVorth :
        ((V : Matrix (Fin N) (Fin N) ℝ)ᵀ * (V : Matrix (Fin N) (Fin N) ℝ)) = 1 :=
      orthogonal_transpose_mul_eq_one V.prop
    -- The same computation on the other side gives `Wᵀ W = 1`.
    calc
      Wᵀ * W
          = ((((U : Matrix (Fin N) (Fin N) ℝ)ᵀ * (V : Matrix (Fin N) (Fin N) ℝ))ᵀ) *
              ((U : Matrix (Fin N) (Fin N) ℝ)ᵀ * (V : Matrix (Fin N) (Fin N) ℝ))) := by
              rfl
      _ = (((V : Matrix (Fin N) (Fin N) ℝ)ᵀ * (U : Matrix (Fin N) (Fin N) ℝ)) *
            ((U : Matrix (Fin N) (Fin N) ℝ)ᵀ * (V : Matrix (Fin N) (Fin N) ℝ))) := by
            simp [Matrix.transpose_mul]
      _ = (V : Matrix (Fin N) (Fin N) ℝ)ᵀ *
            (((U : Matrix (Fin N) (Fin N) ℝ) * (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) *
              (V : Matrix (Fin N) (Fin N) ℝ)) := by
            simp [Matrix.mul_assoc]
      _ = (V : Matrix (Fin N) (Fin N) ℝ)ᵀ * (V : Matrix (Fin N) (Fin N) ℝ) := by
            simp [hUorth]
      _ = 1 := hVorth
  have hMmem :
      ((fun i j ↦ (W i j) ^ 2) : Matrix (Fin N) (Fin N) ℝ) ∈ doublyStochastic ℝ (Fin N) :=
    sq_entry_matrix_mem_doublyStochastic hWWt hWtW
  rcases exists_eq_sum_perm_of_mem_doublyStochastic hMmem with ⟨w, hw_nonneg, hw_sum, hwM⟩
  let e : Fin (Fintype.card (Fin N)) ≃ Fin N :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N)))
  have hmono₀ : Monovary hH.eigenvalues₀ hK.eigenvalues₀ :=
    (hH.eigenvalues₀_antitone).monovary (hK.eigenvalues₀_antitone)
  have hmono : Monovary hH.eigenvalues hK.eigenvalues := by
    -- The arbitrary `Fin N` indexing of `eigenvalues` is the same reindexing on both spectra.
    simpa [Matrix.IsHermitian.eigenvalues, e, Function.comp] using hmono₀.comp_right e.symm
  calc
    Matrix.trace (H * K)
        = Matrix.trace
            (((((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal hH.eigenvalues) *
                (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) *
              (((V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal hK.eigenvalues) *
                (V : Matrix (Fin N) (Fin N) ℝ)ᵀ)) :
              Matrix (Fin N) (Fin N) ℝ) := by
            simp [hHdiag, hKdiag]
    _ = dotProduct hH.eigenvalues
          ((((fun i j ↦ (W i j) ^ 2) : Matrix (Fin N) (Fin N) ℝ) *ᵥ hK.eigenvalues)) := by
          -- The trace pairing reduces to the overlap matrix between the two orthogonal
          -- eigenbases.
          simpa [W] using
            trace_orthogonal_conj_diagonal_mul_eq_dotProduct_sq_entry_mulVec_fin
              U V hH.eigenvalues hK.eigenvalues
    _ = dotProduct hH.eigenvalues
          ((((∑ σ, w σ • σ.permMatrix ℝ) : Matrix (Fin N) (Fin N) ℝ)) *ᵥ hK.eigenvalues) := by
          -- Replace the orthostochastic overlap matrix by its Birkhoff expansion.
          symm
          simpa [W] using
            congrArg
              (fun X : Matrix (Fin N) (Fin N) ℝ ↦ dotProduct hH.eigenvalues (X *ᵥ hK.eigenvalues))
              hwM
    _ = ∑ σ, w σ * dotProduct hH.eigenvalues (hK.eigenvalues ∘ σ) := by
          -- Push the convex decomposition through `mulVec` and the dot product.
          exact
            dotProduct_birkhoff_sum_permMatrix_mulVec_eq_sum_mul_dotProduct_comp_perm_fin
              hH.eigenvalues hK.eigenvalues w
    _ ≤ dotProduct hH.eigenvalues hK.eigenvalues := by
          -- Each permutation term is bounded by the rearrangement inequality.
          exact convex_sum_dotProduct_comp_perm_le_dotProduct_fin
            hH.eigenvalues hK.eigenvalues w hw_nonneg hw_sum hmono

/-- Helper for Fact 24.59: reindexing to `Fin (Fintype.card ι)` packages the general Hermitian
trace bound in a single canonical `Fin` model. -/
private theorem trace_le_reindexFin_eigenvalues_dotProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H K : Matrix ι ι ℝ} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let Hfin : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ := Matrix.reindex e e H
    let Kfin : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ := Matrix.reindex e e K
    let hHfin : Hfin.IsHermitian := hH.reindex e
    let hKfin : Kfin.IsHermitian := hK.reindex e
    Matrix.trace (H * K) ≤ dotProduct hHfin.eigenvalues hKfin.eigenvalues := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Hfin : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ := Matrix.reindex e e H
  let Kfin : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ := Matrix.reindex e e K
  let hHfin : Hfin.IsHermitian := hH.reindex e
  let hKfin : Kfin.IsHermitian := hK.reindex e
  have htrace :
      Matrix.trace (H * K) = Matrix.trace (Hfin * Kfin) := by
    -- Multiplication commutes with reindexing, and the resulting diagonal sum is unchanged.
    calc
      Matrix.trace (H * K) = Matrix.trace (Matrix.reindex e e (H * K)) := by
        rw [trace_reindex_eq e (H * K)]
      _ = Matrix.trace (Hfin * Kfin) := by
        simp [Hfin, Kfin]
  -- Route correction: package the arbitrary finite index type as a single `Fin` model, then apply
  -- the source-faithful local inequality already proved on that model.
  calc
    Matrix.trace (H * K) = Matrix.trace (Hfin * Kfin) := htrace
    _ ≤ dotProduct hHfin.eigenvalues hKfin.eigenvalues :=
          trace_le_eigenvalues_dotProduct_local hHfin hKfin

/-- Helper for Fact 24.59: the Hermitian trace bound can be stated directly in terms of the
canonical ordered spectra `eigenvalues₀`. -/
private theorem trace_le_eigenvalues₀_dotProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H K : Matrix ι ι ℝ} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    Matrix.trace (H * K) ≤ dotProduct hH.eigenvalues₀ hK.eigenvalues₀ := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Hfin : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ := Matrix.reindex e e H
  let Kfin : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ := Matrix.reindex e e K
  let hHfin : Hfin.IsHermitian := hH.reindex e
  let hKfin : Kfin.IsHermitian := hK.reindex e
  let a₀ : Fin (Fintype.card ι) → ℝ := fun i ↦
    hHfin.eigenvalues₀ (Fin.cast (Fintype.card_fin (Fintype.card ι)).symm i)
  let b₀ : Fin (Fintype.card ι) → ℝ := fun i ↦
    hKfin.eigenvalues₀ (Fin.cast (Fintype.card_fin (Fintype.card ι)).symm i)
  have htrace_bound :
      Matrix.trace (H * K) ≤ dotProduct hHfin.eigenvalues hKfin.eigenvalues := by
    -- First move to the canonical `Fin` model where the local trace theorem applies.
    simpa [e, Hfin, Kfin, hHfin, hKfin] using trace_le_reindexFin_eigenvalues_dotProduct hH hK
  have hH₀ : a₀ = hH.eigenvalues₀ := by
    -- Then remove the reindexing from the canonical ordered spectrum.
    apply List.ofFn_inj.mp
    simpa [a₀, e, Hfin, hHfin, Fintype.card_fin] using
      (reindexFin_eigenvalues₀_eq (ι := ι) (H := H) (hH := hH))
  have hK₀ : b₀ = hK.eigenvalues₀ := by
    -- The same transport is used for the second Hermitian matrix.
    apply List.ofFn_inj.mp
    simpa [b₀, e, Kfin, hKfin, Fintype.card_fin] using
      (reindexFin_eigenvalues₀_eq (ι := ι) (H := K) (hH := hK))
  have ha₀_finCongr :
      (fun i : Fin (Fintype.card ι) ↦
        hHfin.eigenvalues₀ ((finCongr (Fintype.card_fin (Fintype.card ι)).symm) i)) = a₀ := by
    -- The `finCongr` and `Fin.cast` presentations of the same index transport agree pointwise.
    funext i
    cases i
    rfl
  have hb₀_finCongr :
      (fun i : Fin (Fintype.card ι) ↦
        hKfin.eigenvalues₀ ((finCongr (Fintype.card_fin (Fintype.card ι)).symm) i)) = b₀ := by
    -- The same transport agreement is used for the second ordered spectrum.
    funext i
    cases i
    rfl
  have hcast_dot :
      dotProduct hHfin.eigenvalues₀ hKfin.eigenvalues₀ = dotProduct a₀ b₀ := by
    -- Pull the `Fin (card (Fin _))` sum back to the canonical `Fin _` indexing, then rewrite the
    -- transport into the `Fin.cast` form used by `a₀` and `b₀`.
    calc
      dotProduct hHfin.eigenvalues₀ hKfin.eigenvalues₀
          = dotProduct
              (fun i : Fin (Fintype.card ι) ↦
                hHfin.eigenvalues₀ ((finCongr (Fintype.card_fin (Fintype.card ι)).symm) i))
              (fun i : Fin (Fintype.card ι) ↦
                hKfin.eigenvalues₀ ((finCongr (Fintype.card_fin (Fintype.card ι)).symm) i)) := by
                  simpa using dotProduct_cast_card_fin_eq hHfin.eigenvalues₀ hKfin.eigenvalues₀
      _ = dotProduct a₀ b₀ := by
            rw [ha₀_finCongr, hb₀_finCongr]
  have hdot₀ :
      dotProduct hHfin.eigenvalues hKfin.eigenvalues = dotProduct a₀ b₀ := by
    -- Replace `eigenvalues` by `eigenvalues₀` on the `Fin` model and then discharge the reindex.
    calc
      dotProduct hHfin.eigenvalues hKfin.eigenvalues
          = dotProduct hHfin.eigenvalues₀ hKfin.eigenvalues₀ := by
              simpa using dotProduct_eigenvalues_eq_dotProduct_eigenvalues₀_fin hHfin hKfin
      _ = dotProduct a₀ b₀ := hcast_dot
  calc
    Matrix.trace (H * K) ≤ dotProduct hHfin.eigenvalues hKfin.eigenvalues := htrace_bound
    _ = dotProduct a₀ b₀ := hdot₀
    _ = dotProduct hH.eigenvalues₀ hK.eigenvalues₀ := by
          rw [hH₀, hK₀]

/-- Helper for Fact 24.59: passing from `eigenvalues₀` to the entry-indexed `eigenvalues` leaves
their dot product unchanged. -/
private theorem dotProduct_eigenvalues_eq_dotProduct_eigenvalues₀
    {n : Type u} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    dotProduct hA.eigenvalues hB.eigenvalues = dotProduct hA.eigenvalues₀ hB.eigenvalues₀ := by
  let e : n ≃ Fin (Fintype.card n) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm
  -- Both `eigenvalues` vectors are the same simultaneous reindexing of the canonical lists.
  unfold Matrix.IsHermitian.eigenvalues
  simpa [dotProduct, e] using
    (Equiv.sum_comp e (fun i : Fin (Fintype.card n) ↦ hA.eigenvalues₀ i * hB.eigenvalues₀ i))

/-- Helper for Fact 24.59: squaring the Frobenius norm gives the sum of the squared entries. -/
private theorem frobenius_norm_sq_eq_sum
    {n : Type u} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  -- Expand the Frobenius norm and collapse the resulting square root.
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul]
  · norm_num
  · positivity

/-- Helper for Fact 24.59: the Frobenius norm square of a real matrix is `trace (Aᵀ A)`. -/
private theorem frobenius_norm_sq_eq_trace_transpose_mul
    {n : Type u} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    ‖A‖ ^ 2 = Matrix.trace (Aᵀ * A) := by
  -- Compare both sides entrywise after expanding the trace diagonal and swapping the finite sums.
  calc
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := frobenius_norm_sq_eq_sum A
    _ = ∑ j, ∑ i, A i j * A i j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro j hj
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [sq_abs, sq]
    _ = Matrix.trace (Aᵀ * A) := by
          simp [Matrix.trace, Matrix.mul_apply]

/-- Helper for Fact 24.59: the trace of `A²` equals the squared Euclidean norm of its canonical
ordered eigenvalue vector. -/
private theorem trace_mul_self_eq_dotProduct_eigenvalues
    {n : Type u} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    Matrix.trace (A * A) = dotProduct hA.eigenvalues hA.eigenvalues := by
  let a : n → ℝ := hA.eigenvalues
  let U : Matrix.orthogonalGroup n ℝ :=
    ⟨hA.eigenvectorUnitary, by
      simpa using hA.eigenvectorUnitary.prop⟩
  have hdiag :
      A = ((U : Matrix n n ℝ) * Matrix.diagonal a) * (U : Matrix n n ℝ)ᵀ := by
    -- The spectral theorem diagonalizes `A` in its orthogonal eigenbasis.
    simpa [a, U, Matrix.conjTranspose_eq_transpose_of_trivial, Unitary.conjStarAlgAut_apply,
      Matrix.mul_assoc] using hA.spectral_theorem
  -- Once both factors share the same orthogonal basis, the trace collapses to the diagonal
  -- dot product.
  calc
    Matrix.trace (A * A)
        = Matrix.trace
            (((((U : Matrix n n ℝ) * Matrix.diagonal a) * (U : Matrix n n ℝ)ᵀ) *
              (((U : Matrix n n ℝ) * Matrix.diagonal a) * (U : Matrix n n ℝ)ᵀ)) :
                Matrix n n ℝ) := by
            rw [hdiag]
    _ = dotProduct a a := trace_orthogonal_conj_diagonal_mul_eq_dotProduct U a a
    _ = dotProduct hA.eigenvalues hA.eigenvalues := by
          simp [a]

/-- Helper for Fact 24.59: the Euclidean norm of the canonical ordered eigenvalue vector equals the
Frobenius norm of the Hermitian matrix. -/
private theorem eigenvalue_vector_norm_eq_frobenius_norm
    {n : Type u} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    ‖(EuclideanSpace.equiv n ℝ).symm hA.eigenvalues‖ = ‖A‖ := by
  have hAtrans : Aᵀ = A := by
    -- Over `ℝ`, Hermitian and symmetric coincide.
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  have hvecsq :
      ‖(EuclideanSpace.equiv n ℝ).symm hA.eigenvalues‖ ^ 2 =
        dotProduct hA.eigenvalues hA.eigenvalues := by
    -- The Euclidean norm square is exactly the sum of the squared coordinates.
    simpa [dotProduct, sq] using
      (EuclideanSpace.real_norm_sq_eq ((EuclideanSpace.equiv n ℝ).symm hA.eigenvalues))
  have hmatrixsq :
      ‖A‖ ^ 2 = dotProduct hA.eigenvalues hA.eigenvalues := by
    -- Rewrite the Frobenius square as `trace (Aᵀ A)` and then use the spectral diagonalization.
    calc
      ‖A‖ ^ 2 = Matrix.trace (Aᵀ * A) := frobenius_norm_sq_eq_trace_transpose_mul A
      _ = Matrix.trace (A * A) := by
            simp [hAtrans]
      _ = dotProduct hA.eigenvalues hA.eigenvalues :=
            trace_mul_self_eq_dotProduct_eigenvalues hA
  have hsq :
      ‖(EuclideanSpace.equiv n ℝ).symm hA.eigenvalues‖ ^ 2 = ‖A‖ ^ 2 := by
    rw [hvecsq, hmatrixsq]
  nlinarith [hsq, norm_nonneg ((EuclideanSpace.equiv n ℝ).symm hA.eigenvalues), norm_nonneg A]

/-- First inequality from Fact 24.59 (Theobald) (See [344]): the Frobenius pairing is bounded by the dot product
of the canonical
decreasing eigenvalue lists. -/
theorem theobald_trace_le_eigenvalues_dotProduct
    {n : Type u} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Matrix.trace (A * B) ≤ dotProduct hA.eigenvalues hB.eigenvalues := by
  -- First prove the source-faithful inequality on the canonical `eigenvalues₀` model.
  calc
    Matrix.trace (A * B) ≤ dotProduct hA.eigenvalues₀ hB.eigenvalues₀ :=
      trace_le_eigenvalues₀_dotProduct hA hB
    _ = dotProduct hA.eigenvalues hB.eigenvalues := by
          symm
          exact dotProduct_eigenvalues_eq_dotProduct_eigenvalues₀ hA hB

/-- Second inequality from Fact 24.59 (Theobald) (See [344]): the eigenvalue dot product is bounded by the product
of the Euclidean
norms of the canonical decreasing eigenvalue lists. -/
theorem theobald_eigenvalues_dotProduct_le_mul_norm
    {n : Type u} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    dotProduct hA.eigenvalues hB.eigenvalues ≤
      ‖(EuclideanSpace.equiv n ℝ).symm hA.eigenvalues‖ *
        ‖(EuclideanSpace.equiv n ℝ).symm hB.eigenvalues‖ := by
  let x : EuclideanSpace ℝ n := (EuclideanSpace.equiv n ℝ).symm hA.eigenvalues
  let y : EuclideanSpace ℝ n := (EuclideanSpace.equiv n ℝ).symm hB.eigenvalues
  have hinner :
      dotProduct hA.eigenvalues hB.eigenvalues = ⟪x, y⟫_ℝ := by
    -- On the canonical Euclidean model, the real inner product is the coordinate dot product.
    simpa [x, y, dotProduct_comm] using
      (EuclideanSpace.inner_eq_star_dotProduct x y).symm
  -- Apply the real Cauchy--Schwarz inequality after rewriting the dot product as an inner product.
  calc
    dotProduct hA.eigenvalues hB.eigenvalues = ⟪x, y⟫_ℝ := hinner
    _ ≤ |⟪x, y⟫_ℝ| := le_abs_self _
    _ ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y

/-- Norm identity from Fact 24.59 (Theobald) (See [344]): the product of those Euclidean norms equals the
product of the
Frobenius norms. -/
theorem theobald_mul_eigenvalues_norm_eq_mul_frobenius_norm
    {n : Type u} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖(EuclideanSpace.equiv n ℝ).symm hA.eigenvalues‖ *
        ‖(EuclideanSpace.equiv n ℝ).symm hB.eigenvalues‖ =
      ‖A‖ * ‖B‖ := by
  -- Prove the one-matrix identity for each factor and then multiply the resulting equalities.
  rw [eigenvalue_vector_norm_eq_frobenius_norm hA, eigenvalue_vector_norm_eq_frobenius_norm hB]

/-- Helper for Fact 24.59: a permutation matrix is an orthogonal matrix over `ℝ`. -/
private theorem permMatrix_mem_orthogonalGroup_fin
    {n : Type*} [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) :
    (σ.permMatrix ℝ) ∈ Matrix.orthogonalGroup n ℝ := by
  -- The transpose of a permutation matrix is the inverse permutation matrix, so their product is
  -- the identity.
  rw [Matrix.mem_orthogonalGroup_iff]
  calc
    (σ.permMatrix ℝ) * (σ.permMatrix ℝ)ᵀ = (σ⁻¹ * σ).permMatrix ℝ := by
      rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
    _ = 1 := by simp

/-- Helper for Fact 24.59: conjugating a diagonal matrix by a permutation matrix permutes its
diagonal entries by that permutation. -/
private theorem permMatrix_diagonal_mul_transpose_eq_diagonal_comp
    {n : Type*} [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) (d : n → ℝ) :
    ((σ.permMatrix ℝ) * Matrix.diagonal d) * (σ.permMatrix ℝ)ᵀ =
      Matrix.diagonal (d ∘ σ) := by
  have hsymm_inv : (σ⁻¹).symm = σ := by
    ext i
    rfl
  -- View each multiplication by a permutation matrix as a submatrix reindexing, then combine the
  -- two reindexings into a single diagonal permutation.
  calc
    ((σ.permMatrix ℝ) * Matrix.diagonal d) * (σ.permMatrix ℝ)ᵀ
        = ((Matrix.diagonal d).submatrix σ id) * ((σ⁻¹).permMatrix ℝ) := by
            rw [PEquiv.toMatrix_toPEquiv_mul, Matrix.transpose_permMatrix]
    _ = Matrix.diagonal (d ∘ σ) := by
          change ((Matrix.diagonal d).submatrix σ id) * (Equiv.toPEquiv (σ⁻¹)).toMatrix =
            Matrix.diagonal (d ∘ σ)
          rw [PEquiv.mul_toMatrix_toPEquiv]
          rw [hsymm_inv]
          simpa using Matrix.submatrix_diagonal_equiv d σ

/-- Helper for Fact 24.59: on `Fin N`, the spectral theorem can be rewritten using the canonical
ordered eigenvalue owner obtained by reindexing `eigenvalues₀` along `finCongr`. -/
private theorem ordered_spectral_theorem_fin
    {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    let a₀ : Fin N → ℝ := fun i ↦ hA.eigenvalues₀ ((finCongr (Fintype.card_fin N)).symm i)
    ∃ U0 : Matrix.orthogonalGroup (Fin N) ℝ,
      A = (((U0 : Matrix _ _ ℝ) * Matrix.diagonal a₀) * (U0 : Matrix _ _ ℝ)ᵀ) := by
  let e₀ : Fin N ≃ Fin (Fintype.card (Fin N)) := (finCongr (Fintype.card_fin N)).symm
  let e : Fin N ≃ Fin (Fintype.card (Fin N)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N)))).symm
  let σ : Equiv.Perm (Fin N) := e.trans e₀.symm
  let a₀ : Fin N → ℝ := fun i ↦ hA.eigenvalues₀ (e₀ i)
  have hvals : hA.eigenvalues = a₀ ∘ σ := by
    -- This isolates the hidden permutation inside `Matrix.IsHermitian.eigenvalues` on `Fin N`.
    funext i
    simp [Matrix.IsHermitian.eigenvalues, a₀, σ, e₀, e, Function.comp]
  let P : Matrix.orthogonalGroup (Fin N) ℝ :=
    ⟨σ.permMatrix ℝ, permMatrix_mem_orthogonalGroup_fin σ⟩
  let U : Matrix.orthogonalGroup (Fin N) ℝ :=
    ⟨hA.eigenvectorUnitary, by
      simpa using hA.eigenvectorUnitary.prop⟩
  refine ⟨U * P, ?_⟩
  -- Route correction: replace the unordered diagonal from `spectral_theorem` by conjugating the
  -- canonical ordered diagonal with the permutation hidden in `hA.eigenvalues`.
  calc
    A = (((U : Matrix _ _ ℝ) * Matrix.diagonal hA.eigenvalues) * (U : Matrix _ _ ℝ)ᵀ) := by
          simpa [U, Matrix.conjTranspose_eq_transpose_of_trivial,
            Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using hA.spectral_theorem
    _ = (((U : Matrix _ _ ℝ) *
          (((P : Matrix _ _ ℝ) * Matrix.diagonal a₀) * (P : Matrix _ _ ℝ)ᵀ)) *
          (U : Matrix _ _ ℝ)ᵀ) := by
            rw [permMatrix_diagonal_mul_transpose_eq_diagonal_comp, hvals]
    _ = ((((U * P : Matrix.orthogonalGroup (Fin N) ℝ) : Matrix _ _ ℝ) *
          Matrix.diagonal a₀) *
          (((U * P : Matrix.orthogonalGroup (Fin N) ℝ) : Matrix _ _ ℝ)ᵀ)) := by
            simp [U, P, Matrix.mul_assoc, Matrix.transpose_mul]

/-- Helper for Fact 24.59: orthogonal conjugation preserves the canonical ordered eigenvalue list
`eigenvalues₀`. -/
  private theorem ordered_conjugate_eigenvalues₀_eq
    {N : ℕ} {B C : Matrix (Fin N) (Fin N) ℝ}
    (hB : B.IsHermitian) (hC : C.IsHermitian)
    (U : Matrix.orthogonalGroup (Fin N) ℝ)
    (hCdef : C = (U : Matrix _ _ ℝ)ᵀ * B * (U : Matrix _ _ ℝ)) :
    List.ofFn hC.eigenvalues₀ = List.ofFn hB.eigenvalues₀ := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  have hUUt : UM * UMᵀ = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff (n := Fin N) (R := ℝ) (A := UM)).mp U.prop
  have hchar : C.charpoly = B.charpoly := by
    -- Route correction: prove ordered-spectrum invariance through the common characteristic
    -- polynomial, avoiding any transport through specific eigenbases.
    rw [hCdef]
    calc
      (((UMᵀ * B) * UM) : Matrix (Fin N) (Fin N) ℝ).charpoly
          = ((UM * (UMᵀ * B)) : Matrix (Fin N) (Fin N) ℝ).charpoly := by
              rw [Matrix.charpoly_mul_comm]
      _ = (((UM * UMᵀ) * B) : Matrix (Fin N) (Fin N) ℝ).charpoly := by
            simp [Matrix.mul_assoc]
      _ = B.charpoly := by
            simp [hUUt]
  -- The canonical ordered spectra are both the sorted real roots of that common characteristic
  -- polynomial.
  calc
    List.ofFn hC.eigenvalues₀ = (C.charpoly.roots.map RCLike.re).sort (· ≥ ·) := by
      simpa using hC.sort_roots_charpoly_eq_eigenvalues₀.symm
    _ = (B.charpoly.roots.map RCLike.re).sort (· ≥ ·) := by
          rw [hchar]
    _ = List.ofFn hB.eigenvalues₀ := by
          simpa using hB.sort_roots_charpoly_eq_eigenvalues₀

/-- Helper for Fact 24.59: the sorted roots of a real diagonal characteristic polynomial are
exactly the canonical nonincreasing rearrangement of the diagonal entries. -/
private theorem diagonal_charpoly_sort_roots_eq_nonincreasingRearrangement
    {N : ℕ} (d : Fin N → ℝ) :
    (((Matrix.diagonal d).charpoly.roots).sort (· ≥ ·)) =
      List.ofFn (nonincreasingRearrangement d) := by
  classical
  have hpermMerge :
      List.Perm ((List.ofFn d).mergeSort (· ≥ ·)) (List.ofFn d) :=
    List.mergeSort_perm _ _
  have hpermSort :
      List.Perm (List.ofFn (nonincreasingRearrangement d)) (List.ofFn d) := by
    -- The tuple sorted by `Tuple.sort` is still just a permutation of the original tuple.
    simpa [nonincreasingRearrangement] using
      (Equiv.Perm.ofFn_comp_perm (Tuple.sort (OrderDual.toDual ∘ d)) d)
  have hsortedSort :
      (List.ofFn (nonincreasingRearrangement d)).SortedGE := by
    -- The canonical rearrangement is antitone by construction, hence descending-sorted.
    simpa [nonincreasingRearrangement] using
      (antitone_nonincreasingRearrangement (x := d)).sortedGE_ofFn
  have hsortEq :
      ((List.ofFn d).mergeSort (· ≥ ·)) = List.ofFn (nonincreasingRearrangement d) :=
    -- Two descending sorted permutations of the same finite list must coincide.
    List.Perm.eq_of_sortedGE List.sortedGE_mergeSort hsortedSort
      (hpermMerge.trans hpermSort.symm)
  -- Expand the diagonal characteristic polynomial into linear factors and identify the resulting
  -- sorted root list with the tuple sort defining `nonincreasingRearrangement`.
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simpa [Multiset.coe_sort] using hsortEq
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- Helper for Fact 24.59: if one matrix has both an ordered diagonalization and an unsorted
common diagonalization, then the ordered diagonal is the nonincreasing rearrangement of the
unsorted diagonal. -/
private theorem nonincreasingRearrangement_eq_orderedDiagonal_of_commonDiagonalizations
    {N : ℕ} {c c0 : Fin N → ℝ}
    {C : Matrix (Fin N) (Fin N) ℝ}
    {U Q : Matrix.orthogonalGroup (Fin N) ℝ}
    (hc : Antitone c)
    (hCdiag :
      C = (((U : Matrix _ _ ℝ) * Matrix.diagonal c) * (U : Matrix _ _ ℝ)ᵀ))
    (hQdiag :
      C = (((Q : Matrix _ _ ℝ) * Matrix.diagonal c0) * (Q : Matrix _ _ ℝ)ᵀ)) :
    nonincreasingRearrangement c0 = c := by
  apply List.ofFn_inj.mp
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  let QM : Matrix (Fin N) (Fin N) ℝ := Q
  have hQtQ : QMᵀ * QM = 1 := orthogonal_transpose_mul_eq_one Q.prop
  have hUtU : UMᵀ * UM = 1 := orthogonal_transpose_mul_eq_one U.prop
  have hchar0 : C.charpoly = (Matrix.diagonal c0).charpoly := by
    -- Collapse the orthogonal conjugation of `diag c0` inside the characteristic polynomial.
    rw [hQdiag]
    calc
      (((QM * Matrix.diagonal c0) * QMᵀ) : Matrix (Fin N) (Fin N) ℝ).charpoly
          = (QMᵀ * (QM * Matrix.diagonal c0) : Matrix (Fin N) (Fin N) ℝ).charpoly := by
              rw [Matrix.charpoly_mul_comm]
      _ = (((QMᵀ * QM) * Matrix.diagonal c0) : Matrix (Fin N) (Fin N) ℝ).charpoly := by
            simp [Matrix.mul_assoc]
      _ = (Matrix.diagonal c0).charpoly := by
            simp [hQtQ]
  have hchar : C.charpoly = (Matrix.diagonal c).charpoly := by
    -- The same cyclic characteristic-polynomial argument applies to the ordered diagonalization.
    rw [hCdiag]
    calc
      (((UM * Matrix.diagonal c) * UMᵀ) : Matrix (Fin N) (Fin N) ℝ).charpoly
          = (UMᵀ * (UM * Matrix.diagonal c) : Matrix (Fin N) (Fin N) ℝ).charpoly := by
              rw [Matrix.charpoly_mul_comm]
      _ = (((UMᵀ * UM) * Matrix.diagonal c) : Matrix (Fin N) (Fin N) ℝ).charpoly := by
            simp [Matrix.mul_assoc]
      _ = (Matrix.diagonal c).charpoly := by
            simp [hUtU]
  -- Both diagonals have the same characteristic polynomial, so their descending root lists agree.
  calc
    List.ofFn (nonincreasingRearrangement c0)
        = (((Matrix.diagonal c0).charpoly.roots).sort (· ≥ ·)) := by
            symm
            exact diagonal_charpoly_sort_roots_eq_nonincreasingRearrangement c0
    _ = (((Matrix.diagonal c).charpoly.roots).sort (· ≥ ·)) := by
          rw [← hchar0, hchar]
    _ = List.ofFn (nonincreasingRearrangement c) :=
          diagonal_charpoly_sort_roots_eq_nonincreasingRearrangement c
    _ = List.ofFn c := by
          rw [nonincreasingRearrangement_eq_self_of_antitone hc]

/-- Helper for Fact 24.59: if a convex combination of bounded real numbers attains the upper
bound, then every positively weighted term already attains that bound. -/
private theorem positive_weight_term_eq_of_convex_bound_equality
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w t : ι → ℝ} {T : ℝ}
    (hbound : ∀ i, t i ≤ T) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hEq : ∑ i, w i * t i = T) :
    ∀ i, w i ≠ 0 → t i = T := by
  intro i hwi
  by_contra hti
  have hti_lt : t i < T := lt_of_le_of_ne (hbound i) hti
  have hwi_pos : 0 < w i := lt_of_le_of_ne (hw_nonneg i) hwi.symm
  have hsum_lt :
      ∑ j, w j * t j < ∑ j, w j * T := by
    -- Split off the strict term at `i`, while the remaining terms only satisfy the weak bound.
    calc
      ∑ j, w j * t j = w i * t i + Finset.sum (Finset.univ.erase i) (fun j ↦ w j * t j) := by
        symm
        simpa [add_comm] using
          (Finset.univ.sum_erase_add (fun j ↦ w j * t j) (Finset.mem_univ i))
      _ < w i * T + Finset.sum (Finset.univ.erase i) (fun j ↦ w j * T) := by
        refine add_lt_add_of_lt_of_le ?_ ?_
        · exact mul_lt_mul_of_pos_left hti_lt hwi_pos
        · refine Finset.sum_le_sum ?_
          intro j hj
          exact mul_le_mul_of_nonneg_left (hbound j) (hw_nonneg j)
      _ = ∑ j, w j * T := by
        simpa [add_comm] using
          (Finset.univ.sum_erase_add (fun j ↦ w j * T) (Finset.mem_univ i))
  have hsum_eq_T : ∑ j, w j * T = T := by
    calc
      ∑ j, w j * T = (∑ j, w j) * T := by
        rw [Finset.sum_mul]
      _ = T := by simp [hw_sum]
  have hneq : ∑ j, w j * t j ≠ T := ne_of_lt (hsum_lt.trans_eq hsum_eq_T)
  exact hneq (by simpa using hEq)

/-- Helper for Fact 24.59: once `A` is presented in an orthogonal diagonal basis, cycling the
trace moves the pairing against `B` into that basis as well. -/
private theorem trace_mul_eq_trace_diagonal_mul_in_orthogonal_basis
    {n : Type u} [Fintype n] [DecidableEq n] {A B : Matrix n n ℝ}
    (U : Matrix.orthogonalGroup n ℝ) (a : n → ℝ)
    (hA : A = (((U : Matrix _ _ ℝ) * Matrix.diagonal a) * (U : Matrix _ _ ℝ)ᵀ)) :
    let C : Matrix n n ℝ := (U : Matrix _ _ ℝ)ᵀ * B * (U : Matrix _ _ ℝ)
    Matrix.trace (A * B) = Matrix.trace (Matrix.diagonal a * C) := by
  dsimp
  rw [hA]
  -- First move the left orthogonal factor across the trace, then move the diagonal factor.
  calc
    Matrix.trace ((((U : Matrix _ _ ℝ) * Matrix.diagonal a) * (U : Matrix _ _ ℝ)ᵀ) * B)
        = Matrix.trace (((U : Matrix _ _ ℝ) * Matrix.diagonal a) * ((U : Matrix _ _ ℝ)ᵀ * B)) := by
            simp [Matrix.mul_assoc]
    _ = Matrix.trace (((U : Matrix _ _ ℝ)ᵀ * B) * ((U : Matrix _ _ ℝ) * Matrix.diagonal a)) := by
          exact Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((((U : Matrix _ _ ℝ)ᵀ * B) * (U : Matrix _ _ ℝ)) * Matrix.diagonal a) := by
          simp [Matrix.mul_assoc]
    _ = Matrix.trace (Matrix.diagonal a * (((U : Matrix _ _ ℝ)ᵀ * B) * (U : Matrix _ _ ℝ))) := by
          exact Matrix.trace_mul_comm _ _

/-- Helper for Fact 24.59: after diagonalizing `A` in its canonical orthogonal eigenbasis, the
trace pairing against `B` becomes the trace pairing of `diag λ(A)` against the conjugated matrix
`U_Aᵀ B U_A`. This is the fixed source route for the equality case. -/
private theorem trace_mul_eq_trace_diagonal_mul_in_A_eigenbasis
    {n : Type u} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) :
    let a : n → ℝ := hA.eigenvalues
    let hUAorth : ((hA.eigenvectorUnitary : Matrix n n ℝ) ∈ Matrix.orthogonalGroup n ℝ) := by
      simpa using hA.eigenvectorUnitary.prop
    let UA : Matrix.orthogonalGroup n ℝ := ⟨hA.eigenvectorUnitary, hUAorth⟩
    let C : Matrix n n ℝ := (UA : Matrix n n ℝ)ᵀ * B * (UA : Matrix n n ℝ)
    Matrix.trace (A * B) = Matrix.trace (Matrix.diagonal a * C) := by
  let a : n → ℝ := hA.eigenvalues
  let hUAorth : ((hA.eigenvectorUnitary : Matrix n n ℝ) ∈ Matrix.orthogonalGroup n ℝ) := by
    simpa using hA.eigenvectorUnitary.prop
  let UA : Matrix.orthogonalGroup n ℝ := ⟨hA.eigenvectorUnitary, hUAorth⟩
  let C : Matrix n n ℝ := (UA : Matrix n n ℝ)ᵀ * B * (UA : Matrix n n ℝ)
  have hdiag :
      A = (((UA : Matrix n n ℝ) * Matrix.diagonal a) * (UA : Matrix n n ℝ)ᵀ) := by
    -- This is the spectral theorem in the orthogonal basis of eigenvectors.
    simpa [a, UA, Matrix.conjTranspose_eq_transpose_of_trivial,
      Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using hA.spectral_theorem
  -- Specialize the orthogonal-basis trace rewrite to the eigenbasis of `A`.
  simpa [a, hUAorth, UA, C] using
    (trace_mul_eq_trace_diagonal_mul_in_orthogonal_basis
      (U := UA) (A := A) (B := B) (a := a) hdiag)

/-- Helper for Fact 24.59: once the conjugated matrix `U_Aᵀ B U_A` has been diagonalized by an
orthogonal matrix that preserves `diag λ(A)`, multiplying that blockwise change of basis back into
`U_A` yields the common orthogonal diagonalization required by the theorem. -/
private theorem common_orthogonal_diagonalization_from_A_eigenbasis
    {n : Type u} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ)
    {Q : Matrix.orthogonalGroup n ℝ}
    (hQA :
      (((Q : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues) * (Q : Matrix n n ℝ)ᵀ) =
        Matrix.diagonal hA.eigenvalues)
    (hQB :
      let hUAorth : ((hA.eigenvectorUnitary : Matrix n n ℝ) ∈ Matrix.orthogonalGroup n ℝ) := by
        simpa using hA.eigenvectorUnitary.prop
      let UA : Matrix.orthogonalGroup n ℝ := ⟨hA.eigenvectorUnitary, hUAorth⟩
      let C : Matrix n n ℝ := (UA : Matrix n n ℝ)ᵀ * B * (UA : Matrix n n ℝ)
      C = (((Q : Matrix n n ℝ) * Matrix.diagonal b) * (Q : Matrix n n ℝ)ᵀ)) :
    ∃ U : Matrix.orthogonalGroup n ℝ,
      (A, B) =
        ((U : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues * (U : Matrix n n ℝ)ᵀ,
          (U : Matrix n n ℝ) * Matrix.diagonal b * (U : Matrix n n ℝ)ᵀ) := by
  let hUAorth : ((hA.eigenvectorUnitary : Matrix n n ℝ) ∈ Matrix.orthogonalGroup n ℝ) := by
    simpa using hA.eigenvectorUnitary.prop
  let UA : Matrix.orthogonalGroup n ℝ := ⟨hA.eigenvectorUnitary, hUAorth⟩
  let C : Matrix n n ℝ := (UA : Matrix n n ℝ)ᵀ * B * (UA : Matrix n n ℝ)
  have hUA_mul_transpose : (UA : Matrix n n ℝ) * (UA : Matrix n n ℝ)ᵀ = 1 :=
    orthogonal_mul_transpose_eq_one hUAorth
  have hAdiag :
      A =
        (((UA : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues) * (UA : Matrix n n ℝ)ᵀ) := by
    -- The spectral theorem gives the canonical ordered diagonalization of `A` in the `UA` basis.
    simpa [UA, hUAorth, Matrix.conjTranspose_eq_transpose_of_trivial,
      Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using hA.spectral_theorem
  have hCdiag :
      C = (((Q : Matrix n n ℝ) * Matrix.diagonal b) * (Q : Matrix n n ℝ)ᵀ) := by
    -- Unpack the conjugated `B` core from the theorem-local `let`-surface in `hQB`.
    simpa [C, UA, hUAorth] using hQB
  refine ⟨UA * Q, ?_⟩
  rw [Prod.mk.injEq]
  constructor
  · -- Replace `diag λ(A)` by the `Q`-conjugate form, then absorb the basis change into `UA * Q`.
    calc
      A = (((UA : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues) * (UA : Matrix n n ℝ)ᵀ) := hAdiag
      _ =
          (((UA : Matrix n n ℝ) *
              (((Q : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues) *
                (Q : Matrix n n ℝ)ᵀ)) *
            (UA : Matrix n n ℝ)ᵀ) := by rw [hQA]
      _ =
          ((((UA * Q : Matrix.orthogonalGroup n ℝ) : Matrix n n ℝ) *
              Matrix.diagonal hA.eigenvalues) *
            (((UA * Q : Matrix.orthogonalGroup n ℝ) : Matrix n n ℝ)ᵀ)) := by
            simp [Matrix.mul_assoc, Matrix.transpose_mul]
  · -- Conjugate the diagonalization of `C = UAᵀ B UA` back by `UA`.
    calc
      B = (((UA : Matrix n n ℝ) * C) * (UA : Matrix n n ℝ)ᵀ) := by
            calc
              B = ((1 : Matrix n n ℝ) * B) := by simp
              _ = (((UA : Matrix n n ℝ) * (UA : Matrix n n ℝ)ᵀ) * B) := by
                    rw [hUA_mul_transpose]
              _ = ((UA : Matrix n n ℝ) * ((UA : Matrix n n ℝ)ᵀ * B)) := by
                    simp [Matrix.mul_assoc]
              _ = ((UA : Matrix n n ℝ) *
                    ((((UA : Matrix n n ℝ)ᵀ * B) * (UA : Matrix n n ℝ)) *
                      (UA : Matrix n n ℝ)ᵀ)) := by
                    simp [Matrix.mul_assoc, hUA_mul_transpose]
              _ = (((UA : Matrix n n ℝ) * C) * (UA : Matrix n n ℝ)ᵀ) := by
                    simp [C, Matrix.mul_assoc]
      _ =
          (((UA : Matrix n n ℝ) *
              (((Q : Matrix n n ℝ) * Matrix.diagonal b) * (Q : Matrix n n ℝ)ᵀ)) *
            (UA : Matrix n n ℝ)ᵀ) := by rw [hCdiag]
      _ =
          ((((UA * Q : Matrix.orthogonalGroup n ℝ) : Matrix n n ℝ) * Matrix.diagonal b) *
            (((UA * Q : Matrix.orthogonalGroup n ℝ) : Matrix n n ℝ)ᵀ)) := by
            simp [Matrix.mul_assoc, Matrix.transpose_mul]

/-- Helper for Fact 24.59: once `Afin` is in its ordered `Fin` eigenbasis and the conjugated
`Bfin` core is diagonalized by a change of basis that preserves `diag a`, multiplying those basis
changes yields a common ordered diagonalization on `Fin N`. -/
private theorem common_orthogonal_diagonalization_from_ordered_fin_basis
    {N : ℕ}
    {Afin Bfin : Matrix (Fin N) (Fin N) ℝ}
    {a b : Fin N → ℝ}
    {UA0 Qfin : Matrix.orthogonalGroup (Fin N) ℝ}
    (hAfin :
      Afin = (((UA0 : Matrix _ _ ℝ) * Matrix.diagonal a) * (UA0 : Matrix _ _ ℝ)ᵀ))
    (hQfinA :
      (((Qfin : Matrix _ _ ℝ) * Matrix.diagonal a) * (Qfin : Matrix _ _ ℝ)ᵀ) =
        Matrix.diagonal a)
    (hQfinB :
      let Cfin : Matrix (Fin N) (Fin N) ℝ :=
        (UA0 : Matrix _ _ ℝ)ᵀ * Bfin * (UA0 : Matrix _ _ ℝ)
      Cfin = (((Qfin : Matrix _ _ ℝ) * Matrix.diagonal b) * (Qfin : Matrix _ _ ℝ)ᵀ)) :
    ∃ Ufin : Matrix.orthogonalGroup (Fin N) ℝ,
      (Afin, Bfin) =
        ((((Ufin : Matrix _ _ ℝ) * Matrix.diagonal a) * (Ufin : Matrix _ _ ℝ)ᵀ),
         (((Ufin : Matrix _ _ ℝ) * Matrix.diagonal b) * (Ufin : Matrix _ _ ℝ)ᵀ)) := by
  let Cfin : Matrix (Fin N) (Fin N) ℝ :=
    (UA0 : Matrix (Fin N) (Fin N) ℝ)ᵀ * Bfin * (UA0 : Matrix (Fin N) (Fin N) ℝ)
  have hUA0_mul_transpose :
      (UA0 : Matrix (Fin N) (Fin N) ℝ) * (UA0 : Matrix (Fin N) (Fin N) ℝ)ᵀ = 1 :=
    orthogonal_mul_transpose_eq_one UA0.prop
  have hCfin_diag :
      Cfin = (((Qfin : Matrix _ _ ℝ) * Matrix.diagonal b) * (Qfin : Matrix _ _ ℝ)ᵀ) := by
    -- Unpack the conjugated `Bfin` core from the theorem-local `let`-surface in `hQfinB`.
    simpa [Cfin] using hQfinB
  refine ⟨UA0 * Qfin, ?_⟩
  rw [Prod.mk.injEq]
  constructor
  · -- Replace `diag a` by its `Qfin`-conjugate form and absorb the basis change into `UA0 * Qfin`.
    calc
      Afin = (((UA0 : Matrix _ _ ℝ) * Matrix.diagonal a) * (UA0 : Matrix _ _ ℝ)ᵀ) := hAfin
      _ =
          (((UA0 : Matrix _ _ ℝ) *
              (((Qfin : Matrix _ _ ℝ) * Matrix.diagonal a) * (Qfin : Matrix _ _ ℝ)ᵀ)) *
            (UA0 : Matrix _ _ ℝ)ᵀ) := by rw [hQfinA]
      _ =
          ((((UA0 * Qfin : Matrix.orthogonalGroup (Fin N) ℝ) : Matrix _ _ ℝ) *
              Matrix.diagonal a) *
            (((UA0 * Qfin : Matrix.orthogonalGroup (Fin N) ℝ) : Matrix _ _ ℝ)ᵀ)) := by
            simp [Matrix.mul_assoc, Matrix.transpose_mul]
  · -- Conjugate the diagonalization of `Cfin = UA0ᵀ Bfin UA0` back by `UA0`.
    calc
      Bfin = (((UA0 : Matrix _ _ ℝ) * Cfin) * (UA0 : Matrix _ _ ℝ)ᵀ) := by
              calc
                Bfin = ((1 : Matrix (Fin N) (Fin N) ℝ) * Bfin) := by simp
                _ = (((UA0 : Matrix _ _ ℝ) * (UA0 : Matrix _ _ ℝ)ᵀ) * Bfin) := by
                      rw [hUA0_mul_transpose]
                _ = ((UA0 : Matrix _ _ ℝ) * ((UA0 : Matrix _ _ ℝ)ᵀ * Bfin)) := by
                      simp [Matrix.mul_assoc]
                _ = ((UA0 : Matrix _ _ ℝ) *
                      ((((UA0 : Matrix _ _ ℝ)ᵀ * Bfin) * (UA0 : Matrix _ _ ℝ)) *
                        (UA0 : Matrix _ _ ℝ)ᵀ)) := by
                      simp [Matrix.mul_assoc, hUA0_mul_transpose]
                _ = (((UA0 : Matrix _ _ ℝ) * Cfin) * (UA0 : Matrix _ _ ℝ)ᵀ) := by
                      simp [Cfin, Matrix.mul_assoc]
      _ =
          (((UA0 : Matrix _ _ ℝ) *
              (((Qfin : Matrix _ _ ℝ) * Matrix.diagonal b) * (Qfin : Matrix _ _ ℝ)ᵀ)) *
            (UA0 : Matrix _ _ ℝ)ᵀ) := by rw [hCfin_diag]
      _ =
          ((((UA0 * Qfin : Matrix.orthogonalGroup (Fin N) ℝ) : Matrix _ _ ℝ) *
              Matrix.diagonal b) *
            (((UA0 * Qfin : Matrix.orthogonalGroup (Fin N) ℝ) : Matrix _ _ ℝ)ᵀ)) := by
            simp [Matrix.mul_assoc, Matrix.transpose_mul]

/-- Helper for Fact 24.59: a common ordered diagonalization on `Fin (card n)` transports back to
the original index type after correcting the hidden permutation between `eigenvalues₀` and
`eigenvalues`. -/
private theorem reindex_common_orthogonal_diagonalization_fin
    {n : Type u} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (e : n ≃ Fin (Fintype.card n))
    {Ufin : Matrix.orthogonalGroup (Fin (Fintype.card n)) ℝ}
    (hpair_fin :
      (Matrix.reindex e e A, Matrix.reindex e e B) =
        ((((Ufin : Matrix _ _ ℝ) * Matrix.diagonal hA.eigenvalues₀) * (Ufin : Matrix _ _ ℝ)ᵀ),
         (((Ufin : Matrix _ _ ℝ) * Matrix.diagonal hB.eigenvalues₀) * (Ufin : Matrix _ _ ℝ)ᵀ))) :
    ∃ U : Matrix.orthogonalGroup n ℝ,
      (A, B) =
        ((((U : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues) * (U : Matrix n n ℝ)ᵀ),
         (((U : Matrix n n ℝ) * Matrix.diagonal hB.eigenvalues) * (U : Matrix n n ℝ)ᵀ)) := by
  let a : n → ℝ := fun i ↦ hA.eigenvalues₀ (e i)
  let b : n → ℝ := fun i ↦ hB.eigenvalues₀ (e i)
  let U0m : Matrix n n ℝ := Matrix.reindex e.symm e.symm (Ufin : Matrix _ _ ℝ)
  have hU0orth : U0m ∈ Matrix.orthogonalGroup n ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff]
    calc
      U0m * U0mᵀ
          = Matrix.reindex e.symm e.symm ((Ufin : Matrix _ _ ℝ) * (Ufin : Matrix _ _ ℝ)ᵀ) := by
              -- Reindexing the orthogonal product of `Ufin` transports the identity surface back
              -- to the original index type `n`.
              simpa [U0m, Matrix.transpose_reindex] using
                (Matrix.submatrix_mul_equiv (Ufin : Matrix _ _ ℝ) ((Ufin : Matrix _ _ ℝ)ᵀ)
                  e e id)
      _ = Matrix.reindex e.symm e.symm (1 : Matrix _ _ ℝ) := by
            congr
            exact
              (Matrix.mem_orthogonalGroup_iff
                (n := Fin (Fintype.card n)) (R := ℝ) (A := (Ufin : Matrix _ _ ℝ))).mp Ufin.prop
      _ = 1 := by simp
  let U0 : Matrix.orthogonalGroup n ℝ := ⟨U0m, hU0orth⟩
  have hAfin :
      Matrix.reindex e e A =
        (((Ufin : Matrix _ _ ℝ) * Matrix.diagonal hA.eigenvalues₀) * (Ufin : Matrix _ _ ℝ)ᵀ) :=
    congrArg Prod.fst hpair_fin
  have hBfin :
      Matrix.reindex e e B =
        (((Ufin : Matrix _ _ ℝ) * Matrix.diagonal hB.eigenvalues₀) * (Ufin : Matrix _ _ ℝ)ᵀ) :=
    congrArg Prod.snd hpair_fin
  have hAback :
      A = (((U0 : Matrix n n ℝ) * Matrix.diagonal a) * (U0 : Matrix n n ℝ)ᵀ) := by
    -- Move the ordered `Fin` diagonalization of `A` back to the original index type using `e`.
    calc
      A = Matrix.reindex e.symm e.symm (Matrix.reindex e e A) := by simp
      _ = Matrix.reindex e.symm e.symm
            ((((Ufin : Matrix _ _ ℝ) * Matrix.diagonal hA.eigenvalues₀) *
              (Ufin : Matrix _ _ ℝ)ᵀ)) := by
            rw [hAfin]
      _ = (((U0 : Matrix n n ℝ) * Matrix.diagonal a) * (U0 : Matrix n n ℝ)ᵀ) := by
            simpa [U0, U0m, a] using
              (reindex_symm_diagonalization_eq e (Ufin : Matrix _ _ ℝ) hA.eigenvalues₀)
  have hBback :
      B = (((U0 : Matrix n n ℝ) * Matrix.diagonal b) * (U0 : Matrix n n ℝ)ᵀ) := by
    -- The same transport moves the ordered `Fin` diagonalization of `B` back to the `n` model.
    calc
      B = Matrix.reindex e.symm e.symm (Matrix.reindex e e B) := by simp
      _ = Matrix.reindex e.symm e.symm
            ((((Ufin : Matrix _ _ ℝ) * Matrix.diagonal hB.eigenvalues₀) *
              (Ufin : Matrix _ _ ℝ)ᵀ)) := by
            rw [hBfin]
      _ = (((U0 : Matrix n n ℝ) * Matrix.diagonal b) * (U0 : Matrix n n ℝ)ᵀ) := by
            simpa [U0, U0m, b] using
              (reindex_symm_diagonalization_eq e (Ufin : Matrix _ _ ℝ) hB.eigenvalues₀)
  let e₀ : n ≃ Fin (Fintype.card n) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  let σ : Equiv.Perm n := e.trans e₀.symm
  have hσa : a = hA.eigenvalues ∘ σ := by
    -- This isolates the hidden canonical permutation inside `Matrix.IsHermitian.eigenvalues`.
    funext i
    simp [a, σ, e₀, Matrix.IsHermitian.eigenvalues, Function.comp]
  have hσb : b = hB.eigenvalues ∘ σ := by
    -- The same hidden permutation transports the ordered spectrum of `B`.
    funext i
    simp [b, σ, e₀, Matrix.IsHermitian.eigenvalues, Function.comp]
  let P : Matrix.orthogonalGroup n ℝ := ⟨σ.permMatrix ℝ, permMatrix_mem_orthogonalGroup_fin σ⟩
  refine ⟨U0 * P, ?_⟩
  rw [Prod.mk.injEq]
  constructor
  · -- Conjugate the `a`-diagonal by the hidden permutation and absorb that permutation into `U0`.
    calc
      A = (((U0 : Matrix n n ℝ) * Matrix.diagonal a) * (U0 : Matrix n n ℝ)ᵀ) := hAback
      _ =
          (((U0 : Matrix n n ℝ) *
              (((P : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues) *
                (P : Matrix n n ℝ)ᵀ)) *
            (U0 : Matrix n n ℝ)ᵀ) := by
              rw [hσa,
                ← permMatrix_diagonal_mul_transpose_eq_diagonal_comp
                  (σ := σ) (d := hA.eigenvalues)]
      _ =
          ((((U0 * P : Matrix.orthogonalGroup n ℝ) : Matrix n n ℝ) *
              Matrix.diagonal hA.eigenvalues) *
            (((U0 * P : Matrix.orthogonalGroup n ℝ) : Matrix n n ℝ)ᵀ)) := by
              simp [U0, P, Matrix.mul_assoc, Matrix.transpose_mul]
  · -- The same permutation packaging converts the transported `b`-diagonal into
    -- `Matrix.diagonal hB.eigenvalues`.
    calc
      B = (((U0 : Matrix n n ℝ) * Matrix.diagonal b) * (U0 : Matrix n n ℝ)ᵀ) := hBback
      _ =
          (((U0 : Matrix n n ℝ) *
              (((P : Matrix n n ℝ) * Matrix.diagonal hB.eigenvalues) *
                (P : Matrix n n ℝ)ᵀ)) *
            (U0 : Matrix n n ℝ)ᵀ) := by
              rw [hσb,
                ← permMatrix_diagonal_mul_transpose_eq_diagonal_comp
                  (σ := σ) (d := hB.eigenvalues)]
      _ =
          ((((U0 * P : Matrix.orthogonalGroup n ℝ) : Matrix n n ℝ) *
              Matrix.diagonal hB.eigenvalues) *
            (((U0 * P : Matrix.orthogonalGroup n ℝ) : Matrix n n ℝ)ᵀ)) := by
              simp [U0, P, Matrix.mul_assoc, Matrix.transpose_mul]

/-- Helper for Fact 24.59: the strict-side action data in the ordered `c`-basis already forces
each strict-drop prefix projector of `a` to commute with `C`. -/
private theorem strict_drop_prefix_commutes_of_strict_side_action
    {N : ℕ} {a c : Fin N → ℝ}
    {C : Matrix (Fin N) (Fin N) ℝ}
    {U : Matrix.orthogonalGroup (Fin N) ℝ}
    (hCdiag :
      C = (((U : Matrix _ _ ℝ) * Matrix.diagonal c) * (U : Matrix _ _ ℝ)ᵀ))
    (hstrict_side :
      ∀ {r : Fin N} (hrN : r.1 + 1 < N) (hr : a r > a ⟨r.1 + 1, hrN⟩),
        let Pr : Matrix (Fin N) (Fin N) ℝ :=
          (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
        (∀ i, c i > c r →
          (∀ j, Pr i j = if i = j then 1 else 0) ∧
            ∀ j, Pr j i = if j = i then 1 else 0) ∧
          ∀ i, c i < c r →
            (∀ j, Pr i j = 0) ∧ ∀ j, Pr j i = 0) :
    ∀ {r : Fin N} (hrN : r.1 + 1 < N) (hr : a r > a ⟨r.1 + 1, hrN⟩),
      Commute (prefixProj r) C := by
  intro r hrN hr
  let Pr : Matrix (Fin N) (Fin N) ℝ :=
    (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
  have hcomm_diag : Commute Pr (Matrix.diagonal c) := by
    -- The strict-side basis action already identifies the conjugated projector as a spectral
    -- projector for `diag c`.
    simpa [Pr] using
      commute_diagonal_of_strict_side_basis_action (c := c) (P := Pr) (r := r)
        (hstrict_side hrN hr)
  have hcomm_C :
      Commute (prefixProj r) (((U : Matrix _ _ ℝ) * Matrix.diagonal c) * (U : Matrix _ _ ℝ)ᵀ) := by
    -- Conjugate that commutation statement back out of the `U`-basis.
    simpa [Pr] using
      commute_of_orthogonal_conjugate_commute (U := U) (P := prefixProj r)
        (D := Matrix.diagonal c) hcomm_diag
  simpa [hCdiag] using hcomm_C

/-- Helper for Fact 24.59: the strict-side action data already forces `C` to commute with the
ordered diagonal `diag a`. -/
private theorem diagonal_a_commutes_of_strict_side_actions
    {N : ℕ} {a c : Fin N → ℝ}
    {C : Matrix (Fin N) (Fin N) ℝ}
    {U : Matrix.orthogonalGroup (Fin N) ℝ}
    (ha : Antitone a)
    (hCdiag :
      C = (((U : Matrix _ _ ℝ) * Matrix.diagonal c) * (U : Matrix _ _ ℝ)ᵀ))
    (hstrict_side :
      ∀ {r : Fin N} (hrN : r.1 + 1 < N) (hr : a r > a ⟨r.1 + 1, hrN⟩),
        let Pr : Matrix (Fin N) (Fin N) ℝ :=
          (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
        (∀ i, c i > c r →
          (∀ j, Pr i j = if i = j then 1 else 0) ∧
            ∀ j, Pr j i = if j = i then 1 else 0) ∧
          ∀ i, c i < c r →
            (∀ j, Pr i j = 0) ∧ ∀ j, Pr j i = 0) :
    Commute (Matrix.diagonal a) C := by
  -- Route correction: instead of working entrywise with `diag a` directly, pass through the
  -- strict-drop projector family and the existing cross-block-zero API.
  refine diagonal_commutes_of_cross_block_zero ?_
  intro i j hij
  exact
    cross_block_entry_eq_zero_of_distinct_a_values ha
      (C := C)
      (fun {r} hrN hr ↦
        strict_drop_prefix_commutes_of_strict_side_action (a := a) (c := c)
          (C := C) (U := U) hCdiag hstrict_side hrN hr)
      hij

/-- Helper for Fact 24.59: if an orthogonal matrix fixes every strict-drop prefix projector of an
antitone diagonal `a`, then it fixes `diag a` itself. -/
private theorem strict_drop_prefix_family_characterizes_diag_a
    {N : ℕ} {a : Fin N → ℝ} (ha : Antitone a)
    {Q : Matrix.orthogonalGroup (Fin N) ℝ}
    (hprefix :
      ∀ {r : Fin N} (hrN : r.1 + 1 < N) (hr : a r > a ⟨r.1 + 1, hrN⟩),
        (((Q : Matrix _ _ ℝ)ᵀ * prefixProj r) * (Q : Matrix _ _ ℝ)) = prefixProj r) :
    (((Q : Matrix _ _ ℝ) * Matrix.diagonal a) * (Q : Matrix _ _ ℝ)ᵀ) =
      Matrix.diagonal a := by
  let QM : Matrix (Fin N) (Fin N) ℝ := Q
  have hQQt : QM * QMᵀ = 1 := orthogonal_mul_transpose_eq_one Q.prop
  have hQtQ : QMᵀ * QM = 1 := orthogonal_transpose_mul_eq_one Q.prop
  have hprefix_comm :
      ∀ {r : Fin N} (hrN : r.1 + 1 < N) (hr : a r > a ⟨r.1 + 1, hrN⟩),
        Commute (prefixProj r) QM := by
    intro r hrN hr
    change prefixProj r * QM = QM * prefixProj r
    have hfix := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ ↦ QM * M) (hprefix hrN hr)
    -- Multiplying the fixed-prefix identity on the left by `Q` turns it into commutation with `Q`.
    calc
      prefixProj r * QM = ((QM * QMᵀ) * prefixProj r) * QM := by simp [hQQt]
      _ = QM * (((QMᵀ * prefixProj r) * QM) : Matrix (Fin N) (Fin N) ℝ) := by
            simp [Matrix.mul_assoc]
      _ = QM * prefixProj r := by rw [hprefix hrN hr]
  have hdiag_comm : Commute (Matrix.diagonal a) QM := by
    -- The fixed strict-drop projector family forces `Q` to preserve every `a`-plateau.
    refine diagonal_commutes_of_cross_block_zero ?_
    intro i j hij
    exact cross_block_entry_eq_zero_of_distinct_a_values ha hprefix_comm hij
  have hconj :=
    congrArg (fun M : Matrix (Fin N) (Fin N) ℝ ↦ M * QMᵀ) hdiag_comm.eq
  -- Collapsing the orthogonal factor on the right turns the commutation identity into the desired
  -- conjugation formula.
  simpa [QM, Matrix.mul_assoc, hQQt] using hconj.symm

/-- Helper for Fact 24.59: if `Q = U * Rᵀ`, then conjugating a prefix projector by `Q` is the same
as first transporting it into the `U`-basis and then correcting by `R`. -/
private theorem corrected_basis_prefix_projector_transport
    {N : ℕ} (U R : Matrix.orthogonalGroup (Fin N) ℝ) (r : Fin N) :
    let Qm : Matrix (Fin N) (Fin N) ℝ := (U : Matrix _ _ ℝ) * (R : Matrix _ _ ℝ)ᵀ
    (((Qmᵀ * prefixProj r) * Qm) : Matrix (Fin N) (Fin N) ℝ) =
      (((R : Matrix _ _ ℝ) *
          ((((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ)) :
            Matrix (Fin N) (Fin N) ℝ)) *
        (R : Matrix _ _ ℝ)ᵀ : Matrix (Fin N) (Fin N) ℝ) := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  let RM : Matrix (Fin N) (Fin N) ℝ := R
  let Qm : Matrix (Fin N) (Fin N) ℝ := UM * RMᵀ
  -- Expand `Q = U * Rᵀ` and reassociate the factors until only the transported projector remains.
  calc
    (((Qmᵀ * prefixProj r) * Qm) : Matrix (Fin N) (Fin N) ℝ)
        = ((((RM * UMᵀ) * prefixProj r) * (UM * RMᵀ)) : Matrix (Fin N) (Fin N) ℝ) := by
            simp [Qm, Matrix.transpose_mul]
    _ = (((RM * (((UMᵀ * prefixProj r) * UM) : Matrix (Fin N) (Fin N) ℝ)) * RMᵀ) :
          Matrix (Fin N) (Fin N) ℝ) := by
            simp [Matrix.mul_assoc]
    _ =
        (((R : Matrix _ _ ℝ) *
            ((((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ)) :
              Matrix (Fin N) (Fin N) ℝ)) *
          (R : Matrix _ _ ℝ)ᵀ : Matrix (Fin N) (Fin N) ℝ) := by
            simp [UM, RM]

/-- Helper for Fact 24.59: every transported strict-drop prefix projector already has the expected
projector-chain structure away from the equal-`c` plateau. -/
private theorem transportedPrefixProjectorChainOnPlateaus
    {N : ℕ} {a c : Fin N → ℝ}
    {U : Matrix.orthogonalGroup (Fin N) ℝ}
    (hstrict_side :
      ∀ {r : Fin N} (hrN : r.1 + 1 < N) (hr : a r > a ⟨r.1 + 1, hrN⟩),
        let Pr : Matrix (Fin N) (Fin N) ℝ :=
          (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
        (∀ i, c i > c r →
          (∀ j, Pr i j = if i = j then 1 else 0) ∧
            ∀ j, Pr j i = if j = i then 1 else 0) ∧
          ∀ i, c i < c r →
            (∀ j, Pr i j = 0) ∧ ∀ j, Pr j i = 0)
    {r : Fin N} (hrN : r.1 + 1 < N) (hr : a r > a ⟨r.1 + 1, hrN⟩) :
    let Pr : Matrix (Fin N) (Fin N) ℝ :=
      (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
    Pr.IsSymm ∧
      Pr * Pr = Pr ∧
      Matrix.trace Pr = (∑ i, if i ≤ r then (1 : ℝ) else 0) ∧
      (∀ i, c i > c r →
        (∀ j, Pr i j = if i = j then 1 else 0) ∧
          ∀ j, Pr j i = if j = i then 1 else 0) ∧
      ∀ i, c i < c r →
        (∀ j, Pr i j = 0) ∧ ∀ j, Pr j i = 0 := by
  rcases conjugated_prefix_projection_chain (U := U) (r := r) (s := r) le_rfl with
    ⟨hPsymm, hPidem, htrace, -, -⟩
  -- Combine the existing conjugated-projector chain API with the strict-side basis action data.
  exact ⟨hPsymm, hPidem, htrace, (hstrict_side hrN hr).1, (hstrict_side hrN hr).2⟩

/-- Helper for Fact 24.59: transporting `diag a` into the ordered `c`-eigenbasis turns the
strict-side action data into a clean commutation statement with `diag c`. -/
private theorem transportedDiagonalACommutesDiagonalC
    {N : ℕ} {a c : Fin N → ℝ}
    {C : Matrix (Fin N) (Fin N) ℝ}
    {U : Matrix.orthogonalGroup (Fin N) ℝ}
    (ha : Antitone a)
    (hCdiag :
      C = (((U : Matrix _ _ ℝ) * Matrix.diagonal c) * (U : Matrix _ _ ℝ)ᵀ))
    (hstrict_side :
      ∀ {r : Fin N} (hrN : r.1 + 1 < N) (hr : a r > a ⟨r.1 + 1, hrN⟩),
        let Pr : Matrix (Fin N) (Fin N) ℝ :=
          (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
        (∀ i, c i > c r →
          (∀ j, Pr i j = if i = j then 1 else 0) ∧
            ∀ j, Pr j i = if j = i then 1 else 0) ∧
          ∀ i, c i < c r →
            (∀ j, Pr i j = 0) ∧ ∀ j, Pr j i = 0) :
    let D : Matrix (Fin N) (Fin N) ℝ :=
      (((U : Matrix _ _ ℝ)ᵀ * Matrix.diagonal a) * (U : Matrix _ _ ℝ))
    D.IsSymm ∧ Commute D (Matrix.diagonal c) := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  have hUtU : UMᵀ * UM = 1 := orthogonal_transpose_mul_eq_one U.prop
  have hdiagAcommC :
      Commute (Matrix.diagonal a) C :=
    diagonal_a_commutes_of_strict_side_actions (a := a) (c := c) (C := C) (U := U)
      ha hCdiag hstrict_side
  refine ⟨?_, ?_⟩
  · -- Orthogonal conjugation preserves the symmetry of the diagonal matrix `diag a`.
    rw [Matrix.IsSymm]
    calc
      ((((UMᵀ * Matrix.diagonal a) * UM) : Matrix (Fin N) (Fin N) ℝ)ᵀ)
          = UMᵀ * (Matrix.diagonal a)ᵀ * UM := by
              simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (UMᵀ * Matrix.diagonal a) * UM := by
            simp [Matrix.mul_assoc]
  · -- Conjugate the commuting identity by `Uᵀ` on the left and `U` on the right.
    change
      Commute (((UMᵀ * Matrix.diagonal a) * UM) : Matrix (Fin N) (Fin N) ℝ)
        (Matrix.diagonal c)
    have hcomm_in_basis :
        Matrix.diagonal a * (((UM * Matrix.diagonal c) * UMᵀ) : Matrix (Fin N) (Fin N) ℝ) =
          (((UM * Matrix.diagonal c) * UMᵀ) : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a := by
      simpa [UM, hCdiag] using hdiagAcommC.eq
    have hconj :=
      congrArg
        (fun M : Matrix (Fin N) (Fin N) ℝ ↦ ((UMᵀ * M) * UM : Matrix (Fin N) (Fin N) ℝ))
        hcomm_in_basis
    calc
      ((((UMᵀ * Matrix.diagonal a) * UM) * Matrix.diagonal c) :
          Matrix (Fin N) (Fin N) ℝ)
          =
            ((UMᵀ *
                (Matrix.diagonal a * (((UM * Matrix.diagonal c) * UMᵀ) :
                  Matrix (Fin N) (Fin N) ℝ))) *
              UM : Matrix (Fin N) (Fin N) ℝ) := by
                simp [Matrix.mul_assoc, hUtU]
      _ =
          ((UMᵀ *
              ((((UM * Matrix.diagonal c) * UMᵀ) : Matrix (Fin N) (Fin N) ℝ) *
                Matrix.diagonal a)) *
            UM : Matrix (Fin N) (Fin N) ℝ) := by
              simpa using hconj
      _ = (Matrix.diagonal c * ((UMᵀ * Matrix.diagonal a) * UM) :
            Matrix (Fin N) (Fin N) ℝ) := by
              calc
                ((UMᵀ *
                    ((((UM * Matrix.diagonal c) * UMᵀ) : Matrix (Fin N) (Fin N) ℝ) *
                      Matrix.diagonal a)) *
                  UM : Matrix (Fin N) (Fin N) ℝ)
                    =
                      (UMᵀ * (UM * (Matrix.diagonal c * (UMᵀ * (Matrix.diagonal a * UM)))) :
                        Matrix (Fin N) (Fin N) ℝ) := by
                          simp [Matrix.mul_assoc]
                _ =
                    (((UMᵀ * UM) * (Matrix.diagonal c * (UMᵀ * (Matrix.diagonal a * UM)))) :
                      Matrix (Fin N) (Fin N) ℝ) := by
                        simp [Matrix.mul_assoc]
                _ = (Matrix.diagonal c * (UMᵀ * (Matrix.diagonal a * UM)) :
                      Matrix (Fin N) (Fin N) ℝ) := by
                        rw [hUtU]
                        simp
                _ = (Matrix.diagonal c * ((UMᵀ * Matrix.diagonal a) * UM) :
                      Matrix (Fin N) (Fin N) ℝ) := by
                        simp [Matrix.mul_assoc]

/-- Helper for Fact 24.59: the transported core `Uᵀ * diag a * U` already vanishes between
distinct `c`-plateaux. -/
private theorem transportedDiagonalCoreCrossBlockZero
    {N : ℕ} {a c : Fin N → ℝ}
    {C : Matrix (Fin N) (Fin N) ℝ}
    {U : Matrix.orthogonalGroup (Fin N) ℝ}
    (ha : Antitone a)
    (hCdiag :
      C = (((U : Matrix _ _ ℝ) * Matrix.diagonal c) * (U : Matrix _ _ ℝ)ᵀ))
    (hstrict_side :
      ∀ {r : Fin N} (hrN : r.1 + 1 < N) (hr : a r > a ⟨r.1 + 1, hrN⟩),
        let Pr : Matrix (Fin N) (Fin N) ℝ :=
          (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
        (∀ i, c i > c r →
          (∀ j, Pr i j = if i = j then 1 else 0) ∧
            ∀ j, Pr j i = if j = i then 1 else 0) ∧
          ∀ i, c i < c r →
            (∀ j, Pr i j = 0) ∧ ∀ j, Pr j i = 0)
    {i j : Fin N} (hij : c i ≠ c j) :
    let D : Matrix (Fin N) (Fin N) ℝ :=
      (((U : Matrix _ _ ℝ)ᵀ * Matrix.diagonal a) * (U : Matrix _ _ ℝ))
    D i j = 0 := by
  let D : Matrix (Fin N) (Fin N) ℝ :=
    (((U : Matrix _ _ ℝ)ᵀ * Matrix.diagonal a) * (U : Matrix _ _ ℝ))
  have hDcomm : Commute D (Matrix.diagonal c) :=
    (transportedDiagonalACommutesDiagonalC
      (a := a) (c := c) (C := C) (U := U) ha hCdiag hstrict_side).2
  -- Once the transported core commutes with `diag c`, distinct `c`-values force the
  -- corresponding matrix entry to vanish.
  exact cross_block_entry_eq_zero_of_diagonal_commute hDcomm.symm hij

/-- Helper for Fact 24.59: every transported prefix projector commutes with the transported core
`Uᵀ * diag a * U`. -/
private theorem transportedPrefixProjectorCommutesDiagonalCore
    {N : ℕ} {a : Fin N → ℝ}
    {U : Matrix.orthogonalGroup (Fin N) ℝ} (r : Fin N) :
    let Pr : Matrix (Fin N) (Fin N) ℝ :=
      (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
    let D : Matrix (Fin N) (Fin N) ℝ :=
      (((U : Matrix _ _ ℝ)ᵀ * Matrix.diagonal a) * (U : Matrix _ _ ℝ))
    Commute Pr D := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  have hUUt : UM * UMᵀ = 1 := orthogonal_mul_transpose_eq_one U.prop
  -- Conjugating by `Uᵀ` and `U` preserves the obvious diagonal commutation relation.
  change
    Commute (((UMᵀ * prefixProj r) * UM) : Matrix (Fin N) (Fin N) ℝ)
      (((UMᵀ * Matrix.diagonal a) * UM) : Matrix (Fin N) (Fin N) ℝ)
  calc
    ((((UMᵀ * prefixProj r) * UM) * ((UMᵀ * Matrix.diagonal a) * UM)) :
        Matrix (Fin N) (Fin N) ℝ)
        = (UMᵀ * (prefixProj r * Matrix.diagonal a) * UM : Matrix (Fin N) (Fin N) ℝ) := by
            calc
              ((((UMᵀ * prefixProj r) * UM) * ((UMᵀ * Matrix.diagonal a) * UM)) :
                  Matrix (Fin N) (Fin N) ℝ)
                  = (((UMᵀ * prefixProj r) * (UM * UMᵀ)) * Matrix.diagonal a) * UM := by
                      simp [Matrix.mul_assoc]
              _ = (((UMᵀ * prefixProj r) * (1 : Matrix (Fin N) (Fin N) ℝ)) * Matrix.diagonal a) *
                    UM := by
                    rw [hUUt]
              _ = (UMᵀ * (prefixProj r * Matrix.diagonal a)) * UM := by
                    simp [Matrix.mul_assoc]
    _ = (UMᵀ * (Matrix.diagonal a * prefixProj r) * UM : Matrix (Fin N) (Fin N) ℝ) := by
          rw [prefixProj, (Matrix.commute_diagonal (prefixMask r) a).eq]
    _ =
        ((((UMᵀ * Matrix.diagonal a) * UM) * ((UMᵀ * prefixProj r) * UM)) :
          Matrix (Fin N) (Fin N) ℝ) := by
            symm
            calc
              ((((UMᵀ * Matrix.diagonal a) * UM) * ((UMᵀ * prefixProj r) * UM)) :
                  Matrix (Fin N) (Fin N) ℝ)
                  = (((UMᵀ * Matrix.diagonal a) * (UM * UMᵀ)) * prefixProj r) * UM := by
                      simp [Matrix.mul_assoc]
              _ = (((UMᵀ * Matrix.diagonal a) * (1 : Matrix (Fin N) (Fin N) ℝ)) * prefixProj r) *
                    UM := by
                    rw [hUUt]
              _ = (UMᵀ * (Matrix.diagonal a * prefixProj r)) * UM := by
                    simp [Matrix.mul_assoc]

/-- Helper for Fact 24.59: reindexing along the fibers of `c` turns a matrix with no
cross-fiber entries into a literal block diagonal matrix. -/
private theorem reindex_eq_blockDiagonal'_of_sigmaFiberZero
    {N : ℕ} {c : Fin N → ℝ} {M : Matrix (Fin N) (Fin N) ℝ}
    (hzero : ∀ {i j : Fin N}, c i ≠ c j → M i j = 0) :
    let eC : Fin N ≃ Σ y : ℝ, { i : Fin N // c i = y } := (Equiv.sigmaFiberEquiv c).symm
    Matrix.reindex eC eC M =
      Matrix.blockDiagonal' (fun y => Matrix.toSquareBlock M c y) := by
  let eC : Fin N ≃ Σ y : ℝ, { i : Fin N // c i = y } := (Equiv.sigmaFiberEquiv c).symm
  -- Compare the reindexed matrix and the block diagonal form entrywise on the sigma-fiber index.
  ext ik jk
  rcases ik with ⟨y, i⟩
  rcases jk with ⟨y', j⟩
  by_cases hyy : y = y'
  · subst hyy
    -- On one fiber, both sides are just the corresponding square block of `M`.
    simp [eC, Matrix.reindex_apply, Matrix.toSquareBlock_def]
  · have hij : c i.1 ≠ c j.1 := by
      simpa [i.2, j.2] using hyy
    have hM : M i.1 j.1 = 0 := hzero hij
    -- Distinct fibers contribute only off-diagonal zero blocks.
    simp [eC, Matrix.reindex_apply, Matrix.blockDiagonal'_apply_ne, Matrix.toSquareBlock_def,
      hyy, hM]

/-- Helper for Fact 24.59: replace the raw `ℝ`-fiber index by the finite index
`Set.range c`. -/
private def rangeFiberEquiv
    {N : ℕ} (c : Fin N → ℝ) :
    Fin N ≃ Σ y : Set.range c, { i : Fin N // c i = y.1 } :=
  ((Equiv.sigmaFiberEquiv c).symm).trans
    { toFun := fun x ↦ ⟨⟨x.1, ⟨x.2.1, x.2.2⟩⟩, x.2⟩
      invFun := fun x ↦ ⟨x.1.1, x.2⟩
      left_inv := by
        intro x
        rcases x with ⟨y, i⟩
        rfl
      right_inv := by
        intro x
        rcases x with ⟨y, i⟩
        rcases y with ⟨y, hy⟩
        rfl }

/-- Helper for Fact 24.59: the finite range-fiber reindex sends a fiber coordinate back to its
underlying matrix index. -/
@[simp] private theorem rangeFiberEquiv_symm_apply
    {N : ℕ} (c : Fin N → ℝ) (y : Set.range c)
    (i : { j : Fin N // c j = y.1 }) :
    (rangeFiberEquiv c).symm ⟨y, i⟩ = i.1 := by
  rfl

/-- Helper for Fact 24.59: reindexing along the finite range-fiber surface keeps the same block
normal form while exposing a finite outer index for later block algebra. -/
private theorem reindex_eq_blockDiagonal'_of_rangeFiberZero
    {N : ℕ} {c : Fin N → ℝ} {M : Matrix (Fin N) (Fin N) ℝ}
    (hzero : ∀ {i j : Fin N}, c i ≠ c j → M i j = 0) :
    let eR : Fin N ≃ Σ y : Set.range c, { i : Fin N // c i = y.1 } := rangeFiberEquiv c
    Matrix.reindex eR eR M =
      Matrix.blockDiagonal' (fun y : Set.range c => Matrix.toSquareBlock M c y.1) := by
  let eR : Fin N ≃ Σ y : Set.range c, { i : Fin N // c i = y.1 } := rangeFiberEquiv c
  -- Compare the finite range-fiber reindex and the dependent block diagonal entrywise.
  ext ik jk
  rcases ik with ⟨y, i⟩
  rcases jk with ⟨y', j⟩
  by_cases hyy : y = y'
  · subst hyy
    -- On one finite range fiber, both sides are the same square block of `M`.
    simp [Matrix.reindex_apply, Matrix.toSquareBlock_def]
  · have hyy' : y.1 ≠ y'.1 := by
      intro hy
      apply hyy
      exact Subtype.ext hy
    have hM : M i.1 j.1 = 0 := by
      apply hzero
      simpa [i.2, j.2] using hyy'
    -- Distinct range fibers contribute only off-diagonal zero blocks.
    simp [Matrix.reindex_apply, Matrix.blockDiagonal'_apply_ne, Matrix.toSquareBlock_def, hyy, hM]

/-- Helper for Fact 24.59: the square block of a symmetric matrix on one `c`-fiber is still
symmetric. -/
private theorem toSquareBlock_isSymm
    {N : ℕ} {c : Fin N → ℝ} {M : Matrix (Fin N) (Fin N) ℝ}
    (hM : M.IsSymm) (y : ℝ) :
    (Matrix.toSquareBlock M c y).IsSymm := by
  -- Restricting a symmetric matrix to one fiber keeps the transpose relation entrywise.
  simpa [Matrix.toSquareBlock_def] using
    (Matrix.IsSymm.submatrix hM fun i : { a // c a = y } => i.1)

/-- Helper for Fact 24.59: reindexing `diag c` along the fibers of `c` produces scalar diagonal
blocks. -/
private theorem reindex_diagonal_eq_blockDiagonal'_sigmaFiber
    {N : ℕ} (c : Fin N → ℝ) :
    let eC : Fin N ≃ Σ y : ℝ, { i : Fin N // c i = y } := (Equiv.sigmaFiberEquiv c).symm
    Matrix.reindex eC eC (Matrix.diagonal c) =
      Matrix.blockDiagonal'
        (fun y => Matrix.diagonal fun _ : { i : Fin N // c i = y } => y) := by
  let eC : Fin N ≃ Σ y : ℝ, { i : Fin N // c i = y } := (Equiv.sigmaFiberEquiv c).symm
  have hdiagBlock :
      Matrix.reindex eC eC (Matrix.diagonal c) =
        Matrix.blockDiagonal' (fun y => Matrix.toSquareBlock (Matrix.diagonal c) c y) := by
    -- Distinct fibers of `c` do not interact in the diagonal matrix `diag c`.
    refine reindex_eq_blockDiagonal'_of_sigmaFiberZero (c := c) ?_
    intro i j hij
    have hij' : i ≠ j := by
      intro hijEq
      exact hij (by simpa [hijEq])
    simp [Matrix.diagonal_apply, hij']
  refine hdiagBlock.trans ?_
  -- Each diagonal fiber block is the scalar diagonal matrix with value `y`.
  congr
  funext y
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.toSquareBlock_def, Matrix.diagonal_apply, i.2]
  · have hijVal : i.1 ≠ j.1 := by
      intro hEq
      apply hij
      exact Subtype.ext hEq
    simp [Matrix.toSquareBlock_def, Matrix.diagonal_apply, hij, hijVal]

/-- Helper for Fact 24.59: reindexing `diag c` along the finite range-fiber surface produces the
same scalar diagonal blocks, now indexed by `Set.range c`. -/
private theorem reindex_diagonal_eq_blockDiagonal'_rangeFiber
    {N : ℕ} (c : Fin N → ℝ) :
    let eR : Fin N ≃ Σ y : Set.range c, { i : Fin N // c i = y.1 } := rangeFiberEquiv c
    Matrix.reindex eR eR (Matrix.diagonal c) =
      Matrix.blockDiagonal'
        (fun y : Set.range c => Matrix.diagonal fun _ : { i : Fin N // c i = y.1 } => y.1) := by
  let eR : Fin N ≃ Σ y : Set.range c, { i : Fin N // c i = y.1 } := rangeFiberEquiv c
  -- Compare the finite range-fiber reindex of `diag c` and the scalar block form entrywise.
  ext ik jk
  rcases ik with ⟨y, i⟩
  rcases jk with ⟨y', j⟩
  by_cases hyy : y = y'
  · subst hyy
    by_cases hij : i = j
    · subst hij
      -- On the diagonal of one range fiber, both sides are the common scalar `y.1`.
      simp [Matrix.reindex_apply, i.2]
    · have hijVal : i.1 ≠ j.1 := by
        intro hEq
        apply hij
        exact Subtype.ext hEq
      -- Off the diagonal inside one range fiber, both matrices vanish.
      simp [Matrix.reindex_apply, hij, hijVal]
  · have hyy' : y.1 ≠ y'.1 := by
      intro hy
      apply hyy
      exact Subtype.ext hy
    have hijVal : i.1 ≠ j.1 := by
      intro hEq
      apply hyy'
      simpa [i.2, j.2] using congrArg c hEq
    -- Distinct range fibers contribute only off-diagonal zero blocks.
    simp [Matrix.reindex_apply, Matrix.blockDiagonal'_apply_ne, hyy, hijVal]

/-- Helper for Fact 24.59: a block diagonal matrix is orthogonal once each block is orthogonal. -/
private theorem blockDiagonal'_mem_orthogonalGroup
    {o : Type*} [Fintype o] [DecidableEq o]
    {m : o → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {U : (i : o) → Matrix (m i) (m i) ℝ}
    (hU : ∀ i, U i ∈ Matrix.orthogonalGroup (m i) ℝ) :
    Matrix.blockDiagonal' U ∈ Matrix.orthogonalGroup (Σ i, m i) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  -- Multiply blockwise and collapse each orthogonal block to the identity matrix.
  calc
    Matrix.blockDiagonal' U * (Matrix.blockDiagonal' U)ᵀ
        = Matrix.blockDiagonal' (fun i => U i * (U i)ᵀ) := by
            rw [Matrix.blockDiagonal'_transpose, ← Matrix.blockDiagonal'_mul]
    _ = Matrix.blockDiagonal' (fun i => (1 : Matrix (m i) (m i) ℝ)) := by
          congr
          funext i
          exact (Matrix.mem_orthogonalGroup_iff (A := U i)).mp (hU i)
    _ = 1 := by
          calc
            Matrix.blockDiagonal' (fun i => (1 : Matrix (m i) (m i) ℝ))
                = Matrix.blockDiagonal'
                    (fun i => Matrix.diagonal (fun _ : m i => (1 : ℝ))) := by
                      simpa [diagonal_one]
            _ = Matrix.diagonal
                  (fun _ : Σ i, m i => (1 : ℝ)) := by
                    simpa using
                      (Matrix.blockDiagonal'_diagonal
                        (d := fun i => fun _ : m i => (1 : ℝ)))
            _ = 1 := by
                  ext i j
                  by_cases hij : i = j
                  · subst hij
                    simp
                  · simp [Matrix.diagonal_apply, hij]

/-- Helper for Fact 24.59: orthogonal conjugation fixes a scalar diagonal block. -/
private theorem orthogonal_conj_diagonal_const
    {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix.orthogonalGroup n ℝ} (x : ℝ) :
    (((U : Matrix n n ℝ) * Matrix.diagonal (fun _ : n => x)) * (U : Matrix n n ℝ)ᵀ) =
      Matrix.diagonal (fun _ : n => x) := by
  let UM : Matrix n n ℝ := U
  have hUUt : UM * UMᵀ = 1 := orthogonal_mul_transpose_eq_one U.prop
  -- Rewrite the scalar diagonal as `x • 1`, then collapse the orthogonal factors.
  calc
    (((U : Matrix n n ℝ) * Matrix.diagonal (fun _ : n => x)) * (U : Matrix n n ℝ)ᵀ)
        = ((UM * (x • (1 : Matrix n n ℝ))) * UMᵀ) := by
            rw [Matrix.smul_one_eq_diagonal]
    _ = x • ((UM * (1 : Matrix n n ℝ)) * UMᵀ) := by
          simp [Matrix.mul_assoc]
    _ = x • (1 : Matrix n n ℝ) := by
          simp [hUUt]
    _ = Matrix.diagonal (fun _ : n => x) := by
          rw [Matrix.smul_one_eq_diagonal]

/-- Helper for Fact 24.59: reindexing a block diagonal orthogonal witness back to `Fin N`
preserves orthogonality. -/
private theorem reindexBlockOrthogonalWitness
    {N : ℕ} {a : Fin N → ℝ}
    {Uy : (y : Set.range a) → Matrix { i : Fin N // a i = y.1 } { i : Fin N // a i = y.1 } ℝ}
    (hUy : ∀ y, Uy y ∈ Matrix.orthogonalGroup { i : Fin N // a i = y.1 } ℝ) :
    let eR : Fin N ≃ Σ y : Set.range a, { i : Fin N // a i = y.1 } := rangeFiberEquiv a
    Matrix.reindex eR.symm eR.symm (Matrix.blockDiagonal' Uy) ∈ Matrix.orthogonalGroup (Fin N) ℝ := by
  let eR : Fin N ≃ Σ y : Set.range a, { i : Fin N // a i = y.1 } := rangeFiberEquiv a
  have hBlock :
      Matrix.blockDiagonal' Uy ∈
        Matrix.orthogonalGroup (Σ y : Set.range a, { i : Fin N // a i = y.1 }) ℝ :=
    blockDiagonal'_mem_orthogonalGroup hUy
  rw [Matrix.mem_orthogonalGroup_iff]
  -- Reindex the blockwise orthogonality identity back to the original `Fin N` coordinates.
  calc
    Matrix.reindex eR.symm eR.symm (Matrix.blockDiagonal' Uy) *
        (Matrix.reindex eR.symm eR.symm (Matrix.blockDiagonal' Uy))ᵀ
        =
          Matrix.reindex eR.symm eR.symm
            (Matrix.blockDiagonal' Uy * (Matrix.blockDiagonal' Uy)ᵀ) := by
              simpa [Matrix.transpose_reindex] using
                (Matrix.submatrix_mul_equiv
                  (Matrix.blockDiagonal' Uy) ((Matrix.blockDiagonal' Uy)ᵀ)
                  eR.symm eR.symm eR.symm).symm
    _ = Matrix.reindex eR.symm eR.symm
          (1 :
            Matrix
              (Σ y : Set.range a, { i : Fin N // a i = y.1 })
              (Σ y : Set.range a, { i : Fin N // a i = y.1 }) ℝ) := by
            congr
            exact (Matrix.mem_orthogonalGroup_iff (A := Matrix.blockDiagonal' Uy)).mp hBlock
    _ = 1 := by
          simp

/-- Helper for Fact 24.59: after reindexing by the equal-`a` fibers, a symmetric matrix with no
cross-fiber entries diagonalizes blockwise while preserving `diag a`. -/
private theorem fiberwiseDiagonalizationPreservingScalarBlocks
    {N : ℕ} {a : Fin N → ℝ} {D : Matrix (Fin N) (Fin N) ℝ}
    (hDsymm : D.IsSymm)
    (hzero : ∀ {i j : Fin N}, a i ≠ a j → D i j = 0) :
    ∃ R : Matrix.orthogonalGroup (Fin N) ℝ, ∃ d : Fin N → ℝ,
      (((R : Matrix _ _ ℝ) * Matrix.diagonal a) * (R : Matrix _ _ ℝ)ᵀ) =
        Matrix.diagonal a ∧
      D = (((R : Matrix _ _ ℝ) * Matrix.diagonal d) * (R : Matrix _ _ ℝ)ᵀ) := by
  let eR : Fin N ≃ Σ y : Set.range a, { i : Fin N // a i = y.1 } := rangeFiberEquiv a
  let aSigma : (Σ y : Set.range a, { i : Fin N // a i = y.1 }) → ℝ := fun x ↦ x.1.1
  have hDblock :
      Matrix.reindex eR eR D =
        Matrix.blockDiagonal' (fun y : Set.range a => Matrix.toSquareBlock D a y.1) := by
    -- The commuting hypothesis has already collapsed the matrix to equal-`a` fiber blocks.
    simpa [eR] using reindex_eq_blockDiagonal'_of_rangeFiberZero (c := a) (M := D) hzero
  have hBlockHermitian :
      ∀ y : Set.range a, (Matrix.toSquareBlock D a y.1).IsHermitian := by
    intro y
    -- Each equal-`a` fiber inherits symmetry, hence Hermitianity over `ℝ`.
    exact (toSquareBlock_isSymm (c := a) (M := D) hDsymm y.1).isHermitian
  let Uy :
      (y : Set.range a) →
        Matrix.orthogonalGroup { i : Fin N // a i = y.1 } ℝ :=
    fun y ↦
      ⟨(hBlockHermitian y).eigenvectorUnitary, by
        simpa using (hBlockHermitian y).eigenvectorUnitary.prop⟩
  let UyM :
      (y : Set.range a) →
        Matrix { i : Fin N // a i = y.1 } { i : Fin N // a i = y.1 } ℝ :=
    fun y ↦ (Uy y : Matrix _ _ ℝ)
  let blockU :
      Matrix (Σ y : Set.range a, { i : Fin N // a i = y.1 })
        (Σ y : Set.range a, { i : Fin N // a i = y.1 }) ℝ :=
    Matrix.blockDiagonal' UyM
  have hUyM :
      ∀ y : Set.range a, UyM y ∈ Matrix.orthogonalGroup { i : Fin N // a i = y.1 } ℝ := by
    intro y
    exact (Uy y).prop
  let dSigma : (Σ y : Set.range a, { i : Fin N // a i = y.1 }) → ℝ :=
    fun x ↦ (hBlockHermitian x.1).eigenvalues x.2
  let d : Fin N → ℝ := dSigma ∘ eR
  let R :
      Matrix.orthogonalGroup (Fin N) ℝ :=
    ⟨Matrix.reindex eR.symm eR.symm blockU,
      by
        simpa [eR, blockU, UyM] using
          reindexBlockOrthogonalWitness (a := a) (Uy := UyM) hUyM⟩
  have hBlockPreservesDiagA :
      (((blockU * Matrix.diagonal aSigma) * blockUᵀ) :
          Matrix (Σ y : Set.range a, { i : Fin N // a i = y.1 })
            (Σ y : Set.range a, { i : Fin N // a i = y.1 }) ℝ) =
        Matrix.diagonal aSigma := by
    have hDiagSigma :
        Matrix.diagonal aSigma =
          Matrix.blockDiagonal'
            (fun y : Set.range a =>
              Matrix.diagonal (fun _ : { i : Fin N // a i = y.1 } => y.1)) := by
      -- The reindexed `diag a` is blockwise scalar on each equal-value plateau.
      symm
      simpa [aSigma] using
        (Matrix.blockDiagonal'_diagonal
          (d := fun y : Set.range a => fun _ : { i : Fin N // a i = y.1 } => y.1))
    -- Conjugate each scalar block by its local orthogonal eigenbasis.
    calc
      (((blockU * Matrix.diagonal aSigma) * blockUᵀ) :
          Matrix (Σ y : Set.range a, { i : Fin N // a i = y.1 })
            (Σ y : Set.range a, { i : Fin N // a i = y.1 }) ℝ)
          =
            (((blockU *
                Matrix.blockDiagonal'
                  (fun y : Set.range a =>
                    Matrix.diagonal (fun _ : { i : Fin N // a i = y.1 } => y.1))) *
                blockUᵀ) :
              Matrix (Σ y : Set.range a, { i : Fin N // a i = y.1 })
                (Σ y : Set.range a, { i : Fin N // a i = y.1 }) ℝ) := by
              rw [hDiagSigma]
      _ =
          Matrix.blockDiagonal'
            (fun y : Set.range a =>
              (((UyM y) *
                  Matrix.diagonal (fun _ : { i : Fin N // a i = y.1 } => y.1)) *
                (UyM y)ᵀ)) := by
            rw [Matrix.blockDiagonal'_transpose, ← Matrix.blockDiagonal'_mul,
              ← Matrix.blockDiagonal'_mul]
      _ =
          Matrix.blockDiagonal'
            (fun y : Set.range a =>
              Matrix.diagonal (fun _ : { i : Fin N // a i = y.1 } => y.1)) := by
            congr
            funext y
            exact orthogonal_conj_diagonal_const (U := Uy y) y.1
      _ = Matrix.diagonal aSigma := by
            simpa [aSigma] using
              (Matrix.blockDiagonal'_diagonal
                (d := fun y : Set.range a => fun _ : { i : Fin N // a i = y.1 } => y.1))
  have hBlockDiagonalizesD :
      (((blockU * Matrix.diagonal dSigma) * blockUᵀ) :
          Matrix (Σ y : Set.range a, { i : Fin N // a i = y.1 })
            (Σ y : Set.range a, { i : Fin N // a i = y.1 }) ℝ) =
        Matrix.blockDiagonal' (fun y : Set.range a => Matrix.toSquareBlock D a y.1) := by
    have hDiagSigma :
        Matrix.diagonal dSigma =
          Matrix.blockDiagonal'
            (fun y : Set.range a =>
              Matrix.diagonal
                (fun i : { j : Fin N // a j = y.1 } => (hBlockHermitian y).eigenvalues i)) := by
      -- The blockwise eigenvalue lists assemble into one diagonal on the sigma index.
      symm
      simpa [dSigma] using
        (Matrix.blockDiagonal'_diagonal
          (d := fun y : Set.range a =>
            fun i : { j : Fin N // a j = y.1 } => (hBlockHermitian y).eigenvalues i))
    -- The spectral theorem closes each symmetric block independently.
    calc
      (((blockU * Matrix.diagonal dSigma) * blockUᵀ) :
          Matrix (Σ y : Set.range a, { i : Fin N // a i = y.1 })
            (Σ y : Set.range a, { i : Fin N // a i = y.1 }) ℝ)
          =
            (((blockU *
                Matrix.blockDiagonal'
                  (fun y : Set.range a =>
                    Matrix.diagonal
                      (fun i : { j : Fin N // a j = y.1 } =>
                        (hBlockHermitian y).eigenvalues i))) *
                blockUᵀ) :
              Matrix (Σ y : Set.range a, { i : Fin N // a i = y.1 })
                (Σ y : Set.range a, { i : Fin N // a i = y.1 }) ℝ) := by
              rw [hDiagSigma]
      _ =
          Matrix.blockDiagonal'
            (fun y : Set.range a =>
              (((UyM y) *
                  Matrix.diagonal
                    (fun i : { j : Fin N // a j = y.1 } =>
                      (hBlockHermitian y).eigenvalues i)) *
                (UyM y)ᵀ)) := by
            rw [Matrix.blockDiagonal'_transpose, ← Matrix.blockDiagonal'_mul,
              ← Matrix.blockDiagonal'_mul]
      _ = Matrix.blockDiagonal' (fun y : Set.range a => Matrix.toSquareBlock D a y.1) := by
            congr
            funext y
            simpa [Uy, UyM, Matrix.conjTranspose_eq_transpose_of_trivial,
              Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
              (hBlockHermitian y).spectral_theorem.symm
  refine ⟨R, d, ?_, ?_⟩
  · -- Reindex the blockwise scalar preservation back to the original `Fin N` coordinates.
    have hReindexA :=
      reindex_symm_diagonalization_eq eR blockU aSigma
    calc
      (((R : Matrix _ _ ℝ) * Matrix.diagonal a) * (R : Matrix _ _ ℝ)ᵀ)
          =
            Matrix.reindex eR.symm eR.symm
              ((((blockU) * Matrix.diagonal aSigma) * (blockU)ᵀ) :
                Matrix (Σ y : Set.range a, { i : Fin N // a i = y.1 })
                  (Σ y : Set.range a, { i : Fin N // a i = y.1 }) ℝ) := by
                symm
                simpa [R, d, eR, blockU, aSigma]
                  using hReindexA
      _ = Matrix.reindex eR.symm eR.symm (Matrix.diagonal aSigma) := by
            rw [hBlockPreservesDiagA]
      _ = Matrix.diagonal a := by
            ext i j
            by_cases hij : i = j
            · subst hij
              simpa [Matrix.reindex_apply, aSigma, eR] using
                (((eR i).2).2).symm
            · simp [Matrix.reindex_apply, Matrix.diagonal_apply, hij]
  · -- Reindex the blockwise spectral decomposition of `D` back to `Fin N`.
    have hReindexD :=
      reindex_symm_diagonalization_eq eR blockU dSigma
    calc
      D = Matrix.reindex eR.symm eR.symm (Matrix.reindex eR eR D) := by
            simp [eR]
      _ =
          Matrix.reindex eR.symm eR.symm
            (Matrix.blockDiagonal' (fun y : Set.range a => Matrix.toSquareBlock D a y.1)) := by
              rw [hDblock]
      _ =
          Matrix.reindex eR.symm eR.symm
            ((((blockU) * Matrix.diagonal dSigma) * (blockU)ᵀ) :
              Matrix (Σ y : Set.range a, { i : Fin N // a i = y.1 })
                (Σ y : Set.range a, { i : Fin N // a i = y.1 }) ℝ) := by
              rw [← hBlockDiagonalizesD]
      _ = (((R : Matrix _ _ ℝ) * Matrix.diagonal d) * (R : Matrix _ _ ℝ)ᵀ) := by
            simpa [R, d, eR, blockU, dSigma] using hReindexD

/-- Helper for Fact 24.59: a commuting symmetric pair consisting of `diag a` and `C` admits a
common orthogonal eigenbasis that preserves the scalar blocks of `diag a`, though the resulting
diagonal entries for `C` are not yet sorted. -/
private theorem commonOrthogonalDiagonalizationOfCommutingSymm
    {N : ℕ} {a : Fin N → ℝ} {C : Matrix (Fin N) (Fin N) ℝ}
    (hCsymm : C.IsSymm) (hcomm : Commute (Matrix.diagonal a) C) :
    ∃ Q : Matrix.orthogonalGroup (Fin N) ℝ, ∃ c' : Fin N → ℝ,
      (((Q : Matrix _ _ ℝ) * Matrix.diagonal a) * (Q : Matrix _ _ ℝ)ᵀ) =
        Matrix.diagonal a ∧
      C = (((Q : Matrix _ _ ℝ) * Matrix.diagonal c') * (Q : Matrix _ _ ℝ)ᵀ) := by
  have hzero :
      ∀ {i j : Fin N}, a i ≠ a j → C i j = 0 := by
    intro i j hij
    -- Commutation with `diag a` kills every cross-fiber entry of `C`.
    exact cross_block_entry_eq_zero_of_diagonal_commute hcomm hij
  -- Package the commuting-symmetric pair into the blockwise spectral helper.
  simpa using
    fiberwiseDiagonalizationPreservingScalarBlocks (a := a) (D := C) hCsymm hzero

/-- Helper for Fact 24.59: an orthogonal symmetry of `diag a` fixes every strict-drop prefix
projector of `a`. -/
private theorem strictDropPrefixFixedOfDiagonalPreserving
    {N : ℕ} {a : Fin N → ℝ} (ha : Antitone a)
    {Q : Matrix.orthogonalGroup (Fin N) ℝ}
    (hQdiag :
      (((Q : Matrix _ _ ℝ) * Matrix.diagonal a) * (Q : Matrix _ _ ℝ)ᵀ) =
        Matrix.diagonal a)
    {r : Fin N} (hrN : r.1 + 1 < N)
    (hr : a r > a ⟨r.1 + 1, hrN⟩) :
    ((((Q : Matrix _ _ ℝ)ᵀ * prefixProj r) * (Q : Matrix _ _ ℝ)) :
      Matrix (Fin N) (Fin N) ℝ) = prefixProj r := by
  let QM : Matrix (Fin N) (Fin N) ℝ := Q
  have hQtQ : QMᵀ * QM = 1 := orthogonal_transpose_mul_eq_one Q.prop
  have hdiagComm : Commute (Matrix.diagonal a) QM := by
    change Matrix.diagonal a * QM = QM * Matrix.diagonal a
    have hmul := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ ↦ M * QM) hQdiag
    simpa [QM, Matrix.mul_assoc, hQtQ] using hmul.symm
  have hprefixComm : Commute (prefixProj r) QM :=
    strict_drop_prefix_commutes_of_diagonal_commute ha hdiagComm hrN hr
  have hfix :=
    congrArg (fun M : Matrix (Fin N) (Fin N) ℝ ↦ QMᵀ * M) hprefixComm.eq
  -- Multiplying the commuting prefix identity on the left by `Qᵀ` collapses the orthogonal factor
  -- and leaves the prefix projector unchanged.
  calc
    ((((Q : Matrix _ _ ℝ)ᵀ * prefixProj r) * (Q : Matrix _ _ ℝ)) :
        Matrix (Fin N) (Fin N) ℝ)
        = QMᵀ * (QM * prefixProj r) := by
            simpa [QM, Matrix.mul_assoc] using hfix
    _ = (QMᵀ * QM) * prefixProj r := by
          simp [QM, Matrix.mul_assoc]
    _ = prefixProj r := by
          simp [QM, hQtQ]

/-- Helper for Fact 24.59: strict-side basis action forces the corresponding weighted trace
equality for the same cutoff. -/
private theorem trace_diagonal_eq_sum_prefix_of_strict_side_action
    {N : ℕ} {c : Fin N → ℝ} (hc : Antitone c)
    {P : Matrix (Fin N) (Fin N) ℝ} {r : Fin N}
    (htraceP : Matrix.trace P = ∑ i, if i ≤ r then (1 : ℝ) else 0)
    (hside :
      (∀ i, c i > c r →
        (∀ j, P i j = if i = j then 1 else 0) ∧
          ∀ j, P j i = if j = i then 1 else 0) ∧
        ∀ i, c i < c r →
          (∀ j, P i j = 0) ∧ ∀ j, P j i = 0) :
    Matrix.trace (P * Matrix.diagonal c) = ∑ i, if i ≤ r then c i else 0 := by
  let S : ℝ := ∑ i, if i ≤ r then c i else 0
  let T : ℝ := Matrix.trace (P * Matrix.diagonal c)
  let K : ℝ := ∑ i, if i ≤ r then (1 : ℝ) else 0
  let R : ℝ := Matrix.trace P
  have habove : ∀ i, c i > c r → P i i = 1 := by
    intro i hi
    simpa using (hside.1 i hi).1 i
  have hbelow : ∀ i, c i < c r → P i i = 0 := by
    intro i hi
    simpa using (hside.2 i hi).1 i
  let center : ℝ :=
    ∑ i, if i ≤ r then (1 - P i i) * (c i - c r) else P i i * (c r - c i)
  have hcenter_zero : center = 0 := by
    -- Each centered term vanishes separately: above the cutoff `P i i = 1`, below it
    -- `P i i = 0`, and on the plateau `c i = c r`.
    calc
      center = ∑ i : Fin N, 0 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        dsimp [center]
        by_cases hir : i ≤ r
        · by_cases hgt : c i > c r
          · have hPii : P i i = 1 := habove i hgt
            simp [hir, hgt, hPii]
          · have hieq : c i = c r := by
              exact le_antisymm (le_of_not_gt hgt) (hc hir)
            simp [hir, hieq]
        · by_cases hlt : c i < c r
          · have hPii : P i i = 0 := hbelow i hlt
            simp [hir, hlt, hPii]
          · have hieq : c i = c r := by
              exact le_antisymm (hc (le_of_not_ge hir)) (le_of_not_gt hlt)
            simp [hir, hieq]
      _ = 0 := by simp
  have hcalc :
      center = S - T - c r * (K - R) := by
    dsimp [center, S, T, K, R]
    calc
      (∑ i, if i ≤ r then (1 - P i i) * (c i - c r) else P i i * (c r - c i))
          = ∑ i,
              ((if i ≤ r then c i else 0) - P i i * c i -
                c r * ((if i ≤ r then (1 : ℝ) else 0) - P i i)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                by_cases hir : i ≤ r
                · simp [hir]
                  ring
                · simp [hir]
                  ring
      _ = (∑ i, if i ≤ r then c i else 0) - ∑ i, P i i * c i -
            ∑ i, c r * ((if i ≤ r then (1 : ℝ) else 0) - P i i) := by
              rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      _ = (∑ i, if i ≤ r then c i else 0) - ∑ i, P i i * c i -
            c r * ((∑ i, if i ≤ r then (1 : ℝ) else 0) - ∑ i, P i i) := by
              rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      _ = S - T - c r * (K - R) := by
            simp [S, T, K, R, Matrix.trace, Matrix.mul_diagonal]
  have hKR : K - R = 0 := by
    -- The strict-side action leaves the same total projector rank as the prefix projection.
    nlinarith [htraceP]
  have hST : S - T = 0 := by
    -- The centered identity collapses exactly to the desired weighted trace equality.
    calc
      S - T = center + c r * (K - R) := by
        nlinarith [hcalc]
      _ = 0 := by
        rw [hcenter_zero, hKR]
        ring
  nlinarith [hST]

/-- Helper for Fact 24.59: the strict-side basis action on the transported prefix projector
rewrites back to the corresponding trace equality on `prefixProj r * C`. -/
private theorem strictDropPrefixTraceEqOfStrictSideAction
    {N : ℕ} {a c : Fin N → ℝ}
    {C : Matrix (Fin N) (Fin N) ℝ}
    {U : Matrix.orthogonalGroup (Fin N) ℝ}
    (hc : Antitone c)
    (hCdiag :
      C = (((U : Matrix _ _ ℝ) * Matrix.diagonal c) * (U : Matrix _ _ ℝ)ᵀ))
    (hstrict_side :
      ∀ {r : Fin N} (hrN : r.1 + 1 < N) (hr : a r > a ⟨r.1 + 1, hrN⟩),
        let Pr : Matrix (Fin N) (Fin N) ℝ :=
          (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
        (∀ i, c i > c r →
          (∀ j, Pr i j = if i = j then 1 else 0) ∧
            ∀ j, Pr j i = if j = i then 1 else 0) ∧
          ∀ i, c i < c r →
            (∀ j, Pr i j = 0) ∧ ∀ j, Pr j i = 0)
    {r : Fin N} (hrN : r.1 + 1 < N)
    (hr : a r > a ⟨r.1 + 1, hrN⟩) :
    Matrix.trace (prefixProj r * C) = ∑ i, if i ≤ r then c i else 0 := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  let Pr : Matrix (Fin N) (Fin N) ℝ :=
    (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
  rcases conjugated_prefix_projection_chain (U := U) (r := r) (s := r) le_rfl with
    ⟨hPsymm, hPidem, htraceP, -, -⟩
  have htraceDiag :
      Matrix.trace (Pr * Matrix.diagonal c) = ∑ i, if i ≤ r then c i else 0 :=
    trace_diagonal_eq_sum_prefix_of_strict_side_action hc htraceP (hstrict_side hrN hr)
  have hrewrite :
      Matrix.trace (prefixProj r * C) = Matrix.trace (Pr * Matrix.diagonal c) := by
    -- Cycle the trace until the prefix projector is expressed in the diagonal `U`-basis.
    rw [hCdiag]
    calc
      Matrix.trace (prefixProj r * ((UM * Matrix.diagonal c) * UMᵀ))
          = Matrix.trace (((prefixProj r * UM) * Matrix.diagonal c) * UMᵀ) := by
              simp [UM, Matrix.mul_assoc]
      _ = Matrix.trace (UMᵀ * ((prefixProj r * UM) * Matrix.diagonal c)) := by
            simpa [UM, Matrix.mul_assoc] using
              (Matrix.trace_mul_cycle (prefixProj r * UM) (Matrix.diagonal c) UMᵀ)
      _ = Matrix.trace ((((UMᵀ * prefixProj r) * UM) * Matrix.diagonal c) :
            Matrix (Fin N) (Fin N) ℝ) := by
            simp [UM, Matrix.mul_assoc]
      _ = Matrix.trace (Pr * Matrix.diagonal c) := by
            simp [Pr, UM, Matrix.mul_assoc]
  -- Replace the transported diagonal-basis trace by the original strict-drop trace surface.
  rwa [hrewrite]

/-- Helper for Fact 24.59: the remaining source-faithful equality-case frontier is to refine the
ordered `c`-eigenbasis using the already proved strict-side prefix action data. -/
private theorem common_orthogonal_refinement_of_ordered_c_eigenbasis
    {N : ℕ} {a c : Fin N → ℝ}
    {C : Matrix (Fin N) (Fin N) ℝ}
    {U : Matrix.orthogonalGroup (Fin N) ℝ}
    (ha : Antitone a) (hc : Antitone c)
    (hCdiag :
      C = (((U : Matrix _ _ ℝ) * Matrix.diagonal c) * (U : Matrix _ _ ℝ)ᵀ))
    (htrace_diag : Matrix.trace (Matrix.diagonal a * C) = dotProduct a c)
    (hstrict_side :
      ∀ {r : Fin N} (hrN : r.1 + 1 < N) (hr : a r > a ⟨r.1 + 1, hrN⟩),
        let Pr : Matrix (Fin N) (Fin N) ℝ :=
          (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
        (∀ i, c i > c r →
          (∀ j, Pr i j = if i = j then 1 else 0) ∧
            ∀ j, Pr j i = if j = i then 1 else 0) ∧
          ∀ i, c i < c r →
            (∀ j, Pr i j = 0) ∧ ∀ j, Pr j i = 0) :
    ∃ Q : Matrix.orthogonalGroup (Fin N) ℝ,
      (((Q : Matrix _ _ ℝ) * Matrix.diagonal a) * (Q : Matrix _ _ ℝ)ᵀ) =
        Matrix.diagonal a ∧
      C = (((Q : Matrix _ _ ℝ) * Matrix.diagonal c) * (Q : Matrix _ _ ℝ)ᵀ) := by
  have hdiagAcommC : Commute (Matrix.diagonal a) C :=
    diagonal_a_commutes_of_strict_side_actions (a := a) (c := c) (C := C) (U := U)
      ha hCdiag hstrict_side
  have hCsymm : C.IsSymm := by
    let UM : Matrix (Fin N) (Fin N) ℝ := U
    -- Route correction: pivot from the earlier range-fiber transport route to a common-eigenbasis
    -- route. The equality-case data already forces `diag a` to commute with the symmetric matrix
    -- `C`, so we first diagonalize that commuting symmetric pair without ordering constraints.
    rw [hCdiag, Matrix.IsSymm]
    calc
      ((((UM * Matrix.diagonal c) * UMᵀ) : Matrix (Fin N) (Fin N) ℝ)ᵀ)
          = UM * (Matrix.diagonal c)ᵀ * UMᵀ := by
              simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (UM * Matrix.diagonal c) * UMᵀ := by
            simp [Matrix.mul_assoc]
  rcases commonOrthogonalDiagonalizationOfCommutingSymm
      (a := a) (C := C) hCsymm hdiagAcommC with
    ⟨Q0, c0, hQ0A, hQ0C⟩
  have hsorted_c0 : nonincreasingRearrangement c0 = c :=
    nonincreasingRearrangement_eq_orderedDiagonal_of_commonDiagonalizations
      (c := c) (c0 := c0) (C := C) (U := U) (Q := Q0) hc hCdiag hQ0C
  have hdot_c0 :
      dotProduct a c0 = dotProduct a c := by
    have htrace_c0 : Matrix.trace (Matrix.diagonal a * C) = dotProduct a c0 := by
      -- Route correction: once `Q0` preserves `diag a`, the remaining equality-case work is a
      -- finite vector identity for the unsorted diagonal `c0`, not another blockwise witness.
      have htraceRewriteA :
          Matrix.trace (Matrix.diagonal a * C) =
            Matrix.trace
              (((((Q0 : Matrix _ _ ℝ) * Matrix.diagonal a) * (Q0 : Matrix _ _ ℝ)ᵀ) * C) :
                Matrix (Fin N) (Fin N) ℝ) := by
        simpa [Matrix.mul_assoc] using
          congrArg (fun X : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (X * C)) hQ0A.symm
      calc
        Matrix.trace (Matrix.diagonal a * C)
            = Matrix.trace
                (((((Q0 : Matrix _ _ ℝ) * Matrix.diagonal a) * (Q0 : Matrix _ _ ℝ)ᵀ) * C) :
                  Matrix (Fin N) (Fin N) ℝ) := htraceRewriteA
        _ = Matrix.trace
                (((((Q0 : Matrix _ _ ℝ) * Matrix.diagonal a) * (Q0 : Matrix _ _ ℝ)ᵀ) *
                    (((Q0 : Matrix _ _ ℝ) * Matrix.diagonal c0) *
                      (Q0 : Matrix _ _ ℝ)ᵀ)) :
                  Matrix (Fin N) (Fin N) ℝ) := by
                    rw [hQ0C]
        _ = dotProduct a c0 := trace_orthogonal_conj_diagonal_mul_eq_dotProduct Q0 a c0
    calc
      dotProduct a c0 = Matrix.trace (Matrix.diagonal a * C) := htrace_c0.symm
      _ = dotProduct a c := htrace_diag
  have hEq_hlp :
      dotProduct a c0 =
        dotProduct (nonincreasingRearrangement a) (nonincreasingRearrangement c0) := by
    -- Rewrite the HLP equality surface using the already ordered `a` and the sorted version of
    -- the unsorted diagonal `c0`.
    simpa [nonincreasingRearrangement_eq_self_of_antitone ha, hsorted_c0] using hdot_c0
  rcases (hardy_littlewood_polya_inequality_eq_iff (x := a) (y := c0)).mp hEq_hlp with
    ⟨σ, hσa0, hσc0⟩
  have hσa : a = a ∘ σ := by
    simpa [nonincreasingRearrangement_eq_self_of_antitone ha] using hσa0
  have hσc : c = c0 ∘ σ := by
    simpa [hsorted_c0] using hσc0
  have hσinv_a : a ∘ σ.symm = a := by
    funext i
    -- Evaluating the common-sorting identity at `σ⁻¹ i` gives the inverse preservation law.
    simpa [Function.comp] using congrArg (fun f : Fin N → ℝ ↦ f (σ.symm i)) hσa
  have hσinv_c : c ∘ σ.symm = c0 := by
    funext i
    -- The same inverse evaluation turns the ordered diagonal `c` back into the unsorted `c0`.
    simpa [Function.comp] using congrArg (fun f : Fin N → ℝ ↦ f (σ.symm i)) hσc
  let σsymm : Equiv.Perm (Fin N) := σ.symm
  let P : Matrix.orthogonalGroup (Fin N) ℝ :=
    ⟨σsymm.permMatrix ℝ, permMatrix_mem_orthogonalGroup_fin σsymm⟩
  refine ⟨Q0 * P, ?_, ?_⟩
  · have hPdiagA :
        (((P : Matrix _ _ ℝ) * Matrix.diagonal a) * (P : Matrix _ _ ℝ)ᵀ) =
          Matrix.diagonal a := by
      -- The correction permutation moves indices only inside equal-`a` plateaus.
      have hperm :
          ((σsymm.permMatrix ℝ) * Matrix.diagonal a) * (σsymm.permMatrix ℝ)ᵀ =
            Matrix.diagonal a := by
        rw [permMatrix_diagonal_mul_transpose_eq_diagonal_comp]
        simpa [σsymm] using congrArg Matrix.diagonal hσinv_a
      simpa [P, σsymm] using hperm
    -- Absorb the plateau-preserving permutation into `Q0` without changing the `diag a` factor.
    calc
      ((((Q0 * P : Matrix.orthogonalGroup (Fin N) ℝ) : Matrix _ _ ℝ) * Matrix.diagonal a) *
          (((Q0 * P : Matrix.orthogonalGroup (Fin N) ℝ) : Matrix _ _ ℝ)ᵀ))
          = (((Q0 : Matrix _ _ ℝ) *
              ((((P : Matrix _ _ ℝ) * Matrix.diagonal a) * (P : Matrix _ _ ℝ)ᵀ))) *
              (Q0 : Matrix _ _ ℝ)ᵀ) := by
                simp [P, Matrix.mul_assoc, Matrix.transpose_mul]
      _ = (((Q0 : Matrix _ _ ℝ) * Matrix.diagonal a) * (Q0 : Matrix _ _ ℝ)ᵀ) := by
            rw [hPdiagA]
      _ = Matrix.diagonal a := hQ0A
  · have hPdiagC :
        (((P : Matrix _ _ ℝ) * Matrix.diagonal c) * (P : Matrix _ _ ℝ)ᵀ) =
          Matrix.diagonal c0 := by
      -- The inverse permutation matrix transports the ordered diagonal `c` back to `c0`.
      have hperm :
          ((σsymm.permMatrix ℝ) * Matrix.diagonal c) * (σsymm.permMatrix ℝ)ᵀ =
            Matrix.diagonal c0 := by
        rw [permMatrix_diagonal_mul_transpose_eq_diagonal_comp]
        simpa [σsymm] using congrArg Matrix.diagonal hσinv_c
      simpa [P, σsymm] using hperm
    -- The final assembly is now a single permutation-matrix correction of the unsorted basis `Q0`.
    calc
      C = (((Q0 : Matrix _ _ ℝ) * Matrix.diagonal c0) * (Q0 : Matrix _ _ ℝ)ᵀ) := hQ0C
      _ = (((Q0 : Matrix _ _ ℝ) *
            ((((P : Matrix _ _ ℝ) * Matrix.diagonal c) * (P : Matrix _ _ ℝ)ᵀ))) *
            (Q0 : Matrix _ _ ℝ)ᵀ) := by
              rw [hPdiagC]
      _ =
          ((((Q0 * P : Matrix.orthogonalGroup (Fin N) ℝ) : Matrix _ _ ℝ) * Matrix.diagonal c) *
            (((Q0 * P : Matrix.orthogonalGroup (Fin N) ℝ) : Matrix _ _ ℝ)ᵀ)) := by
              simp [P, Matrix.mul_assoc, Matrix.transpose_mul]

/-- Helper for Fact 24.59: equality in Theobald's trace bound yields a common orthogonal
diagonalization after transporting the canonical `Fin` model back to the original index type. -/
private theorem common_orthogonal_diagonalization_of_trace_equality
    {n : Type u} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hEq : Matrix.trace (A * B) = dotProduct hA.eigenvalues hB.eigenvalues) :
    ∃ U : Matrix.orthogonalGroup n ℝ,
      A = (((U : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues) * (U : Matrix n n ℝ)ᵀ) ∧
      B = (((U : Matrix n n ℝ) * Matrix.diagonal hB.eigenvalues) * (U : Matrix n n ℝ)ᵀ) := by
  classical
  let N : ℕ := Fintype.card n
  let e : n ≃ Fin N := Fintype.equivFin n
  let Afin : Matrix (Fin N) (Fin N) ℝ := Matrix.reindex e e A
  let Bfin : Matrix (Fin N) (Fin N) ℝ := Matrix.reindex e e B
  let hAfin : Afin.IsHermitian := hA.reindex e
  let hBfin : Bfin.IsHermitian := hB.reindex e
  let a : Fin N → ℝ := fun i ↦ hAfin.eigenvalues₀ (Fin.cast (by simp [N]) i)
  let b : Fin N → ℝ := fun i ↦ hBfin.eigenvalues₀ (Fin.cast (by simp [N]) i)
  have ha : Antitone a := by
    -- The ordered `Fin` spectral owner is antitone by construction.
    intro i j hij
    simpa [a] using hAfin.eigenvalues₀_antitone (by simpa [N] using hij)
  have hb : Antitone b := by
    -- The same ordered-spectrum monotonicity holds for `Bfin`.
    intro i j hij
    simpa [b] using hBfin.eigenvalues₀_antitone (by simpa [N] using hij)
  have htrace_reindex :
      Matrix.trace (A * B) = Matrix.trace (Afin * Bfin) := by
    -- Reindex the source equality to the canonical `Fin` model where the local spectral API
    -- already lives.
    calc
      Matrix.trace (A * B) = Matrix.trace (Matrix.reindex e e (A * B)) := by
        rw [trace_reindex_eq e (A * B)]
      _ = Matrix.trace (Afin * Bfin) := by
        simp [Afin, Bfin]
  have hA0 : a = hA.eigenvalues₀ := by
    -- The ordered spectrum of `A` agrees with that of its canonical `Fin` reindex.
    apply List.ofFn_inj.mp
    simpa [a, e, Afin, hAfin, N] using
      (reindexFin_eigenvalues₀_eq (ι := n) (H := A) (hH := hA))
  have hB0 : b = hB.eigenvalues₀ := by
    -- The same transport identifies the ordered spectrum of `B`.
    apply List.ofFn_inj.mp
    simpa [b, e, Bfin, hBfin, N] using
      (reindexFin_eigenvalues₀_eq (ι := n) (H := B) (hH := hB))
  have hdot_ab :
      dotProduct a b = dotProduct hA.eigenvalues hB.eigenvalues := by
    -- Rewrite the target dot product through the canonical ordered spectra on both sides.
    calc
      dotProduct a b = dotProduct hA.eigenvalues₀ hB.eigenvalues₀ := by
        rw [hA0, hB0]
      _ = dotProduct hA.eigenvalues hB.eigenvalues := by
        symm
        exact dotProduct_eigenvalues_eq_dotProduct_eigenvalues₀ hA hB
  rcases ordered_spectral_theorem_fin hAfin with ⟨UA0, hAfin_diag⟩
  let Cfin : Matrix (Fin N) (Fin N) ℝ :=
    (UA0 : Matrix _ _ ℝ)ᵀ * Bfin * (UA0 : Matrix _ _ ℝ)
  have hCfin : Cfin.IsHermitian := by
    -- Orthogonal conjugation preserves Hermitianity of the `Bfin` core.
    simpa [Cfin, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using
      (Matrix.isHermitian_conjTranspose_mul_mul
        (A := Bfin) (B := (UA0 : Matrix (Fin N) (Fin N) ℝ)) hBfin)
  let c : Fin N → ℝ := fun i ↦ hCfin.eigenvalues₀ (Fin.cast (by simp [N]) i)
  have hc : Antitone c := by
    -- The conjugated `Bfin` core still carries its canonical ordered spectrum.
    intro i j hij
    simpa [c] using hCfin.eigenvalues₀_antitone (by simpa [N] using hij)
  rcases ordered_spectral_theorem_fin hCfin with ⟨U, hCdiag⟩
  have hcb : c = b := by
    -- Orthogonal conjugation does not change the ordered eigenvalue list of `Bfin`.
    apply List.ofFn_inj.mp
    simpa [b, c, Cfin, N] using
      (ordered_conjugate_eigenvalues₀_eq hBfin hCfin UA0 rfl)
  have htrace_A_basis :
      Matrix.trace (Afin * Bfin) = Matrix.trace (Matrix.diagonal a * Cfin) := by
    -- Move the trace pairing into the ordered eigenbasis of `Afin`.
    simpa [Cfin] using
      (trace_mul_eq_trace_diagonal_mul_in_orthogonal_basis
        (U := UA0) (A := Afin) (B := Bfin) (a := a) hAfin_diag)
  have hEq_fin :
      Matrix.trace (Matrix.diagonal a * Cfin) = dotProduct a c := by
    -- This is exactly the equality case transported to the ordered `Fin` model.
    calc
      Matrix.trace (Matrix.diagonal a * Cfin) = Matrix.trace (Afin * Bfin) := htrace_A_basis.symm
      _ = Matrix.trace (A * B) := htrace_reindex.symm
      _ = dotProduct hA.eigenvalues hB.eigenvalues := hEq
      _ = dotProduct a b := hdot_ab.symm
      _ = dotProduct a c := by rw [← hcb]
  let M : Matrix (Fin N) (Fin N) ℝ := fun i j ↦ (((U : Matrix _ _ ℝ) i j) ^ 2)
  have hMmem :
      M ∈ doublyStochastic ℝ (Fin N) := by
    -- The squared-entry overlap matrix of an orthogonal matrix is doubly stochastic.
    exact
      sq_entry_matrix_mem_doublyStochastic
        (orthogonal_mul_transpose_eq_one U.prop)
        (orthogonal_transpose_mul_eq_one U.prop)
  rcases exists_eq_sum_perm_of_mem_doublyStochastic hMmem with ⟨w, hw_nonneg, hw_sum, hwM⟩
  have hmono : Monovary a c := ha.monovary hc
  have hterm_bound :
      ∀ σ : Equiv.Perm (Fin N), dotProduct a (c ∘ σ) ≤ dotProduct a c := by
    intro σ
    -- Every permutation term is bounded by the same rearrangement inequality.
    simpa [dotProduct] using hmono.sum_mul_comp_perm_le_sum_mul (σ := σ)
  have hconv_eq :
      ∑ σ, w σ * dotProduct a (c ∘ σ) = dotProduct a c := by
    have htrace_overlap :
        Matrix.trace (Matrix.diagonal a * Cfin) = dotProduct a (M *ᵥ c) := by
      -- With the first basis fixed to the standard one, the trace depends only on the squared
      -- entries of the orthogonal diagonalizer of `Cfin`.
      rw [hCdiag]
      simpa [M, Matrix.mul_assoc] using
        (trace_orthogonal_conj_diagonal_mul_eq_dotProduct_sq_entry_mulVec_fin
          (U := (1 : Matrix.orthogonalGroup (Fin N) ℝ)) (V := U) a c)
    calc
      ∑ σ, w σ * dotProduct a (c ∘ σ)
          = dotProduct a ((((∑ σ, w σ • σ.permMatrix ℝ) : Matrix _ _ ℝ)) *ᵥ c) := by
              symm
              exact
                dotProduct_birkhoff_sum_permMatrix_mulVec_eq_sum_mul_dotProduct_comp_perm_fin
                  a c w
      _ = dotProduct a (M *ᵥ c) := by
            rw [← hwM]
      _ = Matrix.trace (Matrix.diagonal a * Cfin) := htrace_overlap.symm
      _ = dotProduct a c := hEq_fin
  have hsupport_correction :
      ∀ σ : Equiv.Perm (Fin N), w σ ≠ 0 →
        ∃ ρ : Equiv.Perm (Fin N), a ∘ ρ = a ∧ c ∘ σ ∘ ρ = c := by
    intro σ hwσ
    have hσeq :
        dotProduct a (c ∘ σ) = dotProduct a c :=
      positive_weight_term_eq_of_convex_bound_equality
        hterm_bound hw_nonneg hw_sum hconv_eq σ hwσ
    -- Equality in the rearrangement term yields a correction permutation respecting the
    -- strict-drop decomposition of `a`.
    exact equality_term_has_prefix_preserving_correction ha hc σ hσeq
  have hstrict_trace :
      ∀ {r : Fin N} (hrN : r.1 + 1 < N) (hr : a r > a ⟨r.1 + 1, hrN⟩),
        Matrix.trace (prefixProj r * Cfin) = ∑ i, if i ≤ r then c i else 0 := by
    intro r hrN hr
    -- Every strict-drop prefix already attains equality against the conjugated `Bfin` core.
    exact
      strict_drop_prefix_trace_eq_of_hsupport_correction
        ha (C := Cfin) (U := U) hCdiag w hw_sum hwM.symm hsupport_correction hrN hr
  have hstrict_side :
      ∀ {r : Fin N} (hrN : r.1 + 1 < N) (hr : a r > a ⟨r.1 + 1, hrN⟩),
        let Pr : Matrix (Fin N) (Fin N) ℝ :=
          (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
        (∀ i, c i > c r →
          (∀ j, Pr i j = if i = j then 1 else 0) ∧
            ∀ j, Pr j i = if j = i then 1 else 0) ∧
          ∀ i, c i < c r →
            (∀ j, Pr i j = 0) ∧ ∀ j, Pr j i = 0 := by
    intro r hrN hr
    let Pr : Matrix (Fin N) (Fin N) ℝ :=
      (((U : Matrix _ _ ℝ)ᵀ * prefixProj r) * (U : Matrix _ _ ℝ))
    have hchain :=
      conjugated_prefix_projection_chain (U := U) (r := r) (s := r) le_rfl
    rcases hchain with ⟨hPsymm, hPidem, htraceP, -, -⟩
    have htracePD :
        Matrix.trace (Pr * Matrix.diagonal c) = ∑ i, if i ≤ r then c i else 0 := by
      -- Rewrite the strict-drop trace equality in the already diagonal `c`-basis.
      simpa [Pr] using
        trace_conjugated_prefixProj_mul_diagonal_eq_of_trace_prefixProj
          (U := U) (c := c) hCdiag (hstrict_trace hrN hr)
    -- The centered-cutoff argument upgrades the trace equalities to actual basis action.
    exact strict_side_basis_action_of_centered_cutoff hc hPsymm hPidem htraceP htracePD
  rcases common_orthogonal_refinement_of_ordered_c_eigenbasis
    (a := a) (c := c) (C := Cfin) (U := U) ha hc hCdiag hEq_fin hstrict_side with
    ⟨Qfin, hQfinA, hQfinC⟩
  have hQfinB :
      let Cfin' : Matrix (Fin N) (Fin N) ℝ :=
        (UA0 : Matrix _ _ ℝ)ᵀ * Bfin * (UA0 : Matrix _ _ ℝ)
      Cfin' = (((Qfin : Matrix _ _ ℝ) * Matrix.diagonal b) * (Qfin : Matrix _ _ ℝ)ᵀ) := by
    -- Replace the ordered spectrum of `Cfin` by that of `Bfin`, which is the same list.
    simpa [Cfin, hcb] using hQfinC
  rcases common_orthogonal_diagonalization_from_ordered_fin_basis
    (Afin := Afin) (Bfin := Bfin) (a := a) (b := b) (UA0 := UA0) (Qfin := Qfin)
    hAfin_diag hQfinA hQfinB with ⟨Ufin, hpair_fin⟩
  have hpair_fin0 :
      (Afin, Bfin) =
        ((((Ufin : Matrix _ _ ℝ) * Matrix.diagonal hA.eigenvalues₀) *
            (Ufin : Matrix _ _ ℝ)ᵀ),
         (((Ufin : Matrix _ _ ℝ) * Matrix.diagonal hB.eigenvalues₀) *
            (Ufin : Matrix _ _ ℝ)ᵀ)) := by
    -- Finally rewrite the ordered `Fin` diagonals back to the canonical owners for `A` and `B`.
    simpa [hA0, hB0] using hpair_fin
  rcases reindex_common_orthogonal_diagonalization_fin hA hB e hpair_fin0 with ⟨U, hpair⟩
  refine ⟨U, ?_, ?_⟩
  · exact congrArg Prod.fst hpair
  · exact congrArg Prod.snd hpair

/-- Fact 24.59 (Theobald) (See [344]): equality in the trace/eigenvalue inequality holds iff
one orthogonal matrix diagonalizes both `A` and `B` with those canonical eigenvalue lists. -/
theorem theobald_trace_eq_eigenvalues_dotProduct_iff
    {n : Type u} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Matrix.trace (A * B) = dotProduct hA.eigenvalues hB.eigenvalues ↔
      ∃ U : Matrix.orthogonalGroup n ℝ,
        A = (((U : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues) * (U : Matrix n n ℝ)ᵀ) ∧
        B = (((U : Matrix n n ℝ) * Matrix.diagonal hB.eigenvalues) * (U : Matrix n n ℝ)ᵀ) := by
  constructor
  · intro hEq
    rcases common_orthogonal_diagonalization_of_trace_equality hA hB hEq with ⟨U, hAU, hBU⟩
    refine ⟨U, ?_, ?_⟩
    · exact hAU
    · exact hBU
  · rintro ⟨U, hAdiag, hBdiag⟩
    -- Once `A` and `B` share an orthogonal eigenbasis, the trace pairing is exactly the diagonal
    -- dot product in that basis.
    calc
      Matrix.trace (A * B)
          = Matrix.trace
              (((((U : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues) *
                    (U : Matrix n n ℝ)ᵀ) *
                  (((U : Matrix n n ℝ) * Matrix.diagonal hB.eigenvalues) *
                    (U : Matrix n n ℝ)ᵀ)) : Matrix n n ℝ) := by
                  simpa [hAdiag, hBdiag]
      _ = dotProduct hA.eigenvalues hB.eigenvalues :=
            trace_orthogonal_conj_diagonal_mul_eq_dotProduct
              U hA.eigenvalues hB.eigenvalues

end
