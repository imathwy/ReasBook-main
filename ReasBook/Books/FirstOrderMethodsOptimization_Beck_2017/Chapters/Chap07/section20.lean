import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_20 (from Chap07) -/
open Matrix WithLp
open scoped BigOperators Matrix Matrix.Norms.Frobenius

noncomputable section

section

variable {m n : ℕ}

/- Definition 7.20 is `source-facing`: it introduces the Schatten `p`-norm on real rectangular
matrices as the `ℓ^p` norm of the singular-value list. The `core/canonical` owner in mathlib is
the singular-value sequence `X.toEuclideanLin.singularValues`, and the finite-vector
`ℓ^p` structure is the canonical `WithLp p` norm on `Fin (min m n) → ℝ`. The special cases
`p = 1`, `p = 2`, and `p = ∞` are then recorded as atomic companion theorems. -/

/-- Definition 7.20: the Schatten `p`-norm of a real `m × n` matrix is the `ℓ^p` norm of its
finite singular-value vector. -/
noncomputable def matrix_schatten_norm (p : ENNReal) [Fact (1 ≤ p)]
    (X : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ‖toLp p (fun i : Fin (min m n) ↦ X.toEuclideanLin.singularValues i)‖

notation "S_[" p "]" => matrix_schatten_norm p

-- Proof sketch: unfold `matrix_schatten_norm`; it is defined exactly as the `WithLp p` norm of
-- the finite singular-value vector obtained by restricting `X.toEuclideanLin.singularValues` to
-- `Fin (min m n)`.
/-- The defining formula for the matrix Schatten `p`-norm is the `WithLp p` norm of the singular
value vector. -/
@[simp] theorem matrix_schatten_norm_def (p : ENNReal) [Fact (1 ≤ p)]
    (X : Matrix (Fin m) (Fin n) ℝ) :
    matrix_schatten_norm p X =
      ‖toLp p (fun i : Fin (min m n) ↦ X.toEuclideanLin.singularValues i)‖ := by
  -- This is exactly the definition introduced for the source-facing wrapper.
  rfl

-- Proof sketch: rewrite by `matrix_schatten_norm_def`; the right-hand side is a norm in the
-- finite-dimensional `WithLp p` space, hence is nonnegative.
/-- The matrix Schatten `p`-norm is nonnegative. -/
theorem matrix_schatten_norm_nonneg (p : ENNReal) [Fact (1 ≤ p)]
    (X : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ matrix_schatten_norm p X := by
  -- Rewrite to the ambient `WithLp` norm and use norm nonnegativity.
  rw [matrix_schatten_norm_def]
  exact norm_nonneg _

-- Proof sketch: specialize the defining `ℓ^p` formula to `p = 1` and apply
-- `PiLp.norm_eq_of_L1`; since singular values are nonnegative, this is the trace norm formula.
/-- The Schatten `1`-norm of a real matrix is the sum of its finite singular values. -/
theorem matrix_schatten_one_norm_eq_sum_singular_values
    (X : Matrix (Fin m) (Fin n) ℝ) :
    S_[(1 : ENNReal)] X =
      ∑ i : Fin (min m n), X.toEuclideanLin.singularValues i := by
  -- Specialize the defining `ℓ¹` formula and remove absolute values using singular-value
  -- nonnegativity.
  rw [matrix_schatten_norm_def, PiLp.norm_eq_of_L1]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Real.norm_eq_abs, abs_of_nonneg]
  exact X.toEuclideanLin.singularValues_nonneg i

/-- Helper for Definition 7.20: the `ℓ^∞` norm of a finite nonnegative antitone real vector is its
first coordinate. -/
lemma linfty_norm_eq_first_of_antitone_nonneg {k : ℕ} (hk : 0 < k) {f : Fin k → ℝ}
    (hf_mono : Antitone f) (hf_nonneg : ∀ i, 0 ≤ f i) :
    ‖toLp (⊤ : ENNReal) f‖ = f ⟨0, hk⟩ := by
  let i0 : Fin k := ⟨0, hk⟩
  -- Rewrite the `WithLp ∞` norm as the sup norm on the finite coordinate family.
  rw [PiLp.norm_toLp, Pi.norm_def]
  have hsup : Finset.univ.sup (fun i : Fin k ↦ ‖f i‖₊) = ‖f i0‖₊ := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i hi
      -- Antitonicity shows every coordinate is bounded above by the first one.
      have hle : f i ≤ f i0 := hf_mono (show i0 ≤ i by exact Nat.zero_le i)
      rw [Real.nnnorm_of_nonneg (hf_nonneg i), Real.nnnorm_of_nonneg (hf_nonneg i0)]
      exact hle
    · -- The first coordinate itself appears in the finite supremum.
      simpa using
        (Finset.le_sup (s := Finset.univ) (f := fun i : Fin k ↦ ‖f i‖₊)
          (Finset.mem_univ i0) : ‖f i0‖₊ ≤ Finset.univ.sup (fun i : Fin k ↦ ‖f i‖₊))
  rw [hsup, Real.nnnorm_of_nonneg (hf_nonneg i0)]
  simp [i0]

-- Proof sketch: specialize the defining `ℓ^p` formula to `p = ⊤`, identify the resulting
-- `WithLp ∞` norm with the coordinate supremum, and use the antitone ordering of singular values
-- to see that the supremum is the first singular value.
/-- The Schatten `∞`-norm of a real matrix is its largest singular value. -/
theorem matrix_schatten_top_norm_eq_first_singular_value
    (X : Matrix (Fin m) (Fin n) ℝ) :
    S_[⊤] X = X.toEuclideanLin.singularValues 0 := by
  by_cases hk : 0 < min m n
  · -- In the nonempty case, the ordered singular-value vector is antitone and nonnegative, so its
    -- `ℓ^∞` norm is its first coordinate.
    rw [matrix_schatten_norm_def]
    simpa using linfty_norm_eq_first_of_antitone_nonneg hk
      (fun i j hij ↦
        X.toEuclideanLin.singularValues_antitone (show (i : ℕ) ≤ j from hij))
      (fun i ↦ X.toEuclideanLin.singularValues_nonneg i)
  · -- If `min m n = 0`, then one side of the matrix is empty, so the matrix and all its singular
    -- values vanish.
    have hmin : min m n = 0 := Nat.eq_zero_of_not_pos hk
    have hm_or_hn : m = 0 ∨ n = 0 := by
      omega
    rcases hm_or_hn with hm | hn
    · subst hm
      have hX : X = 0 := Subsingleton.elim _ _
      have hfun : (fun i : Fin (min 0 n) ↦ X.toEuclideanLin.singularValues i) = 0 := by
        ext i
        exact Fin.elim0 i
      have htoLp :
          toLp (⊤ : ENNReal) (fun i : Fin (min 0 n) ↦ X.toEuclideanLin.singularValues i) = 0 := by
        rw [WithLp.toLp_eq_zero]
        exact hfun
      have hσ : X.toEuclideanLin.singularValues 0 = 0 := by
        simp [hX]
      rw [matrix_schatten_norm_def, htoLp, hσ]
      simp
    · subst hn
      have hX : X = 0 := Subsingleton.elim _ _
      have hfun : (fun i : Fin (min m 0) ↦ X.toEuclideanLin.singularValues i) = 0 := by
        rw [Nat.min_eq_right (Nat.zero_le m)]
        ext i
        exact Fin.elim0 i
      have htoLp :
          toLp (⊤ : ENNReal) (fun i : Fin (min m 0) ↦ X.toEuclideanLin.singularValues i) = 0 := by
        rw [WithLp.toLp_eq_zero]
        exact hfun
      have hσ : X.toEuclideanLin.singularValues 0 = 0 := by
        simp [hX]
      rw [matrix_schatten_norm_def, htoLp, hσ]
      simp

-- Proof sketch: combine the previous theorem with the operator-norm/singular-value identity for
-- real matrices from Proposition 1.2.
section L2Operator

open scoped Matrix.Norms.L2Operator

/-- Helper for Definition 7.20: on a positive real finite-dimensional endomorphism, the operator
norm is the largest eigenvalue. -/
lemma positive_operator_norm_eq_top_eigenvalue
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {S : E →ₗ[ℝ] E} {k : ℕ} (hn : Module.finrank ℝ E = k) (hk : 0 < k)
    (hS : S.IsPositive) :
    ‖S.toContinuousLinearMap‖ = hS.isSymmetric.eigenvalues hn ⟨0, hk⟩ := by
  have hS_nonneg : ∀ x : E, 0 ≤ S.toContinuousLinearMap.rayleighQuotient x := by
    intro x
    by_cases hx : x = 0
    · simp [ContinuousLinearMap.rayleighQuotient, hx]
    · rw [ContinuousLinearMap.rayleighQuotient]
      exact div_nonneg (hS.inner_nonneg_left x) (sq_nonneg ‖x‖)
  have hbdd_all :
      BddAbove (Set.range fun x : E ↦ S.toContinuousLinearMap.rayleighQuotient x) := by
    refine ⟨‖S.toContinuousLinearMap‖, ?_⟩
    rintro y ⟨x, rfl⟩
    exact le_trans
      (by
        simpa [abs_of_nonneg (hS_nonneg x)] using
          S.toContinuousLinearMap.rayleighQuotient_le_norm x)
      le_rfl
  have hbdd_nonzero :
      BddAbove
        (Set.range fun x : {x : E // x ≠ 0} ↦ S.toContinuousLinearMap.rayleighQuotient x) :=
    hbdd_all.mono <| by
      rintro y ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (hn ▸ hk)
  haveI : Nonempty {x : E // x ≠ 0} := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact ⟨⟨x, hx⟩⟩
  have hiSup_nonzero_nonneg :
      0 ≤ ⨆ x : {x : E // x ≠ 0}, S.toContinuousLinearMap.rayleighQuotient x := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact le_trans (hS_nonneg x) (le_ciSup hbdd_nonzero ⟨x, hx⟩)
  have hsup_eq : (⨆ x : E, S.toContinuousLinearMap.rayleighQuotient x) =
      ⨆ x : {x : E // x ≠ 0}, S.toContinuousLinearMap.rayleighQuotient x := by
    apply le_antisymm
    · refine ciSup_le ?_
      intro x
      by_cases hx : x = 0
      · rw [hx, ContinuousLinearMap.rayleighQuotient_apply_zero]
        exact hiSup_nonzero_nonneg
      · exact le_ciSup hbdd_nonzero ⟨x, hx⟩
    · refine ciSup_le ?_
      intro x
      exact le_ciSup hbdd_all x.1
  have hnorm_eq_sup :
      ‖S.toContinuousLinearMap‖ = ⨆ x : E, S.toContinuousLinearMap.rayleighQuotient x := by
    -- Positivity removes the absolute value from the Rayleigh-quotient formula for the norm.
    rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hS.isSymmetric]
    congr with x
    exact abs_of_nonneg (hS_nonneg x)
  have hM_eig :
      Module.End.HasEigenvalue S
        (⨆ x : {x : E // x ≠ 0}, S.toContinuousLinearMap.rayleighQuotient x) := by
    -- The source-faithful step is that the maximal Rayleigh quotient is itself an eigenvalue.
    simpa [ContinuousLinearMap.rayleighQuotient] using
      (LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional (T := S) hS.isSymmetric)
  obtain ⟨j, hj⟩ := hS.isSymmetric.exists_eigenvalues_eq hn hM_eig
  rw [hnorm_eq_sup, hsup_eq]
  apply le_antisymm
  · -- Any eigenvalue is bounded above by the first entry of the decreasing eigenvalue list.
    rw [← hj]
    exact (hS.isSymmetric.eigenvalues_antitone hn)
      (show (⟨0, hk⟩ : Fin k) ≤ j by exact Nat.zero_le _)
  · let i0 : Fin k := ⟨0, hk⟩
    have hi0_ne : hS.isSymmetric.eigenvectorBasis hn i0 ≠ 0 := by
      intro hzero
      have hnorm : ‖hS.isSymmetric.eigenvectorBasis hn i0‖ = 1 :=
        OrthonormalBasis.norm_eq_one _ _
      simp [hzero] at hnorm
    have hray :
        S.toContinuousLinearMap.rayleighQuotient (hS.isSymmetric.eigenvectorBasis hn i0) =
          hS.isSymmetric.eigenvalues hn i0 := by
      -- Evaluate the Rayleigh quotient on a unit eigenvector for the top eigenvalue.
      rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
      change
        RCLike.re
            (inner ℝ (S (hS.isSymmetric.eigenvectorBasis hn i0))
              (hS.isSymmetric.eigenvectorBasis hn i0)) /
          ‖hS.isSymmetric.eigenvectorBasis hn i0‖ ^ 2 = hS.isSymmetric.eigenvalues hn i0
      rw [hS.isSymmetric.apply_eigenvectorBasis hn i0, inner_smul_left,
        OrthonormalBasis.norm_eq_one]
      simp
    rw [← hray]
    exact le_ciSup hbdd_nonzero ⟨hS.isSymmetric.eigenvectorBasis hn i0, hi0_ne⟩

/-- Helper for Definition 7.20: the operator norm of a real finite-dimensional linear map is its
first singular value. -/
lemma operator_norm_eq_first_singular_value
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E →ₗ[ℝ] F) :
    ‖T.toContinuousLinearMap‖ = T.singularValues 0 := by
  by_cases hk : 0 < Module.finrank ℝ E
  · let k : ℕ := Module.finrank ℝ E
    have hn : Module.finrank ℝ E = k := rfl
    have hgram :=
      positive_operator_norm_eq_top_eigenvalue hn hk
        (LinearMap.isPositive_adjoint_comp_self T)
    have hnorm_sq : ‖T.toContinuousLinearMap‖ ^ 2 =
        (LinearMap.isPositive_adjoint_comp_self T).isSymmetric.eigenvalues hn ⟨0, hk⟩ := by
      -- Compare `‖T‖²` with the top eigenvalue of the Gram operator `T†T`.
      calc
        ‖T.toContinuousLinearMap‖ ^ 2 = ‖(LinearMap.adjoint T ∘ₗ T).toContinuousLinearMap‖ := by
          simpa [pow_two] using
            (ContinuousLinearMap.norm_adjoint_comp_self T.toContinuousLinearMap).symm
        _ = (LinearMap.isPositive_adjoint_comp_self T).isSymmetric.eigenvalues hn ⟨0, hk⟩ := hgram
    have hsq : ‖T.toContinuousLinearMap‖ ^ 2 = T.singularValues 0 ^ 2 := by
      -- The Gram eigenvalues are exactly the squared singular values.
      exact hnorm_sq.trans (LinearMap.sq_singularValues_fin T hn ⟨0, hk⟩).symm
    have hnorm_nonneg : 0 ≤ ‖T.toContinuousLinearMap‖ := norm_nonneg _
    have hσ_nonneg : 0 ≤ T.singularValues 0 := T.singularValues_nonneg 0
    -- Both quantities are nonnegative, so equality of squares implies equality.
    exact le_antisymm
      (by nlinarith [hsq])
      (by nlinarith [hsq])
  · have hfinrank : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hk
    have hzero : ∀ x : E, x = 0 := finrank_zero_iff_forall_zero.mp hfinrank
    have hT : T = 0 := by
      -- In zero domain dimension the map itself is zero.
      ext x
      simp [hzero x]
    rw [hT]
    simp

/-- Helper for Definition 7.20: the Euclidean induced matrix norm is the largest singular value. -/
theorem l2_induced_matrix_norm_eq_max_singular_value
    (X : Matrix (Fin m) (Fin n) ℝ) :
    ‖X‖ = X.toEuclideanLin.singularValues 0 := by
  -- Rewrite the matrix norm through `toEuclideanLin` and apply the linear-map bridge.
  simpa [Matrix.l2_opNorm_def] using operator_norm_eq_first_singular_value X.toEuclideanLin

/-- The Schatten `∞`-norm of a real matrix equals the Euclidean induced matrix operator norm. -/
theorem matrix_schatten_top_norm_eq_l2_induced_matrix_norm
    (X : Matrix (Fin m) (Fin n) ℝ) :
    S_[⊤] X = ‖X‖ := by
  -- Route correction: avoid the unavailable chapter import and prove the operator-norm bridge
  -- locally from the Gram operator and singular-value API.
  calc
    S_[⊤] X = X.toEuclideanLin.singularValues 0 := by
      exact matrix_schatten_top_norm_eq_first_singular_value X
    _ = ‖X‖ := by
      exact (l2_induced_matrix_norm_eq_max_singular_value X).symm

end L2Operator

-- Proof sketch: specialize the defining `ℓ^p` formula to `p = 2` and apply `PiLp.norm_eq_of_L2`
-- to obtain the square-root-of-sum-of-squares expression.
/-- The Schatten `2`-norm of a real matrix is the Euclidean norm of its singular-value vector. -/
theorem matrix_schatten_two_norm_eq_sqrt_sum_sq_singular_values
    (X : Matrix (Fin m) (Fin n) ℝ) :
    S_[(2 : ENNReal)] X =
      Real.sqrt (∑ i : Fin (min m n), X.toEuclideanLin.singularValues i ^ (2 : ℕ)) := by
  -- Specialize the defining `ℓ²` formula for the singular-value vector.
  simp [matrix_schatten_norm_def, PiLp.norm_eq_of_L2]

/-- Helper for Definition 7.20: the trace of the Gram matrix `Xᵀ X` is the sum of the squares of
the singular values of `X`, truncated at `min m n`. -/
lemma sum_sq_singular_values_eq_trace_transpose_mul
    (X : Matrix (Fin m) (Fin n) ℝ) :
    (∑ i : Fin (min m n), X.toEuclideanLin.singularValues i ^ (2 : ℕ)) =
      Matrix.trace (Xᵀ * X) := by
  have htrace_n :
      Matrix.trace (Xᵀ * X) = ∑ i : Fin n, X.toEuclideanLin.singularValues i ^ (2 : ℕ) := by
    let G : Matrix (Fin n) (Fin n) ℝ := Xᵀ * X
    have hcomp :
        LinearMap.adjoint (Matrix.toEuclideanLin X) ∘ₗ Matrix.toEuclideanLin X =
          Matrix.toEuclideanLin G := by
      -- Identify the matrix Gram operator with `T†T` for `T = X.toEuclideanLin`.
      rw [show LinearMap.adjoint (Matrix.toEuclideanLin X) = Matrix.toEuclideanLin Xᵀ by
        simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := X)).symm]
      ext v j
      simp [G, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
      simp
    calc
      Matrix.trace (Xᵀ * X) = G.trace := by
        simp [G]
      _ = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (Matrix.toEuclideanLin G) := by
        rw [LinearMap.trace_eq_matrix_trace ℝ ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)]
        simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]
      _ = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
            (LinearMap.adjoint (Matrix.toEuclideanLin X) ∘ₗ Matrix.toEuclideanLin X) := by
        rw [hcomp]
      _ = ∑ i : Fin n,
            ((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvalues hn i : ℝ) := by
        simpa using
          ((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self).trace_eq_sum_eigenvalues hn
      _ = ∑ i : Fin n, X.toEuclideanLin.singularValues i ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        -- Each Gram eigenvalue is the square of the corresponding singular value.
        simpa using (LinearMap.sq_singularValues_fin (T := X.toEuclideanLin) hn i).symm
  by_cases hmn : m ≤ n
  · let f : ℕ → ℝ := fun i ↦ X.toEuclideanLin.singularValues i ^ (2 : ℕ)
    have htrace_range : Matrix.trace (Xᵀ * X) = Finset.sum (Finset.range n) f := by
      exact htrace_n.trans (by simpa [f] using (Fin.sum_univ_eq_sum_range f n))
    have htail : Finset.sum (Finset.Ico m n) f = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : m ≤ i := (Finset.mem_Ico.mp hi).1
      have hfinrank : Module.finrank ℝ X.toEuclideanLin.range ≤ m := by
        simpa using (Submodule.finrank_le X.toEuclideanLin.range)
      have hzero : X.toEuclideanLin.singularValues i = 0 := by
        -- Past the codomain dimension, the singular values of a rectangular `m × n` matrix vanish.
        rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range]
        exact le_trans hfinrank hi'
      simp [hzero]
    -- When `m ≤ n`, split the full `n`-sum into the first `m` terms and the zero tail.
    rw [htrace_range, ← Finset.sum_range_add_sum_Ico f hmn, htail, add_zero]
    rw [Nat.min_eq_left hmn]
    simpa [f] using (Fin.sum_univ_eq_sum_range f m)
  · have hnm : n ≤ m := le_of_not_ge hmn
    -- When `n ≤ m`, the `min m n` truncation already includes every singular value coming from the
    -- domain dimension.
    rw [Nat.min_eq_right hnm]
    exact htrace_n.symm

-- Proof sketch: combine the previous theorem with the Frobenius-norm identity
-- `‖X‖ = √(Tr(Xᵀ X))` from Definition 1.33, using that the Frobenius norm is the Schatten
-- `2`-norm.
/-- The Schatten `2`-norm of a real matrix equals `√(Tr(Xᵀ X))`. -/
theorem matrix_schatten_two_norm_eq_sqrt_trace_transpose_mul
    (X : Matrix (Fin m) (Fin n) ℝ) :
    S_[(2 : ENNReal)] X =
      Real.sqrt (Matrix.trace (Xᵀ * X)) := by
  -- Rewrite the `ℓ²` formula using the Gram-trace identity for squared singular values.
  rw [matrix_schatten_two_norm_eq_sqrt_sum_sq_singular_values]
  rw [sum_sq_singular_values_eq_trace_transpose_mul]

end
