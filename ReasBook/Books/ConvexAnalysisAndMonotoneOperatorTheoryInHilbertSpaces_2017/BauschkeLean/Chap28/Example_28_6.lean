import BauschkeLean.Chap24.Example_24_69
import BauschkeLean.Chap28.Example_28_5

open Filter
open Matrix
open Set
open scoped BigOperators InnerProductSpace Topology

namespace ERealFunction

noncomputable section

/- Source/core/bridge triage:
- `source-facing`: Example 28.6 specifies the robust-PCA recursion `(28.28)` in the matrix
  coordinates `C`, `R`, `S`, `X1`, `X2`, `Y1`, and `Y2`.
- `core/canonical`: Example 28.5 already owns the finite-family Douglas--Rachford convergence
  theorem for a direct-sum objective under the coordinate-sum affine constraint.
- `bridge/view`: this file keeps the source matrix recursion and objective/constraint language, and
  packages the two matrix coordinates into the canonical product-space orbit needed to reuse
  Example 28.5.
-/

-- Semantic recall: `lean_leansearch` only surfaced generic matrix-norm facts for this item.
-- The verified local owners are Example 24.69 for the nuclear-norm proximal step and
-- Example 28.5 for the two-function linear-constraint Douglas--Rachford convergence template, so
-- the sparse penalty and the recursion `(28.28)` are kept explicit below.

section RobustPCA

variable {M N : ℕ}

local notation "ProductSpace" => lp (fun _ : Fin 2 ↦ RectangularMatrixSpace M N) 2

/-- The sparse penalty `S ↦ ‖S‖₁`, realized as the sum of the absolute values of the entries of a
real `M × N` matrix on the ambient Euclidean matrix space. -/
def matrixEntrywiseL1Penalty :
    RectangularMatrixSpace M N → Set.Ioi (⊥ : EReal) :=
  (fun S ↦ ∑ i : Fin M, ∑ j : Fin N, |euclideanToMatrix S i j|).toEReal

/-- The coordinatewise soft-thresholding map on real `M × N` matrices, viewed on the ambient
Euclidean matrix space. -/
def matrixEntrywiseSoftThreshold (γ : PosReal) :
    RectangularMatrixSpace M N → RectangularMatrixSpace M N :=
  fun Y ↦
    matrixToEuclidean
      (fun i j ↦
        Real.sign (euclideanToMatrix Y i j) *
          max (|euclideanToMatrix Y i j| - (γ : ℝ)) 0)

/-- The two-function family underlying robust PCA: the nuclear norm in coordinate `0` and the
entrywise `ℓ¹` penalty in coordinate `1`. -/
def robustPCAFunctionFamily :
    Fin 2 → RectangularMatrixSpace M N → Set.Ioi (⊥ : EReal) :=
  Fin.cases nuclearNormPenalty (fun _ : Fin 1 ↦ matrixEntrywiseL1Penalty)

/-- The robust PCA objective on pairs `(R, S)`, written as the direct sum of the nuclear norm and
the entrywise `ℓ¹` penalty. -/
def robustPCAObjective : ProductSpace → Set.Ioi (⊥ : EReal) :=
  directSumFunction robustPCAFunctionFamily

/-- The affine constraint set for the decomposition `A = R + S`. -/
def robustPCAConstraintSet (A : Matrix (Fin M) (Fin N) ℝ) :
    Set ProductSpace :=
  {z | z (0 : Fin 2) + z (1 : Fin 2) = matrixToEuclidean A}

/-- The two robust-PCA coordinates packaged as a point of the canonical product space from
Example 28.5. -/
abbrev robustPCAPoint
    (Z1 Z2 : RectangularMatrixSpace M N) : ProductSpace :=
  ⟨Fin.cases Z1 (fun _ : Fin 1 ↦ Z2), Memℓp.all _⟩

@[simp] theorem robustPCAPoint_apply_zero
    (Z1 Z2 : RectangularMatrixSpace M N) :
    robustPCAPoint Z1 Z2 (0 : Fin 2) = Z1 := rfl

@[simp] theorem robustPCAPoint_apply_one
    (Z1 Z2 : RectangularMatrixSpace M N) :
    robustPCAPoint Z1 Z2 (1 : Fin 2) = Z2 := rfl

/-- A pair of matrix-valued sequences packaged as the canonical product-space sequence used in
Example 28.5. -/
abbrev robustPCASequence
    (Z1 Z2 : ℕ → RectangularMatrixSpace M N) : ℕ → ProductSpace :=
  fun n ↦ robustPCAPoint (Z1 n) (Z2 n)

@[simp] theorem robustPCASequence_apply_zero
    (Z1 Z2 : ℕ → RectangularMatrixSpace M N) (n : ℕ) :
    robustPCASequence Z1 Z2 n (0 : Fin 2) = Z1 n := rfl

@[simp] theorem robustPCASequence_apply_one
    (Z1 Z2 : ℕ → RectangularMatrixSpace M N) (n : ℕ) :
    robustPCASequence Z1 Z2 n (1 : Fin 2) = Z2 n := rfl

/-- The affine correction attached to a pair of matrix sequences, written in the source form
`(A - Z₁,n - Z₂,n) / 2`. -/
abbrev robustPCAAffineCorrection
    (A : Matrix (Fin M) (Fin N) ℝ)
    (Z1 Z2 : ℕ → RectangularMatrixSpace M N) :
    ℕ → RectangularMatrixSpace M N :=
  fun n ↦ ((1 / 2 : ℝ) • (matrixToEuclidean A - Z1 n - Z2 n))

/-- The sparse entrywise `ℓ¹` penalty is the second `Γ₀` summand in the robust-PCA direct-sum
objective. -/
theorem matrixEntrywiseL1Penalty_mem_gammaZero :
    matrixEntrywiseL1Penalty ∈ Γ₀(RectangularMatrixSpace M N) := by
  sorry

/-- The two-function family of Example 28.6 belongs to `Γ₀` coordinatewise. -/
theorem robustPCAFunctionFamily_mem_gammaZero :
    ∀ i : Fin 2, robustPCAFunctionFamily i ∈ Γ₀(RectangularMatrixSpace M N) := by
  intro i
  exact
    Fin.cases
      (by
        simpa [robustPCAFunctionFamily] using
          nuclearNormPenalty_mem_gammaZero)
      (fun _ : Fin 1 ↦ by
        simpa [robustPCAFunctionFamily] using
          matrixEntrywiseL1Penalty_mem_gammaZero)
      i

/-- The robust-PCA constraint `R + S = A` is the affine fiber of the coordinate-sum map from
Example 28.5. -/
theorem robustPCAConstraintSet_eq_affineFiber
    (A : Matrix (Fin M) (Fin N) ℝ) :
    robustPCAConstraintSet A =
      affineFiber ContinuousLinearMap.sumCoordinateMap (matrixToEuclidean A) := by
  rw [ContinuousLinearMap.affineFiber_sumCoordinateMap_eq]
  ext z
  simp [robustPCAConstraintSet]

/-- The source argmin set of Example 28.6 is exactly the affine-fiber argmin owner from
Example 28.5. -/
theorem argmin_robustPCAConstraintSet_eq
    (A : Matrix (Fin M) (Fin N) ℝ) :
    Argmin[robustPCAConstraintSet A] robustPCAObjective.asEReal =
      Argmin[affineFiber ContinuousLinearMap.sumCoordinateMap (matrixToEuclidean A)]
        robustPCAObjective.asEReal := by
  rw [robustPCAConstraintSet_eq_affineFiber]

@[simp] theorem mem_effectiveDomain_matrixEntrywiseL1Penalty
    (S : RectangularMatrixSpace M N) :
    S ∈ effectiveDomain matrixEntrywiseL1Penalty := by
  rw [mem_effectiveDomain_iff, matrixEntrywiseL1Penalty]
  simp

@[simp] theorem mem_effectiveDomain_nuclearNormPenalty
    (S : RectangularMatrixSpace M N) :
    S ∈ effectiveDomain nuclearNormPenalty := by
  rw [← matrixToEuclidean_euclideanToMatrix S, mem_effectiveDomain_iff, nuclearNormPenalty_apply]
  simp

@[simp] theorem mem_effectiveDomain_robustPCAObjective
    (z : ProductSpace) :
    z ∈ effectiveDomain robustPCAObjective := by
  rw [robustPCAObjective, mem_effectiveDomain_directSumFunction_iff]
  intro i
  exact
    Fin.cases
      (by simp [robustPCAFunctionFamily])
      (fun _ : Fin 1 ↦ by simp [robustPCAFunctionFamily])
      i

/-- The effective-domain image required by Example 28.5 is all of
`RectangularMatrixSpace M N`, so the strong-relative-interior hypothesis is automatic for
robust PCA. -/
theorem sumCoordinateMap_image_effectiveDomain_robustPCAObjective_eq_univ :
    ContinuousLinearMap.sumCoordinateMap '' effectiveDomain robustPCAObjective =
      (Set.univ : Set (RectangularMatrixSpace M N)) := by
  ext s
  constructor
  · intro hs
    simp
  · intro hs
    refine ⟨robustPCAPoint s 0, ?_, ?_⟩
    · simp
    · rw [ContinuousLinearMap.sumCoordinateMap_apply, Fin.sum_univ_two]
      rw [robustPCAPoint_apply_zero, robustPCAPoint_apply_one]
      simp

/-- A tuple of sequences satisfies the robust PCA Douglas--Rachford recursion `(28.28)` when the
auxiliary correction `C`, the primal shadows `R` and `S`, the proximal steps `X1` and `X2`, and
the dual iterates `Y1` and `Y2` obey the textbook formulas. -/
structure IsRobustPCADouglasRachfordOrbit
    (A : Matrix (Fin M) (Fin N) ℝ) (lam : ℕ → ℝ) (γ : PosReal)
    (Y10 Y20 : RectangularMatrixSpace M N)
    (U : ℕ → Matrix.orthogonalGroup (Fin M) ℝ)
    (V : ℕ → Matrix.orthogonalGroup (Fin N) ℝ)
    (C R S X1 X2 Y1 Y2 : ℕ → RectangularMatrixSpace M N) : Prop where
  /-- The first dual sequence starts from the prescribed point `Y10`. -/
  y1_zero : Y1 0 = Y10
  /-- The second dual sequence starts from the prescribed point `Y20`. -/
  y2_zero : Y2 0 = Y20
  /-- Each iterate `Y1 n` is equipped with a chosen singular value decomposition. -/
  y1_svd :
    ∀ n : ℕ,
      euclideanToMatrix (Y1 n) =
        (((U n : Matrix (Fin M) (Fin M) ℝ) *
            singularValueDiagonal (euclideanToMatrix (Y1 n))) *
          Matrix.transpose (V n : Matrix (Fin N) (Fin N) ℝ))
  /-- The affine correction is `C_n = (A - Y₁,n - Y₂,n) / 2`. -/
  c_eq :
    ∀ n : ℕ,
      C n = ((1 / 2 : ℝ) • (matrixToEuclidean A - Y1 n - Y2 n))
  /-- The low-rank shadow is `R_n = Y₁,n + C_n`. -/
  r_eq : ∀ n : ℕ, R n = Y1 n + C n
  /-- The sparse shadow is `S_n = Y₂,n + C_n`. -/
  s_eq : ∀ n : ℕ, S n = Y2 n + C n
  /-- The nuclear-norm proximal step is obtained by soft-thresholding the singular values of
  `Y1 n` at level `γ`. -/
  x1_eq :
    ∀ n : ℕ,
      X1 n =
        matrixToEuclidean
          ((((U n : Matrix (Fin M) (Fin M) ℝ) *
              nuclearSoftThresholdDiagonal γ (euclideanToMatrix (Y1 n))) *
            Matrix.transpose (V n : Matrix (Fin N) (Fin N) ℝ)))
  /-- The entrywise `ℓ¹` proximal step is the coordinatewise soft-threshold of `Y2 n`. -/
  x2_eq : ∀ n : ℕ, X2 n = matrixEntrywiseSoftThreshold γ (Y2 n)
  /-- The first relaxed update is `Y₁,n+1 = Y₁,n + λ_n (A - X₂,n - Y₁,n - C_n)`. -/
  y1_succ_eq :
    ∀ n : ℕ,
      Y1 (n + 1) =
        Y1 n + lam n • (matrixToEuclidean A - X2 n - Y1 n - C n)
  /-- The second relaxed update is `Y₂,n+1 = Y₂,n + λ_n (A - X₁,n - Y₂,n - C_n)`. -/
  y2_succ_eq :
    ∀ n : ℕ,
      Y2 (n + 1) =
        Y2 n + lam n • (matrixToEuclidean A - X1 n - Y2 n - C n)

namespace IsRobustPCADouglasRachfordOrbit

variable
    {A : Matrix (Fin M) (Fin N) ℝ} {lam : ℕ → ℝ} {γ : PosReal}
    {Y10 Y20 : RectangularMatrixSpace M N}
    {U : ℕ → Matrix.orthogonalGroup (Fin M) ℝ}
    {V : ℕ → Matrix.orthogonalGroup (Fin N) ℝ}
    {C R S X1 X2 Y1 Y2 : ℕ → RectangularMatrixSpace M N}

/-- Bridge view: the source recursion `(28.28)` is the `m = 2` specialization of the canonical
finite-family Douglas--Rachford orbit from Example 28.5, with the two coordinates corresponding to
the low-rank and sparse matrix components. -/
theorem toIsFiniteFamilyLinearConstraintDouglasRachfordOrbit
    (hOrbit :
      IsRobustPCADouglasRachfordOrbit A lam γ Y10 Y20 U V C R S X1 X2 Y1 Y2) :
    IsFiniteFamilyLinearConstraintDouglasRachfordOrbit
      robustPCAFunctionFamily
      robustPCAFunctionFamily_mem_gammaZero
      (matrixToEuclidean A)
      lam
      γ
      (robustPCAPoint Y10 Y20)
      C
      (robustPCAAffineCorrection A X1 X2)
      (robustPCASequence R S)
      (robustPCASequence X1 X2)
      (robustPCASequence Y1 Y2) := by
  sorry

end IsRobustPCADouglasRachfordOrbit

/-- Canonical bridge for Example 28.6: after packaging the two matrix coordinates into the
finite-family product space from Example 28.5, the robust-PCA recursion becomes a direct-sum
Douglas--Rachford orbit whose projected coordinates converge weakly to a constrained minimizer. -/
theorem robustPCA_exists_componentwise_weakLimit_mem_argmin_canonical
    (A : Matrix (Fin M) (Fin N) ℝ)
    (hargmin :
      (Argmin[affineFiber ContinuousLinearMap.sumCoordinateMap (matrixToEuclidean A)]
        robustPCAObjective.asEReal).Nonempty)
    (lam : ℕ → ℝ) (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun K : ℕ ↦
          (Finset.range K).sum
            (fun n : ℕ ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (Y10 Y20 : RectangularMatrixSpace M N)
    {U : ℕ → Matrix.orthogonalGroup (Fin M) ℝ}
    {V : ℕ → Matrix.orthogonalGroup (Fin N) ℝ}
    {C R S X1 X2 Y1 Y2 : ℕ → RectangularMatrixSpace M N}
    (hOrbit :
      IsRobustPCADouglasRachfordOrbit A lam γ Y10 Y20 U V C R S X1 X2 Y1 Y2) :
    ∃ zbar ∈
        Argmin[affineFiber ContinuousLinearMap.sumCoordinateMap (matrixToEuclidean A)]
          robustPCAObjective.asEReal,
      ∀ i : Fin 2,
        Tendsto
          (fun n : ℕ ↦
            toWeakSpace ℝ (RectangularMatrixSpace M N) (robustPCASequence R S n i))
          atTop
          (𝓝 (toWeakSpace ℝ (RectangularMatrixSpace M N) (zbar i))) := by
  sorry

/-- Example 28.6 (Robust PCA): let `ℋ = ℝ^(M × N)`, let `A = R + S`, let `λ_n ∈ [0, 2]` with
`∑ λ_n (2 - λ_n) = +∞`, let `γ ∈ ℝ_{++}`, and let the sequences
`C`, `R`, `S`, `X1`, `X2`, `Y1`, and `Y2` satisfy the robust PCA Douglas--Rachford recursion
`(28.28)` from the initial points `Y10` and `Y20`. Then there exists a solution pair of the
robust PCA problem `min ‖R‖_nuc + ‖S‖₁` subject to `R + S = A`, represented as a point of
`Argmin[robustPCAConstraintSet A] robustPCAObjective.asEReal`, such that `R_n` and `S_n`
converge weakly to its two components. -/
theorem robustPCA_exists_componentwise_weakLimit_mem_argmin
    (A : Matrix (Fin M) (Fin N) ℝ)
    (hargmin :
      (Argmin[robustPCAConstraintSet A] robustPCAObjective.asEReal).Nonempty)
    (lam : ℕ → ℝ) (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun K : ℕ ↦
          (Finset.range K).sum
            (fun n : ℕ ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (Y10 Y20 : RectangularMatrixSpace M N)
    {U : ℕ → Matrix.orthogonalGroup (Fin M) ℝ}
    {V : ℕ → Matrix.orthogonalGroup (Fin N) ℝ}
    {C R S X1 X2 Y1 Y2 : ℕ → RectangularMatrixSpace M N}
    (hOrbit :
      IsRobustPCADouglasRachfordOrbit A lam γ Y10 Y20 U V C R S X1 X2 Y1 Y2) :
    ∃ zbar ∈ Argmin[robustPCAConstraintSet A] robustPCAObjective.asEReal,
      Tendsto
          (fun n : ℕ ↦ toWeakSpace ℝ (RectangularMatrixSpace M N) (R n))
          atTop
          (𝓝 (toWeakSpace ℝ (RectangularMatrixSpace M N) (zbar (0 : Fin 2)))) ∧
        Tendsto
          (fun n : ℕ ↦ toWeakSpace ℝ (RectangularMatrixSpace M N) (S n))
          atTop
          (𝓝 (toWeakSpace ℝ (RectangularMatrixSpace M N) (zbar (1 : Fin 2)))) := by
  have hargmin' :
      (Argmin[affineFiber ContinuousLinearMap.sumCoordinateMap (matrixToEuclidean A)]
        robustPCAObjective.asEReal).Nonempty := by
    simpa [argmin_robustPCAConstraintSet_eq A] using hargmin
  obtain ⟨zbar, hzbar, hzlim⟩ :=
    robustPCA_exists_componentwise_weakLimit_mem_argmin_canonical
      A hargmin' lam hlam hdiv γ Y10 Y20 hOrbit
  refine ⟨zbar, ?_, ?_, ?_⟩
  · simpa [argmin_robustPCAConstraintSet_eq A] using hzbar
  · simpa using hzlim (0 : Fin 2)
  · simpa using hzlim (1 : Fin 2)

end RobustPCA

end

end ERealFunction
