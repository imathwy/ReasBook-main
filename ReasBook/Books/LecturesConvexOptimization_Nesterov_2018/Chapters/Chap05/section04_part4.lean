import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_5_4_4_4 (from Chap05) -/
noncomputable section

open Matrix
open scoped BigOperators RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "SymmMat" => 𝕊^n

/- Proposition 5.4.4.4 lies in the rank-one specialization of the Chapter 5 semidefinite
Newton-system domain.

Sampled owner-style declarations:
* `Matrix.vecMulVec`, the canonical outer-product owner for the rank-one matrices `aⱼ aⱼᵀ`;
* `semidefiniteNewtonNormalMatrix` in `Alg_5_4_4_1`, the chapter owner for the multiplier normal
  matrix `⟪Aᵢ, X Aⱼ X⟫_F`;
* `IsSemidefiniteNewtonDirectionOutput` in `Alg_5_4_4_1`, the chapter owner for a semidefinite
  Newton output described by an explicit multiplier and reconstructed direction;
* `HasLpBarrierNewtonSystemArithmeticComplexityBound` in `Theorem_5_4_9_3`, the nearby Chapter 5
  source-facing owner for a primitive Newton-system arithmetic-work bound.

Best owner abstraction:
* source-facing: the rank-one Newton system with constraints `Aⱼ = aⱼ aⱼᵀ`;
* core/canonical: the Chapter 5 symmetric-matrix owners `𝕊^n`, `𝕊^n₊₊`, and the normal-system
  API from `Alg_5_4_4_1`, together with the chapter's direct asymptotic owner pattern on
  primitive cost functions;
* bridge/view: the derived symmetric family `j ↦ aⱼ aⱼᵀ`, built directly from `Matrix.vecMulVec`.

Primitive data:
* the vectors `a : Fin m → Eₙ`;
* the strict-cone point `X : 𝕊^n₊₊`;
* the symmetric matrix `S : 𝕊^n`;
* the residual vector `r : Eₘ`;
* a primitive rank-one solver/work pair on those inputs.

Derived API:
* the symmetric rank-one constraint family `rankOneConstraintFamily a`;
* the multiplier `λ = -Δy`;
* the matrix-level normal equations via `semidefiniteNewtonNormalMatrix` and `Matrix.mulVec`;
* the recovered Newton direction `rankOneLogDetNewtonDirection a X S Δy`;
* the zero-residual bridge to `IsSemidefiniteNewtonDirectionOutput`;
* the source-facing step-bound and arithmetic-complexity owners on primitive solver/work data.

Source/core/bridge triage:
* source-facing: the rank-one Newton system and its primitive solver/work bound;
* core/canonical: the Chapter 5 semidefinite normal-system owners;
* bridge/view: the specialization `Aⱼ = aⱼ aⱼᵀ`.

This refinement removes the duplicate raw-matrix Frobenius owner and keeps the public
mathematical surface on the Chapter 5 matrix-level normal-system owner. The primal Newton
direction is derived canonically from the multiplier through
`semidefiniteNewtonDirectionFromMultiplier`, and the arithmetic-complexity statement is kept
on a direct Chapter 5-style `Prop` owner on primitive solver/work data instead of a long
existential theorem surface. -/

/-- The rank-one symmetric constraint family `Aⱼ = aⱼ aⱼᵀ` specialized from
`Matrix.vecMulVec`. -/
def rankOneConstraintFamily
    (a : Fin m → Eₙ) : Fin m → SymmMat :=
  fun j ↦ ⟨Matrix.vecMulVec (a j) (a j), by
    rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
    simp [Matrix.IsSymm]⟩

/-- The recovered primal Newton direction attached to the textbook multiplier `λ = -Δy`. -/
def rankOneLogDetNewtonDirection
    (a : Fin m → Eₙ)
    (X : 𝕊^n₊₊) (S : SymmMat)
    (Δy : Eₘ) : SymmMat :=
  semidefiniteNewtonDirectionFromMultiplier
    X
    (-S)
    (rankOneConstraintFamily a)
    (-Δy)

/-- The rank-one Newton system for the log-determinant barrier, written using the Chapter 5
normal-system owners specialized to `Aⱼ = aⱼ aⱼᵀ`, with explicit multiplier `λ = -Δy`. The
primal Newton direction is the derived matrix `rankOneLogDetNewtonDirection a X S Δy`. -/
def IsRankOneLogDetNewtonSystemSolution
    (a : Fin m → Eₙ)
    (X : 𝕊^n₊₊) (S : SymmMat)
    (r : Eₘ)
    (Δy : Eₘ) : Prop :=
  let A := rankOneConstraintFamily a
  Matrix.mulVec (semidefiniteNewtonNormalMatrix X A) (-Δy) =
    semidefiniteNewtonNormalRhs X (-S) A + r

/-- With zero residual shift, a rank-one Newton-system solution yields a Chapter 5 semidefinite
Newton output for the specialized rank-one constraint family. -/
theorem IsRankOneLogDetNewtonSystemSolution.toSemidefiniteNewtonDirectionOutput
    {a : Fin m → Eₙ}
    {X : 𝕊^n₊₊} {S : SymmMat}
    {Δy : Eₘ}
    (hstep : IsRankOneLogDetNewtonSystemSolution a X S 0 Δy) :
    IsSemidefiniteNewtonDirectionOutput
      X
      (-S)
      (rankOneConstraintFamily a)
      (-Δy)
      (rankOneLogDetNewtonDirection a X S Δy) := by
  refine ⟨?_, ?_⟩
  · simpa [IsRankOneLogDetNewtonSystemSolution] using hstep
  · rfl

/-- The arithmetic-work estimate for one execution of a primitive rank-one log-determinant
Newton solver. -/
def RankOneLogDetNewtonStepBound
    (solver : (Fin m → Eₙ) → 𝕊^n₊₊ → SymmMat → Eₘ → Eₘ)
    (arithmeticWork : (Fin m → Eₙ) → 𝕊^n₊₊ → SymmMat → Eₘ → ℕ)
    (C : ℕ)
    (a : Fin m → Eₙ)
    (X : 𝕊^n₊₊)
    (S : SymmMat)
    (r : Eₘ) : Prop :=
  let Δy := solver a X S r
  IsRankOneLogDetNewtonSystemSolution a X S r Δy ∧
    arithmeticWork a X S r ≤ C * (m + n) ^ 3

/-- With zero residual shift, a bounded primitive rank-one Newton step yields the Chapter 5
semidefinite Newton output attached to its recovered direction. -/
theorem RankOneLogDetNewtonStepBound.toSemidefiniteNewtonDirectionOutput
    {solver : (Fin m → Eₙ) → 𝕊^n₊₊ → SymmMat → Eₘ → Eₘ}
    {arithmeticWork : (Fin m → Eₙ) → 𝕊^n₊₊ → SymmMat → Eₘ → ℕ}
    {C : ℕ}
    {a : Fin m → Eₙ}
    {X : 𝕊^n₊₊}
    {S : SymmMat}
    (hstep : RankOneLogDetNewtonStepBound solver arithmeticWork C a X S 0) :
    IsSemidefiniteNewtonDirectionOutput
      X
      (-S)
      (rankOneConstraintFamily a)
      (-solver a X S 0)
      (rankOneLogDetNewtonDirection a X S (solver a X S 0)) := by
  exact hstep.1.toSemidefiniteNewtonDirectionOutput

/-- Proposition 5.4.4.4's source-facing arithmetic-complexity owner for the rank-one
log-determinant Newton system. It records a uniform `O((m + n)^3)` bound on primitive solver/work
data, and each bounded run is required to solve the displayed rank-one normal equations. Through
the zero-residual bridge `RankOneLogDetNewtonStepBound.toSemidefiniteNewtonDirectionOutput`, the
same primitive data also yields the canonical Chapter 5 semidefinite Newton-direction output when
`r = 0`. -/
def HasRankOneLogDetNewtonSystemArithmeticComplexityBound
    (solver : (Fin m → Eₙ) → 𝕊^n₊₊ → SymmMat → Eₘ → Eₘ)
    (arithmeticWork : (Fin m → Eₙ) → 𝕊^n₊₊ → SymmMat → Eₘ → ℕ) : Prop :=
  ∃ C : ℕ,
    ∀ (a : Fin m → Eₙ)
      (X : 𝕊^n₊₊)
      (S : SymmMat)
      (r : Eₘ),
      RankOneLogDetNewtonStepBound solver arithmeticWork C a X S r

/-- Unfolding `HasRankOneLogDetNewtonSystemArithmeticComplexityBound solver arithmeticWork`
recovers the explicit constant-factor cubic arithmetic bound on primitive rank-one solver/work
data. -/
theorem hasRankOneLogDetNewtonSystemArithmeticComplexityBound_iff
    (solver : (Fin m → Eₙ) → 𝕊^n₊₊ → SymmMat → Eₘ → Eₘ)
    (arithmeticWork : (Fin m → Eₙ) → 𝕊^n₊₊ → SymmMat → Eₘ → ℕ) :
    HasRankOneLogDetNewtonSystemArithmeticComplexityBound solver arithmeticWork ↔
      ∃ C : ℕ,
        ∀ (a : Fin m → Eₙ)
          (X : 𝕊^n₊₊)
          (S : SymmMat)
          (r : Eₘ),
          RankOneLogDetNewtonStepBound solver arithmeticWork C a X S r := by
  rfl

-- Proof sketch: for `Aⱼ = aⱼ aⱼᵀ`, the normal matrix coefficients reduce to
-- `(aⱼᵀ X aᵢ)^2`, so the system matrix and right-hand side can be formed using the Gram data
-- `aⱼᵀ X aᵢ` in cubic arithmetic complexity in `m + n`; solving the dense `m × m` system yields
-- `Δy`, and `ΔX` is then recovered by the Chapter 5 reconstruction formula.
/-- Proposition 5.4.4.4: under the rank-one specialization `Aⱼ = aⱼ aⱼᵀ`, the Chapter 5
semidefinite Newton system admits, for each pair `(n, m)`, primitive rank-one solver/work data
whose arithmetic work is bounded by a constant multiple of `(m + n)^3`. Each bounded run solves
the displayed rank-one normal equations, and in the zero-residual case its recovered matrix is
the canonical Chapter 5 semidefinite Newton-direction output. -/
theorem rankOneLogDetNewtonSystem_cubic_arithmeticComplexity_bound (n m : ℕ) :
    ∃ solver : (Fin m → EuclideanSpace ℝ (Fin n)) → 𝕊^n₊₊ → 𝕊^n →
        EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      ∃ arithmeticWork : (Fin m → EuclideanSpace ℝ (Fin n)) → 𝕊^n₊₊ → 𝕊^n →
          EuclideanSpace ℝ (Fin m) → ℕ,
        HasRankOneLogDetNewtonSystemArithmeticComplexityBound solver arithmeticWork := sorry

end

/-! ### Theorem_5_4_4_1 (from Chap05) -/
noncomputable section

open Matrix
open scoped RealSymmetricMatrixSpace

section

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

private theorem mem_positiveSemidefiniteCone_iff_dotProduct_nonneg
    (X : SymmMat) :
    X ∈ (𝕊^n₊ : Set SymmMat) ↔ ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ ((X : Mat) *ᵥ x) := by
  rw [mem_positiveSemidefiniteCone_iff, Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨_, hX⟩
    simpa using hX
  · intro hX
    exact ⟨RealSymmetricMatrixSpace.isHermitian X, by simpa using hX⟩

/- Theorem 5.4.4.1 lies in the chapter's positive-semidefinite symmetric-matrix cone domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` from `Definition_5_4_4_1`, the symmetric-matrix carrier owner;
- Chapter 5 `𝕊^n₊` and `mem_positiveSemidefiniteCone_iff` from `Definition_5_4_4_3`, the
  source-facing cone owner and its canonical membership bridge;
- mathlib `Matrix.PosSemidef`, the core owner predicate for positive semidefiniteness;
- mathlib `Matrix.isPositive_toEuclideanLin_iff`, the quadratic-form bridge for
  positive-semidefinite matrices.

Best owner abstraction:
- source-facing: the cone `𝕊^n₊ : Set (𝕊^n)`;
- core/canonical: `Matrix.PosSemidef`;
- bridge/view: the membership and quadratic-form characterizations already provided upstream in
  `Definition_5_4_4_3`.

Primitive data:
- `n : ℕ`

Derived API:
- the source-facing theorem that `𝕊^n₊` is a closed convex set;
- the companion projection lemmas giving closedness and convexity separately.

This file therefore stays at the theorem layer over the existing cone owner `𝕊^n₊`. It does not
introduce a new set owner or restate matrix positivity as primitive data. The closedness and
convexity statements are kept only as thin projections from the textbook combined conclusion.
-/

/-- The positive-semidefinite cone is closed in the symmetric-matrix space `𝕊^n`. -/
theorem positiveSemidefiniteCone_isClosed (n : ℕ) :
    IsClosed (𝕊^n₊) := by
  rw [show (𝕊^n₊ : Set (𝕊^n)) =
      ⋂ x : Fin n → ℝ,
        {X : 𝕊^n | 0 ≤ x ⬝ᵥ ((X : Matrix (Fin n) (Fin n) ℝ) *ᵥ x)} by
    ext X
    simpa using (mem_positiveSemidefiniteCone_iff_dotProduct_nonneg X)]
  refine isClosed_iInter fun x ↦ ?_
  exact isClosed_le continuous_const <| by fun_prop

/-- The positive-semidefinite cone is convex in the symmetric-matrix space `𝕊^n`. -/
theorem positiveSemidefiniteCone_convex (n : ℕ) :
    Convex ℝ (𝕊^n₊) := by
  intro X hX Y hY a b ha hb hab
  rw [mem_positiveSemidefiniteCone_iff] at hX hY ⊢
  simpa using (hX.smul ha).add (hY.smul hb)

/-- Theorem 5.4.4.1: the cone `𝕊ⁿ₊` of positive semidefinite real `n × n` matrices is a closed
convex set. -/
theorem positiveSemidefiniteCone_isClosed_convex (n : ℕ) :
    IsClosed (𝕊^n₊) ∧ Convex ℝ (𝕊^n₊) :=
  ⟨positiveSemidefiniteCone_isClosed n, positiveSemidefiniteCone_convex n⟩

end

end

/-! ### Theorem_5_4_4_2 (from Chap05) -/
noncomputable section

open Matrix
open RealSymmetricMatrixSpace
open scoped RealSymmetricMatrixSpace

/-
Theorem 5.4.4.2 lies in the positive-definite real symmetric matrix / spectral barrier domain.

Sampled owner-style declarations:
* Chapter 5 `logDetBarrier`, the source-facing owner for `-log det` on `𝕊^n₊₊`;
* Chapter 5 `RealSymmetricMatrixSpace.eigenvalues`, the intrinsic eigenvalue API on `𝕊^n`;
* `Matrix.IsHermitian.det_eq_prod_eigenvalues`, the canonical determinant/eigenvalue bridge;
* `Matrix.PosDef.eigenvalues_pos`, the positivity owner for eigenvalues of positive-definite
  matrices;
* `Real.log_prod`, the canonical logarithm-of-product identity.

Best owner abstraction:
* source-facing: `logDetBarrier n` on the strict cone `𝕊^n₊₊`;
* core/canonical: Hermitian eigenvalues and positive-definite positivity;
* bridge/view: `logDetBarrier_apply`.

This refinement removes the duplicated ambient `-log det` surface from the theorem statement and
restates the identity directly for the Chapter 5 barrier owner.
-/

/-- Theorem 5.4.4.2: for a positive-definite real symmetric matrix `X`, the Chapter 5 owner
`logDetBarrier` equals the negative sum of the logarithms of the eigenvalues of `X`. -/
theorem logDetBarrier_eq_neg_sum_log_eigenvalues
    {n : ℕ} (X : 𝕊^n₊₊) :
    logDetBarrier n X =
      -∑ i : Fin n, Real.log (eigenvalues X i) := by
  have hlog :
      Real.log (∏ i : Fin n, eigenvalues X i) =
        ∑ i : Fin n, Real.log (eigenvalues X i) := by
    simpa using
      (Real.log_prod fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
        (eigenvalues_pos X i).ne')
  calc
    logDetBarrier n X = -Real.log (((X : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ).det) := by
      simp [logDetBarrier_apply]
    _ = -Real.log (∏ i : Fin n, eigenvalues X i) := by
      rw [det_eq_prod_eigenvalues (X : 𝕊^n)]
    _ = -∑ i : Fin n, Real.log (eigenvalues X i) := by
      rw [hlog]

end

/-! ### Theorem_5_4_4_3 (from Chap05) -/
noncomputable section

open scoped RealSymmetricMatrixSpace

-- Proof sketch: for `X ∈ int(𝕊ⁿ₊)` and a symmetric direction `Δ`, conjugate by `X^(-1 / 2)` to
-- reduce the first three directional derivatives of `X ↦ -log det X` to sums of eigenvalue
-- powers of `Q = X^(-1 / 2) Δ X^(-1 / 2)`. Then the barrier-parameter bound with `ν = n`
-- follows from Cauchy--Schwarz, and the self-concordance inequality follows from the estimate
-- `|∑ λᵢ^3| ≤ (∑ λᵢ^2)^(3 / 2)`.
/-- Theorem 5.4.4.3: the log-determinant function `X ↦ -log det X` is an `n`-self-concordant
barrier on the interior of the positive-semidefinite cone `𝕊ⁿ₊`. -/
theorem negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone
    (n : ℕ) :
    IsSelfConcordantBarrierOnWith
      (𝕊^n₊₊ : Set (𝕊^n))
      n
      (logDetBarrierAmbient n) := by
  sorry

end

/-! ### Theorem_5_4_4_4 (from Chap05) -/
noncomputable section

open Matrix
open scoped RealSymmetricMatrixSpace

variable {m n : ℕ}

/- This item lies in the semidefinite short-step path-following domain.

Sampled owner-style declarations:
* `SemidefiniteOptimizationProblem` and `SemidefiniteOptimizationProblem.feasibleSet` in
  `Definition_5_4_4_4`, the chapter owner for SDP data, feasible matrices, and the trace
  objective `trace (C X)`;
* `SemidefiniteOptimizationProblem.strictFeasibleSet` and `logDetBarrierAmbient` in
  `Definition_5_4_4_5`, the source-facing strict-feasibility owner and the ambient bridge for
  the textbook barrier formula `X ↦ -log det X`;
* `realSymmetricMatrixConstraintMap` and
  `realSymmetricMatrixAssociatedAffineSubspace` in `Definition_5_4_4_6`, the canonical owner
  bridge from the SDP Frobenius equalities to the intrinsic affine constraint space;
* `negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone` in
  `Theorem_5_4_4_3`, the chapter owner theorem for the `n`-self-concordant barrier on
  `𝕊ⁿ₊₊`;
* `BarrierPathFollowingScheme` in `Definition_5_3_4_1`, the chapter owner for short-step
  barrier path-following data;
* `IsSelfConcordantBarrierOnWith.comp_affineMap` in `Theorem_5_3_3`, the canonical affine
  pullback owner theorem for restricting a barrier to an affine slice.

Best owner abstraction:
* source-facing: the SDP owner `SemidefiniteOptimizationProblem n m` together with its explicit
  strict feasible set `problem.strictFeasibleSet`;
* core/canonical: `BarrierPathFollowingScheme`;
* bridge/view: the canonical affine bridge from the constraint kernel
  `(realSymmetricMatrixConstraintMap problem.constraintMatrices).ker` to the affine slice
  `realSymmetricMatrixAssociatedAffineSubspace problem.constraintMatrices problem.rhs`,
  together with the affine pullback of `logDetBarrierAmbient n`.

Primitive data:
* `problem : SemidefiniteOptimizationProblem n m`.

Derived API:
* the strict feasible owner `problem.strictFeasibleSet`;
* the affine constraint space
  `realSymmetricMatrixAssociatedAffineSubspace problem.constraintMatrices problem.rhs`;
* the public affine bridge from
  `(realSymmetricMatrixAssociatedAffineSubspace problem.constraintMatrices problem.rhs).direction`
  back to the affine slice;
* the common short-step existence package theorem and its source-facing projections.

Source/core/bridge triage:
* source-facing: the SDP owner `problem` and its strict feasible set `problem.strictFeasibleSet`;
* core/canonical: `BarrierPathFollowingScheme`;
* bridge/view: the affine translation from `𝓛.direction` to the affine slice `𝓛`, together
  with its induced strict domain and pulled-back `logDetBarrierAmbient n`.

This refinement removes the mathematically incorrect ambient-domain barrier hypothesis on
`problem.strictFeasibleSet`, which is generally not open in `𝕊^n`. The theorem now runs the
short-step scheme on the direction space of the canonical affine slice
`realSymmetricMatrixAssociatedAffineSubspace problem.constraintMatrices problem.rhs`, and the
required affine translation by a strict feasible base point is exposed as a public bridge on the
SDP owner. -/

local notation "SymmMat" => 𝕊^n

namespace SemidefiniteOptimizationProblem

instance affineSliceLogDetBarrier.instIsSelfConcordantBarrierOnWith
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint) :
    IsSelfConcordantBarrierOnWith
      (problem.affineSliceStrictDomain xRef)
      n
      (problem.affineSliceLogDetBarrier xRef) := by
  have hbarrier :
      IsSelfConcordantBarrierOnWith
        (𝕊^n₊₊ : Set SymmMat)
        n
        (logDetBarrierAmbient n) := by
    simpa using negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone n
  simpa [affineSliceStrictDomain, affineSliceLogDetBarrier] using
    hbarrier.comp_affineMap (problem.affineSliceMap xRef)

theorem affineSliceMap_mem_affineSlice
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint)
    (Δ : problem.affineSlice.direction) :
    problem.affineSliceMap xRef Δ ∈ problem.affineSlice := by
  have hxRef_strict : (xRef : SymmMat) ∈ problem.strictFeasibleSet := xRef.2
  change
    (xRef : SymmMat) ∈ (𝕊^n₊₊ : Set SymmMat) ∩ (problem.affineSlice : Set SymmMat) at hxRef_strict
  rw [Set.mem_inter_iff] at hxRef_strict
  have hxRef : (xRef : SymmMat) ∈ problem.affineSlice := by
    exact hxRef_strict.2
  simpa using AffineSubspace.vadd_mem_of_mem_direction Δ.2 hxRef

theorem affineSliceMap_mem_strictFeasibleSet_of_mem_affineSliceStrictDomain
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint)
    {Δ : problem.affineSlice.direction}
    (hΔ : Δ ∈ problem.affineSliceStrictDomain xRef) :
    problem.affineSliceMap xRef Δ ∈ problem.strictFeasibleSet := by
  rw [strictFeasibleSet, Set.mem_inter_iff]
  refine ⟨?_, problem.affineSliceMap_mem_affineSlice xRef Δ⟩
  simpa [affineSliceStrictDomain] using hΔ

theorem affineSliceMap_mem_feasibleSet_of_mem_affineSliceStrictDomain
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint)
    {Δ : problem.affineSlice.direction}
    (hΔ : Δ ∈ problem.affineSliceStrictDomain xRef) :
    problem.affineSliceMap xRef Δ ∈ problem.feasibleSet := by
  have hstrict :
      problem.affineSliceMap xRef Δ ∈ problem.strictFeasibleSet :=
    problem.affineSliceMap_mem_strictFeasibleSet_of_mem_affineSliceStrictDomain xRef hΔ
  rcases (problem.mem_strictFeasibleSet_iff _).1 hstrict with ⟨hpd, hEq⟩
  rw [problem.mem_feasibleSet_iff]
  refine ⟨?_, hEq⟩
  rw [mem_positiveSemidefiniteCone_iff]
  exact (strictPositiveSemidefiniteCone_posDef ⟨_, hpd⟩).posSemidef

end SemidefiniteOptimizationProblem

section

variable (problem : SemidefiniteOptimizationProblem n m)
local notation "𝓕°" => problem.strictFeasibleSet

variable {ε : ℝ}

/-- Theorem 5.4.4.4 (1): if `problem.strictFeasibleSet` is nonempty, `xOpt` is optimal for the
SDP owner `problem` on `problem.feasibleSet`, and `ε > 0`, then there exist common short-step
path-following data for the SDP affine-slice barrier: a strict feasible base point `X̄`,
parameters `β`, `γ`, an iteration-bound constant `C₀`, a strict starting point in the direction
space, and a barrier path-following scheme whose stopping iterate is strictly feasible (hence
feasible), `ε`-accurate relative to `xOpt`, and whose stopping index satisfies the stated
`O(√n log (n / ε))` bound. -/
theorem exists_semidefinitePathFollowingScheme
    (hstrict : 𝓕°.Nonempty)
    (xOpt : problem.feasibleSet)
    (hopt : IsMinOn problem problem.feasibleSet (xOpt : SymmMat))
    (hε : 0 < ε) :
    ∃ xRef : 𝓕°,
      ∃ β : ℝ,
        ∃ γ : ℝ,
          ∃ C₀ : NNRealˣ,
            ∃ z0 : problem.affineSliceStrictDomain xRef,
              ∃ scheme :
                BarrierPathFollowingScheme
                  problem.affineSliceProjectedCost
                  (problem.affineSliceLogDetBarrier xRef)
                  n z0 β γ ε,
                β < 1 / 2 ∧
                  0 < γ ∧
                  problem.affineSliceMap xRef (scheme scheme.stopIndex) ∈
                    problem.strictFeasibleSet ∧
                  problem.affineSliceMap xRef (scheme scheme.stopIndex) ∈ problem.feasibleSet ∧
                  problem (problem.affineSliceMap xRef (scheme scheme.stopIndex)) ≤
                    problem (xOpt : SymmMat) + ε ∧
                  scheme.stopIndex ≤
                    ⌈((C₀ : NNReal) : ℝ) * Real.sqrt (n : ℝ) * Real.log ((n : ℝ) / ε)⌉₊ := sorry

-- Proof sketch: extract the positive constant controlling the iteration bound from the core
-- short-step existence theorem.
/-- Theorem 5.4.4.4 (2): under the same hypotheses, there exists a positive constant `C₀`
appearing in the short-step complexity estimate for the semidefinite path-following scheme. -/
theorem exists_semidefinitePathFollowingScheme_iteration_constant_pos
    (hstrict : 𝓕°.Nonempty)
    (xOpt : problem.feasibleSet)
    (hopt : IsMinOn problem problem.feasibleSet (xOpt : SymmMat))
    (hε : 0 < ε) :
    ∃ xRef : 𝓕°,
      ∃ β : ℝ,
        ∃ γ : ℝ,
          ∃ C₀ : ℝ,
            ∃ z0 : problem.affineSliceStrictDomain xRef,
              ∃ _scheme :
                BarrierPathFollowingScheme
                  problem.affineSliceProjectedCost
                  (problem.affineSliceLogDetBarrier xRef)
                  n z0 β γ ε,
                0 < C₀ := by
  rcases exists_semidefinitePathFollowingScheme problem hstrict xOpt hopt hε with
    ⟨xRef, β, γ, C₀, z0, scheme, -, -, -, -, -, -⟩
  refine ⟨xRef, β, γ, ((C₀ : NNReal) : ℝ), z0, scheme, ?_⟩
  have hC₀ : (0 : NNReal) < (C₀ : NNReal) := by
    exact pos_iff_ne_zero.mpr (Units.ne_zero C₀)
  exact_mod_cast hC₀

-- Proof sketch: extract the stopping-index estimate from the core short-step existence theorem.
/-- Theorem 5.4.4.4 (3): under the same hypotheses, there exists a semidefinite path-following
scheme whose stopping index is bounded by `O(√n log (n / ε))`. This bound depends on the barrier
parameter `n`, not on the ambient dimension `dim (𝕊ⁿ) = n (n + 1) / 2`. -/
theorem exists_semidefinitePathFollowingScheme_stopIndex_le_iteration_bound
    (hstrict : 𝓕°.Nonempty)
    (xOpt : problem.feasibleSet)
    (hopt : IsMinOn problem problem.feasibleSet (xOpt : SymmMat))
    (hε : 0 < ε) :
    ∃ xRef : 𝓕°,
      ∃ β : ℝ,
        ∃ γ : ℝ,
          ∃ C₀ : ℝ,
            ∃ z0 : problem.affineSliceStrictDomain xRef,
              ∃ scheme :
                BarrierPathFollowingScheme
                  problem.affineSliceProjectedCost
                  (problem.affineSliceLogDetBarrier xRef)
                  n z0 β γ ε,
                scheme.stopIndex ≤
                  ⌈C₀ * Real.sqrt (n : ℝ) * Real.log ((n : ℝ) / ε)⌉₊ := by
  rcases exists_semidefinitePathFollowingScheme problem hstrict xOpt hopt hε with
    ⟨xRef, β, γ, C₀, z0, scheme, -, -, -, -, -, hscheme⟩
  exact ⟨xRef, β, γ, ((C₀ : NNReal) : ℝ), z0, scheme, by simpa using hscheme⟩

-- Proof sketch: extract the strict-feasibility, feasibility, and owner-level `ε`-accuracy
-- clauses from the common short-step existence theorem.
/-- Theorem 5.4.4.4 (4): under the same hypotheses, there exists a semidefinite path-following
scheme whose stopping iterate is strictly feasible (hence feasible) and whose SDP objective value
is within `ε` of the optimal reference value `problem (xOpt : SymmMat)`. -/
theorem exists_semidefinitePathFollowingScheme_stop_trace_le_add_epsilon
    (hstrict : 𝓕°.Nonempty)
    (xOpt : problem.feasibleSet)
    (hopt : IsMinOn problem problem.feasibleSet (xOpt : SymmMat))
    (hε : 0 < ε) :
    ∃ xRef : 𝓕°,
      ∃ β : ℝ,
        ∃ γ : ℝ,
          ∃ z0 : problem.affineSliceStrictDomain xRef,
            ∃ scheme :
                BarrierPathFollowingScheme
                  problem.affineSliceProjectedCost
                  (problem.affineSliceLogDetBarrier xRef)
                  n z0 β γ ε,
              problem.affineSliceMap xRef (scheme scheme.stopIndex) ∈ problem.strictFeasibleSet ∧
                problem.affineSliceMap xRef (scheme scheme.stopIndex) ∈ problem.feasibleSet ∧
                problem (problem.affineSliceMap xRef (scheme scheme.stopIndex)) ≤
                  problem (xOpt : SymmMat) + ε := by
  rcases exists_semidefinitePathFollowingScheme problem hstrict xOpt hopt hε with
    ⟨xRef, β, γ, C₀, z0, scheme, -, -, hstrictStop, hfeasStop, hgap, -⟩
  exact ⟨xRef, β, γ, z0, scheme, hstrictStop, hfeasStop, hgap⟩

end

end

/-! ### Definition_5_4_5_1 (from Chap05) -/
/- Definition 5.4.5.1 lies in the minimum-volume enclosing-ellipsoid / constrained-optimization
domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
* `𝕊^n₊₊` and `strictPositiveSemidefiniteCone_posDef` in `Chap05/Definition_5_4_4_5`, the
  chapter owner and matrix-level bridge for positive-definite symmetric shapes;
* `minimumVolumeEnclosingEllipsoidBarrierDomain` in `Chap05/Definition_5_4_5_2`, the immediate
  downstream MVEE barrier domain already written on `𝕊^n₊₊ × Eₙ × ℝ`;
* `circumscribedEllipsoidBarrierDomain` in `Chap05/Definition_5_4_5_5`, the nearby ellipsoid
  barrier file that uses the same strict-cone owner level rather than a raw positive-definite
  subtype.

Best owner abstraction:
* source-facing data: the finite point family `a`, the enclosing-ellipsoid set `W(H, v)` with shape
  `H : 𝕊^n₊₊`, and the epigraph variable `τ`;
* core/canonical: `SetConstrainedMinimizationProblem` on the ambient decision-variable type
  `𝕊^n₊₊ × Eₙ × ℝ`;
* bridge/view: the canonical coercion from `H : 𝕊^n₊₊` to its ambient symmetric matrix in `𝕊^n`,
  followed by the matrix view in `Matrix (Fin n) (Fin n) ℝ`.

Primitive data:
* the feasible set of strict-cone shapes, centers, and epigraph variables satisfying the
  enclosing inequalities;
* the objective `τ`.

Derived API:
* the source-facing image-form notation `W(H, v)`;
* its bridge to the Chapter 3 ellipsoid owner `E(H, x̄)`;
* the membership and objective-expansion lemmas below.

Source/core/bridge triage:
* source-facing: the notation `W(H, v)` and the textbook feasible inequalities for
  `(H, v, τ) ∈ 𝕊^n₊₊ × Eₙ × ℝ`;
* core/canonical: `SetConstrainedMinimizationProblem`;
* bridge/view: the matrix-action coercion `H ↦ ((H : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ)`,
  followed by the Chapter 3 ellipsoid owner `E(H, x̄)`. -/

noncomputable section

open Matrix
open StrictPositiveSemidefiniteCone
open scoped EllipsoidNotation RealSymmetricMatrixSpace

variable {ι : Type*} {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-- Definition 5.4.5.1: the source-facing image-form ellipsoid `W(H, v)` is the set of points
`x` satisfying the textbook constraint `‖H x - v‖ ≤ 1`. -/
def enclosingEllipsoid
    (H : 𝕊^n₊₊) (v : Eₙ) : Set Eₙ :=
  {x | ‖(toMatrix H).toEuclideanLin x - v‖ ≤ 1}

namespace EnclosingEllipsoidNotation

/-- The source-facing image-form ellipsoid `W(H, v)`. -/
scoped notation:max "W(" H ", " v ")" =>
  enclosingEllipsoid H v

end EnclosingEllipsoidNotation

open scoped EnclosingEllipsoidNotation

/-- The image-form ellipsoid `W(H, v)` is the Chapter 3 affine ellipsoid with shape
`(H⁻¹)^2` and center `H⁻¹ v`. -/
theorem enclosingEllipsoid_eq_affineEllipsoid
    (H : 𝕊^n₊₊) (v : Eₙ) :
    W(H, v) = E((toMatrix H)⁻¹ * (toMatrix H)⁻¹, ((toMatrix H)⁻¹).toEuclideanLin v) := by
  sorry

-- Proof sketch: rewrite `W(H, v)` through `enclosingEllipsoid_eq_affineEllipsoid`, expand
-- `mem_affineEllipsoid_iff`, and simplify the resulting quadratic form.
/-- Membership in `W(H, v)` is exactly the constraint `‖H x - v‖ ≤ 1`. -/
@[simp] theorem mem_enclosingEllipsoid_iff
    {H : 𝕊^n₊₊} {v x : Eₙ} :
    x ∈ W(H, v) ↔ ‖(toMatrix H).toEuclideanLin x - v‖ ≤ 1 :=
  Iff.rfl

/-- Definition 5.4.5.1: the minimum-volume enclosing ellipsoid problem for a finite family of
points `a i` minimizes the scalar upper bound `τ` over strict-cone shapes `H : 𝕊ⁿ₊₊`, offsets
`v`, and `τ`, subject to `logDetBarrier n H ≤ τ` and the enclosing constraints
`a_i ∈ W(H, v)` for every index `i`. The raw `-log det H ≤ τ` and `‖H a_i - v‖ ≤ 1` formulas are
companion bridge views. -/
def minimumVolumeEnclosingEllipsoidProblem
    (a : ι → Eₙ) :
    SetConstrainedMinimizationProblem
      (𝕊^n₊₊ × Eₙ × ℝ) where
  feasibleSet := {Hvτ | logDetBarrier n Hvτ.1 ≤ Hvτ.2.2 ∧
    ∀ i, a i ∈ W(Hvτ.1, Hvτ.2.1)}
  objective := Prod.snd ∘ Prod.snd

-- Proof sketch: unfold `minimumVolumeEnclosingEllipsoidProblem`; the feasible set is
-- definitionally the conjunction of the owner determinant barrier bound and the source-facing
-- enclosing-ellipsoid constraints.
/-- A triple `(H, v, τ)` is feasible for the minimum-volume enclosing ellipsoid problem exactly
when `logDetBarrier n H ≤ τ` and every point `a i` belongs to the enclosing ellipsoid
`W(H, v)`. -/
@[simp] theorem mem_minimumVolumeEnclosingEllipsoidProblem_feasibleSet_iff
    (a : ι → Eₙ)
    (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    (H, v, τ) ∈ (minimumVolumeEnclosingEllipsoidProblem a).feasibleSet ↔
      logDetBarrier n H ≤ τ ∧
        ∀ i, a i ∈ W(H, v) :=
  Iff.rfl

-- Proof sketch: expand the owner determinant barrier with `logDetBarrier_apply` and rewrite the
-- source-facing ellipsoid constraints using `mem_enclosingEllipsoid_iff`.
/-- Expanding the owner feasible-set description rewrites MVEE feasibility back to the textbook
formula `-log det H ≤ τ` together with the norm constraints `‖H a_i - v‖ ≤ 1`. -/
theorem mem_minimumVolumeEnclosingEllipsoidProblem_feasibleSet_iff_formula
    (a : ι → Eₙ)
    (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    (H, v, τ) ∈ (minimumVolumeEnclosingEllipsoidProblem a).feasibleSet ↔
      -Real.log (toMatrix H).det ≤ τ ∧
        ∀ i, ‖(toMatrix H).toEuclideanLin (a i) - v‖ ≤ 1 := by
  simp [mem_minimumVolumeEnclosingEllipsoidProblem_feasibleSet_iff, logDetBarrier_apply,
    mem_enclosingEllipsoid_iff]

-- Proof sketch: unfold `minimumVolumeEnclosingEllipsoidProblem`; the objective field is exactly
-- the third coordinate `τ`.
/-- Evaluating the objective of the minimum-volume enclosing ellipsoid problem returns the
auxiliary variable `τ`. -/
@[simp] theorem minimumVolumeEnclosingEllipsoidProblem_objective_apply
    (a : ι → Eₙ)
    (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    (minimumVolumeEnclosingEllipsoidProblem a) (H, v, τ) = τ :=
  rfl

end

/-! ### Definition_5_4_5_2 (from Chap05) -/
/- Definition 5.4.5.2 lies in the minimum-volume enclosing-ellipsoid / logarithmic-barrier
domain.

Sampled owner-style declarations in this domain:
* `logDetBarrier` in `Chap05/Definition_5_4_4_5`, the chapter owner for the `-\log \det`
  contribution on `𝕊^n₊₊`;
* `logDetBarrier_apply` in the same file, the canonical expansion bridge back to the textbook
  determinant formula;
* the ambient symmetric-space bridge in `Chap05/Theorem_5_4_5_1`, which transports this owner
  barrier to the path-following setting without introducing a second public MVEE barrier owner;
* `logarithmicBarrier` in `Chap05/Definition_5_4_5_7`, the nearby inscribed-ellipsoid analogue
  with the same `τ`-shifted logarithmic-barrier pattern.

Best owner abstraction:
* source-facing: the MVEE barrier and strict domain on `(H, v, τ)`;
* core/canonical: `logDetBarrier n` for the determinant barrier on `𝕊^n₊₊`;
* bridge/view: the textbook expansion `logDetBarrier n H = -log det H`.

Primitive data:
* the finite point family `a`;
* the strict-cone variable `H : 𝕊^n₊₊`, center `v`, and scalar `τ`.

Derived API:
* the strict barrier domain `minimumVolumeEnclosingEllipsoidBarrierDomain a`;
* its owner carrier `MinimumVolumeEnclosingEllipsoidBarrierPoint a`;
* the determinant contribution `logDetBarrier n H`;
* the ambient bridge formula `minimumVolumeEnclosingEllipsoidBarrierAmbient a`.

This file therefore keeps the source-facing MVEE barrier on its strict domain, and reuses the
chapter owner `logDetBarrier` instead of repeating a parallel local `-log det` API. The raw
formula on `𝕊^n₊₊ × Eₙ × ℝ` is retained only as a bridge view.
-/

noncomputable section

open Matrix
open scoped BigOperators RealSymmetricMatrixSpace

variable {ι : Type*} {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n

private abbrev pointSlack (H : SymmMat) (v x : Eₙ) : ℝ :=
  1 - ‖(H : Mat).toEuclideanLin x - v‖ ^ (2 : ℕ)

/-- The strict domain on which the minimum-volume enclosing ellipsoid logarithmic barrier is
defined. -/
def minimumVolumeEnclosingEllipsoidBarrierDomain
    (a : ι → Eₙ) : Set (𝕊^n₊₊ × Eₙ × ℝ) :=
  {Hvτ | 0 < Hvτ.2.2 - logDetBarrier n Hvτ.1 ∧
    ∀ i, 0 < pointSlack Hvτ.1 Hvτ.2.1 (a i)}

/-- The ambient pullback domain of the MVEE logarithmic barrier on `𝕊ⁿ × Eₙ × ℝ`. It is a
bridge/view that records strict positivity of the shape variable together with the same strict
slack inequalities used by the source-facing strict-domain owner
`minimumVolumeEnclosingEllipsoidBarrierDomain a`. -/
def minimumVolumeEnclosingEllipsoidBarrierAmbientDomain
    (a : ι → Eₙ) : Set (SymmMat × Eₙ × ℝ) :=
  {Hvτ | Hvτ.1 ∈ (𝕊^n₊₊ : Set SymmMat) ∧
    0 < Hvτ.2.2 - logDetBarrierAmbient n Hvτ.1 ∧
      ∀ i, 0 < pointSlack Hvτ.1 Hvτ.2.1 (a i)}

/-- Membership in the barrier domain means that the shifted logarithmic argument
`τ - logDetBarrier n H = τ + log det H` is positive and every ellipsoid slack
`1 - ‖H a_i - v‖²` is positive. -/
theorem mem_minimumVolumeEnclosingEllipsoidBarrierDomain_iff
    (a : ι → Eₙ) (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    (H, v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierDomain a ↔
      0 < τ - logDetBarrier n H ∧
        ∀ i,
          0 < 1 - ‖((H : SymmMat) : Mat).toEuclideanLin (a i) - v‖ ^ (2 : ℕ) := by
  simp [minimumVolumeEnclosingEllipsoidBarrierDomain, pointSlack]

/-- Expanding `logDetBarrier n` rewrites barrier-domain membership back to the textbook
`τ + log det H` formula. -/
theorem mem_minimumVolumeEnclosingEllipsoidBarrierDomain_iff_formula
    (a : ι → Eₙ) (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    (H, v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierDomain a ↔
      0 < τ + Real.log (((H : SymmMat) : Mat).det) ∧
        ∀ i,
          0 < 1 - ‖((H : SymmMat) : Mat).toEuclideanLin (a i) - v‖ ^ (2 : ℕ) := by
  simp [mem_minimumVolumeEnclosingEllipsoidBarrierDomain_iff]

/-- Membership in the ambient bridge domain means that the shape variable lies in the strict cone,
the shifted logarithmic argument `τ + log det H` is positive, and every ellipsoid slack
`1 - ‖H a_i - v‖²` is positive. -/
theorem mem_minimumVolumeEnclosingEllipsoidBarrierAmbientDomain_iff
    (a : ι → Eₙ) (H : SymmMat) (v : Eₙ) (τ : ℝ) :
    (H, v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierAmbientDomain a ↔
      H ∈ (𝕊^n₊₊ : Set SymmMat) ∧
        0 < τ - logDetBarrierAmbient n H ∧
          ∀ i,
            0 < 1 - ‖(H : Mat).toEuclideanLin (a i) - v‖ ^ (2 : ℕ) := by
  rfl

/-- Restricting the ambient bridge domain to a strict-cone shape recovers the source-facing
strict-domain owner. -/
@[simp] theorem mem_minimumVolumeEnclosingEllipsoidBarrierAmbientDomain_iff_strict
    (a : ι → Eₙ) (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    ((H : SymmMat), v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierAmbientDomain a ↔
      (H, v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierDomain a := by
  simp [minimumVolumeEnclosingEllipsoidBarrierAmbientDomain,
    minimumVolumeEnclosingEllipsoidBarrierDomain, logDetBarrier, logDetBarrierAmbient]

/-- The subtype of points in the strict MVEE barrier domain. This is the natural owner carrier
for the MVEE logarithmic barrier. -/
abbrev MinimumVolumeEnclosingEllipsoidBarrierPoint
    (a : ι → Eₙ) :=
  {Hvτ : 𝕊^n₊₊ × Eₙ × ℝ // Hvτ ∈ minimumVolumeEnclosingEllipsoidBarrierDomain a}

/-- The ambient formula underlying the MVEE logarithmic barrier. It is only a bridge view; the
owner barrier is `minimumVolumeEnclosingEllipsoidBarrier a` on
`MinimumVolumeEnclosingEllipsoidBarrierPoint a`. -/
def minimumVolumeEnclosingEllipsoidBarrierAmbient
    [Fintype ι] (a : ι → Eₙ) : SymmMat × Eₙ × ℝ → ℝ :=
  fun Hvτ ↦
    logDetBarrierAmbient n Hvτ.1
      - Real.log (Hvτ.2.2 - logDetBarrierAmbient n Hvτ.1)
      - ∑ i,
          Real.log (pointSlack Hvτ.1 Hvτ.2.1 (a i))

/-- Definition 5.4.5.2: the logarithmic barrier for the minimum-volume enclosing ellipsoid
problem, kept on its strict domain. -/
def minimumVolumeEnclosingEllipsoidBarrier
    [Fintype ι] (a : ι → Eₙ) : MinimumVolumeEnclosingEllipsoidBarrierPoint a → ℝ :=
  fun Hvτ ↦ minimumVolumeEnclosingEllipsoidBarrierAmbient a
    ((Hvτ.1.1 : SymmMat), Hvτ.1.2.1, Hvτ.1.2.2)

/-- Evaluating the ambient MVEE barrier recovers the canonical owner formula equivalent to the
textbook expression
`-\log \det H - \log (\tau + \log \det H) - \sum_i \log (1 - \|H a_i - v\|^2)`. -/
theorem minimumVolumeEnclosingEllipsoidBarrierAmbient_apply
    [Fintype ι] (a : ι → Eₙ) (H : SymmMat) (v : Eₙ) (τ : ℝ) :
    minimumVolumeEnclosingEllipsoidBarrierAmbient a (H, v, τ) =
      logDetBarrierAmbient n H
        - Real.log (τ - logDetBarrierAmbient n H)
        - ∑ i,
            Real.log (1 - ‖(H : Mat).toEuclideanLin (a i) - v‖ ^ (2 : ℕ)) := by
  simp [minimumVolumeEnclosingEllipsoidBarrierAmbient, pointSlack]

/-- Expanding `logDetBarrier n` rewrites the ambient MVEE barrier back to the textbook
formula `-log det H - log (τ + log det H) - \sum_i log (1 - \|H a_i - v\|^2)`. -/
theorem minimumVolumeEnclosingEllipsoidBarrierAmbient_apply_formula
    [Fintype ι] (a : ι → Eₙ) (H : SymmMat) (v : Eₙ) (τ : ℝ) :
    minimumVolumeEnclosingEllipsoidBarrierAmbient a (H, v, τ) =
      -Real.log (H : Mat).det
        - Real.log (τ + Real.log (H : Mat).det)
        - ∑ i,
            Real.log (1 - ‖(H : Mat).toEuclideanLin (a i) - v‖ ^ (2 : ℕ)) := by
  simp [minimumVolumeEnclosingEllipsoidBarrierAmbient_apply]

/-- Evaluating the MVEE barrier on a strict-domain point recovers its ambient bridge formula. -/
@[simp] theorem minimumVolumeEnclosingEllipsoidBarrier_apply
    [Fintype ι] (a : ι → Eₙ) (Hvτ : MinimumVolumeEnclosingEllipsoidBarrierPoint a) :
    minimumVolumeEnclosingEllipsoidBarrier a Hvτ =
      minimumVolumeEnclosingEllipsoidBarrierAmbient a
        ((Hvτ.1.1 : SymmMat), Hvτ.1.2.1, Hvτ.1.2.2) :=
  rfl

/-- At a strict-domain triple `(H, v, τ)`, the MVEE logarithmic barrier is the textbook
formula. -/
theorem minimumVolumeEnclosingEllipsoidBarrier_apply_triple
    [Fintype ι] (a : ι → Eₙ) (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ)
    (h : (H, v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierDomain a) :
    minimumVolumeEnclosingEllipsoidBarrier a ⟨(H, v, τ), h⟩ =
      logDetBarrier n H
        - Real.log (τ - logDetBarrier n H)
        - ∑ i,
            Real.log (1 - ‖((H : SymmMat) : Mat).toEuclideanLin (a i) - v‖ ^ (2 : ℕ)) := by
  simp [minimumVolumeEnclosingEllipsoidBarrier, minimumVolumeEnclosingEllipsoidBarrierAmbient,
    pointSlack, logDetBarrier, logDetBarrierAmbient]

/-- At a strict-domain triple `(H, v, τ)`, the MVEE logarithmic barrier is the textbook formula
`-log det H - log (τ + log det H) - \sum_i log (1 - \|H a_i - v\|^2)`. -/
theorem minimumVolumeEnclosingEllipsoidBarrier_apply_triple_formula
    [Fintype ι] (a : ι → Eₙ) (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ)
    (h : (H, v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierDomain a) :
    minimumVolumeEnclosingEllipsoidBarrier a ⟨(H, v, τ), h⟩ =
      -Real.log (((H : SymmMat) : Mat).det)
        - Real.log (τ + Real.log (((H : SymmMat) : Mat).det))
        - ∑ i,
            Real.log (1 - ‖((H : SymmMat) : Mat).toEuclideanLin (a i) - v‖ ^ (2 : ℕ)) := by
  rw [minimumVolumeEnclosingEllipsoidBarrier_apply_triple]
  simp

end

/-! ### Definition_5_4_5_3 (from Chap05) -/
noncomputable section

open MeasureTheory Matrix
open StrictPositiveSemidefiniteCone
open scoped EllipsoidNotation RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/-
Definition 5.4.5.3 lies in the Euclidean ellipsoid / polyhedral convex-geometry domain.

Sampled owner-style declarations:
* `innerLePolyhedron` and `mem_innerLePolyhedron_iff` in `Chap03/Definition_3_62`, the project
  owner/view for a set cut out by finitely many inequalities `⟪a i, x⟫ ≤ b i`;
* `affineEllipsoid` and the notation `E(H, x̄)` in `Chap03/Lemma_3_2_7`, the chapter owner for a
  matrix-defined ellipsoid centered at `x̄`;
* `mem_affineEllipsoid_iff` in the same file, the canonical companion view of ellipsoid
  membership;
* `𝕊^n₊₊` and `strictPositiveSemidefiniteCone_posDef` in `Chap05/Definition_5_4_4_5`, the
  chapter owner/bridge for positive-definite ellipsoid shapes;
* `IsMaximalVolumeInscribedEllipsoid` in `Chap03/Definition_3_61`, the nearby all-centers maximal
  inscribed-ellipsoid predicate built on the same owner ellipsoid.

Best owner abstraction:
* source-facing: the fixed-center maximality predicate `IsMaximumVolumeEllipsoidIn`;
* core/canonical owners: the strict-cone shape owner `𝕊^n₊₊` and the centered ellipsoid owner
  `affineEllipsoid`;
* bridge/view: the owner-level matrix realization
  `StrictPositiveSemidefiniteCone.toMatrix H` of a strict-cone point.

Primitive data:
* the ambient set `Q : Set E`;
* the center `v : E`;
* a candidate shape `H : 𝕊^n₊₊`.

Derived API:
* the candidate ellipsoid `E(toMatrix H, v)`;
* the derived positive-definite bridge `strictPositiveSemidefiniteCone_posDef H`;
* the derived interiority consequence `v ∈ interior Q`;
* the containment and volume-maximality statements for that owner ellipsoid;
* any textbook set-level phrase “the ellipsoid `W` centered at `v`” via the derived identity
  `W = E(toMatrix H, v)`.

This file therefore keeps only the source-facing fixed-center maximality notion stated directly on
the existing ellipsoid owner `E(toMatrix H, v)`, while lifting the primitive shape data to the
intrinsic Chapter 5 strict-cone owner `𝕊^n₊₊` instead of storing a raw matrix together with a
separate positive-definiteness field.
-/

/-- Definition 5.4.5.3: the ellipsoid `E(toMatrix H, v)` is a maximum-volume ellipsoid in `Q`
centered at `v` when it lies inside `Q`, and no other ellipsoid with the same center `v` and
strict-cone shape parameter has larger volume. The positive-definite matrix view of `H` is the
derived bridge `strictPositiveSemidefiniteCone_posDef H`. -/
structure IsMaximumVolumeEllipsoidIn
    (Q : Set E) (v : E) (H : 𝕊^n₊₊) : Prop where
  /-- The candidate ellipsoid lies inside `Q`. -/
  subset : E(toMatrix H, v) ⊆ Q
  /-- No other ellipsoid centered at `v` and contained in `Q` has larger volume. -/
  volume_maximal {shape' : 𝕊^n₊₊}
      (hsubset' : E(toMatrix shape', v) ⊆ Q) :
      volume (E(toMatrix shape', v)) ≤ volume (E(toMatrix H, v))

namespace IsMaximumVolumeEllipsoidIn

/-- The center of a maximum-volume ellipsoid in `Q` is automatically an interior point of `Q`. -/
theorem center_mem_interior
    {Q : Set E} {v : E} {H : 𝕊^n₊₊}
    (hH : IsMaximumVolumeEllipsoidIn Q v H) :
    v ∈ interior Q := by
  have hPos : (toMatrix H).PosDef := by
    simpa [toMatrix_def] using strictPositiveSemidefiniteCone_posDef H
  have hcenter : v ∈ interior (E(toMatrix H, v) : Set E) :=
    center_mem_interior_affineEllipsoid (toMatrix H) v hPos
  exact interior_mono hH.subset hcenter

end IsMaximumVolumeEllipsoidIn

end

/-! ### Definition_5_4_5_4 (from Chap05) -/
noncomputable section

open Matrix
open StrictPositiveSemidefiniteCone
open scoped EllipsoidNotation RealInnerProductSpace RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Definition 5.4.5.4 lies in the symmetric-positive-definite ellipsoid / constrained-minimization
domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem` and `SetConstrainedMinimizationProblem.coe_apply` in
  `Chap01/Definition_1_3_3`, the project owner and evaluation view for constrained minimization
  problems;
* `constrainedEpigraph` and `mem_constrainedEpigraph_iff` in `Chap03/Definition_3_3`, the
  chapter owner/view for epigraph feasible sets built from primitive base constraints and an
  objective;
* `innerLePolyhedron` and `mem_innerLePolyhedron_iff` in `Chap03/Definition_3_62`, the project
  owner/view for the half-space intersection cut out by `⟪aᵢ, x⟫ ≤ bᵢ`;
* `affineEllipsoid`, the notation `E(H, v)`, and `center_mem_affineEllipsoid` in
  `Chap03/Lemma_3_2_7`, the chapter owner/view for the ellipsoid centered at `v`;
* `𝕊^n₊₊` in `Definition_5_4_4_5`, the intrinsic strict-cone owner for positive-definite shape
  matrices;
* `affine_le_on_affineEllipsoid_iff` in `Lemma_5_4_5_1`, the chapter bridge from ellipsoid
  containment in one half-space to the quadratic inequality plus the center-slack sign condition.

Best owner abstraction:
* source-facing: the circumscribed-ellipsoid shape set on `H : 𝕊^n₊₊`, expressed by the textbook
  quadratic inequalities `⟪H aᵢ, aᵢ⟫ ≤ (bᵢ - ⟪aᵢ, v⟫)^2`, together with its epigraph
  reformulation in the variables `(H, τ)`;
* core/canonical: `constrainedEpigraph` over the primitive shape set and the owner
  `SetConstrainedMinimizationProblem (𝕊^n₊₊ × ℝ)`;
* bridge/view: the objective-evaluation lemma together with the containment bridge theorems below,
  which compare the source-facing quadratic owner to the geometric condition
  `E(H, v) ⊆ innerLePolyhedron a b` under the explicit center-slack hypotheses needed by
  `affine_le_on_affineEllipsoid_iff`.

Primitive data:
* the half-space data `a`, `b`, the center `v`, and the quadratic inequalities on `𝕊^n₊₊`.

Derived API:
* the epigraph feasible set built by `constrainedEpigraph`;
* the packaged optimization problem with objective `Prod.snd`;
* the bridge lemmas identifying its objective and relating the quadratic constraints to geometric
  containment when the center satisfies the half-space inequalities.

This file therefore keeps the source-facing quadratic feasible set on the intrinsic strict-cone
owner `𝕊^n₊₊`, and treats geometric containment only as a companion bridge under the explicit
center-slack assumptions from Lemma `5.4.5.1`.
-/

/-- The primitive shape set of the circumscribed-ellipsoid reformulation consists of
positive-definite shapes `H : 𝕊ⁿ₊₊` satisfying the textbook quadratic constraints
`⟪H aᵢ, aᵢ⟫ ≤ (bᵢ - ⟪aᵢ, v⟫)^2`. -/
def circumscribedEllipsoidShapeSet
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) : Set 𝕊^n₊₊ :=
  {H | ∀ i : Fin m,
    ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ ≤
      (b i - ⟪a i, v⟫) ^ (2 : ℕ)}

/-- Membership in the primitive circumscribed-ellipsoid shape set is exactly the textbook
quadratic constraint family. -/
@[simp] theorem mem_circumscribedEllipsoidShapeSet_iff
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) :
    H ∈ circumscribedEllipsoidShapeSet a b v ↔
      ∀ i : Fin m,
        ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ ≤
          (b i - ⟪a i, v⟫) ^ (2 : ℕ) :=
  Iff.rfl

/-- Geometric containment of the ellipsoid `E(H, v)` in the half-space intersection
`innerLePolyhedron a b` implies the source-facing quadratic constraints. -/
theorem mem_circumscribedEllipsoidShapeSet_of_subset_innerLePolyhedron
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) :
    E(toMatrix H, v) ⊆ innerLePolyhedron a b →
      H ∈ circumscribedEllipsoidShapeSet a b v := by
  intro hsubset
  rw [mem_circumscribedEllipsoidShapeSet_iff]
  intro i
  have hhalfspace : ∀ x ∈ E(toMatrix H, v), ⟪a i, x⟫ ≤ b i := by
    intro x hx
    exact (mem_innerLePolyhedron_iff a b).1 (hsubset hx) i
  have hcenter : ⟪a i, v⟫ ≤ b i := by
    exact hhalfspace v (center_mem_affineEllipsoid (toMatrix H) v)
  have hslack : 0 ≤ b i - ⟪a i, v⟫ := sub_nonneg.mpr hcenter
  have hPosDef : (toMatrix H).PosDef := by
    simpa [toMatrix_def] using strictPositiveSemidefiniteCone_posDef H
  have hquad :
      ⟪a i, (toMatrix H).toEuclideanLin (a i)⟫ ≤
        (b i - ⟪a i, v⟫) ^ (2 : ℕ) :=
    (affine_le_on_affineEllipsoid_iff (a i) v (b i) (toMatrix H) hslack hPosDef).1 hhalfspace
  simpa [real_inner_comm] using hquad

/-- Under the explicit center-slack hypotheses `⟪aᵢ, v⟫ ≤ bᵢ`, the source-facing quadratic
constraints imply the geometric containment `E(H, v) ⊆ innerLePolyhedron a b`. -/
theorem subset_innerLePolyhedron_of_mem_circumscribedEllipsoidShapeSet
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊)
    (hcenter : ∀ i : Fin m, ⟪a i, v⟫ ≤ b i)
    (hH : H ∈ circumscribedEllipsoidShapeSet a b v) :
    E(toMatrix H, v) ⊆ innerLePolyhedron a b := by
  intro x hx
  rw [mem_innerLePolyhedron_iff]
  intro i
  have hslack : 0 ≤ b i - ⟪a i, v⟫ := sub_nonneg.mpr (hcenter i)
  have hPosDef : (toMatrix H).PosDef := by
    simpa [toMatrix_def] using strictPositiveSemidefiniteCone_posDef H
  have hquad :
      ⟪a i, (toMatrix H).toEuclideanLin (a i)⟫ ≤
        (b i - ⟪a i, v⟫) ^ (2 : ℕ) := by
    have hi := (mem_circumscribedEllipsoidShapeSet_iff a b v H).1 hH i
    simpa [real_inner_comm] using hi
  exact
    (affine_le_on_affineEllipsoid_iff (a i) v (b i) (toMatrix H) hslack hPosDef).2 hquad x hx

/-- Under the explicit center-slack hypotheses `⟪aᵢ, v⟫ ≤ bᵢ`, the source-facing quadratic
constraints are equivalent to geometric containment of the ellipsoid in the half-space
intersection. -/
theorem mem_circumscribedEllipsoidShapeSet_iff_subset_innerLePolyhedron
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊)
    (hcenter : ∀ i : Fin m, ⟪a i, v⟫ ≤ b i) :
    H ∈ circumscribedEllipsoidShapeSet a b v ↔
      E(toMatrix H, v) ⊆ innerLePolyhedron a b := by
  constructor
  · exact subset_innerLePolyhedron_of_mem_circumscribedEllipsoidShapeSet a b v H hcenter
  · exact mem_circumscribedEllipsoidShapeSet_of_subset_innerLePolyhedron a b v H

/-- Definition 5.4.5.4: the circumscribed-ellipsoid optimization problem minimizes the auxiliary
variable `τ` over pairs `(H, τ)` satisfying `H ∈ 𝕊ⁿ₊₊`, `logDetBarrier n H ≤ τ`, and the
textbook quadratic constraints
`⟪H aᵢ, aᵢ⟫ ≤ (bᵢ - ⟪aᵢ, v⟫)^2`. The geometric containment formulation is kept only as a bridge
under the explicit center-slack hypotheses. -/
def circumscribedEllipsoidOptimizationProblem
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) :
    SetConstrainedMinimizationProblem (𝕊^n₊₊ × ℝ) where
  feasibleSet := constrainedEpigraph
    (circumscribedEllipsoidShapeSet a b v)
    fun H ↦ (logDetBarrier n H : WithTop ℝ)
  objective := Prod.snd

/-- Evaluating the objective of the circumscribed-ellipsoid optimization problem returns the
auxiliary scalar variable `τ`. -/
@[simp] theorem circumscribedEllipsoidOptimizationProblem_objective_apply
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ) :
    circumscribedEllipsoidOptimizationProblem a b v (H, τ) = τ :=
  rfl

/-- Membership in the feasible set of the circumscribed-ellipsoid optimization problem is exactly
the conjunction of the chapter-owner determinant barrier and the textbook quadratic constraints,
with the strict cone condition absorbed into the ambient owner `𝕊ⁿ₊₊ × ℝ`. -/
@[simp] theorem mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ) :
    (H, τ) ∈ (circumscribedEllipsoidOptimizationProblem a b v).feasibleSet ↔
      logDetBarrier n H ≤ τ ∧
        ∀ i : Fin m,
          ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ ≤
            (b i - ⟪a i, v⟫) ^ (2 : ℕ) := by
  change (H, τ) ∈ constrainedEpigraph
      (circumscribedEllipsoidShapeSet a b v)
      (fun H ↦ (logDetBarrier n H : WithTop ℝ)) ↔
    logDetBarrier n H ≤ τ ∧
      ∀ i : Fin m,
        ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ ≤
          (b i - ⟪a i, v⟫) ^ (2 : ℕ)
  rw [mem_constrainedEpigraph_iff, mem_circumscribedEllipsoidShapeSet_iff]
  constructor
  · rintro ⟨hshape, hτ⟩
    exact ⟨by exact_mod_cast hτ, hshape⟩
  · rintro ⟨hτ, hshape⟩
    exact ⟨hshape, by exact_mod_cast hτ⟩

/-- Under the explicit center-slack hypotheses `⟪aᵢ, v⟫ ≤ bᵢ`, feasible points for the
circumscribed-ellipsoid optimization problem are exactly those satisfying the determinant bound
and the geometric containment `E(H, v) ⊆ innerLePolyhedron a b`. -/
theorem mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff_subset_innerLePolyhedron
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ)
    (hcenter : ∀ i : Fin m, ⟪a i, v⟫ ≤ b i) :
    (H, τ) ∈ (circumscribedEllipsoidOptimizationProblem a b v).feasibleSet ↔
      logDetBarrier n H ≤ τ ∧
        E(toMatrix H, v) ⊆ innerLePolyhedron a b := by
  rw [mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff]
  constructor
  · rintro ⟨hτ, hshape⟩
    exact
      ⟨hτ, subset_innerLePolyhedron_of_mem_circumscribedEllipsoidShapeSet a b v H hcenter hshape⟩
  · rintro ⟨hτ, hshape⟩
    exact ⟨hτ, mem_circumscribedEllipsoidShapeSet_of_subset_innerLePolyhedron a b v H hshape⟩

/-- Expanding the owner determinant barrier rewrites circumscribed-ellipsoid feasibility back to
the textbook `-log det` inequality together with the quadratic constraints. -/
theorem mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff_formula
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ) :
    (H, τ) ∈ (circumscribedEllipsoidOptimizationProblem a b v).feasibleSet ↔
      -Real.log (toMatrix H).det ≤ τ ∧
        ∀ i : Fin m,
          ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ ≤
            (b i - ⟪a i, v⟫) ^ (2 : ℕ) := by
  rw [mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff, logDetBarrier_apply]
  simp [toMatrix_def]

end

/-! ### Definition_5_4_5_5 (from Chap05) -/
noncomputable section

open Matrix
open StrictPositiveSemidefiniteCone
open scoped BigOperators RealInnerProductSpace RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n

private abbrev quadraticSlack
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : SymmMat) (i : Fin m) : ℝ :=
  (b i - ⟪a i, v⟫) ^ (2 : ℕ) - ⟪(H : Mat).toEuclideanLin (a i), a i⟫

/- Definition 5.4.5.5 lies in the circumscribed-ellipsoid / logarithmic-barrier domain.

Sampled owner-style declarations in this domain:
* `logDetBarrier` and `logDetBarrier_apply` in `Chap05/Definition_5_4_4_5`, the chapter owner of
  the `-log det` contribution on `𝕊^n₊₊`;
* `circumscribedEllipsoidShapeSet` and
  `mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff` in
  `Chap05/Definition_5_4_5_4`, the adjacent primitive shape constraints and their nonstrict
  epigraph reformulation;
* `minimumVolumeEnclosingEllipsoidBarrier` and
  `MinimumVolumeEnclosingEllipsoidBarrierPoint` in `Chap05/Definition_5_4_5_2`, the chapter
  barrier-owner pattern on a strict-domain subtype;
* `semidefiniteAffineLogDetBarrier` and `SemidefiniteAffineBarrierPoint` in
  `Chap05/Definition_5_4_4_8`, the same log-determinant barrier pattern on a pullback strict
  domain;
* `Matrix.toEuclideanLin` in `Chap05/Definition_5_0_6`, the canonical linear-operator owner for a
  matrix acting on `EuclideanSpace ℝ (Fin n)`;
* `inner ℝ` and `EuclideanSpace.inner_eq_star_dotProduct` in `Chap01/Definition_1_4_4`, the
  owner/bridge pair showing that the quadratic term should live in the intrinsic inner-product
  language, with `dotProduct` only as its coordinate realization.

Source/core/bridge triage:
* source-facing: the strict circumscribed-ellipsoid barrier domain and barrier;
* core/canonical: `logDetBarrier n` on `𝕊^n₊₊`;
* bridge/view: the ambient pair domain
  `circumscribedEllipsoidBarrierAmbientDomain` and formula
  `circumscribedEllipsoidBarrierAmbient` on `𝕊^n × ℝ`.

Primitive data:
* the half-space data `a`, `b`, and the fixed center `v`.

Derived API:
* the strict domain `circumscribedEllipsoidBarrierDomain a b v`;
* the strict-domain carrier `CircumscribedEllipsoidBarrierPoint a b v`;
* the ambient bridge domain `circumscribedEllipsoidBarrierAmbientDomain a b v`;
* the ambient bridge formula `circumscribedEllipsoidBarrierAmbient a b v`;
* the source-facing barrier `circumscribedEllipsoidBarrier a b v`.

This file therefore reuses the chapter owner `logDetBarrier` for the determinant contribution and
keeps the raw formula only as a bridge, instead of maintaining a parallel ambient barrier owner on
all pairs `(H, τ)`.
-/

/-- The strict domain on which the circumscribed-ellipsoid logarithmic barrier is defined. -/
def circumscribedEllipsoidBarrierDomain
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) : Set (𝕊^n₊₊ × ℝ) :=
  {Hτ | 0 < Hτ.2 - logDetBarrier n Hτ.1 ∧
    ∀ i : Fin m, 0 < quadraticSlack a b v Hτ.1 i}

/-- The ambient pullback domain of the circumscribed-ellipsoid logarithmic barrier on
`𝕊ⁿ × ℝ`. It is a bridge/view that records strict positivity of the shape variable together with
the same strict slack inequalities used by the source-facing strict-domain owner
`circumscribedEllipsoidBarrierDomain a b v`. -/
def circumscribedEllipsoidBarrierAmbientDomain
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) : Set (SymmMat × ℝ) :=
  {Hτ | Hτ.1 ∈ (𝕊^n₊₊ : Set SymmMat) ∧
    0 < Hτ.2 - logDetBarrierAmbient n Hτ.1 ∧
      ∀ i : Fin m, 0 < quadraticSlack a b v Hτ.1 i}

/-- Membership in the barrier domain means that the shifted logarithmic argument
`τ - logDetBarrier n H = τ + log det H` is positive and every quadratic slack
`(bᵢ - ⟪aᵢ, v⟫)^2 - ⟪H aᵢ, aᵢ⟫` is positive. -/
theorem mem_circumscribedEllipsoidBarrierDomain_iff
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ) :
    (H, τ) ∈ circumscribedEllipsoidBarrierDomain a b v ↔
      0 < τ - logDetBarrier n H ∧
        ∀ i : Fin m,
          0 < (b i - ⟪a i, v⟫) ^ (2 : ℕ) -
            ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ := by
  simp [circumscribedEllipsoidBarrierDomain, quadraticSlack, toMatrix_def]

/-- Membership in the ambient bridge domain means that the shape variable lies in the strict
cone, the shifted logarithmic argument `τ + log det H` is positive, and every quadratic slack
`(bᵢ - ⟪aᵢ, v⟫)^2 - ⟪H aᵢ, aᵢ⟫` is positive. -/
theorem mem_circumscribedEllipsoidBarrierAmbientDomain_iff
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : SymmMat) (τ : ℝ) :
    (H, τ) ∈ circumscribedEllipsoidBarrierAmbientDomain a b v ↔
      H ∈ (𝕊^n₊₊ : Set SymmMat) ∧
        0 < τ - logDetBarrierAmbient n H ∧
          ∀ i : Fin m,
            0 < (b i - ⟪a i, v⟫) ^ (2 : ℕ) -
              ⟪(H : Mat).toEuclideanLin (a i), a i⟫ := by
  rfl

/-- Restricting the ambient bridge domain to a strict-cone shape recovers the source-facing
strict-domain owner. -/
@[simp] theorem mem_circumscribedEllipsoidBarrierAmbientDomain_iff_strict
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ) :
    ((H : SymmMat), τ) ∈ circumscribedEllipsoidBarrierAmbientDomain a b v ↔
      (H, τ) ∈ circumscribedEllipsoidBarrierDomain a b v := by
  simp [circumscribedEllipsoidBarrierAmbientDomain, circumscribedEllipsoidBarrierDomain,
    logDetBarrier, logDetBarrierAmbient]

/-- Expanding `logDetBarrier n` rewrites barrier-domain membership back to the textbook
`τ + log det H` formula. -/
theorem mem_circumscribedEllipsoidBarrierDomain_iff_formula
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ) :
    (H, τ) ∈ circumscribedEllipsoidBarrierDomain a b v ↔
      0 < τ + Real.log (toMatrix H).det ∧
        ∀ i : Fin m,
          0 < (b i - ⟪a i, v⟫) ^ (2 : ℕ) -
            ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ := by
  simp [mem_circumscribedEllipsoidBarrierDomain_iff, toMatrix_def]

/-- The subtype of points in the strict circumscribed-ellipsoid barrier domain. This is the
natural owner carrier for the circumscribed-ellipsoid logarithmic barrier. -/
abbrev CircumscribedEllipsoidBarrierPoint
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) :=
  {Hτ : 𝕊^n₊₊ × ℝ // Hτ ∈ circumscribedEllipsoidBarrierDomain a b v}

/-- The ambient formula underlying the circumscribed-ellipsoid logarithmic barrier. It is only a
bridge view; the owner barrier is `circumscribedEllipsoidBarrier a b v` on
`CircumscribedEllipsoidBarrierPoint a b v`. -/
def circumscribedEllipsoidBarrierAmbient
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) : SymmMat × ℝ → ℝ :=
  fun Hτ ↦
    logDetBarrierAmbient n Hτ.1
      - Real.log (Hτ.2 - logDetBarrierAmbient n Hτ.1)
      - ∑ i : Fin m, Real.log (quadraticSlack a b v Hτ.1 i)

/-- Definition 5.4.5.5: the logarithmic barrier for the circumscribed-ellipsoid reformulation,
kept on its strict domain. -/
def circumscribedEllipsoidBarrier
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) :
    CircumscribedEllipsoidBarrierPoint a b v → ℝ :=
  fun Hτ ↦ circumscribedEllipsoidBarrierAmbient a b v ((Hτ.1.1 : SymmMat), Hτ.1.2)

/-- Evaluating the ambient circumscribed-ellipsoid barrier recovers the owner formula equivalent
to the textbook expression
`-log det H - log (τ + log det H) - \sum_i log ((bᵢ - ⟪aᵢ, v⟫)^2 - aᵢᵀ H aᵢ)`. -/
theorem circumscribedEllipsoidBarrierAmbient_apply
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : SymmMat) (τ : ℝ) :
    circumscribedEllipsoidBarrierAmbient a b v (H, τ) =
      logDetBarrierAmbient n H
        - Real.log (τ - logDetBarrierAmbient n H)
        - ∑ i : Fin m,
            Real.log
              ((b i - ⟪a i, v⟫) ^ (2 : ℕ) -
                ⟪(H : Mat).toEuclideanLin (a i), a i⟫) := by
  simp [circumscribedEllipsoidBarrierAmbient, quadraticSlack]

/-- On a strict-cone slice, the ambient circumscribed-ellipsoid barrier agrees with the owner
formula built from `logDetBarrier n`. -/
theorem circumscribedEllipsoidBarrierAmbient_apply_strict
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ) :
    circumscribedEllipsoidBarrierAmbient a b v ((H : SymmMat), τ) =
      logDetBarrier n H
        - Real.log (τ - logDetBarrier n H)
        - ∑ i : Fin m,
            Real.log
              ((b i - ⟪a i, v⟫) ^ (2 : ℕ) -
                ⟪(toMatrix H).toEuclideanLin (a i), a i⟫) := by
  simp [circumscribedEllipsoidBarrierAmbient_apply, toMatrix_def]

/-- Evaluating the circumscribed-ellipsoid barrier on a strict-domain point recovers its ambient
bridge formula. -/
@[simp] theorem circumscribedEllipsoidBarrier_apply
    (a : Fin m → E) (b : Fin m → ℝ) (v : E)
    (Hτ : CircumscribedEllipsoidBarrierPoint a b v) :
    circumscribedEllipsoidBarrier a b v Hτ =
      circumscribedEllipsoidBarrierAmbient a b v ((Hτ.1.1 : SymmMat), Hτ.1.2) :=
  rfl

/-- At a strict-domain pair `(H, τ)`, the circumscribed-ellipsoid logarithmic barrier is the
owner formula built from the chapter determinant barrier `logDetBarrier n`. -/
theorem circumscribedEllipsoidBarrier_apply_pair
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ)
    (h : (H, τ) ∈ circumscribedEllipsoidBarrierDomain a b v) :
    circumscribedEllipsoidBarrier a b v ⟨(H, τ), h⟩ =
      logDetBarrier n H
        - Real.log (τ - logDetBarrier n H)
        - ∑ i : Fin m,
            Real.log
              ((b i - ⟪a i, v⟫) ^ (2 : ℕ) -
                ⟪(toMatrix H).toEuclideanLin (a i), a i⟫) := by
  simpa [toMatrix_def] using circumscribedEllipsoidBarrierAmbient_apply_strict a b v H τ

/-- Expanding `logDetBarrier n` rewrites the circumscribed-ellipsoid barrier back to the textbook
formula `-log det H - log (τ + log det H) - \sum_i log ((bᵢ - ⟪aᵢ, v⟫)^2 - aᵢᵀ H aᵢ)`. -/
theorem circumscribedEllipsoidBarrier_apply_pair_formula
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ)
    (h : (H, τ) ∈ circumscribedEllipsoidBarrierDomain a b v) :
    circumscribedEllipsoidBarrier a b v ⟨(H, τ), h⟩ =
      -Real.log (toMatrix H).det
        - Real.log (τ + Real.log (toMatrix H).det)
        - ∑ i : Fin m,
            Real.log
              ((b i - ⟪a i, v⟫) ^ (2 : ℕ) -
                ⟪(toMatrix H).toEuclideanLin (a i), a i⟫) := by
  rw [circumscribedEllipsoidBarrier_apply_pair]
  simp [toMatrix_def]

end
