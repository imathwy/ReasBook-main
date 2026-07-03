import LecturesConvexOptimization_Nesterov_2018.Chap05.Alg_5_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

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
