import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_10 (from Chap07) -/
noncomputable section

open Matrix
open scoped SupportFunction

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-- Definition 7.10: a support-function minimization problem consists of a closed bounded convex
set `Q₂ ⊆ ℝᵐ` with `0 ∈ interior Q₂`, a matrix `A ∈ ℝ^(m × n)` with full column rank, and a
closed convex set `Q₁ ⊆ ℝⁿ`; its canonical support-function objective is `x ↦ ξ[Q₂] (A x)`, and
the associated real-valued minimization objective is obtained from that Chapter 3 owner by the
standard `toReal` bridge. -/
structure SupportFunctionOptimizationProblem (m n : ℕ) where
  /-- The closed bounded convex set `Q₂ ⊆ ℝᵐ` defining the support function. -/
  Q2 : Set (EuclideanSpace ℝ (Fin m))
  /-- The set `Q₂` is closed. -/
  Q2_closed : IsClosed Q2
  /-- The set `Q₂` is bounded. -/
  Q2_bounded : Bornology.IsBounded Q2
  /-- The set `Q₂` is convex. -/
  Q2_convex : Convex ℝ Q2
  /-- The origin belongs to the interior of `Q₂`. -/
  zero_mem_interior_Q2 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior Q2
  /-- The matrix `A ∈ ℝ^(m × n)` defining the linear map `x ↦ A x`. -/
  A : Matrix (Fin m) (Fin n) ℝ
  /-- The matrix `A` has full column rank, encoded as injectivity of its Euclidean linear map. -/
  A_full_column_rank : Function.Injective (Matrix.toEuclideanLin A)
  /-- The closed convex feasible set `Q₁ ⊆ ℝⁿ`. -/
  Q1 : Set (EuclideanSpace ℝ (Fin n))
  /-- The feasible set `Q₁` is closed. -/
  Q1_closed : IsClosed Q1
  /-- The feasible set `Q₁` is convex. -/
  Q1_convex : Convex ℝ Q1

namespace SupportFunctionOptimizationProblem

/-- The support set `Q₂`, viewed as the canonical convex-body owner used by the Chapter 7 support
radius API. -/
def supportBody (problem : SupportFunctionOptimizationProblem m n) : ConvexBody Eₘ where
  carrier := problem.Q2
  convex' := problem.Q2_convex
  isCompact' := by
    simpa using Metric.isCompact_of_isClosed_isBounded problem.Q2_closed problem.Q2_bounded
  nonempty' := ⟨0, interior_subset problem.zero_mem_interior_Q2⟩

@[simp] theorem coe_supportBody (problem : SupportFunctionOptimizationProblem m n) :
    (problem.supportBody : Set Eₘ) = problem.Q2 :=
  rfl

/-- The canonical Chapter 3 support-function objective `x ↦ ξ[Q₂] (A x)`. -/
def objectiveEReal (problem : SupportFunctionOptimizationProblem m n) : Eₙ → EReal :=
  ξ[problem.Q2] ∘ Matrix.toEuclideanLin problem.A

@[simp] theorem objectiveEReal_apply (problem : SupportFunctionOptimizationProblem m n) (x : Eₙ) :
    problem.objectiveEReal x = ξ[problem.Q2] (Matrix.toEuclideanLin problem.A x) :=
  rfl

/-- The real-valued objective used by the Chapter 1 constrained minimization owner. -/
def objective (problem : SupportFunctionOptimizationProblem m n) : Eₙ → ℝ :=
  fun x ↦ (problem.objectiveEReal x).toReal

@[simp] theorem objective_apply (problem : SupportFunctionOptimizationProblem m n) (x : Eₙ) :
    problem.objective x = (ξ[problem.Q2] (Matrix.toEuclideanLin problem.A x)).toReal :=
  rfl

/-- The canonical set-constrained minimization owner attached to the support-function problem. -/
def toSetConstrainedMinimizationProblem
    (problem : SupportFunctionOptimizationProblem m n) :
    SetConstrainedMinimizationProblem Eₙ where
  feasibleSet := problem.Q1
  objective := problem.objective

@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : SupportFunctionOptimizationProblem m n) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.Q1 :=
  rfl

@[simp] theorem toSetConstrainedMinimizationProblem_objective
    (problem : SupportFunctionOptimizationProblem m n) :
    problem.toSetConstrainedMinimizationProblem.objective = problem.objective :=
  rfl

@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : SupportFunctionOptimizationProblem m n) (x : Eₙ) :
    problem.toSetConstrainedMinimizationProblem x = problem.objective x :=
  rfl

/-- A support-function optimization problem can be used as its objective function `x ↦ F(Ax)`. -/
instance : CoeFun (SupportFunctionOptimizationProblem m n) (fun _ ↦ Eₙ → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

@[simp] theorem coe_apply (problem : SupportFunctionOptimizationProblem m n) (x : Eₙ) :
    problem x = problem.objective x :=
  rfl

/-- The Chapter 1 owner optimal value of the support-function minimization problem is the infimum
of the real-valued bridge objective on the feasible set `Q₁`, viewed in `EReal`. -/
theorem optimalValue_eq_sInf_image (problem : SupportFunctionOptimizationProblem m n) :
    problem.toSetConstrainedMinimizationProblem.optimalValue =
      sInf ((fun x ↦ (problem.objective x : EReal)) '' problem.Q1) := by
  simpa using problem.toSetConstrainedMinimizationProblem.optimalValue_eq_sInf_image

end SupportFunctionOptimizationProblem

end

/-! ### Lemma_7_10 (from Chap07) -/
open scoped Gradient HessianDualLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 7.10 lies in the Chapter 7 barrier-smoothed support-function / self-concordant upper-model
domain.

Mandatory domain-style sampling before refinement:
- `Uβ` and `Argmaxβ` in `Chap07/Definition_7_53`, the Chapter 7 source-facing owners of the
  smoothed support-function value and its canonical argmax set;
- `smoothedPrimalObjectiveArgmax_unique` in `Chap06/Proposition_6_24` and
  `supportFunctionApproximation_hasFDerivAt_of_unique_argmax` in `Chap07/Proposition_7_28`, the
  owner-level uniqueness and derivative bridge for the positive support-function smoothing problem;
- `Uβ_apply` in `Chap07/Definition_7_53`, the source-facing expansion theorem for `U_β`;
- `IsSelfConcordantBarrierOnWith` in `Chap05/Definition_5_3_2`, the chapter owner for the
  self-concordant barrier structure on `interior Q`;
- `dualLocalNorm` and the determinant bridge `HessianDualLocalNorm.ofDetNeZero` in
  `Chap05/Definition_5_0_20`, the canonical owner of the Hessian dual local norm;
- `selfConcordant_value_bounds_of_dualLocalNorm_gradient_sub` in `Chap05/Theorem_5_1_12`, the
  owner-level Chapter 5 upper/lower value estimate that actually justifies the `ω_*` remainder;
- `ω_*` in `Chap05/Definition_5_0_21`, the canonical Chapter 5 owner of the self-concordant upper
  remainder term.

Best owner abstraction:
- source-facing: Lemma 7.10's derivative identification and upper model for the specialized
  support-function approximation `U_β`;
- core/canonical: `Uβ`, `Argmaxβ`,
  `IsSelfConcordantBarrierOnWith (interior Q) ν F`,
  `HessianDualLocalNorm.ofDetNeZero F x hPos hH g`, and `ω_*`;
- bridge/view: the derivative bridge from unique argmax data together with the Hilbert-space
  evaluation map `x - x₀`.

Primitive data:
- the feasible set `hatP`, ambient barrier set `Q`, barrier `F`, base point `x₀`, and smoothing
  parameter `β`;
- the active maximizer `x` at the dual point `s`;
- the self-concordant barrier owner on `interior Q`;
- the local Hessian nondegeneracy data at `x`.

Derived API:
- the smoothed support-function value owner `Uβ`;
- the argmax predicate owner `Argmaxβ`;
- the local Hessian positivity at `x`, derived from the barrier owner and `hx_int`;
- the local perturbation size `HessianDualLocalNorm.ofDetNeZero F x hPos hH g`;
- the self-concordant remainder `ω_*`.

This lemma stays source-facing: it adds the support-function-specific derivative and perturbation
statement, so it should not collapse to the more general Chapter 6 owner theorem. The refinement
therefore keeps the local statement but rewrites its public surface to the existing owner
abstractions instead of mixing raw `fderiv`/logarithm formulas with the chapter owners. The
Fréchet-derivative clause must still pass through the unique-argmax bridge; the barrier-local
interior and Hessian hypotheses control only the self-concordant upper model, not uniqueness of
the maximizer in the canonical argmax owner.
-/

section

variable (hatP Q : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β})
-- Proof sketch: under the additional owner-level uniqueness hypothesis on `x` inside
-- `Argmaxβ hatP F β s`, apply the Chapter 7 unique-argmax derivative bridge to identify the
-- Fréchet derivative of `Uβ hatP F x0 β` as evaluation at `x - x0`. For the upper
-- model, compare the value at `s + g` with the value at the maximizer `x`, use the Chapter 5
-- self-concordant barrier owner on `interior Q` to derive the needed local Hessian positivity and
-- value bound for `F`, estimate the linear term by the local dual norm
-- `HessianDualLocalNorm.ofDetNeZero F x hPos hH g`, and then invoke the Fenchel conjugacy
-- between the self-concordant auxiliary functions `ω` and `ω_*`.
/-- Lemma 7.10: if `x` is the barrier-regularized maximizer defining `U_β(s)` and lies in the
strict barrier domain, then uniqueness of `x` in the canonical argmax owner at `s` yields the
Fréchet derivative formula `D U_β(s) = ev_{x - x0}`. Moreover, if `F` is a
self-concordant barrier on `interior Q`, then every perturbation `g` with local dual norm
`HessianDualLocalNorm.ofDetNeZero F x hPos hH g < β` satisfies the upper model
`U_β(s + g) ≤ U_β(s) + g (x - x0) + β ω_*(‖g‖*ₓ / β)`, expressed through the canonical
Chapter 5 owner `ω_*`. -/
theorem smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound
    {ν : NNReal} {s : StrongDual ℝ E} {x : E}
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hx_int : x ∈ interior Q)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hH : (hessian F x).det ≠ 0) :
    let hPos := hF.toIsStandardSelfConcordantOn.hessian_isPositive hx_int
    ((∀ y : E, y ∈ Argmaxβ hatP F β s → y = x) →
        HasFDerivAt (Uβ hatP F x0 β)
          (ContinuousLinearMap.apply ℝ ℝ (x - x0)) s) ∧
      ∀ g : StrongDual ℝ E,
        ∀ hg : HessianDualLocalNorm.ofDetNeZero F x hPos hH g < (β : ℝ),
        let τω : Set.Iio (1 : ℝ) := ⟨
          HessianDualLocalNorm.ofDetNeZero F x hPos hH g / (β : ℝ), by
          have hlt : HessianDualLocalNorm.ofDetNeZero F x hPos hH g < 1 * (β : ℝ) := by
            simpa [one_mul] using hg
          exact (div_lt_iff₀ β.2).2 hlt⟩
        Uβ hatP F x0 β (s + g) ≤
          Uβ hatP F x0 β s +
            g (x - x0) +
              (β : ℝ) * ω_* τω := sorry

end

/-! ### Proposition_7_10 (from Chap07) -/
noncomputable section

open Matrix
open scoped BigOperators PositiveDefMatrixNorm WeightedGramMatrix

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.10 lies in the finite-family weighted-Gram / positive-definite dual-norm domain.

Relevant owners sampled before drafting:
- `weightedGramMatrix` and the notation `B[a](w)` in `Chap07/Proposition_7_9`;
- `positiveDefMatrixNorm` and the dual notation `‖·‖[G,*]` in `Chap07/Definition_7_23`;
- mathlib `Matrix.trace`, `Matrix.trace_mul_comm`, and `Matrix.trace_vecMulVec`.

The source-facing item is therefore stated directly on the existing weighted-Gram owner and the
existing Chapter 7 dual norm surface, with the displayed consequence split into atomic clauses.
-/

section WeightedTraceIdentity

variable (a : Fin m → Eₙ) (weights : StdSimplex ℝ (Fin m))
variable (G : {A : Matrix (Fin n) (Fin n) ℝ // A.PosDef})

-- Proof sketch: substitute the weighted Gram representation
-- `(G : Matrix (Fin n) (Fin n) ℝ) = B[a](weights.weights)` from Proposition 7.9 and multiply on
-- the left by `G⁻¹`; the left-hand side reduces to the identity matrix.
/-- Proposition 7.10 [Chapter7_1.json:56] (1): if the positive-definite matrix `G` is represented
as the weighted Gram matrix `B[a](weights.weights) = ∑ᵢ λᵢ aᵢ aᵢᵀ`, then the equivalent canonical
matrix identity `G⁻¹ B[a](weights.weights) = Iₙ` holds. -/
theorem inv_mul_weightedGramMatrix_eq_one
    (hG : (G : Matrix (Fin n) (Fin n) ℝ) = B[a](weights.weights)) :
    ((G : Matrix (Fin n) (Fin n) ℝ)⁻¹) * B[a](weights.weights) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := sorry

-- Proof sketch: take traces in `inv_mul_weightedGramMatrix_eq_one`, use `Matrix.trace_one`, expand
-- `B[a](weights.weights)`, commute traces cyclically, and identify each rank-one trace with
-- `‖a i‖[G,*]^2` via `positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv`.
/-- Proposition 7.10 [Chapter7_1.json:56] (2): tracing the weighted Gram identity gives the exact
formula `(n : ℝ) = ∑ᵢ λᵢ ‖aᵢ‖[G,*]^2`. -/
theorem dim_eq_sum_weights_mul_dualNorm_sq
    (hG : (G : Matrix (Fin n) (Fin n) ℝ) = B[a](weights.weights)) :
    (n : ℝ) =
      ∑ i : Fin m, weights.weights i * ‖a i‖[G,*] ^ (2 : ℕ) := sorry

-- Proof sketch: start from the exact identity
-- `(n : ℝ) = ∑ᵢ λᵢ ‖aᵢ‖[G,*]^2`, bound every squared dual norm by `r^2`, and use the simplex
-- relation `∑ᵢ λᵢ = 1`.
/-- Proposition 7.10 [Chapter7_1.json:56] (3): if every generator satisfies `‖aᵢ‖[G,*] ≤ r`, then
the previous identity implies the estimate `(n : ℝ) ≤ r^2`. -/
theorem dim_le_sq_of_dualNorm_le
    (htrace :
      (n : ℝ) =
        ∑ i : Fin m, weights.weights i * ‖a i‖[G,*] ^ (2 : ℕ))
    {r : ℝ} (hr : ∀ i : Fin m, ‖a i‖[G,*] ≤ r) :
    (n : ℝ) ≤ r ^ (2 : ℕ) := sorry

end WeightedTraceIdentity

end

/-! ### Theorem_7_10 (from Chap07) -/
noncomputable section

open Matrix
open scoped PositiveDefMatrixNorm

variable {n : ℕ} {m : ℕ+}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Matₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "PosMatₙ" => { G : Matₙ // Matrix.PosDef G }

/- Theorem 7.10 lies in Chapter 7's sign-invariant diagonal-rounding / stopping-time domain.

Sampled owner-style declarations:
- `signSymmetricConvexHull` and `averageDiagonalSquare` in `Definition_7_35.lean`, the Chapter 7
  owners for the source hull `Conv ⋃ᵢ B(aᵢ)` and its canonical diagonal initialization;
- `ellipsoidBoxInterpolationMatrix` and `ellipsoidBoxLogVolumePotential` in
  `Definition_7_34.lean`, the source-facing one-step matrix update and its logarithmic potential;
- `ellipsoidBoxAlphaStar`, `ellipsoidBoxLogVolumePotential_alphaStar_le_gammaComparison`, and
  `ellipsoidBoxGammaComparison_neg` in `Lemma_7_7.lean`, the canonical Chapter 7 step-size and
  potential-comparison API;
- `CentralSymmetricRoundingMethod` in `Algorithm_7_5.lean` and
  `CentralSymmetricRoundingMethod.stoppingIndex_le` in `Theorem_7_6.lean`, the nearby owner-level
  pattern where the algorithm object carries the primitive iteration data and the stopping time is
  derived canonically as a first-hit index.

Best owner abstraction:
- source-facing: the sign-invariant rounding method itself, with the canonical initialization
  `D₀ = averageDiagonalSquare a` and the recursive update scheme `(7.2.18)`;
- core/canonical: `signSymmetricConvexHull`, `averageDiagonalSquare`,
  `ellipsoidBoxInterpolationMatrix`, `ellipsoidBoxAlphaStar`, and
  `ellipsoidBoxLogVolumePotential`;
- bridge/view: the potential-drop comparison from Lemma 7.7, applied along the continuing
  iterations of the method.

Primitive data:
- the generating family `a₁, …, aₘ`;
- the current-state dual-norm maximizer choice on positive-definite matrices;
- the positivity of the canonical initial matrix and of each recursive update step.

Derived API:
- the recursive positive-definite orbit `D₀, D₁, …` with
  `D₀ = averageDiagonalSquare a` and
  `Dₖ₊₁ = ellipsoidBoxInterpolationMatrix Dₖ gₖ αₖ`;
- the chosen points `gₖ`;
- the dual radius `rₖ = max {‖g‖*_{Dₖ} | g ∈ signSymmetricConvexHull a}` realized by `gₖ`;
- the step size `αₖ = ellipsoidBoxAlphaStar Dₖ gₖ`;
- the one-step logarithmic drop `ellipsoidBoxLogVolumePotential Dₖ gₖ αₖ`;
- the stopping criterion `rₖ ≤ γ √n` and its canonical first stopping time.

The previous version used a public wrapper whose primitive fields were arbitrary sequences. This
refinement follows the Chapter 7 iterate-owner pattern instead: the public owner is the recursive
sign-invariant algorithm itself, the maximizer property is primitive owner data rather than a
downstream theorem hypothesis, and the matrix/radius/stopping-time API is derived canonically from
that recursion.
-/

section PotentialDrop

variable {potential : ℕ → ℝ}

-- Proof sketch: iterate `hstep` to obtain
-- `potential k ≤ potential 0 - k * drop` for every `k ≤ Nat.find hTerminate`. The defining
-- property of `Nat.find hTerminate` supplies the first nonpositive index, and minimality excludes
-- earlier stopping. Combine this with the initial bound `potential 0 ≤ B`, the nonnegativity
-- `0 ≤ B`, and divide by `drop > 0`.
/-- A potential sequence that starts below an explicit nonnegative bound `B` and decreases by at
least a fixed positive amount `δ` at every continuing step must terminate after at most `δ⁻¹ B`
steps. -/
theorem stoppingTime_le_of_positive_drop
    (hTerminate : ∃ k : ℕ, potential k ≤ 0)
    (B drop : ℝ)
    (hdrop : 0 < drop)
    (hinitial : potential 0 ≤ B)
    (hB : 0 ≤ B)
    (hstep :
      ∀ k : ℕ, k < Nat.find hTerminate →
        potential (k + 1) ≤ potential k - drop) :
    (Nat.find hTerminate : ℝ) ≤ drop⁻¹ * B := sorry

end PotentialDrop

/-- A sign-invariant diagonal rounding algorithm for the family `a₁, …, aₘ` is determined by the
canonical initial matrix `D₀ = averageDiagonalSquare a`, a choice of a current dual-norm
maximizer `gₖ ∈ signSymmetricConvexHull a` from each positive-definite matrix state, and the
requirement that the Chapter 7 update `(7.2.18)` stays positive definite. The actual orbit
`D₀, D₁, …`, the chosen points `g₀, g₁, …`, and the stopping time for the radius threshold are
derived recursively from this source-facing owner.
-/
structure SignInvariantRoundingAlgorithm where
  /-- The generating family `a₁, …, aₘ`. -/
  vectors : Fin (m : ℕ) → EuclideanSpace ℝ (Fin n)
  /-- The canonical initial matrix `D₀ = averageDiagonalSquare a` is positive definite. -/
  initial_posDef : (averageDiagonalSquare vectors).PosDef
  /-- The current-state choice of the point `gₖ ∈ signSymmetricConvexHull a`. -/
  selectMaximizer : PosMatₙ → Eₙ
  /-- Every chosen point lies in the generated sign-symmetric hull and maximizes the current
  `G`-dual norm there. -/
  selectMaximizer_spec :
    ∀ G : PosMatₙ,
      selectMaximizer G ∈ signSymmetricConvexHull vectors ∧
        IsMaxOn (fun g : Eₙ ↦ ‖g‖[G,*]) (signSymmetricConvexHull vectors) (selectMaximizer G)
  /-- The recursive update `(7.2.18)` remains positive definite at every positive-definite state.
  -/
  step_posDef :
    ∀ G : PosMatₙ,
      (ellipsoidBoxInterpolationMatrix G.1 (selectMaximizer G)
        (ellipsoidBoxAlphaStar G.1 G.2 (selectMaximizer G))).PosDef

namespace SignInvariantRoundingAlgorithm

local notation "SignAlg" => @SignInvariantRoundingAlgorithm n m

/-- The sign-symmetric hull generated by the input family `a₁, …, aₘ`. -/
def generatedSet (algorithm : SignAlg) : Set Eₙ :=
  signSymmetricConvexHull algorithm.vectors

/-- The current positive-definite matrix owner at stage `0`. -/
def initialMatrix (algorithm : SignAlg) : PosMatₙ :=
  ⟨averageDiagonalSquare algorithm.vectors, algorithm.initial_posDef⟩

/-- The Chapter 7 step size `α*(D, g)` attached to a positive-definite matrix state `D` and its
selected maximizer `g`. -/
def stepAlpha
    (algorithm : SignAlg) (G : PosMatₙ) : ℝ :=
  ellipsoidBoxAlphaStar G.1 G.2 (algorithm.selectMaximizer G)

/-- The one-step recursive update `(7.2.18)` on positive-definite matrix states. -/
def step
    (algorithm : SignAlg) (G : PosMatₙ) : PosMatₙ :=
  ⟨ellipsoidBoxInterpolationMatrix G.1 (algorithm.selectMaximizer G) (algorithm.stepAlpha G),
    algorithm.step_posDef G⟩

/-- The recursive positive-definite matrix orbit `D₀, D₁, D₂, ...` generated by the sign-
invariant rounding update. -/
def currentMatrix
    (algorithm : SignAlg) : ℕ → PosMatₙ :=
  fun k ↦ (algorithm.step^[k]) (algorithm.initialMatrix)

/-- A sign-invariant rounding algorithm can be used as its underlying matrix orbit
`D₀, D₁, D₂, ...`. -/
instance : CoeFun SignAlg (fun _ ↦ ℕ → Matₙ) where
  coe algorithm k := (algorithm.currentMatrix k).1

/-- The algorithm starts from the canonical Chapter 7 initialization
`D₀ = averageDiagonalSquare a`. -/
@[simp] theorem matrix_zero
    (algorithm : SignAlg) :
    algorithm 0 = averageDiagonalSquare algorithm.vectors :=
  rfl

/-- The recursive orbit at stage `0` is the canonical initial positive-definite matrix owner. -/
@[simp] theorem currentMatrix_zero
    (algorithm : SignAlg) :
    algorithm.currentMatrix 0 = algorithm.initialMatrix :=
  rfl

/-- The chosen point `gₖ` at stage `k` is the state-dependent maximizer selected from `Dₖ`. -/
def maximizer (algorithm : SignAlg) (k : ℕ) : Eₙ :=
  algorithm.selectMaximizer (algorithm.currentMatrix k)

/-- Every chosen point belongs to the generated sign-symmetric hull. -/
theorem maximizer_mem_generatedSet
    (algorithm : SignAlg) (k : ℕ) :
    algorithm.maximizer k ∈ generatedSet algorithm :=
  (algorithm.selectMaximizer_spec (algorithm.currentMatrix k)).1

/-- At stage `k`, the chosen point maximizes the current dual norm on the generated
sign-symmetric hull. -/
theorem maximizer_isMaxOn_generatedSet
    (algorithm : SignAlg) (k : ℕ) :
    IsMaxOn
      (fun g : Eₙ ↦ ‖g‖[algorithm.currentMatrix k,*])
      (generatedSet algorithm)
      (algorithm.maximizer k) :=
  (algorithm.selectMaximizer_spec (algorithm.currentMatrix k)).2

/-- The recursive matrix orbit satisfies the Chapter 7 successor update `(7.2.18)`. -/
theorem matrix_succ
    (algorithm : SignAlg) (k : ℕ) :
    algorithm (k + 1) =
      ellipsoidBoxInterpolationMatrix (algorithm k) (algorithm.maximizer k)
        (algorithm.stepAlpha (algorithm.currentMatrix k)) := by
  simpa [currentMatrix, step, stepAlpha, maximizer] using
    congrArg Subtype.val
      (Function.iterate_succ_apply' algorithm.step k algorithm.initialMatrix)

/-- The positive-definite matrix owner at stage `k + 1` is obtained by one application of the
recursive update step. -/
theorem currentMatrix_succ
    (algorithm : SignAlg) (k : ℕ) :
    algorithm.currentMatrix (k + 1) = algorithm.step (algorithm.currentMatrix k) := by
  simpa [currentMatrix] using
    Function.iterate_succ_apply' algorithm.step k algorithm.initialMatrix

/-- The Chapter 7 step size `αₖ = α*(Dₖ, gₖ)`. -/
def alpha (algorithm : SignAlg) (k : ℕ) : ℝ :=
  algorithm.stepAlpha (algorithm.currentMatrix k)

/-- The maximal dual radius `rₖ = max {‖g‖*_{Dₖ} | g ∈ signSymmetricConvexHull a}` realized by
the chosen maximizer `gₖ`. -/
def radius (algorithm : SignAlg) (k : ℕ) : ℝ :=
  ‖algorithm.maximizer k‖[algorithm.currentMatrix k,*]

/-- Every point of the generated sign-symmetric hull has current dual norm at most the stage-`k`
radius. -/
theorem dualNorm_le_radius
    (algorithm : SignAlg) (k : ℕ) {g : Eₙ}
    (hg : g ∈ generatedSet algorithm) :
    ‖g‖[algorithm.currentMatrix k,*] ≤ algorithm.radius k :=
  (algorithm.maximizer_isMaxOn_generatedSet k) hg

/-- The one-step logarithmic potential contribution at stage `k`. -/
def potentialStep (algorithm : SignAlg) (k : ℕ) : ℝ :=
  ellipsoidBoxLogVolumePotential (algorithm k) (algorithm.maximizer k) (algorithm.alpha k)

/-- The remaining logarithmic-volume budget
`B - (log det Dₖ - log det D₀)` at stage `k`, measured against the canonical matrix orbit of the
sign-invariant rounding algorithm. -/
def remainingLogVolumeBudget
    (algorithm : SignAlg) (B : ℝ) (k : ℕ) : ℝ :=
  B - (Real.log (Matrix.det (algorithm k)) - Real.log (Matrix.det (algorithm 0)))

/-- At stage `0`, the remaining logarithmic-volume budget is exactly the initial budget `B`. -/
@[simp] theorem remainingLogVolumeBudget_zero
    (algorithm : SignAlg) (B : ℝ) :
    algorithm.remainingLogVolumeBudget B 0 = B := by
  simp [remainingLogVolumeBudget]

/-- Advancing one sign-invariant rounding step decreases the remaining logarithmic-volume budget by
exactly the Chapter 7 one-step potential `ellipsoidBoxLogVolumePotential Dₖ gₖ αₖ`. -/
theorem remainingLogVolumeBudget_succ
    (algorithm : SignAlg) (B : ℝ) (k : ℕ) :
    algorithm.remainingLogVolumeBudget B (k + 1) =
      algorithm.remainingLogVolumeBudget B k + algorithm.potentialStep k := sorry

/-- The stopping criterion from Theorem 7.10: the stage-`k` dual radius is at most `γ √n`. -/
def stoppingCriterion (algorithm : SignAlg) (γ : ℝ) (k : ℕ) : Prop :=
  algorithm.radius k ≤ γ * Real.sqrt (n : ℝ)

/-- The algorithm terminates once some iterate satisfies the radius threshold `rₖ ≤ γ √n`. -/
def Terminates (algorithm : SignAlg) (γ : ℝ) : Prop :=
  ∃ k : ℕ, algorithm.stoppingCriterion γ k

/-- The canonical stopping time is the first iterate satisfying the stopping criterion
`rₖ ≤ γ √n`. -/
noncomputable def stoppingTime
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) : ℕ := by
  classical
  exact Nat.find hTerminate

/-- The first stopping time is least with respect to the radius threshold. -/
theorem stoppingTime_isLeast
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) :
    IsLeast {k : ℕ | algorithm.stoppingCriterion γ k} (algorithm.stoppingTime hTerminate) := by
  classical
  simpa [stoppingTime, Terminates] using Nat.isLeast_find hTerminate

/-- The stopping test succeeds at the canonical stopping time. -/
theorem stoppingTime_spec
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) :
    algorithm.stoppingCriterion γ (algorithm.stoppingTime hTerminate) :=
  (algorithm.stoppingTime_isLeast hTerminate).1

/-- No earlier stage satisfies the stopping criterion. -/
theorem stoppingTime_min
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) {k : ℕ}
    (hk : k < algorithm.stoppingTime hTerminate) :
    ¬ algorithm.stoppingCriterion γ k := by
  exact fun hkStop ↦
    (not_le_of_gt hk) ((algorithm.stoppingTime_isLeast hTerminate).2 hkStop)

/-- Before the canonical stopping time, the current dual radius is strictly larger than
`γ √n`. -/
theorem threshold_lt_radius_of_lt_stoppingTime
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) {k : ℕ}
    (hk : k < algorithm.stoppingTime hTerminate) :
    γ * Real.sqrt (n : ℝ) < algorithm.radius k := by
  exact lt_of_not_ge <| by
    simpa [stoppingCriterion] using algorithm.stoppingTime_min hTerminate hk

-- Proof sketch: apply the abstract helper `stoppingTime_le_of_positive_drop` to the canonical
-- remaining logarithmic-volume budget
-- `B - (log det Dₖ - log det D₀)` with
-- `B = n (log n + 2 log m)`. At the canonical stopping time, use
-- `hremaining_nonpos_of_stopping`; before that time, positivity comes from
-- `hremaining_pos_of_continuing` together with
-- `threshold_lt_radius_of_lt_stoppingTime`. The recursion step for the remaining budget is
-- `remainingLogVolumeBudget_succ`, and the one-step drop is bounded above by
-- `ellipsoidBoxLogVolumePotential_alphaStar_le_gammaComparison` on continuing iterates. Combining
-- this with `ellipsoidBoxGammaComparison_neg` yields the uniform positive decrease
-- `((γ² - 1) / γ² - log (1 + (γ² - 1) / γ²))`. The initial budget at stage `0` is exactly `B`,
-- and `0 ≤ B` follows from `hn` and `m.2`.
/-- Theorem 7.10: if a sign-invariant recursive rounding algorithm `(7.2.18)` has the Chapter 7
remaining logarithmic-volume budget
`n (log n + 2 log m) - (log det Dₖ - log det D₀)`, if that canonical budget is positive at every
genuinely continuing iterate `rₖ > γ √n` and nonpositive at every iterate satisfying the
threshold `rₖ ≤ γ √n`, and if the continuing steps satisfy the Chapter 7 potential comparison
with parameter `γ ≥ √(1 + 1 / √n)`, then the canonical first stopping time for the threshold
`rₖ ≤ γ √n` is at most
`[(γ² - 1) / γ² - log (1 + (γ² - 1) / γ²)]⁻¹ n (log n + 2 log m)` steps. -/
theorem stoppingTime_le
    (algorithm : SignAlg)
    (γ : ℝ) (hn : 1 ≤ n)
    (hγ : Real.sqrt (1 + 1 / Real.sqrt (n : ℝ)) ≤ γ)
    (hTerminate : algorithm.Terminates γ)
    (hremaining_pos_of_continuing :
      ∀ k : ℕ,
        γ * Real.sqrt (n : ℝ) < algorithm.radius k →
          0 < algorithm.remainingLogVolumeBudget
            ((n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ))) k)
    (hremaining_nonpos_of_stopping :
      ∀ k : ℕ,
        algorithm.stoppingCriterion γ k →
          algorithm.remainingLogVolumeBudget
            ((n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ))) k ≤ 0) :
    (algorithm.stoppingTime hTerminate : ℝ) ≤
      (((γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) -
          Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)))⁻¹ *
        (n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ))) := sorry

end SignInvariantRoundingAlgorithm

end
