import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_1_9_8 (from Chap01) -/
open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Lemma 1.9.8 lies in the quadratic conjugate-gradient owner domain.

Sampled declarations in this domain:
* `problem.krylovSubspace x₀ k`, the chapter owner for the Krylov stages `𝓛ₖ`;
* `AffineSubspace.vsub_mem_direction`, the canonical affine-space bridge from iterate membership to
  Krylov-space displacement;
* `IsConjugateGradientSequence.mem_affineKrylovSearchSpace`, the owner membership theorem for the
  iterates;
* `IsConjugateGradientSequence.gradient_mem_krylovSubspace_orthogonal`, the owner-side
  orthogonality input from Corollary 1.9.7;
* `problem.gradient_eq`, `problem.matrix_inner_apply_swap`, and `Submodule.orthogonal_le`, the
  quadratic gradient, symmetry, and orthogonal-complement monotonicity owners used to convert
  gradient orthogonality into `A`-orthogonality of step differences.

Best owner abstraction:
* `IsConjugateGradientSequence problem x0 xs`.

Primitive data:
* the quadratic problem `problem`;
* the starting point `x0`;
* the positive-indexed conjugate-gradient iterate sequence `xs`.

Derived API:
* the full trajectory `conjugateGradientTrajectory x0 xs`;
* the owner-side theorem `stepDifference_mem_krylovSubspace`;
* the step differences `xₖ₊₁ - xₖ`;
* the Krylov stages `𝓛(problem, x0, k)` and their orthogonal complements.

Source/core/bridge triage:
* source-facing: pairwise `A`-orthogonality of distinct step differences along the
  conjugate-gradient trajectory;
* core/canonical: the owner Krylov spaces and their gradient-orthogonality API;
* bridge/view: `conjugateGradientTrajectory x0 xs`.
-/

namespace IsConjugateGradientSequence

/-- Helper for Lemma 1.9.8: each positive-indexed iterate displacement from the initial point lies
in the corresponding Krylov subspace. -/
private theorem iterateDisplacement_mem_krylovSubspace
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) (k : ℕ+) :
    xs k - x0 ∈ 𝓛(problem, x0, k) := by
  -- Unpack affine-search-space membership into a displacement in the direction subspace.
  simpa [UnconstrainedQuadraticMinimizationProblem.affineKrylovSearchSpace] using
    (AffineSubspace.mem_mk').1 (hcg.mem_affineKrylovSearchSpace k)

/-- Every conjugate-gradient step difference belongs to the corresponding Krylov stage. -/
theorem stepDifference_mem_krylovSubspace
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) (k : ℕ) :
    conjugateGradientTrajectory x0 xs (k + 1) - conjugateGradientTrajectory x0 xs k ∈
      𝓛(problem, x0, k.succPNat) := by
  let trajectory : ℕ → E := conjugateGradientTrajectory x0 xs
  cases k with
  | zero =>
      -- The first step is exactly the first iterate displacement from `x0`.
      simpa [trajectory] using
        iterateDisplacement_mem_krylovSubspace hcg (1 : ℕ+)
  | succ k =>
      -- Rewrite the later step as a difference of two iterate displacements from `x0`.
      have hk_mem :
          trajectory (k + 1) - x0 ∈ 𝓛(problem, x0, k.succPNat) := by
        simpa [trajectory] using
          iterateDisplacement_mem_krylovSubspace hcg k.succPNat
      have hk_next_mem :
          trajectory (k + 2) - x0 ∈ 𝓛(problem, x0, (k + 1).succPNat) := by
        simpa [trajectory] using
          iterateDisplacement_mem_krylovSubspace hcg (k + 1).succPNat
      have hk_mem' :
          trajectory (k + 1) - x0 ∈ 𝓛(problem, x0, (k + 1).succPNat) :=
        problem.krylovSubspace_mono x0
          ((Nat.succPNat_le_succPNat).2 (Nat.le_succ k))
          hk_mem
      have hsub :
          trajectory (k + 2) - trajectory (k + 1) =
            (trajectory (k + 2) - x0) - (trajectory (k + 1) - x0) := by
        abel
      rw [hsub]
      exact Submodule.sub_mem _ hk_next_mem hk_mem'

/-- Lemma 1.9.8: along a conjugate-gradient sequence for an unconstrained quadratic problem,
distinct step differences are `A`-orthogonal. -/
-- Proof sketch: the `i`th step difference lies in the owner Krylov space `𝓛ᵢ₊₁`, hence also in
-- every later stage by monotonicity. For `i < k`, Corollary 1.9.7 puts both
-- `∇f(x_k)` and `∇f(x_{k+1})` in `𝓛ₖᗮ`, so their difference is orthogonal to the earlier step.
-- The quadratic gradient identity `∇f(x) = A (x - x*)` then rewrites that gradient difference as
-- `A (x_{k+1} - x_k)`. The reverse order follows from symmetry of `A`.
theorem stepDifferences_pairwise_A_orthogonal
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) {k i : ℕ} (hki : k ≠ i) :
    inner ℝ
      (problem.A.toEuclideanLin
        (conjugateGradientTrajectory x0 xs (k + 1) - conjugateGradientTrajectory x0 xs k))
      (conjugateGradientTrajectory x0 xs (i + 1) - conjugateGradientTrajectory x0 xs i) = 0 := by
  let trajectory : ℕ → E := conjugateGradientTrajectory x0 xs
  have hAstep :
      ∀ k : ℕ,
        problem.A.toEuclideanLin (trajectory (k + 1) - trajectory k) =
          ∇ problem.objective (trajectory (k + 1)) -
            ∇ problem.objective (trajectory k) := by
    intro k
    -- Rewrite the step through the minimizer-centered gradient formula `∇f(x) = A (x - x*)`.
    calc
      problem.A.toEuclideanLin (trajectory (k + 1) - trajectory k)
          = problem.A.toEuclideanLin
              ((trajectory (k + 1) - problem.minimizer) -
                (trajectory k - problem.minimizer)) := by
              congr 1
              abel
      _ = problem.A.toEuclideanLin (trajectory (k + 1) - problem.minimizer) -
            problem.A.toEuclideanLin (trajectory k - problem.minimizer) := by
            rw [LinearMap.map_sub]
      _ = ∇ problem.objective (trajectory (k + 1)) -
            ∇ problem.objective (trajectory k) := by
            rw [problem.gradient_eq, problem.gradient_eq]
  have hlt :
      ∀ {a b : ℕ},
        a < b →
          inner ℝ (problem.A.toEuclideanLin (trajectory (b + 1) - trajectory b))
            (trajectory (a + 1) - trajectory a) = 0 := by
    intro a b hab
    obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hab))
    -- Put the earlier step into the later Krylov stage and then use orthogonality of the two
    -- consecutive gradients to that stage.
    have hstep_a :
        trajectory (a + 1) - trajectory a ∈ 𝓛(problem, x0, c.succPNat) := by
      exact
        problem.krylovSubspace_mono x0
          ((Nat.succPNat_le_succPNat).2 (Nat.lt_succ_iff.mp hab))
          (hcg.stepDifference_mem_krylovSubspace a)
    have hgrad_b :
        ∇ problem.objective (trajectory (c + 1)) ∈ (𝓛(problem, x0, c.succPNat))ᗮ := by
      simpa [trajectory] using
        hcg.gradient_mem_krylovSubspace_orthogonal c.succPNat
    have hgrad_b_succ' :
        ∇ problem.objective (trajectory (c + 2)) ∈
          (𝓛(problem, x0, (c + 1).succPNat))ᗮ := by
      simpa [trajectory] using
        hcg.gradient_mem_krylovSubspace_orthogonal (c + 1).succPNat
    have hgrad_b_succ :
        ∇ problem.objective (trajectory (c + 2)) ∈ (𝓛(problem, x0, c.succPNat))ᗮ :=
      Submodule.orthogonal_le
        (problem.krylovSubspace_mono x0
          ((Nat.succPNat_le_succPNat).2 (Nat.le_succ c)))
        hgrad_b_succ'
    have hinner :
        inner ℝ
          (∇ problem.objective (trajectory (c + 2)) -
            ∇ problem.objective (trajectory (c + 1)))
          (trajectory (a + 1) - trajectory a) = 0 := by
      exact
        (Submodule.mem_orthogonal' _ _).1
          (Submodule.sub_mem _ hgrad_b_succ hgrad_b)
          _
          hstep_a
    rw [hAstep (c + 1)]
    exact hinner
  have hswap :
      ∀ a b : ℕ,
        inner ℝ (problem.A.toEuclideanLin (trajectory (a + 1) - trajectory a))
          (trajectory (b + 1) - trajectory b) =
        inner ℝ (problem.A.toEuclideanLin (trajectory (b + 1) - trajectory b))
          (trajectory (a + 1) - trajectory a) := by
    intro a b
    -- Symmetry of the quadratic form lets us swap the two step differences.
    simpa [trajectory, real_inner_comm] using
      problem.matrix_inner_apply_swap
        (trajectory (a + 1) - trajectory a)
        (trajectory (b + 1) - trajectory b)
  rcases lt_or_gt_of_ne hki with hki | hki
  · rw [hswap k i]
    exact hlt hki
  · simpa [trajectory] using hlt hki

end IsConjugateGradientSequence

/-! ### Definition_1_9_10 (from Chap01) -/
universe u

open scoped Gradient

noncomputable section

namespace NonlinearConjugateGradientMethod

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 1.9.10 is `source-facing`: it names the standard nonlinear conjugate-gradient
coefficient sequences in terms of the objective `f`, the iterate sequence `xₖ`, and the search
directions `pₖ`.

Source/core/bridge triage:
* source-facing: the Dai--Yuan, Fletcher--Reeves, and Polak--Ribiere coefficient sequences on
  `(f, x, p)`
* core/canonical: the surrounding recursive owners
  `nonlinearConjugateGradientIterates`, `nonlinearConjugateGradientDirections`, the method owner
  `_root_.NonlinearConjugateGradientMethod`, and the line-search owner
  `SatisfiesExactLineSearchAlong`
* bridge/view: the pointwise evaluation lemmas below

Primary domain:
* nonlinear conjugate-gradient coefficient formulas on a real inner product space

Sampled owner-style declarations:
* `nonlinearConjugateGradientIterates`
* `nonlinearConjugateGradientDirections`
* `_root_.NonlinearConjugateGradientMethod`
* `SatisfiesExactLineSearchAlong`

There is no upstream owner that already defines these three textbook coefficient formulas, so the
primitive public data here remain exactly the source-level triple `(f, x, p)`.
-/

section

variable (f : E → ℝ) (x p : ℕ → E)

/-- Definition 1.9.10 (1): the Dai--Yuan nonlinear conjugate-gradient coefficient sequence is
given by
`βₖ = ‖∇f(xₖ₊₁)‖² / ⟪∇f(xₖ₊₁) - ∇f(xₖ), pₖ⟫`. -/
def daiYuanBeta : ℕ → ℝ :=
  fun k ↦
    ‖∇ f (x (k + 1))‖ ^ 2 / inner ℝ (∇ f (x (k + 1)) - ∇ f (x k)) (p k)

/-- Evaluating the Dai--Yuan coefficient sequence at index `k` recovers the textbook formula. -/
@[simp] theorem daiYuanBeta_apply (k : ℕ) :
    daiYuanBeta f x p k =
      ‖∇ f (x (k + 1))‖ ^ 2 / inner ℝ (∇ f (x (k + 1)) - ∇ f (x k)) (p k) :=
  rfl

/-- Definition 1.9.10 (2): the Fletcher--Reeves nonlinear conjugate-gradient coefficient sequence
is given by `βₖ = ‖∇f(xₖ₊₁)‖² / ‖∇f(xₖ)‖²`. -/
def fletcherReevesBeta : ℕ → ℝ :=
  fun k ↦ ‖∇ f (x (k + 1))‖ ^ 2 / ‖∇ f (x k)‖ ^ 2

/-- Evaluating the Fletcher--Reeves coefficient sequence at index `k` recovers the textbook
formula. -/
@[simp] theorem fletcherReevesBeta_apply (k : ℕ) :
    fletcherReevesBeta f x k =
      ‖∇ f (x (k + 1))‖ ^ 2 / ‖∇ f (x k)‖ ^ 2 :=
  rfl

/-- Definition 1.9.10 (3): the Polak--Ribiere nonlinear conjugate-gradient coefficient sequence is
given by
`βₖ = ⟪∇f(xₖ₊₁), ∇f(xₖ₊₁) - ∇f(xₖ)⟫ / ‖∇f(xₖ)‖²`. -/
def polakRibiereBeta : ℕ → ℝ :=
  fun k ↦
    inner ℝ (∇ f (x (k + 1))) (∇ f (x (k + 1)) - ∇ f (x k)) / ‖∇ f (x k)‖ ^ 2

/-- Evaluating the Polak--Ribiere coefficient sequence at index `k` recovers the textbook
formula. -/
@[simp] theorem polakRibiereBeta_apply (k : ℕ) :
    polakRibiereBeta f x k =
      inner ℝ (∇ f (x (k + 1))) (∇ f (x (k + 1)) - ∇ f (x k)) / ‖∇ f (x k)‖ ^ 2 :=
  rfl

end

end NonlinearConjugateGradientMethod

end

/-! ### Proposition_1_9_11 (from Chap01) -/
open scoped Gradient
open Matrix

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

namespace UnconstrainedQuadraticMinimizationProblem

/- Proposition 1.9.11 stays in the owner domain of
`UnconstrainedQuadraticMinimizationProblem`.

Sampled chapter declarations:
* `minimizer_isMinOn`
* `objective_eq_objective_minimizer_add_quadratic_error`
* `quadraticObjective_gradient_eq`
* `isMinOn_gradient_eq_zero`

Owner abstraction:
* source-facing: the quadratic owner `problem`
* core/canonical: its minimizer, completed-square identity, and general quadratic-gradient formula
* bridge/view: the centered expression `x - problem.minimizer`

Primitive data:
* `problem.α`, `problem.a`, `problem.A`, `problem.posDef`

Derived API:
* the global-minimizer fact and completed-square identity recalled below from
  `Lemma_1_8_8`
* the minimum-value, stationary-point, and uniqueness formulas proved here from those owners
-/

/- Proposition 1.9.11 first reuses the existing owner theorem that `problem.minimizer` is a
global minimizer. -/
recall minimizer_isMinOn
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    IsMinOn problem Set.univ problem.minimizer

/- The completed-square identity is already owned upstream by `Lemma_1.8.8`. -/
recall objective_eq_objective_minimizer_add_quadratic_error
    (problem : UnconstrainedQuadraticMinimizationProblem n) (y : E) :
    problem.objective y =
      problem.objective problem.minimizer +
        (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin (y - problem.minimizer))
          (y - problem.minimizer)

private theorem linear_coefficient_eq_neg_apply_minimizer
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    problem.a = -problem.A.toEuclideanLin problem.minimizer := by
  simpa using (congrArg Neg.neg
    (apply_matrix_to_minimizer_eq_neg_linear_coefficient problem)).symm

private theorem eq_minimizer_of_isMinOn
    (problem : UnconstrainedQuadraticMinimizationProblem n) {x : E}
    (hx : IsMinOn problem Set.univ x) :
    x = problem.minimizer := by
  have hx' := isMinOn_univ_iff.mp hx
  have hmin' := isMinOn_univ_iff.mp (minimizer_isMinOn problem)
  have hvalue : problem.objective x = problem.objective problem.minimizer := by
    exact le_antisymm (hx' problem.minimizer) (hmin' x)
  have hquad :
      inner ℝ (problem.A.toEuclideanLin (x - problem.minimizer))
        (x - problem.minimizer) = 0 := by
    have hobjective := objective_eq_objective_minimizer_add_quadratic_error problem x
    nlinarith [hobjective, hvalue]
  have hsub : x - problem.minimizer = 0 := by
    by_contra hne
    have hcoord_ne : (x - problem.minimizer).ofLp ≠ 0 := by
      intro hcoord
      apply hne
      exact congrArg (WithLp.toLp 2) hcoord
    have hcoord :
        inner ℝ (problem.A.toEuclideanLin (x - problem.minimizer))
          (x - problem.minimizer) =
          dotProduct (x - problem.minimizer).ofLp
            (problem.A *ᵥ (x - problem.minimizer).ofLp) := by
      simpa only [Matrix.ofLp_toLpLin] using
        (EuclideanSpace.inner_eq_star_dotProduct
          (problem.A.toEuclideanLin (x - problem.minimizer)) (x - problem.minimizer))
    have hpos :
        0 <
          inner ℝ (problem.A.toEuclideanLin (x - problem.minimizer))
            (x - problem.minimizer) := by
      rw [hcoord]
      exact problem.posDef.dotProduct_mulVec_pos hcoord_ne
    linarith
  exact sub_eq_zero.mp hsub

/-- Evaluating the objective at its minimizer gives the minimum value formula. -/
-- Proof sketch: specialize the completed-square identity at `x = x*`, where the quadratic error
-- term vanishes.
theorem objective_value_at_minimizer
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    problem.objective problem.minimizer =
      problem.α -
        (1 / 2 : ℝ) *
          inner ℝ (problem.A.toEuclideanLin problem.minimizer) problem.minimizer :=
  by
  rw [UnconstrainedQuadraticMinimizationProblem.objective, quadraticObjective,
    linear_coefficient_eq_neg_apply_minimizer problem]
  simp
  ring

/-- The gradient of the objective is `A (x - x*)` when `x* = -A⁻¹ a`. -/
-- Proof sketch: differentiate the affine and quadratic parts to get `a + A x`, then substitute
-- `a = -A x*` from the definition of the minimizer.
theorem gradient_eq
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    ∇ problem.objective x = problem.A.toEuclideanLin (x - problem.minimizer) := by
  have hsymm : problem.A.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using problem.posDef.1
  have hgrad :=
    congrFun (quadraticObjective_gradient_eq problem.α problem.a problem.A hsymm) x
  calc
    ∇ problem.objective x = problem.a + problem.A.toEuclideanLin x := by
      simpa [UnconstrainedQuadraticMinimizationProblem.objective] using hgrad
    _ = -problem.A.toEuclideanLin problem.minimizer + problem.A.toEuclideanLin x := by
      rw [linear_coefficient_eq_neg_apply_minimizer problem]
    _ = problem.A.toEuclideanLin x - problem.A.toEuclideanLin problem.minimizer := by
      simp [sub_eq_add_neg, add_comm]
    _ = problem.A.toEuclideanLin (x - problem.minimizer) := by
      rw [LinearMap.map_sub]

/-- Any stationary point of the quadratic objective is the canonical minimizer. -/
-- Proof sketch: the gradient formula identifies stationarity with vanishing centered quadratic
-- error. The completed-square identity then shows that `x` has the same objective value as the
-- canonical minimizer `x*`, so `x` is itself a global minimizer; uniqueness below forces
-- `x = x*`.
theorem eq_minimizer_of_gradient_eq_zero
    (problem : UnconstrainedQuadraticMinimizationProblem n) {x : E}
    (hx : ∇ problem.objective x = 0) :
    x = problem.minimizer := by
  have hA : problem.A.toEuclideanLin (x - problem.minimizer) = 0 := by
    simpa [problem.gradient_eq x] using hx
  have hxmin : IsMinOn problem Set.univ x := by
    rw [isMinOn_univ_iff]
    intro y
    calc
      problem.objective x = problem.objective problem.minimizer := by
        calc
          problem.objective x
              = problem.objective problem.minimizer +
                  (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin (x - problem.minimizer))
                      (x - problem.minimizer) := by
                  simpa using
                    objective_eq_objective_minimizer_add_quadratic_error problem x
          _ = problem.objective problem.minimizer := by
                simp [hA]
      _ ≤ problem.objective y := by
        exact (isMinOn_univ_iff.mp (minimizer_isMinOn problem)) y
  exact eq_minimizer_of_isMinOn problem hxmin

/-- Any global minimizer of an unconstrained quadratic minimization problem is the canonical
point `problem.minimizer = -A⁻¹ a`. -/
-- Proof sketch: a global minimizer on `Set.univ` is stationary by the ambient owner theorem
-- `isMinOn_gradient_eq_zero`, and the owner-side stationary-point theorem above identifies the
-- only stationary point with `problem.minimizer`.
theorem minimizer_unique (problem : UnconstrainedQuadraticMinimizationProblem n) {x : E}
    (hx : IsMinOn problem Set.univ x) :
    x = problem.minimizer := by
  exact problem.eq_minimizer_of_gradient_eq_zero (isMinOn_gradient_eq_zero hx)

end UnconstrainedQuadraticMinimizationProblem

/-! ### Theorem_1_9_12 (from Chap01) -/
open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- 
Theorem 1.9.12 lies in finite-dimensional quadratic conjugate-gradient termination.

Sampled owner declarations in this domain:
* `UnconstrainedQuadraticMinimizationProblem`, the quadratic owner object;
* `IsConjugateGradientSequence`, the owner predicate for the textbook iterate sequence;
* `IsConjugateGradientSequence.zero_gradient_within_dimension`, the owner-side finite-dimensional
  termination step;
* `problem.eq_minimizer_of_gradient_eq_zero`, the owner-side identification of a stationary point
  with the canonical minimizer.

Best owner abstraction:
* the pair `UnconstrainedQuadraticMinimizationProblem` / `IsConjugateGradientSequence`.

Primitive data:
* `problem : UnconstrainedQuadraticMinimizationProblem n`;
* the initial point `x0`;
* the positive-indexed iterate sequence `xs`.

Derived API:
* `IsConjugateGradientSequence.zero_gradient_within_dimension hcg`;
* the full trajectory `conjugateGradientTrajectory x0 xs`;
* the canonical minimizer `problem.minimizer`.

Source/core/bridge triage:
* source-facing: finite-step attainment of the conjugate-gradient iterate `x_m = x*`;
* core/canonical: the owner-side zero-gradient theorem and stationary-point identification;
* bridge/view: the trajectory map `conjugateGradientTrajectory x0 xs`.

Accordingly, the theorem is stated directly on the owner hypothesis
`IsConjugateGradientSequence problem x0 xs`, and its proof delegates to the existing owner-side
termination and stationary-point API rather than introducing a parallel local wrapper.
-/

namespace IsConjugateGradientSequence

/-- Helper for Theorem 1.9.12: earlier trajectory gradients are orthogonal to later trajectory
gradients along a conjugate-gradient sequence. -/
-- Proof sketch: `krylovSubspace_eq_span_gradients` places the earlier gradient inside the later
-- Krylov space, and the later-stage orthogonality theorem makes the later gradient orthogonal to
-- that entire space.
lemma gradient_orthogonal_of_lt
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) :
    ∀ {a b : ℕ},
      a < b →
        inner ℝ
          (∇ problem.objective (conjugateGradientTrajectory x0 xs a))
          (∇ problem.objective (conjugateGradientTrajectory x0 xs b)) = 0 := by
  intro a b hab
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hab))
  let stage : ℕ+ := k.succPNat
  -- The earlier gradient belongs to the later Krylov subspace because that subspace is spanned
  -- by all preceding trajectory gradients.
  have hgrad_mem :
      ∇ problem.objective (conjugateGradientTrajectory x0 xs a) ∈ 𝓛(problem, x0, stage) := by
    rw [_root_.UnconstrainedQuadraticMinimizationProblem.IsConjugateGradientSequence.krylovSubspace_eq_span_gradients
      hcg stage]
    exact Submodule.subset_span ⟨⟨a, hab⟩, rfl⟩
  -- The later gradient is orthogonal to the same Krylov subspace by the owner-side optimality API.
  have horth_stage :
      ∇ problem.objective (conjugateGradientTrajectory x0 xs (k + 1)) ∈
        (𝓛(problem, x0, stage))ᗮ := by
    simpa [stage, conjugateGradientTrajectory] using
      gradient_mem_krylovSubspace_orthogonal hcg stage
  rw [Submodule.mem_orthogonal'] at horth_stage
  simpa [real_inner_comm] using horth_stage _ hgrad_mem

/-- Helper for Theorem 1.9.12: the first `n + 1` trajectory gradients form a pairwise orthogonal
family. -/
-- Proof sketch: compare two indices in `Fin (n + 1)`, reduce to one of the strict inequalities,
-- and then apply `gradient_orthogonal_of_lt`, flipping the inner product when needed.
lemma pairwise_gradient_orthogonal_prefix
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) :
    Pairwise fun i j : Fin (n + 1) ↦
      inner ℝ
        (∇ problem.objective (conjugateGradientTrajectory x0 xs i))
        (∇ problem.objective (conjugateGradientTrajectory x0 xs j)) = 0 := by
  intro i j hij
  have hij_nat : (i : ℕ) ≠ (j : ℕ) := by
    intro h
    exact hij (Fin.ext h)
  rcases lt_or_gt_of_ne hij_nat with hij_lt | hij_gt
  · exact gradient_orthogonal_of_lt hcg hij_lt
  · simpa [real_inner_comm] using gradient_orthogonal_of_lt hcg hij_gt

/-- Helper for Theorem 1.9.12: some trajectory point among the first `n + 1` iterates has
vanishing gradient. -/
-- Route correction: the missing compiled import for Corollary 1.9.6 is replaced by rebuilding the
-- same finite-dimensional orthogonality contradiction from the earlier owner-side API.
-- Proof sketch: if all first `n + 1` gradients were nonzero, the pairwise orthogonality lemma
-- would make them linearly independent, contradicting that `ℝⁿ` has dimension `n`.
lemma exists_stationary_trajectory_index_le_dimension
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) :
    ∃ k ≤ n,
      ∇ problem.objective (conjugateGradientTrajectory x0 xs k) = 0 := by
  let gradients : Fin (n + 1) → E := fun i ↦
    ∇ problem.objective (conjugateGradientTrajectory x0 xs i)
  have horth : Pairwise fun i j : Fin (n + 1) ↦ inner ℝ (gradients i) (gradients j) = 0 := by
    -- The strict-order orthogonality result already has exactly the right content on this prefix.
    simpa [gradients] using pairwise_gradient_orthogonal_prefix hcg
  by_contra hzero
  -- Negating the existential stationary point says every gradient in the prefix is nonzero.
  have hz : ∀ i : Fin (n + 1), gradients i ≠ 0 := by
    intro i hi
    exact hzero ⟨i, Nat.le_of_lt_succ i.is_lt, hi⟩
  -- Pairwise orthogonality plus nonvanishing implies linear independence.
  have hlin : LinearIndependent ℝ gradients :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hz horth
  -- This contradicts the ambient dimension bound `finrank ℝ E = n`.
  have hcard : n + 1 ≤ n := by
    simpa [gradients] using hlin.fintype_card_le_finrank
  exact (Nat.not_succ_le_self n) hcard

/-- Theorem 1.9.12: for an unconstrained quadratic minimization problem on `ℝⁿ`, every
conjugate-gradient trajectory reaches the unique minimizer `x*` within at most `n` iterations. -/
-- Proof sketch: each iterate minimizes the quadratic objective on the affine Krylov search space
-- from Definition 1.9.3. The gradients are therefore orthogonal to the current Krylov subspace,
-- and in the positive-definite quadratic geometry the successive nonstationary search directions
-- become linearly independent. Since `ℝⁿ` has dimension `n`, this can happen for at most `n`
-- steps, so some iterate must already be stationary; Proposition 1.9.11 then identifies that
-- stationary iterate with the canonical minimizer `x* = problem.minimizer`.
theorem eq_minimizer_within_dimension
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) :
    ∃ m ≤ n, conjugateGradientTrajectory x0 xs m = problem.minimizer := by
  -- First find a stationary trajectory point within the ambient dimension bound.
  rcases exists_stationary_trajectory_index_le_dimension hcg with ⟨m, hm, hgrad⟩
  -- A zero gradient identifies the canonical minimizer for this positive-definite quadratic.
  refine ⟨m, hm, ?_⟩
  exact problem.eq_minimizer_of_gradient_eq_zero hgrad

end IsConjugateGradientSequence
