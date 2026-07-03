import Mathlib
import Mathlib.Algebra.Module.Submodule.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_11 (from Chap06) -/
universe u v

/-
Definition 6.11 lies in the finite convex/simplex domain.

Sampled owner declarations:
* mathlib `stdSimplex`, the canonical owner of the standard simplex;
* mathlib `stdSimplex_eq_inter`, the canonical decomposition into nonnegativity and mass-one
  constraints;
* mathlib `mem_Icc_of_mem_stdSimplex`, a standard derived bound for simplex coordinates;
* project `Definition_5_4_7_16`, which already recalls the same owner in finite-dimensional
  coordinates and exports the shared notation `Δ[n]`.

Best owner abstraction:
* source-facing: the textbook simplex `Δ_n`;
* core/canonical: `stdSimplex 𝕜 ι`;
* bridge/view: the real-coordinate notation `Δ[n] = stdSimplex ℝ (Fin n)`, already owned by
  `Definition_5_4_7_16`.

Primitive data:
* the coefficient type `𝕜`;
* the finite index type `ι`.

Derived API:
* the set-builder characterization of simplex membership;
* the shared source-facing notation `Δ[n]` for the real `Fin n` specialization.

Source/core/bridge triage:
* this file remains a core/canonical recall of `stdSimplex`;
* the notation `Δ[n]` is the shared source-facing bridge reused by Chapter 6 statements, not a
  second owner layer.
-/

open scoped StandardSimplex

/- The source-facing simplex notation is the canonical real `Fin n` specialization. -/
example (n : ℕ) : Set (Fin n → ℝ) := Δ[n]

/- Definition 6.11: the standard simplex `Δ_n` is the canonical mathlib set
`Δ[n] = stdSimplex ℝ (Fin n)`, and in general `stdSimplex 𝕜 ι` is the set of functions with
nonnegative coordinates and total sum equal to `1`. -/
recall stdSimplex (𝕜 : Type v) (ι : Type u) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι] : Set (ι → 𝕜)

/-! ### Lemma_6_11 (from Chap06) -/
universe u v

/- Lemma 6.11 lies in the linear-algebra / submodule domain.

Primary mathematical domain:
- closure of a submodule under subtraction.

Sampled owner-style declarations:
- `Submodule.sub_mem` in mathlib, the canonical subtraction-closure theorem for a submodule;
- `Submodule.add_mem` in mathlib, the additive-closure companion on the same owner;
- `Submodule.neg_mem` in mathlib, the inverse-closure companion deriving subtraction closure.

Best owner abstraction:
- source-facing/core: a submodule `Q₂ : Submodule R M` together with the owner theorem
  `Submodule.sub_mem`;
- bridge/view: this numbered file, which is only a recall surface for that owner theorem.

Primitive data:
- a submodule `Q₂ : Submodule R M`;
- vectors `u`, `uHat : M`;
- membership hypotheses `hu : u ∈ Q₂` and `huHat : uHat ∈ Q₂`.

Derived API:
- the canonical conclusion `u - uHat ∈ Q₂`, provided directly by `Submodule.sub_mem`.

Source/core/bridge triage:
- source-facing: the textbook statement that `Q₂` is closed under subtraction;
- core/canonical: `Submodule.sub_mem`;
- bridge/view: this later numbered recall surface.

This file therefore does not keep a parallel theorem name `sub_mem_of_mem_Q2`: downstream files
should use `Q₂.sub_mem hu huHat` or `Submodule.sub_mem Q₂ hu huHat` directly.
-/

/- Lemma 6.11: for any `u, \hat u ∈ Q₂`, the difference `u - \hat u` also belongs to `Q₂`;
this is exactly the canonical subtraction-closure theorem for a submodule. -/
#check (Submodule.sub_mem : ∀ {R : Type u} {M : Type v}, [Ring R] → [AddCommGroup M] →
  [Module R M] → (Q₂ : Submodule R M) → {u uHat : M} → u ∈ Q₂ → uHat ∈ Q₂ → u - uHat ∈ Q₂)

/-! ### Proposition_6_11 (from Chap06) -/
noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Proposition 6.11 lies in the zero-model smoothing / primal-dual gap complexity domain.

Sampled owner declarations in this domain:
* `explicitModelSmoothingParameter` in `Chap06/Theorem_6_3`, the chapter owner for the chosen
  smoothing scale `μ(N)`;
* `optimized_primal_dual_gap_bound_for_explicit_model_smoothing` in `Chap06/Theorem_6_3`, the
  source-facing owner for the explicit-model gap estimate before fixing `ε`;
* `primal_dual_gap_le_epsilon_of_iteration_bound` in `Chap06/Theorem_6_3`, the stronger chapter
  corollary using the simpler but more restrictive hypothesis `(4 ‖A‖ √(D₁ D₂)) / ε ≤ N`;
* `explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn` in
  `Chap06/Example_6_1_3`, the example-level recall showing that the displayed `L_μ` formula is a
  derived bound rather than a second public owner to be repackaged here.

Best owner abstraction:
* source-facing: the zero-model `ε`-accuracy bridge under the displayed threshold
  `√(N (N + 1)) ≥ 4 ‖A‖ √(D₁ D₂) / ε`;
* core/canonical: `optimized_primal_dual_gap_bound_for_explicit_model_smoothing`;
* bridge/view: the scalar inequality converting that optimized bound to the final `≤ ε`
  conclusion when `M = 0`.

Primitive data:
* the explicit-model smoothing hypotheses from Theorem 6.3;
* the zero-model specialization `M = 0`;
* the displayed lower bound on `√(N (N + 1))`.

Derived API:
* the final bound `f x_N - φ(\hat u_N) ≤ ε`.

Source/core/bridge triage:
* source-facing: the zero-model complexity consequence stated in Proposition 6.11;
* core/canonical: `optimized_primal_dual_gap_bound_for_explicit_model_smoothing`;
* bridge/view: the final scalar comparison between
  `4 ‖A‖ √(D₁ D₂) / √(N (N + 1))` and `ε`.

The previous version introduced a tautological wrapper that merely returned its own threshold
hypothesis together with definitional equalities for `μ` and `L_μ`. This refinement deletes that
parallel packaging and states Proposition 6.11 as the actual zero-model specialization of the
chapter smoothing-gap owner.
-/

-- Proof sketch: specialize
-- `optimized_primal_dual_gap_bound_for_explicit_model_smoothing` at `M = 0`, so the upper bound
-- becomes `4 ‖A‖ √(D₁ D₂) / √(N (N + 1))`. Then use the displayed threshold
-- `4 ‖A‖ √(D₁ D₂) / ε ≤ √(N (N + 1))` to bound that quantity by `ε`.
/-- Proposition 6.11: in the case `M = 0`, if the explicit-model smoothing hypotheses from
Theorem 6.3 hold and
`√(N (N + 1)) ≥ 4 ‖A‖ √(D₁ D₂) / ε`, then the primal-dual gap at `(x_N, \hat u_N)` is at most
`ε`. -/
theorem zero_model_smoothing_complexity_relation
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (f fμ : E₁ → ℝ) (φ : E₂ → ℝ)
    (N : ℕ+) (xN : E₁) (u : Fin ((N : ℕ) + 1) → E₂)
    (D₁ D₂ ε : ℝ) (hε : 0 < ε) (hD₁ : 0 ≤ D₁) (hD₂ : 0 < D₂)
    (hxN_approx :
      fμ xN ≥ f xN - explicitModelSmoothingParameter A D₁ D₂ N * D₂)
    (hφ_le : φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤ fμ xN)
    (hfμ_le : fμ xN ≤ f xN)
    (hsmoothed_gap :
      fμ xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤
        (4 * ‖A‖ ^ (2 : ℕ) * D₁) /
          (explicitModelSmoothingParameter A D₁ D₂ N * ((N : ℝ) * ((N : ℝ) + 1))))
    (hiter :
      (4 * ‖A‖ * Real.sqrt (D₁ * D₂)) / ε ≤
        Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) :
    f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤ ε := by
  have hgap :=
    optimized_primal_dual_gap_bound_for_explicit_model_smoothing
      A f fμ φ N xN u D₁ D₂ 0 hD₁ hD₂ hxN_approx hφ_le hfμ_le (by
        simpa using hsmoothed_gap)
  have hupper :
      f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤
        (4 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) := by
    simpa using hgap.2
  have hsqrt_pos : 0 < Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) := by
    positivity
  have hiter' :
      4 * ‖A‖ * Real.sqrt (D₁ * D₂) ≤
        ε * Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) := by
    have hiter'' := (div_le_iff₀ hε).mp hiter
    simpa [mul_comm] using hiter''
  have hε_bound :
      (4 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) ≤ ε := by
    have :
        (4 * ‖A‖ * Real.sqrt (D₁ * D₂)) /
            Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) ≤ ε :=
      (div_le_iff₀ hsqrt_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hiter')
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  exact le_trans hupper hε_bound

end

/-! ### Theorem_6_11 (from Chap06) -/
open scoped ConstrainedArgmin

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Q : Set E}

/- Theorem 6.11 lies in the Chapter 6 constrained-minimization / primal-oracle domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
- `constrainedArgmin` with notation `argmin[Q]` and `mem_constrainedArgmin_iff` in
  `Chap01/Definition_1_3_3`, the project owner for minimizer sets;
- `explicitModelSmoothedProblem` in `Chap06/Definition_6_9`, the Chapter 6 pattern of keeping the
  objective/problem as the source-facing owner and deriving minimizers canonically;
- `AffineVariationalInequalityProblem.gapProblem` in `Chap06/Definition_6_18`, the nearby Chapter
  6 owner pattern using `Set.univ` on a feasible subtype.

Best owner abstraction:
- source-facing: `linearOptimizationOracleObjective`;
- core/canonical: `argmin[Set.univ] (linearOptimizationOracleObjective s Ψ)`;
- bridge/view: the pointwise evaluation formula and the translation from `IsMinOn` attainment to
  argmin membership.

Primitive data:
- a feasible set `Q : Set E`;
- a linear functional `s : StrongDual ℝ E`;
- a regularizer `Ψ : Q → ℝ`.

Derived API:
- the affine-plus-regularizer objective on the feasible subtype `Q`;
- its canonical minimizer set `argmin[Set.univ] (linearOptimizationOracleObjective s Ψ)`.

Source/core/bridge triage:
- source-facing: `linearOptimizationOracleObjective`;
- core/canonical: `argmin[Set.univ]`;
- bridge/view: `linearOptimizationOracleObjective_apply` and
  `exists_linear_optimization_oracle_point`.

The previous theorem encoded existence of an optimal point through equality with
`sInf (Set.range ...)`. In this project domain, minimizers are canonically owned by `argmin`,
so the main existence theorem now lands in that owner instead of keeping a parallel value-level
existence surface.
-/

/-- The affine-plus-regularizer objective `x ↦ ⟨s, x⟩ + Ψ(x)` on the feasible set `Q`, viewed as
a function on the subtype `Q`. -/
def linearOptimizationOracleObjective (s : StrongDual ℝ E) (Ψ : Q → ℝ) : Q → ℝ :=
  fun x ↦ s x + Ψ x

/-- Evaluating `linearOptimizationOracleObjective s Ψ` at a feasible point `x : Q` gives the sum
of the linear functional value `s x` and the regularizer value `Ψ x`. -/
@[simp]
theorem linearOptimizationOracleObjective_apply
    (s : StrongDual ℝ E) (Ψ : Q → ℝ) (x : Q) :
    linearOptimizationOracleObjective s Ψ x = s x + Ψ x :=
  rfl

/-- Theorem 6.11: if the problem
`min_{x ∈ Q} {⟨s, x⟩ + Ψ(x)}`
admits an optimal solution, then there exists a feasible point `v_Ψ(s)` in the canonical minimizer
set of `linearOptimizationOracleObjective s Ψ` on the feasible subtype `Q`. -/
theorem exists_linear_optimization_oracle_point
    (s : StrongDual ℝ E) (Ψ : Q → ℝ)
    (hattains : ∃ x : Q, IsMinOn (linearOptimizationOracleObjective s Ψ) Set.univ x) :
    ∃ vPsi : Q,
      vPsi ∈ argmin[Set.univ] (linearOptimizationOracleObjective s Ψ) := by
  rcases hattains with ⟨vPsi, hvPsi⟩
  refine ⟨vPsi, ?_⟩
  rw [mem_constrainedArgmin_iff]
  exact ⟨by simp, hvPsi⟩

end
