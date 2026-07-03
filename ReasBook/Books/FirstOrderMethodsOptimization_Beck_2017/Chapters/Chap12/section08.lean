import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_8 (from Chap12) -/
noncomputable section

section

variable {n p : ℕ}

/- Definition 12.8 is `source-facing`: it introduces the polyhedral feasible region cut out by
`A x ≤ b` in `ℝ^n` and then reuses the chapter owner `projectionPoint` for orthogonal projection
onto that set.

Domain sampling for this file identifies the relevant owner abstractions as follows.
- `inequality_feasible_set` from Chapter 3 is the canonical owner for finitely many inequality
  constraints;
- orthogonal projection onto a nonempty closed convex set is already owned upstream in Chapter 3
  by `projectionPoint` and its derived API.

Primitive data are therefore only the matrix-induced constraint family
`(i, x) ↦ A.toEuclideanLin x i - b i`; the feasible set is derived from the Chapter 3 owner, and
the projection/minimizer facts stay upstream at that owner level rather than being repackaged as
parallel local theorems here. -/

/-- Definition 12.8. The polyhedral feasible set `S = {x ∈ ℝ^n | A x ≤ b}` associated to the
matrix inequality system `A x ≤ b`. -/
def polyhedral_projection_feasible_set
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  inequality_feasible_set (fun i x ↦ A.toEuclideanLin x i - b i)

/-- Helper for Definition 12.8: membership in the polyhedral feasible set means satisfying each
row inequality `A x ≤ b`. -/
@[simp] theorem mem_polyhedral_projection_feasible_set
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ polyhedral_projection_feasible_set A b ↔
      ∀ i : Fin p, A.toEuclideanLin x i ≤ b i := by
  -- Unfold the Chapter 3 feasible-set owner and translate each residual inequality rowwise.
  constructor
  · intro hx i
    exact sub_nonpos.mp (show A.toEuclideanLin x i - b i ≤ 0 from hx i)
  · intro hx i
    exact sub_nonpos.mpr (hx i)

/-- Helper for Definition 12.8: the polyhedral feasible set is exactly the set of points
satisfying every row inequality `A x ≤ b`. -/
theorem polyhedral_projection_feasible_set_eq_setOf
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) :
    polyhedral_projection_feasible_set A b =
      {x | ∀ i : Fin p, A.toEuclideanLin x i ≤ b i} := by
  -- Extensionality reduces the set equality to the rowwise membership characterization.
  ext x
  simp [mem_polyhedral_projection_feasible_set]

/- Definition 12.8 packages the feasible region `S = {x ∈ ℝ^n | A x ≤ b}` itself. The orthogonal
projection problem onto `S` is then handled by the upstream Chapter 3 owner `projectionPoint`
once nonemptiness, closedness, and convexity of `S` are supplied in later developments. -/

end

/-! ### Proposition_12_8 (from Chap12) -/
open scoped ENNReal BigOperators

noncomputable section

universe u

section

variable {E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 12.8 is `source-facing`: it computes the dual smoothness constant for the specific
diagonal duplication operator `𝒜(z) = (z, …, z)` used to rewrite the block problem in Chapter 12.

Domain sampling against nearby project owners and mathlib points to:
- `dual_based_proximal_gradient_dual_lipschitz_constant` from Algorithm 12.1 as the canonical
  owner for the FDPG parameter `L = ‖𝒜‖² / σ`;
- `PiLp (2 : ENNReal)` as the canonical `L²` block-product owner from Chapter 11;
- `ContinuousLinearMap.pi` together with `PiLp.continuousLinearEquiv` as the canonical realization
  of the diagonal map into the `p`-fold block product.

The public API should therefore expose the actual diagonal continuous linear map and state the
constant formula directly for that canonical owner, rather than through a surrogate package. -/

variable (E) in
/-- The diagonal duplication operator sending `z` to the constant `p`-block vector
`(z, \ldots, z)` in the `L²` block product `PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)`. -/
abbrev dual_block_duplication
    (p : ℕ) : E →L[ℝ] PiLp (2 : ENNReal) (fun _ : Fin p ↦ E) :=
  ((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun _ : Fin p ↦ ContinuousLinearMap.id ℝ E)

-- Proof sketch: unfold `dual_block_duplication`; `ContinuousLinearMap.pi` forms the constant
-- function `fun _ ↦ z`, and `PiLp.continuousLinearEquiv` identifies that function with its point in
-- the `L²` block product.
/-- Every block coordinate of the duplicated vector `𝒜(z)` is equal to `z`. -/
@[simp] theorem dual_block_duplication_apply
    (p : ℕ) (z : E) (i : Fin p) :
    dual_block_duplication E p z i = z := by
  simp [dual_block_duplication]

variable (E) in
/-- Helper for Proposition 12.8: the duplicated `L²` block vector has squared norm
`p * ‖z‖²`. -/
lemma dual_block_duplication_norm_sq_apply
    (p : ℕ) (z : E) :
    ‖dual_block_duplication E p z‖ ^ (2 : ℕ) = (p : ℝ) * ‖z‖ ^ (2 : ℕ) := by
  -- Expand the `PiLp` norm into the sum of coordinate squares.
  calc
    ‖dual_block_duplication E p z‖ ^ (2 : ℕ)
        = ∑ i : Fin p, ‖dual_block_duplication E p z i‖ ^ (2 : ℕ) := by
            simpa using
              (PiLp.norm_sq_eq_of_L2 (fun _ : Fin p ↦ E) (dual_block_duplication E p z))
    _ = ∑ i : Fin p, ‖z‖ ^ (2 : ℕ) := by
          simp
    _ = (p : ℝ) * ‖z‖ ^ (2 : ℕ) := by
          simp

variable (E) in
/-- Helper for Proposition 12.8: the duplication map scales every norm by `√p`. -/
lemma dual_block_duplication_norm_apply
    (p : ℕ) (z : E) :
    ‖dual_block_duplication E p z‖ = Real.sqrt (p : ℝ) * ‖z‖ := by
  have hp_nonneg : 0 ≤ (p : ℝ) := by
    exact_mod_cast Nat.zero_le p
  -- Compare squares of the two nonnegative quantities.
  refine (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp ?_
  rw [dual_block_duplication_norm_sq_apply, mul_pow, Real.sq_sqrt hp_nonneg]

-- Proof sketch: evaluate `‖dual_block_duplication p z‖²` using `PiLp.norm_sq_eq_of_L2`; this gives
-- `∑ i : Fin p, ‖z‖² = p * ‖z‖²`. The upper bound `‖𝒜‖² ≤ p` follows from this identity and
-- `ContinuousLinearMap.opNorm_le_bound`; the matching lower bound is obtained by testing the map on
-- any nonzero vector of norm `1`.
variable [Nontrivial E]

/-- The diagonal duplication operator on the `p`-fold `L²` block product has squared operator norm
`p`. -/
theorem dual_block_duplication_opNorm_sq
    (p : ℕ) :
    ‖dual_block_duplication E p‖ ^ (2 : ℕ) = (p : ℝ) := by
  have hp_nonneg : 0 ≤ (p : ℝ) := by
    exact_mod_cast Nat.zero_le p
  have hnorm :
      ‖dual_block_duplication E p‖ = Real.sqrt (p : ℝ) := by
    -- The vectorwise scaling formula identifies the map as a homothety of ratio `√p`.
    simpa using
      (ContinuousLinearMap.homothety_norm (dual_block_duplication E p)
        (dual_block_duplication_norm_apply (E := E) p))
  -- Square the operator-norm identity to recover the textbook constant `‖𝒜‖² = p`.
  calc
    ‖dual_block_duplication E p‖ ^ (2 : ℕ) = (Real.sqrt (p : ℝ)) ^ (2 : ℕ) := by
      rw [hnorm]
    _ = (p : ℝ) := by
      exact Real.sq_sqrt hp_nonneg

-- Proof sketch: unfold the Chapter 12.1 owner
-- `dual_based_proximal_gradient_dual_lipschitz_constant`, then substitute
-- `dual_block_duplication_opNorm_sq`.
/-- Proposition 12.8: for the diagonal duplication operator `𝒜(z) = (z, \ldots, z)`, the FDPG
parameter from Algorithm 12.1 satisfies `L = ‖𝒜‖² / σ = p / σ`. -/
@[simp]
theorem dual_block_duplication_fdpg_lipschitz_constant_eq
    (σ : PosReal) (p : ℕ) :
    dual_based_proximal_gradient_dual_lipschitz_constant
        (dual_block_duplication E p) σ =
      (p : ℝ) / (σ : ℝ) := by
  rw [dual_based_proximal_gradient_dual_lipschitz_constant_eq, dual_block_duplication_opNorm_sq]

end

/-! ### Theorem_12_8 (from Chap12) -/
noncomputable section

universe u v

open scoped Gradient

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/- Theorem 12.8 has a `core/canonical` rate statement and a `source-facing` bridge.

Domain sampling in Chapter 12 identifies:
- `is_dual_based_proximal_gradient_dual_trajectory` from Algorithm 12.1 as the owner of the dual
  iterates that enter the objective-gap bound from Theorem 12.4;
- `dual_proximal_gradient_primal_x_argmax` from Algorithm 12.2 as the owner of the primal point
  condition used by Lemma 12.7;
- `is_dual_proximal_gradient_primal_trajectory` as the heavier source trajectory wrapper that
  packages both pieces together.

The distance estimate itself only uses the canonical dual trajectory together with the pointwise
argmax condition for `x k`, so the source trajectory wrapper should appear only through a thin
bridge to those two primitive ingredients. -/

/-- A source-facing Algorithm 12.2 primal trajectory canonically determines the underlying
Algorithm 12.1 dual proximal-gradient trajectory for the Chapter 12 dual composite `F + G`. -/
theorem is_dual_proximal_gradient_primal_trajectory.toDualTrajectory
    {σ : PosReal}
    {f : E → EReal} {g : V → EReal} {A : E →ₗ[ℝ] V}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    {y0 : V} {x : ℕ → E} {y : ℕ → V}
    (htraj : is_dual_proximal_gradient_primal_trajectory f g A L y0 x y) :
    is_dual_based_proximal_gradient_dual_trajectory
      (fun z : V ↦ (g∗) (-z))
      (fun z : V ↦ ∇ (fun z' : V ↦ ((f∗) (A.adjoint z')).toReal) z)
      L y y0 := sorry

-- Proof sketch: combine Lemma 12.7, applied to the pointwise argmax hypothesis `hx k`, with the
-- dual-gap estimate from Theorem 12.4 for the canonical dual trajectory `htraj`. Lemma 12.7 gives
-- `‖x k - xStar‖² ≤ (2 / σ) (q_opt - q(y k))`, and Theorem 12.4 bounds the dual gap by
-- `L ‖y0 - yStar‖² / (2 k)`. Multiplying the bounds and simplifying cancels the factor `2`.
/-- The `core/canonical` primal-distance estimate over the Chapter 12 dual trajectory owner,
with the primal sequence supplied only through the pointwise argmax owner. -/
theorem dual_proximal_gradient_primal_sequence_sqdist_le_of_dual_trajectory
    (σ : PosReal) (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y0 : V) (x : ℕ → E) (y : ℕ → V)
    (htraj :
      is_dual_based_proximal_gradient_dual_trajectory
        (fun z : V ↦ (g∗) (-z))
        (fun z : V ↦ ∇ (fun z' : V ↦ ((f∗) (A.adjoint z')).toReal) z)
        L y y0)
    (hx : ∀ k : ℕ, x k ∈ dual_proximal_gradient_primal_x_argmax f A (y k))
    (xStar : E)
    (hxStar : IsMinOn (composite_model_objective f (g ∘ A)) Set.univ xStar)
    (yStar : V)
    (hyStar :
      dual_based_proximal_gradient_lagrange_dual_objective_primal
          f g A yStar =
        dual_based_proximal_gradient_lagrange_dual_problem_value f g A)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖x k - xStar‖ ^ (2 : ℕ) ≤
      (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / ((σ : ℝ) * (k : ℝ)) := sorry

-- Proof sketch: extract the pointwise argmax membership from the source-facing Algorithm 12.2
-- trajectory via the primitive field `htraj.primal_step`, pass to the canonical dual trajectory
-- owner with `htraj.toDualTrajectory`, and apply the core theorem above.
/-- Theorem 12.8: under Assumption 12.1, if `(x^k, y^k)` is generated by the dual proximal
gradient method with an admissible constant parameter `L`, then for every primal optimal
solution `x*`, every dual optimal solution `y*`, and every `k ≥ 1`, the primal iterate satisfies
the sublinear estimate `‖x^k - x*‖² ≤ L ‖y^0 - y*‖² / (σ k)`. -/
theorem dual_proximal_gradient_primal_sequence_sqdist_le
    (σ : PosReal) (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y0 : V) (x : ℕ → E) (y : ℕ → V)
    (htraj : is_dual_proximal_gradient_primal_trajectory f g A L y0 x y)
    (xStar : E)
    (hxStar : IsMinOn (composite_model_objective f (g ∘ A)) Set.univ xStar)
    (yStar : V)
    (hyStar :
      dual_based_proximal_gradient_lagrange_dual_objective_primal
          f g A yStar =
        dual_based_proximal_gradient_lagrange_dual_problem_value f g A)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖x k - xStar‖ ^ (2 : ℕ) ≤
      (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / ((σ : ℝ) * (k : ℝ)) := by
  simpa using
    dual_proximal_gradient_primal_sequence_sqdist_le_of_dual_trajectory
      σ f g A L h_problem y0 x y (htraj.toDualTrajectory)
      htraj.primal_step
      xStar hxStar yStar hyStar k hk

end
