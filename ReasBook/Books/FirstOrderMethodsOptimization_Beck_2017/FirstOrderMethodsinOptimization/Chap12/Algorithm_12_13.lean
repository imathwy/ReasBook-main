import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Algorithm_12_4
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Algorithm_12_15
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Proposition_12_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Proposition_12_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators

noncomputable section

section

variable {p : ℕ+}

/- Algorithm 12.13 is `source-facing`: it gives the accelerated primal-representation dual block
proximal-gradient method for the finite-sum problem
`min_x {f x + ∑ i, g_i x}`.

Domain sampling against the nearby project owners identifies:
- `dual_proximal_gradient_primal_x_argmax` from Algorithm 12.2 as the canonical owner for the
  step-(a) primal argmax surface, specialized here to `A = LinearMap.id` and the aggregated block
  variable `∑ i, w_i`;
- `dual_proximal_gradient_primal_y_step` from Algorithm 12.2 as the canonical owner for the
  one-block proximal update, specialized here to `A = LinearMap.id` and the block stepsize
  `p / σ`;
- `fista_momentum_update` from Algorithm 10.13 as the canonical owner for the scalar recursion
  `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`;
- `IsFastDualProximalGradientPrimalTrajectory` from Algorithm 12.4 as the `core/canonical`
  accelerated owner after specializing the nonsmooth term to `PiLp.separableSum g` on the block
  Hilbert product and the linear map to the canonical duplication operator from Proposition 12.8.

The primitive data are therefore the explicit sequences `u`, `y`, `w`, and `t`, together with the
coordinatewise Chapter 12 one-block proximal memberships and the momentum recursion. The
source-facing class below keeps the simultaneous block update visible, while a separate bridge
connects it to the Chapter 12.4 accelerated owner. -/

/-- The effective dual-proximal stepsize in Algorithm 12.13 is the positive scalar `p / σ`. -/
def dual_block_proximal_gradient_stepsize (p : ℕ+) (σ : PosReal) : PosReal :=
  (⟨(p : ℝ), show (0 : ℝ) < (p : ℝ) from Nat.cast_pos.mpr p.2⟩ : PosReal) / σ

/-- Coercing the Algorithm 12.13 block stepsize to `ℝ` recovers the scalar `p / σ`. -/
@[simp, norm_cast] theorem dual_block_proximal_gradient_stepsize_coe
    (σ : PosReal) :
    ((dual_block_proximal_gradient_stepsize p σ : PosReal) : ℝ) = (p : ℝ) / (σ : ℝ) :=
  PosReal.coe_div _ σ

end

section

variable {E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℕ+}
variable (E)

/-- The block stepsize `p / σ` is an admissible Chapter 12.1 constant parameter for the diagonal
duplication operator. In the nontrivial case this is exactly Proposition 12.8; in the
subsingleton case the duplication map is zero, so the lower bound is automatic. -/
theorem dual_block_proximal_gradient_stepsize_parameter_lower_bound
    (p : ℕ+) (σ : PosReal) :
    dual_based_proximal_gradient_dual_lipschitz_constant
        (dual_block_duplication E p) σ ≤
      ((dual_block_proximal_gradient_stepsize p σ : PosReal) : ℝ) := by
  obtain hE | hE := subsingleton_or_nontrivial E
  · letI := hE
    have hA : dual_block_duplication E p = 0 := by
      ext z i
      exact Subsingleton.elim _ _
    have h0 : (0 : ℝ) ≤ ((dual_block_proximal_gradient_stepsize p σ : PosReal) : ℝ) :=
      (dual_block_proximal_gradient_stepsize p σ).2.le
    simpa [dual_based_proximal_gradient_dual_lipschitz_constant_eq, hA] using h0
  · letI := hE
    rw [dual_block_duplication_fdpg_lipschitz_constant_eq,
      dual_block_proximal_gradient_stepsize_coe]

/-- The canonical Chapter 12.1 constant parameter for Algorithm 12.13 is the block stepsize
`p / σ` specialized to the diagonal duplication operator. -/
abbrev dual_block_proximal_gradient_stepsize_parameter
    (p : ℕ+) (σ : PosReal) :
    DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) σ :=
  ⟨dual_block_proximal_gradient_stepsize p σ,
    dual_block_proximal_gradient_stepsize_parameter_lower_bound E p σ⟩

end

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {p : ℕ+}

/-- Algorithm 12.13: the sequences `(u^k, y^k, w^k, t_k)` follow the fast dual block
proximal-gradient method when `y⁰ = w⁰ = y0`, `t₀ = 1`, each `u^k` realizes the step-(a) argmax,
each block `y_i^(k+1)` satisfies the canonical Chapter 12 one-block step-(b) proximal condition,
the scalar sequence satisfies `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`, and the extrapolated blocks
satisfy the textbook momentum recursion, recorded in the equivalent public form `w¹ = y¹` and
`w^(k+2) = y^(k+2) + (t_k / t_(k+2)) (y^(k+2) - y^(k+1))`. -/
class IsFastDualBlockProximalGradientPrimalTrajectory
    (f : E → EReal) (g : Fin p → E → EReal) (σ : PosReal)
    (y0 : Fin p → E) (u : ℕ → E) (y w : ℕ → Fin p → E) (t : ℕ → ℝ) : Prop where
  /-- The initial block dual iterate is the prescribed point `y0`. -/
  y_zero : y 0 = y0
  /-- The extrapolated block sequence starts from the same prescribed point `y0`. -/
  w_zero : w 0 = y0
  /-- The acceleration parameter is initialized by `t₀ = 1`. -/
  t_zero : t 0 = 1
  /-- At each step, `u^k` realizes the step-(a) primal argmax at the current extrapolated block
  vector `w^k`. -/
  primal_step (k : ℕ) :
    u k ∈ dual_proximal_gradient_primal_x_argmax f LinearMap.id (∑ i : Fin p, w k i)
  /-- At each step and for each block `i`, the next coordinate `y_i^(k+1)` satisfies the Chapter
  12 one-block proximal update specialized to `A = LinearMap.id`, based at `(u^k, w_i^k)` and
  stepsize `p / σ`. -/
  dual_step (k : ℕ) (i : Fin p) :
    y (k + 1) i ∈
      dual_proximal_gradient_primal_y_step
        (g i)
        LinearMap.id
        (u k)
        (w k i)
        (dual_block_proximal_gradient_stepsize p σ)
  /-- The acceleration scalars satisfy the Chapter 10 FISTA momentum recursion. -/
  acceleration_step (k : ℕ) :
    t (k + 1) = fista_momentum_update (t k)
  /-- The first extrapolated block iterate is recorded explicitly as `w¹ = y¹`. -/
  first_momentum_step : w 1 = y 1
  /-- For every `k`, the later extrapolated block iterates satisfy the shifted textbook momentum
  recursion. -/
  momentum_step (k : ℕ) :
    w (k + 2) =
      y (k + 2) + (t k / t (k + 2)) • (y (k + 2) - y (k + 1))

variable {f : E → EReal} {g : Fin p → E → EReal} {σ : PosReal}
variable {y0 : Fin p → E} {u : ℕ → E} {y w : ℕ → Fin p → E} {t : ℕ → ℝ}

/-- The acceleration field of a fast dual block proximal-gradient primal trajectory expands to the
textbook scalar formula
`t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`. -/
theorem IsFastDualBlockProximalGradientPrimalTrajectory.acceleration_step_formula
    (h : IsFastDualBlockProximalGradientPrimalTrajectory f g σ y0 u y w t)
    (k : ℕ) :
    t (k + 1) = (1 + Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ))) / 2 := by
  simpa [fista_momentum_update_eq] using h.acceleration_step k

/-- Helper for Algorithm 12.13: the linear adjoint of the block duplication map sums the block
coordinates. -/
theorem dual_block_duplication_linear_adjoint_apply
    (v : Fin p → E) :
    ((dual_block_duplication E p).toLinearMap).adjoint (WithLp.toLp 2 v) =
      ∑ i : Fin p, v i := by
  -- Replace the linear adjoint by the already computed continuous adjoint from Proposition 12.7.
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  simpa using dual_block_duplication_adjoint_apply (E := E) (p := (p : ℕ))
    (y := WithLp.toLp 2 v)

/-- Helper for Algorithm 12.13: coordinatewise proximal memberships assemble into proximal
membership for the separable block sum on the `PiLp` product space. -/
theorem mem_prox_separableSum_of_coordinatewise
    {φ : Fin p → E → EReal}
    {x : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)}
    {y : Fin p → E}
    (hy : ∀ i, y i ∈ prox[φ i] (x i)) :
    WithLp.toLp 2 y ∈ prox[PiLp.separableSum φ] x := by
  have hy_min :
      ∀ i, IsMinOn (proximal_objective (φ i) (x i)) Set.univ (y i) := by
    -- Rewrite each coordinatewise proximal membership as a minimizing property.
    intro i
    simpa [mem_proximal_mapping_iff] using hy i
  -- Sum the coordinatewise minimizing inequalities after expanding the separable objective.
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
  intro z
  rw [separable_proximal_objective_eq_sum_coordinate_objectives (f := φ) (x := x)
      (y := WithLp.toLp 2 y)]
  rw [separable_proximal_objective_eq_sum_coordinate_objectives (f := φ) (x := x) (y := z)]
  exact Finset.sum_le_sum (fun i _ ↦ (isMinOn_univ_iff.mp (hy_min i)) (z i))

/-- Helper for Algorithm 12.13: scaling the separable block sum by a positive scalar is the same
as scaling each block function. -/
theorem smul_separableSum_eq_separableSum_smul
    (L : PosReal) :
    (((L : PosReal) : EReal) • PiLp.separableSum g) =
      PiLp.separableSum (fun i ↦ (((L : PosReal) : EReal) • g i)) := by
  funext z
  classical
  let a : EReal := (((L : PosReal) : ℝ) : EReal)
  have ha_nonneg : (0 : EReal) ≤ a := by
    change (0 : EReal) ≤ (((L : PosReal) : ℝ) : EReal)
    exact_mod_cast (show (0 : ℝ) ≤ ((L : PosReal) : ℝ) by exact L.2.le)
  have ha_ne_top : a ≠ ⊤ := EReal.coe_ne_top _
  have hmul_sum :
      a * (∑ i : Fin p, g i (z i)) = ∑ i : Fin p, a * g i (z i) := by
    -- Distribute the positive scalar across the finite block sum in `EReal`.
    refine Finset.induction_on (Finset.univ : Finset (Fin p)) ?_ ?_
    · simp
    · intro i s hi hs
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        EReal.left_distrib_of_nonneg_of_ne_top ha_nonneg ha_ne_top, hs]
  -- Rewrite both sides pointwise to the same finite sum of scaled coordinates.
  rw [Pi.smul_apply, PiLp.separableSum_apply, PiLp.separableSum_apply, smul_eq_mul]
  simpa [a] using hmul_sum

/-- Helper for Algorithm 12.13: coordinatewise block step-(b) updates assemble into the global
Chapter 12.4 primal `y`-step for the duplication operator. -/
theorem mem_dual_primal_y_step_of_coordinatewise_block_steps
    {x : E} {v yNext : Fin p → E}
    (hyNext : ∀ i,
      yNext i ∈
        dual_proximal_gradient_primal_y_step
          (g i)
          LinearMap.id
          x
          (v i)
          (dual_block_proximal_gradient_stepsize p σ)) :
    WithLp.toLp 2 yNext ∈
      dual_proximal_gradient_primal_y_step
        (PiLp.separableSum g)
        (dual_block_duplication E p).toLinearMap
        x
        (WithLp.toLp 2 v)
        (dual_block_proximal_gradient_stepsize p σ) := by
  classical
  let L : PosReal := dual_block_proximal_gradient_stepsize p σ
  have hstep :
      ∀ i,
        ∃ pStep ∈ prox[(((L : PosReal) : EReal) • g i)] (x - (L : ℝ) • v i),
          yNext i = v i - (1 / L : ℝ) • x + (1 / L : ℝ) • pStep := by
    -- Unpack each coordinatewise Chapter 12.2 `y`-step into its proximal witness.
    intro i
    simpa [L] using (mem_dual_proximal_gradient_primal_y_step_iff.mp (hyNext i))
  let pVec : Fin p → E := fun i ↦ Classical.choose (hstep i)
  have hp_mem :
      ∀ i, pVec i ∈ prox[(((L : PosReal) : EReal) • g i)] (x - (L : ℝ) • v i) := by
    intro i
    exact (Classical.choose_spec (hstep i)).1
  have hy_affine :
      ∀ i, yNext i = v i - (1 / L : ℝ) • x + (1 / L : ℝ) • pVec i := by
    intro i
    exact (Classical.choose_spec (hstep i)).2
  have hp_block :
      WithLp.toLp 2 pVec ∈
        prox[(((L : PosReal) : EReal) • PiLp.separableSum g)]
          ((dual_block_duplication E p).toLinearMap x - (L : ℝ) • WithLp.toLp 2 v) := by
    -- The proximal witness is coordinatewise valid at the duplicated block base point.
    rw [smul_separableSum_eq_separableSum_smul (g := g) (p := p) L]
    apply mem_prox_separableSum_of_coordinatewise (p := p)
    intro i
    simpa [L, dual_block_duplication_apply] using hp_mem i
  have hy_block :
      WithLp.toLp 2 yNext =
        WithLp.toLp 2 v - (1 / L : ℝ) • (dual_block_duplication E p).toLinearMap x +
          (1 / L : ℝ) • WithLp.toLp 2 pVec := by
    -- Check the affine update coordinatewise after identifying the duplicated primal block.
    apply PiLp.ext
    intro i
    simpa [L, dual_block_duplication_apply] using hy_affine i
  -- Repackage the assembled proximal witness into the Chapter 12.2 `y`-step owner.
  rw [mem_dual_proximal_gradient_primal_y_step_iff]
  exact ⟨WithLp.toLp 2 pVec, hp_block, hy_block⟩

/-- Helper for Algorithm 12.13: the duplication-space Chapter 12.2 primal argmax condition is
equivalent to the source-facing block-sum argmax condition. -/
theorem mem_dual_primal_x_argmax_duplication_iff
    {x : E} {v : Fin p → E} :
    x ∈
        dual_proximal_gradient_primal_x_argmax
          f
          (dual_block_duplication E p).toLinearMap
          (WithLp.toLp 2 v) ↔
      x ∈ dual_proximal_gradient_primal_x_argmax f LinearMap.id (∑ i : Fin p, v i) := by
  -- TODO: Rewrite both memberships to `isMaxOn_univ_iff`, then bridge the duplication adjoint
  -- to the block sum with an unfolded version of
  -- `dual_block_duplication_linear_adjoint_apply`. The blocker is a coercion mismatch between
  -- `((dual_block_duplication E p).toLinearMap).adjoint` and the unfolded linear-map term
  -- produced by `mem_dual_proximal_gradient_primal_x_argmax_iff`.
  sorry

/-- Any Algorithm 12.13 trajectory canonically yields the Chapter 12.4 accelerated
dual proximal-gradient primal trajectory for the finite-sum block Hilbert-product model, with
nonsmooth term `PiLp.separableSum g`, duplication operator `dual_block_duplication E p`, and
constant parameter `p / σ`. -/
theorem IsFastDualBlockProximalGradientPrimalTrajectory.toFastDualProximalGradientPrimalTrajectory
    (h : IsFastDualBlockProximalGradientPrimalTrajectory f g σ y0 u y w t) :
    IsFastDualProximalGradientPrimalTrajectory
      f (PiLp.separableSum g) (dual_block_duplication E p).toLinearMap σ
      (dual_block_proximal_gradient_stepsize_parameter E p σ)
      (WithLp.toLp 2 y0)
      u
      (fun k ↦ WithLp.toLp 2 (y k))
      (fun k ↦ WithLp.toLp 2 (w k))
      t := by
  refine
    { y_zero := by
        -- Transport the initialization unchanged into the `PiLp` block space.
        simpa using congrArg (WithLp.toLp 2) h.y_zero
      w_zero := by
        -- The extrapolated initialization transports in the same way.
        simpa using congrArg (WithLp.toLp 2) h.w_zero
      t_zero := by
        -- The acceleration scalar is unchanged.
        simpa using h.t_zero
      primal_step := ?_
      dual_step := ?_
      acceleration_step := ?_
      first_momentum_step := ?_
      momentum_step := ?_ }
  · intro k
    -- Route correction: the step-(a) bridge is a local adjoint-normalization lemma, not an import
    -- issue. Use the dedicated duplication/block-sum adapter to transport the source-facing rule.
    exact
      (mem_dual_primal_x_argmax_duplication_iff
        (f := f) (E := E) (p := p) (x := u k) (v := w k)).2 (h.primal_step k)
  · intro k
    -- Assemble the coordinatewise step-(b) witnesses into the product-space proximal step.
    simpa using
      mem_dual_primal_y_step_of_coordinatewise_block_steps
        (g := g) (σ := σ) (x := u k) (v := w k) (yNext := y (k + 1))
        (fun i ↦ h.dual_step k i)
  · intro k
    -- The scalar momentum recursion is identical to Algorithm 12.4.
    simpa using h.acceleration_step k
  · -- The first extrapolated point is transported through `WithLp.toLp`.
    simpa using congrArg (WithLp.toLp 2) h.first_momentum_step
  · intro k
    -- Transport the shifted momentum identity through the linear `WithLp.toLp` map.
    simpa using congrArg (WithLp.toLp 2) (h.momentum_step k)

end
