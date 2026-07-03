import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_14 (from Chap12) -/
universe u

open scoped BigOperators

section

variable {E : Type u}

/- Definition 12.14 is a `bridge/view` recall: the block primal objective
`x ↦ f x + ∑ i : Fin p, g i x` is already owned by the Chapter 10 composite objective applied to
the Chapter 8 finite-sum aggregate.

Domain sampling in the surrounding project identifies:
- `core/canonical`: `composite_model_objective` for the outer two-term split;
- `core/canonical`: `finite_sum_objective` for the block family `g`;
- `bridge/view`: the specialization to a family indexed by `Fin p`.

Primitive data are only `f` and the finite family `g`. Since the source introduces no new owner
beyond that specialization, this file should recall the existing owners and their pointwise
evaluation formulas directly, rather than keep a parallel Chapter 12 alias. -/

/- Definition 12.14: the dual block proximal-gradient primal objective is exactly the Chapter 10
composite objective specialized to the Chapter 8 finite-sum term. -/
recall composite_model_objective
recall finite_sum_objective

/- In source-facing form, Definition 12.14 is the specialization
`fun f g ↦ composite_model_objective f (finite_sum_objective g)`. -/
#check fun {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) ↦
  composite_model_objective f (finite_sum_objective g)

/- Pointwise, the same owner is the block objective `x ↦ f x + ∑ i : Fin p, g i x`. -/
#check fun {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) (x : E) ↦
  f x + ∑ i : Fin p, g i x

end

/-! ### Theorem_12_14 (from Chap12) -/
noncomputable section

universe u v

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory ENNReal

section

variable {Ω : Type v} {E : Type u} {p : ℕ}
variable [NeZero p]
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 12.14 is `source-facing`: it is the randomized-order `O(1 / k)` rate statement for
the Chapter 12 dual block proximal-gradient method.

Domain sampling against the surrounding project APIs identifies the relevant owners:
- `IsDualBlockProximalGradientProblem` for Assumption 12.14;
- `is_dual_block_proximal_gradient_primal_trajectory` from Algorithm 12.15 as the pathwise owner
  of the realized primal/dual iterates driven by a realized block-choice rule;
- `dual_block_proximal_gradient_dual_objective` and
  `dual_block_proximal_gradient_dual_optimal_set` for the canonical block dual objective `q` and
  its optimal set `Λ*`; and
- `μ[...]` from the probability API, with theorem-level `Integrable` hypotheses exactly as in the
  randomized block proximal-gradient results of Chapter 11 and the realized-process style used by
  later randomized block methods in the project.

Primitive stochastic data are therefore the sampled blocks together with the realized iterate
processes `x : ℕ → Ω → E` and `y : ℕ → Ω → Fin p → E`. History-adapted realization is kept only
through the pathwise hypothesis
`∀ ω, is_dual_block_proximal_gradient_primal_trajectory ... (fun k ↦ x k ω) (fun k ↦ y k ω)`,
which is the canonical bridge from the probabilistic layer to the Chapter 12 pathwise algorithmic
owner. No measurable structure on `E` is primitive here: the theorem integrates only the
real-valued observables `(q (y (k + 1) ω)).toReal` and `‖x (k + 1) ω - x*‖²` on the probability
space `Ω`.

The source contains two independent quantitative conclusions, so the item is split into two atomic
theorem statements: the expected dual-gap estimate and the expected primal squared-distance
estimate. -/

section

variable (σ : PosReal) (f : E → EReal) (g : Fin p → E → EReal)
variable (y0 : Fin p → E)
variable (sampled_block : ℕ → Ω → Fin p)
variable (x : ℕ → Ω → E)
variable (y : ℕ → Ω → Fin p → E)

local notation "F" => composite_model_objective f (finite_sum_objective g)

variable
  (h_problem : IsDualBlockProximalGradientProblem f g σ)
  (h_traj :
    ∀ ω,
      is_dual_block_proximal_gradient_primal_trajectory
        f g σ (fun n ↦ sampled_block n ω) y0
        (fun n ↦ x n ω)
        (fun n ↦ y n ω))
  (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
  (h_sampled_block_indep : iIndepFun sampled_block μ)
  (h_sampled_block_uniform :
    ∀ k (i : Fin p), μ ((sampled_block k) ⁻¹' {i}) = 1 / (p : ℝ≥0∞))
  (yStar : Fin p → E)
  (hyStar : yStar ∈ Λ*(f, g))
  (hy0_finite : y0 ∈ finite_domain (q(f, g)))
  (hyStar_finite : yStar ∈ finite_domain (q(f, g)))

/-- Helper for Theorem 12.14: the Chapter 11 constant-weight initial norm term rewrites to the
explicit Lyapunov coefficient on the canonical block `L²` owner `WithLp.toLp 2 (y0 - yStar)`. -/
lemma half_weighted_sqnorm_eq_initial_lyapunov
    (σ : PosReal) (y0 yStar : Fin p → E) :
    (1 / 2 : ℝ) *
        compositeWeightedL2Norm (fun _ : Fin p ↦ σ⁻¹) (y0 - yStar) ^ (2 : ℕ) =
      (1 / (2 * (σ : ℝ))) * ‖WithLp.toLp 2 (y0 - yStar)‖ ^ (2 : ℕ) := by
  have hσ : (σ : ℝ) ≠ 0 := by
    exact ne_of_gt σ.2
  have hsum_nonneg :
      0 ≤ ∑ i : Fin p, (((σ⁻¹ : PosReal) : ℝ)) * ‖(y0 - yStar) i‖ ^ (2 : ℕ) := by
    refine Finset.sum_nonneg ?_
    intro i hi
    have hweight_nonneg : 0 ≤ (((σ⁻¹ : PosReal) : ℝ)) := by
      exact le_of_lt (σ⁻¹).2
    have hnormsq_nonneg : 0 ≤ ‖(y0 - yStar) i‖ ^ (2 : ℕ) := by
      simpa [pow_two] using sq_nonneg ‖(y0 - yStar) i‖
    exact mul_nonneg hweight_nonneg hnormsq_nonneg
  -- Expand the weighted norm into the explicit weighted `L²` sum.
  calc
    (1 / 2 : ℝ) *
        compositeWeightedL2Norm (fun _ : Fin p ↦ σ⁻¹) (y0 - yStar) ^ (2 : ℕ)
        =
      (1 / 2 : ℝ) *
        ∑ i : Fin p, (((σ⁻¹ : PosReal) : ℝ)) * ‖(y0 - yStar) i‖ ^ (2 : ℕ) := by
          rw [compositeWeightedL2Norm_def, Real.sq_sqrt hsum_nonneg]
    _ =
      (1 / 2 : ℝ) *
        ((σ : ℝ)⁻¹ * ∑ i : Fin p, ‖(y0 - yStar) i‖ ^ (2 : ℕ)) := by
          -- The weight is constant across blocks, so it factors out of the finite sum.
          rw [show (((σ⁻¹ : PosReal) : ℝ)) = (σ : ℝ)⁻¹ by rfl, ← Finset.mul_sum]
    _ = (1 / 2 : ℝ) * ((σ : ℝ)⁻¹ * ‖WithLp.toLp 2 (y0 - yStar)‖ ^ (2 : ℕ)) := by
          -- Identify the coordinate sum with the squared norm on the `PiLp` owner.
          congr 2
          symm
          simpa using
            (PiLp.norm_sq_eq_of_L2 (fun _ : Fin p ↦ E) (WithLp.toLp 2 (y0 - yStar)))
    _ = (1 / (2 * (σ : ℝ))) * ‖WithLp.toLp 2 (y0 - yStar)‖ ^ (2 : ℕ) := by
          field_simp [hσ]

/-- Helper for Theorem 12.14: an optimal block-dual point identifies the source-facing dual
optimum after passing to `EReal.toReal`. -/
lemma dual_problem_value_toReal_eq_of_mem_optimal_set
    {yStar : Fin p → E} (hyStar : yStar ∈ Λ*(f, g)) :
    EReal.toReal (q_opt(f, g)) = (q(f, g) yStar).toReal := by
  -- Rewrite the optimum value with the canonical optimal-set owner from Definition 12.17.
  rw [← dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
    f g hyStar]

/-- Helper for Theorem 12.14: each realized DBPG trajectory exposes the source step-(a) primal
argmax condition at every iterate. -/
lemma realized_dbpg_primal_argmax_at
    (h_traj :
      ∀ ω,
        is_dual_block_proximal_gradient_primal_trajectory
          f g σ (fun n ↦ sampled_block n ω) y0
          (fun n ↦ x n ω)
          (fun n ↦ y n ω))
    (k : ℕ) (ω : Ω) :
    x k ω ∈ dual_proximal_gradient_primal_x_argmax f LinearMap.id (∑ j, y k ω j) := by
  -- The realized DBPG trajectory owner already packages the step-(a) argmax membership.
  exact (is_dual_block_proximal_gradient_primal_trajectory_step (h_traj ω) k).1

/-- Helper for Theorem 12.14: the duplication-space Chapter 12 primal argmax owner is equivalent
to the source block-sum argmax owner at the same block vector. -/
lemma dual_primal_x_argmax_duplication_iff_sum
    {xBar : E} {v : Fin p → E} :
    xBar ∈
        dual_proximal_gradient_primal_x_argmax
          f
          (dual_block_duplication E p).toLinearMap
          (WithLp.toLp 2 v) ↔
      xBar ∈ dual_proximal_gradient_primal_x_argmax f LinearMap.id (∑ i : Fin p, v i) := by
  -- Rewrite both owners to the canonical `IsMaxOn` condition and normalize the duplication
  -- adjoint to the block sum.
  rw [mem_dual_proximal_gradient_primal_x_argmax_iff,
    mem_dual_proximal_gradient_primal_x_argmax_iff]
  have hadj := by
    -- Route correction: keep the canonical duplication-adjoint theorem, then let `simpa` unfold
    -- the local duplication owner only at the final transport step.
    simpa using
      (dual_block_duplication_linear_adjoint_apply
        (E := E) (p := p) (y := WithLp.toLp 2 v))
  constructor <;> intro hx <;> simpa [dual_block_duplication, hadj] using hx

/-- Helper for Theorem 12.14: once both the optimal dual point and the sampled dual point are
finite, the `EReal` dual gap rewrites to the scalar gap after applying `toReal`. -/
lemma dual_gap_toReal_eq_of_mem_finite_domain
    {yBar yStar : Fin p → E}
    (hyStar : yStar ∈ Λ*(f, g))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g)))
    (hyBar_finite : yBar ∈ finite_domain (q(f, g))) :
    (q_opt(f, g) - q(f, g) yBar).toReal =
      EReal.toReal (q_opt(f, g)) - (q(f, g) yBar).toReal := by
  have hqOpt_ne_top : q_opt(f, g) ≠ ⊤ := by
    -- The optimal value is attained at `yStar`, so finiteness of `q(yStar)` transfers to `q_opt`.
    rw [← dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
      f g hyStar]
    exact (mem_finite_domain.mp hyStar_finite).1.ne
  have hqOpt_ne_bot : q_opt(f, g) ≠ ⊥ := by
    -- The same attained-value identification also transfers the non-`⊥` side.
    rw [← dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
      f g hyStar]
    exact (mem_finite_domain.mp hyStar_finite).2
  have hyBar_ne_top : q(f, g) yBar ≠ ⊤ := by
    -- Membership in `finite_domain` records that the sampled dual value is finite above.
    exact (mem_finite_domain.mp hyBar_finite).1.ne
  have hyBar_ne_bot : q(f, g) yBar ≠ ⊥ := by
    -- Membership in `finite_domain` also records the non-`⊥` side.
    exact (mem_finite_domain.mp hyBar_finite).2
  -- With both endpoints finite, `EReal.toReal_sub` gives the scalar gap identity directly.
  rw [EReal.toReal_sub hqOpt_ne_top hqOpt_ne_bot hyBar_ne_top hyBar_ne_bot]

/-- Helper for Theorem 12.14: the Chapter 11 minimization surface on block-dual variables is
pointwise the negation of the source-facing block dual objective `q`. -/
lemma dual_block_dual_minimization_view_apply
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (v : Fin p → E) :
    composite_model_objective
        (fun w : Fin p → E ↦ (f∗) (∑ i : Fin p, w i))
        (separableSum (fun i z ↦ ((g i)∗) (-z)))
        v =
      - q(f, g) v := by
  let a : EReal := (f∗) (∑ i : Fin p, v i)
  let b : EReal := ∑ i : Fin p, ((g i)∗) (-v i)
  have ha_ne_bot : a ≠ ⊥ := by
    -- The strongly convex primal term has a finite-valued conjugate at every aggregated dual sum.
    have hfin :=
      conjugate_function_finite_of_proper_closed_strongConvexOn
        (σ : ℝ)
        σ.2
        f
        h_problem.toIsProperExtendedRealFunction.ne_bot
        h_problem.toIsProperExtendedRealFunction.effective_domain_nonempty
        h_problem.f_closed
        h_problem.f_strongly_convex
        (InnerProductSpace.toDual ℝ E (∑ i : Fin p, v i))
    simpa [a, conjugate_function_strongDual, conjugate_function_primal_apply,
      conjugate_function] using hfin.1
  have hb_ne_bot : b ≠ ⊥ := by
    -- Each block conjugate term is proper, so their finite sum also avoids `⊥`.
    refine ereal_sum_ne_bot Finset.univ (fun i ↦ ((g i)∗) (-v i)) ?_
    intro i _
    have hg_conj_proper :
        IsProperExtendedRealFunction (conjugate_function (g i)) :=
      isProperExtendedRealFunction_conjugate_function
        (g i)
        (h_problem.g_proper i)
        (h_problem.g_convex i)
    simpa [conjugate_function_primal_apply] using
      hg_conj_proper.ne_bot (InnerProductSpace.toDualMap ℝ E (-v i))
  have ha_top : -a ≠ ⊤ := by
    -- Negating a non-`⊥` extended-real value cannot produce `⊤`.
    intro ha_top
    have : a = ⊥ := by
      simpa [a] using congrArg Neg.neg ha_top
    exact ha_ne_bot this
  have hneg : -(-a - b) = a + b := by
    -- Excluding the mixed `⊤/⊥` case allows the outer negation to distribute through subtraction.
    have hraw : -(-a - b) = -(-a) + b := by
      exact EReal.neg_sub (Or.inr hb_ne_bot) (Or.inl ha_top)
    simpa [a, b] using hraw
  -- Unfold the Chapter 11 objective and the Chapter 12 dual objective, then match the two sides.
  rw [composite_model_objective_apply, separableSum_apply,
    dual_block_proximal_gradient_dual_objective_apply]
  change a + b = -(-a - b)
  simpa [a, b] using hneg.symm

/-- Helper for Theorem 12.14: a `PiLp` block vector lies in the effective domain of the separable
block penalty exactly when each coordinate lies in the corresponding block effective domain. -/
lemma mem_effective_domain_piLp_separableSum_iff
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    {z : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)} :
    z ∈ effective_domain (PiLp.separableSum g) ↔
      ∀ i : Fin p, z i ∈ effective_domain (g i) := by
  constructor
  · intro hz i
    -- A finite separable-sum value forces every coordinate block penalty to stay finite above.
    exact
      block_mem_effective_domain_of_mem_separableSum_effective_domain
        g hg_proper
        (by simpa [mem_effective_domain] using hz)
        i
  · intro hz
    -- Coordinatewise finite-domain membership makes the finite separable sum stay below `⊤`.
    rw [mem_effective_domain]
    exact
      ereal_sum_lt_top Finset.univ
        (fun i ↦ g i (z i))
        (fun i _ ↦ mem_effective_domain.mp (hz i))

/-- Helper for Theorem 12.14: if a scalar point is feasible for every block penalty, then its
duplicated block vector is feasible for the `PiLp` separable sum. -/
lemma constant_block_mem_effective_domain_piLp_separableSum
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    {xHat : E}
    (hxHat_g : ∀ i : Fin p, xHat ∈ effective_domain (g i)) :
    (dual_block_duplication E p).toLinearMap xHat ∈ effective_domain (PiLp.separableSum g) := by
  -- The duplicated block vector has every coordinate equal to `xHat`, so the coordinatewise
  -- effective-domain criterion closes immediately.
  rw [mem_effective_domain_piLp_separableSum_iff (g := g) hg_proper]
  simpa [dual_block_duplication_apply] using hxHat_g

/-- Helper for Theorem 12.14: the coordinatewise relative-interior witness from Assumption 12.14
already implies that the duplicated block vector lies in the effective domain of the `PiLp`
separable sum. -/
lemma constant_block_mem_effective_domain_piLp_separableSum_of_intrinsicInterior
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    {xHat : E}
    (hxHat_g : ∀ i : Fin p, xHat ∈ intrinsicInterior ℝ (effective_domain (g i))) :
    (dual_block_duplication E p).toLinearMap xHat ∈ effective_domain (PiLp.separableSum g) := by
  -- Strip only the set-membership content from the coordinatewise relative-interior witnesses.
  have hxHat_dom : ∀ i : Fin p, xHat ∈ effective_domain (g i) := by
    intro i
    exact intrinsicInterior_subset (hxHat_g i)
  exact constant_block_mem_effective_domain_piLp_separableSum
    (g := g) hg_proper (xHat := xHat) hxHat_dom

/-- Helper for Theorem 12.14: the relative interiors of two sets combine to the relative interior
of their Cartesian product. This is the finite-product bridge needed before transporting the
coordinatewise qualification witness to the duplicated block owner. -/
private theorem mem_intrinsicInterior_prod
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {S : Set E} {T : Set V} {x : E} {z : V}
    (hx : x ∈ intrinsicInterior ℝ S)
    (hz : z ∈ intrinsicInterior ℝ T) :
    (x, z) ∈ intrinsicInterior ℝ (S ×ˢ T) := by
  -- Route correction: use the closed-ball characterization from Definition 3.7, then project the
  -- product affine-span condition to each coordinate before reusing the source witnesses.
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hx with
    ⟨hx_span, εS, hεS, hballS⟩
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hz with
    ⟨hz_span, εT, hεT, hballT⟩
  refine (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).2 ?_
  refine ⟨subset_affineSpan ℝ (S ×ˢ T) ⟨intrinsicInterior_subset hx, intrinsicInterior_subset hz⟩,
    min εS εT, lt_min hεS hεT, ?_⟩
  intro uv huv
  rcases uv with ⟨u, v⟩
  rcases huv with ⟨huv_ball, huv_span⟩
  have huv_dist : max (dist u x) (dist v z) ≤ min εS εT := by
    simpa [Prod.dist_eq, max_comm, max_left_comm, max_assoc] using huv_ball
  have hu_ball : u ∈ Metric.closedBall x εS := by
    exact Metric.mem_closedBall.2 <|
      le_trans ((max_le_iff.1 huv_dist).1) (min_le_left εS εT)
  have hv_ball : v ∈ Metric.closedBall z εT := by
    exact Metric.mem_closedBall.2 <|
      le_trans ((max_le_iff.1 huv_dist).2) (min_le_right εS εT)
  have hu_span_prod :
      u ∈ affineSpan ℝ (((LinearMap.fst ℝ E V).toAffineMap) '' (S ×ˢ T)) := by
    have hmem_map :
        u ∈ (affineSpan ℝ (S ×ˢ T)).map ((LinearMap.fst ℝ E V).toAffineMap) := by
      simpa using
        (AffineSubspace.mem_map_of_mem (f := (LinearMap.fst ℝ E V).toAffineMap) huv_span)
    rw [AffineSubspace.map_span] at hmem_map
    exact hmem_map
  have hv_span_prod :
      v ∈ affineSpan ℝ (((LinearMap.snd ℝ E V).toAffineMap) '' (S ×ˢ T)) := by
    have hmem_map :
        v ∈ (affineSpan ℝ (S ×ˢ T)).map ((LinearMap.snd ℝ E V).toAffineMap) := by
      simpa using
        (AffineSubspace.mem_map_of_mem (f := (LinearMap.snd ℝ E V).toAffineMap) huv_span)
    rw [AffineSubspace.map_span] at hmem_map
    exact hmem_map
  have hu_span : u ∈ affineSpan ℝ S := by
    refine (affineSpan_mono ℝ ?_) hu_span_prod
    rintro _ ⟨p, hp, rfl⟩
    exact hp.1
  have hv_span : v ∈ affineSpan ℝ T := by
    refine (affineSpan_mono ℝ ?_) hv_span_prod
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2
  exact ⟨hballS ⟨hu_ball, hu_span⟩, hballT ⟨hv_ball, hv_span⟩⟩

/-- Helper for Theorem 12.14: the `PiLp` separable-sum effective domain is exactly the pullback of
the coordinatewise raw product domain along the canonical coordinate equivalence. -/
lemma effective_domain_piLp_separableSum_eq_preimage_raw_product
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i)) :
    let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)
    effective_domain (PiLp.separableSum g) =
      e ⁻¹' Set.pi Set.univ (fun i => effective_domain (g i)) := by
  let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)
  -- Evaluate the `PiLp` separable sum coordinatewise and then read off membership in the product
  -- of the block effective domains.
  ext z
  constructor
  · intro hz
    rw [Set.mem_preimage, Set.mem_univ_pi]
    intro i
    -- Finite separable-sum value forces the `i`th block penalty to stay finite.
    exact
      block_mem_effective_domain_of_mem_separableSum_effective_domain
        g hg_proper
        (by simpa [mem_effective_domain, PiLp.separableSum_apply] using hz)
        i
  · intro hz
    rw [Set.mem_preimage, Set.mem_univ_pi] at hz
    -- Coordinatewise finiteness of the block penalties makes the finite sum stay below `⊤`.
    rw [mem_effective_domain, PiLp.separableSum_apply]
    exact
      ereal_sum_lt_top Finset.univ
        (fun i ↦ g i (z.ofLp i))
        (fun i _ ↦ mem_effective_domain.mp (hz i))

/-- Helper for Theorem 12.14: intrinsic-interior membership pulls back along a continuous linear
equivalence after rewriting the target set as a preimage. -/
lemma mem_intrinsicInterior_preimage_of_continuousLinearEquiv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (e : V ≃L[ℝ] W) {s : Set W} {x : V}
    (hx : e x ∈ intrinsicInterior ℝ s) :
    x ∈ intrinsicInterior ℝ (e ⁻¹' s) := by
  let eA : V ≃ᵃ[ℝ] W := e.toContinuousAffineEquiv.toAffineEquiv
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hx with
    ⟨hx_span, ε, hε, hball⟩
  have hx_mem_preimage : x ∈ e ⁻¹' s := by
    -- Intrinsic-interior membership lies inside the target set itself.
    simpa using intrinsicInterior_subset hx
  have hx_preimage : x ∈ affineSpan ℝ (e ⁻¹' s) := by
    -- The pullback point therefore belongs to the affine span of the pullback set.
    exact subset_affineSpan ℝ (e ⁻¹' s) hx_mem_preimage
  have hnhds :
      e ⁻¹' Metric.ball (e x) ε ∈ nhds x := by
    -- Continuity of the linear equivalence gives a small neighborhood sent into the target ball.
    exact e.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  rcases Metric.mem_nhds_iff.1 hnhds with ⟨δ, hδ, hδball⟩
  refine (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).2 ?_
  refine ⟨hx_preimage, δ / 2, by positivity, ?_⟩
  intro u hu
  rcases hu with ⟨hu_ball, hu_span⟩
  have hu_ball' : u ∈ Metric.ball x δ := by
    refine Metric.closedBall_subset_ball ?_ hu_ball
    linarith
  have heu_ball : e u ∈ Metric.ball (e x) ε := hδball hu_ball'
  have heu_span_map :
      e u ∈ (affineSpan ℝ (e ⁻¹' s)).map eA.toAffineMap := by
    simpa [eA] using
      (AffineSubspace.mem_map_of_mem (f := eA.toAffineMap) hu_span)
  have heu_span :
      e u ∈ affineSpan ℝ s := by
    rw [AffineSubspace.map_span] at heu_span_map
    exact (affineSpan_mono ℝ (Set.image_preimage_subset e s)) heu_span_map
  -- Push the affine-span witness through `e` and use the source closed-ball characterization.
  exact hball ⟨Metric.mem_closedBall.2 (le_of_lt heu_ball), heu_span⟩

/-- Helper for Theorem 12.14: coordinatewise intrinsic-interior membership on the raw block owner
places the full block vector in the intrinsic interior of the coordinate product set. -/
lemma mem_intrinsicInterior_univ_pi_of_forall
    {s : Fin p → Set E} {v : Fin p → E}
    (hv : ∀ i : Fin p, v i ∈ intrinsicInterior ℝ (s i)) :
    v ∈ intrinsicInterior ℝ (Set.pi Set.univ s) := by
  classical
  induction p with
  | zero =>
      have hpi : Set.pi Set.univ s = (Set.univ : Set (Fin 0 → E)) := by
        ext w
        constructor
        · intro _
          trivial
        · intro _
          rw [Set.mem_pi]
          intro i _
          exact Fin.elim0 i
      -- In the zero-block case, the product set is the whole singleton function space.
      simpa [hpi, intrinsicInterior] using
        (show v ∈ intrinsicInterior ℝ (Set.univ : Set (Fin 0 → E)) by
          simp [intrinsicInterior])
  | succ p ih =>
      let e : (Fin (p + 1) → E) ≃L[ℝ] E × (Fin p → E) :=
        (Fin.consLinearEquiv ℝ (fun _ : Fin (p + 1) ↦ E)).symm.toContinuousLinearEquiv
      have hhead : v 0 ∈ intrinsicInterior ℝ (s 0) := hv 0
      have htail :
          (fun i : Fin p ↦ v i.succ) ∈
            intrinsicInterior ℝ (Set.pi Set.univ (fun i : Fin p ↦ s i.succ)) :=
        ih (fun i ↦ hv i.succ)
      have hprod :
          e v ∈
            intrinsicInterior ℝ
              (s 0 ×ˢ Set.pi Set.univ (fun i : Fin p ↦ s i.succ)) := by
        -- Split the finite product into its head coordinate and tail block family.
        simpa [e, Fin.tail] using
          (mem_intrinsicInterior_prod (x := v 0) (z := fun i : Fin p ↦ v i.succ) hhead htail)
      have hpre :
          v ∈ intrinsicInterior ℝ (e ⁻¹' (s 0 ×ˢ Set.pi Set.univ (fun i : Fin p ↦ s i.succ))) :=
        mem_intrinsicInterior_preimage_of_continuousLinearEquiv (e := e) hprod
      have hset :
          e ⁻¹' (s 0 ×ˢ Set.pi Set.univ (fun i : Fin p ↦ s i.succ)) = Set.pi Set.univ s := by
        ext w
        constructor
        · intro hw
          have hw' : w 0 ∈ s 0 ∧ ∀ i : Fin p, w i.succ ∈ s i.succ := by
            simpa [e, Fin.tail] using hw
          rw [Set.mem_pi]
          intro i _
          refine Fin.cases ?_ ?_ i
          · simpa using hw'.1
          · intro j
            simpa using hw'.2 j
        · intro hw
          rw [Set.mem_pi] at hw
          have hhead' : w 0 ∈ s 0 := hw 0 (by simp)
          have htail' : ∀ i : Fin p, w i.succ ∈ s i.succ := fun i ↦ hw i.succ (by simp)
          simpa [e, Fin.tail] using And.intro hhead' htail'
      -- Rewrite the product-set pullback back to the original finite product owner.
      rwa [hset] at hpre

/-- Helper for Theorem 12.14: the duplicated block vector inherits a `PiLp` relative-interior
witness from the coordinatewise block relative interiors. -/
lemma constant_block_mem_intrinsicInterior_piLp_separableSum_of_intrinsicInterior
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    {xHat : E}
    (hxHat_g : ∀ i : Fin p, xHat ∈ intrinsicInterior ℝ (effective_domain (g i))) :
    (dual_block_duplication E p).toLinearMap xHat ∈
      intrinsicInterior ℝ (effective_domain (PiLp.separableSum g)) := by
  let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)
  have hraw :
      e ((dual_block_duplication E p).toLinearMap xHat) ∈
        intrinsicInterior ℝ (Set.pi Set.univ (fun i => effective_domain (g i))) := by
    -- First build the raw product intrinsic-interior witness from the coordinatewise data.
    simpa [e, dual_block_duplication_apply] using
      (mem_intrinsicInterior_univ_pi_of_forall
        (s := fun i => effective_domain (g i))
        (v := fun _ : Fin p ↦ xHat)
        hxHat_g)
  -- Then transport that raw witness back to the `PiLp` owner through the coordinate equivalence.
  rw [effective_domain_piLp_separableSum_eq_preimage_raw_product (g := g) hg_proper]
  exact mem_intrinsicInterior_preimage_of_continuousLinearEquiv (e := e) hraw

/-- Helper for Theorem 12.14: Assumption 12.14 on the block problem should induce the Chapter
12.1 owner for the duplicated block-space model. -/
lemma dual_block_problem_to_dual_based_problem :
    IsDualBlockProximalGradientProblem f g σ →
    IsDualBasedProximalGradientProblem
      f
      (PiLp.separableSum g)
      (dual_block_duplication E p).toLinearMap
      σ := by
  intro h_problem
  -- Populate the Chapter 12.1 owner directly from the block assumptions; the only nontrivial
  -- source-faithful step is transporting the qualification witness to the duplicated `PiLp`
  -- block domain.
  let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)
  have hsum_proper :
      IsProperExtendedRealFunction (separableSum g) :=
    separableSum_proper g h_problem.g_proper
  have hsum_closed :
      LowerSemicontinuous (separableSum g) :=
    separableSum_closed g h_problem.g_closed
  have hsum_convex :
      is_convex_function (separableSum g) :=
    separableSum_convex g h_problem.g_convex
  refine
    { toIsProperExtendedRealFunction := h_problem.toIsProperExtendedRealFunction
      f_closed := h_problem.f_closed
      f_strongly_convex := h_problem.f_strongly_convex
      g_proper := by
        refine
          { ne_bot := ?_
            effective_domain_nonempty := ?_ }
        · intro z
          simpa [PiLp.separableSum, e] using hsum_proper.ne_bot (e z)
        · rcases hsum_proper.effective_domain_nonempty with ⟨z, hz⟩
          refine ⟨e.symm z, ?_⟩
          simpa [PiLp.separableSum, e, mem_effective_domain] using hz
      g_closed := by
        -- Lower semicontinuity transports along the coordinate equivalence to the `PiLp` owner.
        simpa [Function.comp, PiLp.separableSum, e] using hsum_closed.comp e.continuous
      g_convex := by
        -- Convexity is invariant under precomposition with the coordinate linear equivalence.
        simpa [PiLp.separableSum, e] using
          is_convex_function_precompose_linearMap_add hsum_convex e.toLinearMap 0
      qualification := ?_ }
  rcases IsDualBlockProximalGradientProblem.exists_mem_intrinsicInterior h_problem with
    ⟨xHat, hxHat_f, hxHat_g⟩
  refine ⟨xHat, hxHat_f, ?_⟩
  -- TODO: the remaining source-faithful bridge is exactly that the constant block vector
  -- `WithLp.toLp 2 (fun _ ↦ xHat)` lies in
  -- `intrinsicInterior ℝ (effective_domain (PiLp.separableSum g))` whenever
  -- `xHat ∈ intrinsicInterior ℝ (effective_domain (g i))` for every block `i`.
  have hdup_mem_dom :
      (dual_block_duplication E p).toLinearMap xHat ∈
        effective_domain (PiLp.separableSum g) := by
    -- First reduce the duplicated `PiLp` witness to plain coordinatewise domain membership.
    exact
      constant_block_mem_effective_domain_piLp_separableSum_of_intrinsicInterior
        (g := g) h_problem.g_proper (xHat := xHat) hxHat_g
  have hdup_mem_span :
      (dual_block_duplication E p).toLinearMap xHat ∈
        affineSpan ℝ (effective_domain (PiLp.separableSum g)) := by
    -- The domain-membership part of the witness already places the duplicated point in the affine
    -- hull of the duplicated feasible core.
    exact subset_affineSpan ℝ (effective_domain (PiLp.separableSum g)) hdup_mem_dom
  have hdup_mem_ri :
      (dual_block_duplication E p).toLinearMap xHat ∈
        intrinsicInterior ℝ (effective_domain (PiLp.separableSum g)) := by
    -- Combine the coordinatewise witnesses on the raw block owner and then transport them back to
    -- the duplicated `PiLp` owner through the canonical coordinate equivalence.
    exact
      constant_block_mem_intrinsicInterior_piLp_separableSum_of_intrinsicInterior
        (g := g) h_problem.g_proper (xHat := xHat) hxHat_g
  simpa [dual_block_duplication_apply] using hdup_mem_ri

/-- Helper for Theorem 12.14: iterating the textbook one-step factor
`(p + n) / (p + n + 1)` yields the closed-form coefficient `p / (p + k + 1)`. -/
lemma sublinear_bound_of_dbpg_step_contraction
    {V : ℕ → ℝ}
    (h_step :
      ∀ n : ℕ, V (n + 1) ≤ ((p + n : ℝ) / (p + n + 1 : ℝ)) * V n)
    (k : ℕ) :
    V (k + 1) ≤ (p : ℝ) / (p + k + 1 : ℝ) * V 0 := by
  have hp_nat : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  induction k with
  | zero =>
      -- The initial contraction is exactly the `n = 0` instance of the one-step estimate.
      simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using h_step 0
  | succ k hk =>
      have hstep : V (k + 2) ≤ ((p + (k + 1) : ℝ) / (p + (k + 1) + 1 : ℝ)) * V (k + 1) := by
        -- Reindex the one-step contraction at time `k + 1`.
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using h_step (k + 1)
      have hfactor_nonneg :
          0 ≤ ((p + (k + 1) : ℝ) / (p + (k + 1) + 1 : ℝ)) := by
        positivity
      have hscaled :
          ((p + (k + 1) : ℝ) / (p + (k + 1) + 1 : ℝ)) * V (k + 1) ≤
            ((p + (k + 1) : ℝ) / (p + (k + 1) + 1 : ℝ)) *
              ((p : ℝ) / (p + k + 1 : ℝ) * V 0) :=
        mul_le_mul_of_nonneg_left hk hfactor_nonneg
      have hcoeff :
          ((p + (k + 1) : ℝ) / (p + (k + 1) + 1 : ℝ)) *
              ((p : ℝ) / (p + k + 1 : ℝ) * V 0) =
            (p : ℝ) / (p + (k + 1) + 1 : ℝ) * V 0 := by
        have hp_denom : (p + k + 1 : ℝ) ≠ 0 := by
          positivity
        have hsucc_denom : (p + (k + 1) + 1 : ℝ) ≠ 0 := by
          positivity
        -- Cancel the common factor `p + k + 1` between the two consecutive step coefficients.
        field_simp [hp_denom, hsucc_denom]
        ring
      -- The inductive step is the one-step contraction followed by the coefficient telescoping.
      calc
        V (k + 2)
            ≤ ((p + (k + 1) : ℝ) / (p + (k + 1) + 1 : ℝ)) * V (k + 1) := hstep
        _ ≤ ((p + (k + 1) : ℝ) / (p + (k + 1) + 1 : ℝ)) *
              ((p : ℝ) / (p + k + 1 : ℝ) * V 0) := hscaled
        _ = (p : ℝ) / (p + (k + 1) + 1 : ℝ) * V 0 := hcoeff
        _ = (p : ℝ) / (p + (k + 1 : ℕ) + 1 : ℝ) * V 0 := by
              simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 12.14: under integrability of the sampled dual objective, the expected dual
gap can be written as the expectation of the pointwise dual-gap random variable. -/
lemma expected_dual_gap_eq_integral_pointwise_gap
    (k : ℕ)
    (h_dual_value_integrable :
      Integrable (fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal) μ) :
    EReal.toReal (q_opt(f, g)) - μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal] =
      μ[fun ω ↦ EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal] := by
  -- Move the constant optimum value inside the expectation using linearity of the integral.
  rw [integral_sub (integrable_const (EReal.toReal (q_opt(f, g)))) h_dual_value_integrable,
    integral_const]
  simp

/-- Helper for Theorem 12.14: if every block dual term `g_i^*(-v_i)` is finite above, then the
source-facing dual objective value `q(v)` is finite. This is the canonical bridge from
coordinatewise Chapter 12 dual feasibility to the theorem surface `finite_domain (q(f, g))`. -/
lemma dual_value_mem_finite_domain_of_coordinatewise_dual_term
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    {v : Fin p → E}
    (hv : ∀ i : Fin p, v i ∈ effective_domain (fun z : E ↦ ((g i)∗) (-z))) :
    v ∈ finite_domain (q(f, g)) := by
  let a : EReal := (f∗) (∑ i : Fin p, v i)
  let G : Fin p → E → EReal := fun i z ↦ ((g i)∗) (-z)
  have hfin :=
    conjugate_function_finite_of_proper_closed_strongConvexOn
      (σ : ℝ)
      σ.2
      f
      h_problem.toIsProperExtendedRealFunction.ne_bot
      h_problem.toIsProperExtendedRealFunction.effective_domain_nonempty
      h_problem.f_closed
      h_problem.f_strongly_convex
      (InnerProductSpace.toDual ℝ E (∑ i : Fin p, v i))
  have ha_ne_bot : a ≠ ⊥ := by
    -- Strong convexity makes the conjugate finite everywhere on the aggregated dual sum.
    simpa [a, conjugate_function_strongDual, conjugate_function_primal_apply,
      conjugate_function] using hfin.1
  have ha_ne_top : a ≠ ⊤ := by
    -- The same conjugate finiteness also excludes `⊤`.
    exact (lt_top_iff_ne_top.mp (by
      simpa [a, conjugate_function_strongDual, conjugate_function_primal_apply,
        conjugate_function] using hfin.2))
  have hG_proper : ∀ i : Fin p, IsProperExtendedRealFunction (G i) := by
    intro i
    let hconj :=
      isProperExtendedRealFunction_conjugate_function (g i) (h_problem.g_proper i)
        (h_problem.g_convex i)
    refine
      { ne_bot := ?_
        effective_domain_nonempty := ?_ }
    · intro z
      -- Precomposing the conjugate with negation preserves the no-`⊥` property.
      simpa [G, conjugate_function_primal_apply] using
        hconj.ne_bot (InnerProductSpace.toDualMap ℝ E (-z))
    · rcases hconj.effective_domain_nonempty with ⟨φ, hφ⟩
      let φc : StrongDual ℝ E := ⟨φ, φ.continuous_of_finiteDimensional⟩
      have hφ_repr :
          (InnerProductSpace.toDualMap ℝ E ((InnerProductSpace.toDual ℝ E).symm φc) :
            Module.Dual ℝ E) = φ := by
        ext x
        change (((InnerProductSpace.toDual ℝ E) ((InnerProductSpace.toDual ℝ E).symm φc)) :
            StrongDual ℝ E) x = φ x
        have hsymm := (InnerProductSpace.toDual ℝ E).apply_symm_apply φc
        simpa using congrArg (fun ψ : StrongDual ℝ E => ψ x) hsymm
      refine ⟨-((InnerProductSpace.toDual ℝ E).symm φc), ?_⟩
      simpa [G, mem_effective_domain, conjugate_function_primal_apply, hφ_repr] using hφ
  have hb_ne_bot : separableSum G v ≠ ⊥ := by
    -- Properness of each conjugate block keeps the separable sum away from `⊥`.
    simpa [G, separableSum_apply] using
      (ereal_sum_ne_bot Finset.univ (fun i ↦ G i (v i))
        (fun i _ ↦ (hG_proper i).ne_bot (v i)))
  have hb_ne_top : separableSum G v ≠ ⊤ := by
    -- The coordinatewise effective-domain assumptions make the separable sum finite above.
    exact (lt_top_iff_ne_top.mp <| by
      simpa [G, separableSum_apply] using
        (ereal_sum_lt_top Finset.univ (fun i ↦ G i (v i))
          (fun i _ ↦ mem_effective_domain.mp (hv i))))
  have hview :
      a + separableSum G v = - q(f, g) v := by
    -- Rewrite the Chapter 11 composite objective back to the source dual objective `q`.
    simpa [a, G, composite_model_objective_apply] using
      (dual_block_dual_minimization_view_apply
        (σ := σ) (f := f) (g := g) h_problem v)
  rw [mem_finite_domain, mem_effective_domain, lt_top_iff_ne_top]
  constructor
  · intro hq_top
    have hab_ne_bot : a + separableSum G v ≠ ⊥ := by
      simpa [EReal.add_ne_bot_iff, ha_ne_top, hb_ne_bot] using And.intro ha_ne_bot hb_ne_bot
    have hab_eq_bot : a + separableSum G v = ⊥ := by
      rw [hview]
      simpa [hq_top]
    exact hab_ne_bot hab_eq_bot
  · intro hq_bot
    have hab_eq_top : a + separableSum G v = ⊤ := by
      rw [hview]
      simpa [hq_bot]
    exact (EReal.add_ne_top ha_ne_top hb_ne_top) hab_eq_top

/-- Helper for Theorem 12.14: finiteness of the source-facing dual value `q(v)` forces each block
dual term `g_i^*(-v_i)` to be finite above. This isolates the coordinatewise part of the
finite-domain invariant used in the DBPG induction. -/
lemma block_dual_term_mem_effective_domain_of_mem_finite_domain
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    {v : Fin p → E} (hv : v ∈ finite_domain (q(f, g))) (i : Fin p) :
    v i ∈ effective_domain (fun z : E ↦ ((g i)∗) (-z)) := by
  let a : EReal := (f∗) (∑ j : Fin p, v j)
  let G : Fin p → E → EReal := fun j z ↦ ((g j)∗) (-z)
  have hfin :=
    conjugate_function_finite_of_proper_closed_strongConvexOn
      (σ : ℝ)
      σ.2
      f
      h_problem.toIsProperExtendedRealFunction.ne_bot
      h_problem.toIsProperExtendedRealFunction.effective_domain_nonempty
      h_problem.f_closed
      h_problem.f_strongly_convex
      (InnerProductSpace.toDual ℝ E (∑ j : Fin p, v j))
  have ha_ne_bot : a ≠ ⊥ := by
    -- The smooth conjugate term is finite at the aggregated dual sum.
    simpa [a, conjugate_function_strongDual, conjugate_function_primal_apply,
      conjugate_function] using hfin.1
  have ha_ne_top : a ≠ ⊤ := by
    -- Strong convexity also excludes `⊤` for the smooth conjugate term.
    exact (lt_top_iff_ne_top.mp (by
      simpa [a, conjugate_function_strongDual, conjugate_function_primal_apply,
        conjugate_function] using hfin.2))
  have hG_proper : ∀ j : Fin p, IsProperExtendedRealFunction (G j) := by
    intro j
    let hconj :=
      isProperExtendedRealFunction_conjugate_function (g j) (h_problem.g_proper j)
        (h_problem.g_convex j)
    refine
      { ne_bot := ?_
        effective_domain_nonempty := ?_ }
    · intro z
      -- Each negated conjugate block remains proper after the sign flip.
      simpa [G, conjugate_function_primal_apply] using
        hconj.ne_bot (InnerProductSpace.toDualMap ℝ E (-z))
    · rcases hconj.effective_domain_nonempty with ⟨φ, hφ⟩
      let φc : StrongDual ℝ E := ⟨φ, φ.continuous_of_finiteDimensional⟩
      have hφ_repr :
          (InnerProductSpace.toDualMap ℝ E ((InnerProductSpace.toDual ℝ E).symm φc) :
            Module.Dual ℝ E) = φ := by
        ext x
        change (((InnerProductSpace.toDual ℝ E) ((InnerProductSpace.toDual ℝ E).symm φc)) :
            StrongDual ℝ E) x = φ x
        have hsymm := (InnerProductSpace.toDual ℝ E).apply_symm_apply φc
        simpa using congrArg (fun ψ : StrongDual ℝ E => ψ x) hsymm
      refine ⟨-((InnerProductSpace.toDual ℝ E).symm φc), ?_⟩
      simpa [G, mem_effective_domain, conjugate_function_primal_apply, hφ_repr] using hφ
  have hview :
      a + separableSum G v = - q(f, g) v := by
    -- Use the source-facing `q` identity to isolate the separable conjugate sum.
    simpa [a, G, composite_model_objective_apply] using
      (dual_block_dual_minimization_view_apply
        (σ := σ) (f := f) (g := g) h_problem v)
  have hobj_ne_top : a + separableSum G v ≠ ⊤ := by
    -- Finiteness of `q(v)` rules out `⊤` for the negated Chapter 11 objective value.
    rw [hview]
    simpa using (mem_finite_domain.mp hv).2
  have hsep_ne_top : separableSum G v ≠ ⊤ := by
    -- Remove the finite smooth conjugate term from the sum and keep the regularizer finite above.
    exact (EReal.add_ne_top_iff_ne_top_right ha_ne_bot ha_ne_top).1 hobj_ne_top
  have hsep_mem : v ∈ effective_domain (separableSum G) := by
    -- The separable block-dual regularizer is therefore finite at `v`.
    simpa [mem_effective_domain, lt_top_iff_ne_top] using hsep_ne_top
  -- Apply the standard Chapter 11 separable-sum domain projection back to coordinate `i`.
  simpa [G] using
    (block_mem_effective_domain_of_mem_separableSum_effective_domain G hG_proper hsep_mem i)

/-- Helper for Theorem 12.14: the sampled block-dual iterate at time `k + 1` should stay in the
finite domain of the dual objective along every realized DBPG trajectory. -/
lemma randomized_dbpg_dual_iterate_mem_finite_domain
    (k : ℕ) :
    ∀ ω, y (k + 1) ω ∈ finite_domain (q(f, g)) := sorry

/-- Helper for Theorem 12.14: the sampled dual objective at time `k + 1` should be integrable
because the realized DBPG iterate depends only on finitely many uniformly sampled blocks. -/
lemma randomized_dbpg_dual_value_integrable
    (k : ℕ) :
    Integrable (fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal) μ := by
  -- TODO: factor `y (k + 1)` through the finite sampled-block history and use finite-range
  -- integrability of the induced scalar observable.
  sorry

/-- Helper for Theorem 12.14: at each realized iterate, the Chapter 12.7 primal-vs-dual-gap
estimate on the duplicated block model yields the scalar dual-gap bound used in part (2). -/
lemma dbpg_pointwise_primal_sqdist_le_dual_gap_at_succ
    (xStar : E)
    (hxStar : IsMinOn F Set.univ xStar)
    (k : ℕ)
    (ω : Ω)
    (hy_finite : y (k + 1) ω ∈ finite_domain (q(f, g))) :
    ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ) ≤
      (2 / (σ : ℝ)) *
        (EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal) := by
  -- TODO: apply Lemma 12.7 on the duplicated block-space model, rewrite its dual objective back
  -- to `q(f, g)`, and then convert the `EReal` gap to the scalar gap using `hy_finite`.
  sorry

-- Proof sketch: condition on the sampled-block history generated by `sampled_block`, use the
-- one-step randomized DBPG Lyapunov contraction for
-- `(1 / (2 σ)) ‖y^k - y*‖² + q_opt - q(y^k)`, average over the uniformly sampled block, and
-- iterate the recursion to obtain the factor `p / (p + k + 1)`. Finally identify the optimal
-- value by `dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set`.
/-- Theorem 12.14 (1): for primal and dual sequences generated by the dual block proximal-gradient
method with randomized uniformly sampled block order, if the sampled dual objective value is
integrable and the relevant dual points lie in the finite domain of `q`, then the expected dual
objective gap satisfies the sublinear estimate
`q_opt - E[q(y^{k+1})] ≤ (p / (p + k + 1)) ((1 / (2σ)) ‖y^0 - y*‖² + q_opt - q(y^0))`. -/
theorem randomized_dual_block_proximal_gradient_expected_dual_gap_le
    (k : ℕ)
    (h_dual_value_finite : ∀ ω, y (k + 1) ω ∈ finite_domain (q(f, g)))
    (h_dual_value_integrable : Integrable (fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal) μ) :
    EReal.toReal (q_opt(f, g)) - μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal] ≤
      (p : ℝ) / (p + k + 1 : ℝ) *
        ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
          EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) :=
  -- Route correction: keep the source Lyapunov-recursion route and isolate the remaining blocker
  -- to the Chapter 11/12 bridge, rather than switching to a different proof architecture here.
  -- TODO: prove this by transporting each realized DBPG dual trajectory to the Chapter 11 RBPG
  -- method on the block-dual objective `-q`, then apply
  -- `randomized_block_proximal_gradient_expected_objective_gap_le_sublinear` and rewrite the
  -- resulting objective estimate with the already-isolated pointwise identity
  -- `dual_block_dual_minimization_view_apply`, then finish with
  -- `dual_problem_value_toReal_eq_of_mem_optimal_set` and the corrected `PiLp`-owner version of
  -- `half_weighted_sqnorm_eq_initial_lyapunov`. The remaining blocker is now the missing local
  -- Chapter 12-to-Chapter 11 randomized-trajectory package together with the final transport from
  -- that canonical `L²` initial norm to the present theorem surface.
  sorry

/-- Helper for Theorem 12.14: once the pointwise Chapter 12 primal-dual estimate and the sampled
dual-value integrability are available, part (2) is a formal consequence of part (1). -/
lemma expected_primal_sqdist_le_of_dual_gap_bound
    (xStar : E) (k : ℕ)
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (h_traj :
      ∀ ω,
        is_dual_block_proximal_gradient_primal_trajectory
          f g σ (fun n ↦ sampled_block n ω) y0
          (fun n ↦ x n ω)
          (fun n ↦ y n ω))
    (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
    (h_sampled_block_indep : iIndepFun sampled_block μ)
    (h_sampled_block_uniform :
      ∀ k (i : Fin p), μ ((sampled_block k) ⁻¹' {i}) = 1 / (p : ℝ≥0∞))
    (hyStar : yStar ∈ Λ*(f, g))
    (hy0_finite : y0 ∈ finite_domain (q(f, g)))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g)))
    (h_primal_sqdist_integrable :
      Integrable (fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)) μ)
    (h_dual_value_finite : ∀ ω, y (k + 1) ω ∈ finite_domain (q(f, g)))
    (h_dual_value_integrable :
      Integrable (fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal) μ)
    (h_pointwise :
      ∀ ω,
        ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ) ≤
          (2 / (σ : ℝ)) *
            (EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal)) :
    μ[fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)] ≤
      2 * (p : ℝ) / ((σ : ℝ) * (p + k + 1 : ℝ)) *
        ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
          EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) :=
by
  have h_gap_integrable :
      Integrable
        (fun ω ↦ EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal) μ := by
    -- Subtracting the constant dual optimum preserves integrability of the sampled dual gap.
    exact (integrable_const (EReal.toReal (q_opt(f, g)))).sub h_dual_value_integrable
  have h_scaled_gap_integrable :
      Integrable
        (fun ω ↦
          (2 / (σ : ℝ)) *
            (EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal)) μ := by
    -- The pointwise Chapter 12 bound is integrated after scaling by the deterministic factor
    -- `2 / σ`.
    exact h_gap_integrable.const_mul (2 / (σ : ℝ))
  have h_integral_le :
      μ[fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)] ≤
        μ[fun ω ↦
          (2 / (σ : ℝ)) *
            (EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal)] := by
    -- Integrate the pointwise primal-vs-dual-gap comparison from the source proof.
    exact
      integral_mono_ae
        h_primal_sqdist_integrable
        h_scaled_gap_integrable
        (Filter.Eventually.of_forall h_pointwise)
  have h_dual_gap_bound :
      EReal.toReal (q_opt(f, g)) - μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal] ≤
        (p : ℝ) / (p + k + 1 : ℝ) *
          ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
            EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) :=
    randomized_dual_block_proximal_gradient_expected_dual_gap_le
      (μ := μ)
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (y := y)
      (yStar := yStar)
      k
      h_dual_value_finite
      h_dual_value_integrable
  have h_scaled_dual_gap_bound :
      (2 / (σ : ℝ)) *
          (EReal.toReal (q_opt(f, g)) - μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal]) ≤
        (2 / (σ : ℝ)) *
          ((p : ℝ) / (p + k + 1 : ℝ) *
            ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
              EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal)) := by
    -- The scalar factor `2 / σ` is nonnegative, so it preserves the expected dual-gap bound.
    have hscale_nonneg : 0 ≤ 2 / (σ : ℝ) := by
      exact div_nonneg (by norm_num) (le_of_lt σ.2)
    exact mul_le_mul_of_nonneg_left h_dual_gap_bound hscale_nonneg
  have h_rhs_rewrite :
      (2 / (σ : ℝ)) *
          ((p : ℝ) / (p + k + 1 : ℝ) *
            ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
              EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal)) =
        2 * (p : ℝ) / ((σ : ℝ) * (p + k + 1 : ℝ)) *
          ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
            EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) := by
    -- The closing constant is just a rearrangement of the deterministic prefactor.
    field_simp
  calc
    μ[fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)]
        ≤
          μ[fun ω ↦
            (2 / (σ : ℝ)) *
              (EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal)] :=
      h_integral_le
    _ =
        (2 / (σ : ℝ)) *
          μ[fun ω ↦
            EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal] := by
          rw [integral_const_mul]
    _ =
        (2 / (σ : ℝ)) *
          (EReal.toReal (q_opt(f, g)) - μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal]) := by
          rw [expected_dual_gap_eq_integral_pointwise_gap
            (μ := μ)
            (f := f)
            (g := g)
            (y := y)
            k
            h_dual_value_integrable]
    _ ≤
        (2 / (σ : ℝ)) *
          ((p : ℝ) / (p + k + 1 : ℝ) *
            ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
              EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal)) :=
      h_scaled_dual_gap_bound
    _ =
        2 * (p : ℝ) / ((σ : ℝ) * (p + k + 1 : ℝ)) *
          ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
            EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) :=
      h_rhs_rewrite

-- Proof sketch: combine the same history-conditioned randomized Lyapunov contraction used in
-- part (1) with the Chapter 12 primal-dual estimate that bounds `‖x^{k+1} - x*‖²` by `(2 / σ)`
-- times the dual-gap Lyapunov quantity. Taking expectations and substituting the part (1)
-- recursion gives the displayed `O(1 / k)` primal-distance estimate.
/-- Theorem 12.14 (2): for primal and dual sequences generated by the dual block proximal-gradient
method with randomized uniformly sampled block order, if the sampled primal squared distance is
integrable and the dual endpoint values on the right-hand side lie in the finite domain of `q`,
then the expected primal squared distance to a primal optimizer satisfies
`E[‖x^{k+1} - x*‖²] ≤ (2p / (σ (p + k + 1))) ((1 / (2σ)) ‖y^0 - y*‖² + q_opt - q(y^0))`. -/
theorem randomized_dual_block_proximal_gradient_expected_primal_sqdist_le
    (xStar : E) (hxStar : IsMinOn F Set.univ xStar)
    (k : ℕ)
    (h_primal_sqdist_integrable :
      Integrable (fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)) μ) :
    μ[fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)] ≤
      2 * (p : ℝ) / ((σ : ℝ) * (p + k + 1 : ℝ)) *
        ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
          EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) :=
by
  -- TODO: the intended wrapper factors part (2) through
  -- `expected_primal_sqdist_le_of_dual_gap_bound`, but the current theorem statement does not yet
  -- expose the randomized DBPG trajectory data needed to instantiate that helper.
  sorry

end
