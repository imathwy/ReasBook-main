import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_4 (from Chap14) -/
section

/- Definition 14.4 is `source-facing`: the textbook introduces a specific two-variable convex
objective by an explicit formula. Domain sampling in the local convex-analysis API points to the
following owner split.
- `core/canonical`: `ConvexOn` for the convexity statement;
- `core/canonical`: `convexOn_univ_norm` and `ConvexOn.comp_linearMap` for absolute values of
  linear forms;
- `core/canonical`: `ConvexOn.add` for the sum; and
- `bridge/view`: the Chapter 9 coercion `Function.toEReal` for downstream extended-real uses of the
  same objective.

The primitive data are only the displayed real-valued objective itself. Its evaluation formula,
convexity, and any later `EReal` view are derived API, so this file should reuse those owner
declarations directly instead of introducing local wrapper versions. -/

/-- Definition 14.4: Example 14.5 (failure of alternating minimization II) defines the convex
objective `F : ℝ × ℝ → ℝ` by `F(x₁, x₂) = |3x₁ + 4x₂| + |x₁ - 2x₂|`. -/
def alternating_minimization_failure_ii_objective : ℝ × ℝ → ℝ :=
  fun (x₁, x₂) ↦ |3 * x₁ + 4 * x₂| + |x₁ - 2 * x₂|

-- Proof sketch: unfold `alternating_minimization_failure_ii_objective`; evaluating it on the pair
-- `(x₁, x₂)` gives exactly the displayed formula from the source.
/-- Evaluating `alternating_minimization_failure_ii_objective` at `(x₁, x₂)` reproduces the
displayed formula `|3x₁ + 4x₂| + |x₁ - 2x₂|`. -/
@[simp] theorem alternating_minimization_failure_ii_objective_apply (x₁ x₂ : ℝ) :
    alternating_minimization_failure_ii_objective (x₁, x₂) =
      |3 * x₁ + 4 * x₂| + |x₁ - 2 * x₂| := rfl

-- Proof sketch: the maps `(x₁, x₂) ↦ 3x₁ + 4x₂` and `(x₁, x₂) ↦ x₁ - 2x₂` are affine on
-- `ℝ × ℝ`. Since the absolute value on `ℝ` is convex on `Set.univ`, each summand is convex by
-- affine precomposition, and their sum is convex.
/-- The objective from Example 14.5 is convex on all of `ℝ × ℝ`. -/
theorem alternating_minimization_failure_ii_objective_convex :
    ConvexOn ℝ Set.univ alternating_minimization_failure_ii_objective := by
  let l34 : ℝ × ℝ →ₗ[ℝ] ℝ := 3 • LinearMap.fst ℝ ℝ ℝ + 4 • LinearMap.snd ℝ ℝ ℝ
  let l12 : ℝ × ℝ →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ - 2 • LinearMap.snd ℝ ℝ ℝ
  have h34 : ConvexOn ℝ Set.univ (fun x : ℝ × ℝ ↦ ‖l34 x‖) := by
    simpa using convexOn_univ_norm.comp_linearMap l34
  have h12 : ConvexOn ℝ Set.univ (fun x : ℝ × ℝ ↦ ‖l12 x‖) := by
    simpa using convexOn_univ_norm.comp_linearMap l12
  refine (h34.add h12).congr ?_
  intro x hx
  simp [alternating_minimization_failure_ii_objective, l34, l12, Real.norm_eq_abs]

end

/-! ### Lemma_14_4 (from Chap14) -/
noncomputable section

universe u

open scoped Gradient

section

variable {E1 : Type u} {E2 : Type u}
variable [NormedAddCommGroup E1] [NormedAddCommGroup E2]

section ObjectiveGap

/-- Helper for Lemma 14.4: a convex differentiable real-valued function on the whole space
satisfies the first-order support inequality at the base point. -/
lemma convex_real_support_univ
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {φ : E → ℝ} {x y : E}
    (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hφ_diff : DifferentiableAt ℝ φ x) :
    φ y ≥ φ x + inner ℝ (∇ φ x) (y - x) := by
  have hconvex : is_convex_function (fun z ↦ (φ z : EReal)) := by
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro z hz
      simp
    · simpa [effective_domain] using hφ_convex
  -- Reuse the Chapter 13 line-map support proof on the everywhere-finite coercion of `φ`.
  simpa using
    convex_support_toReal_at_basepoint
      (f := fun z ↦ (φ z : EReal))
      (x := x)
      (y := y)
      (fun _ ↦ by simp)
      hconvex
      (by simp [effective_domain])
      hφ_diff
      (by simp [effective_domain])

/- `Lemma 14.4` is a `bridge/view` item. The source-facing objects are the Chapter 14
pair-valued half-step `x^{k+1/2}` and next iterate `x^{k+1}` from Algorithm 14.8, while the
residual term comes from the canonical Chapter 10 gradient-mapping owner.

Domain sampling for the residual side:
- `gradient_mapping` / `G[L, f, g]` from `Chap10/Definition_10_5` is the canonical owner;
- `G[L; f, g]` is the source-facing bridge for real-valued smooth terms on the ambient space;
- `prox_grad_step_gradient_mapping_norm_monotone` from `Chap10/Lemma_10_12` is the nearby
  Chapter 10 residual theorem stated on that owner surface with a `PosReal` stepsize parameter.

Primitive data vs. derived API:
- primitive data for each block estimate are the active block's Hilbert/prox assumptions,
  the corresponding frozen-slice convexity and smoothness of `f`, and the convexity of the full
  pair objective needed to compare against a global minimizer `x^*`;
- the pair objective, half-step, next iterate, and residual norm are derived Chapter 14/10 views.

Accordingly, the Chapter 14 theorems below keep the pair-valued half-step/next-step statements,
but use the Chapter 10 residual bridge directly. The blockwise smoothness assumptions stay on the
active frozen slice, while the objective-gap comparison to `x^*` is stated under the canonical
full-objective convex owner `is_convex_function`. -/

-- Proof sketch: first use the exact `x₂`-minimization at the current iterate `x^k` to identify
-- the second-block prox residual with zero, so the full prox-gradient comparison point reduces to
-- the half-step candidate. Then use the exact `x₁`-minimization hypothesis, apply the one-block
-- convex proximal-gradient gap estimate, and finish with Cauchy-Schwarz.
section X1ObjectiveGap

variable (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (g2 : E2 → EReal)
variable [InnerProductSpace ℝ E1] [ProperSpace E1]
variable [NormedSpace ℝ E2]
variable [IsProperExtendedRealFunction g1] [Fact (LowerSemicontinuous g1)]
  [Fact (is_convex_function g1)]
variable (x1 : ℕ → E1) (x2 : ℕ → E2) (xStar : E1 × E2) (k : ℕ)
variable (L1 : PosReal)

local notation "F" => two_block_alternating_minimization_objective f.toEReal g1 g2
local notation "xk" => (x1 k, x2 k)
local notation "xHalf" => two_block_alternating_minimization_half_step x1 x2 k
local notation "f1" => fun y1 ↦ f (y1, x2 k)
local notation "Fx1" => two_block_alternating_minimization_x1_objective f.toEReal g1 g2 (x2 k)
local notation "Fx2" => two_block_alternating_minimization_x2_objective f.toEReal g1 g2 (x1 k)
local notation "phi1" => fun y1 : E1 ↦ sInf (Set.range (fun z2 : E2 ↦ F (y1, z2)))

/-- Helper for Lemma 14.4: the exact first-block half-step cannot exceed the value of the
frozen-slice prox-gradient comparison point. -/
lemma two_block_half_step_le_x1_prox_test_point
    (hstep1 : IsMinOn Fx1 Set.univ (x1 (k + 1))) :
    F xHalf ≤ F (T[L1; f1, g1] (x1 k), x2 k) := by
  -- Compare the exact first-block minimizer against the prox-gradient test point on the same
  -- frozen `x₂ = x₂^k` slice.
  have hmin := (isMinOn_iff.mp hstep1) (T[L1; f1, g1] (x1 k)) (by simp)
  simpa [two_block_alternating_minimization_half_step] using hmin

/-- Helper for Lemma 14.4: exact minimization of the inactive second block compares the current
iterate directly against the competitor obtained by replacing only the second block with
`xStar.2`. -/
lemma current_x2_slice_minimizer_le_xStar_second_block
    (hx2k : IsMinOn Fx2 Set.univ (x2 k)) :
    F xk ≤ F (x1 k, xStar.2) := by
  -- Freeze the active first block at `x₁^k` and compare the exact `x₂`-minimizer to the
  -- competitor whose second block is `xStar.2`.
  have hmin := (isMinOn_iff.mp hx2k) xStar.2 (by simp)
  simpa using hmin

/-- Helper for Lemma 14.4: exact minimization of the current `x₂` slice identifies the marginal
partial-infimum value at `x₁^k` with the current objective value. -/
lemma x1_partial_infimum_eq_current_value
    (hx2k : IsMinOn Fx2 Set.univ (x2 k)) :
    phi1 (x1 k) = F xk := by
  apply le_antisymm
  · -- The current second block realizes one point in the fiber defining `phi1`.
    exact sInf_le ⟨x2 k, by simp⟩
  · -- Exact slice minimality shows that no other second block gives a smaller fiber value.
    refine le_sInf ?_
    rintro _ ⟨z2, rfl⟩
    simpa using (isMinOn_iff.mp hx2k) z2 (by simp)

/-- Helper for Lemma 14.4: the marginal partial infimum at a first-block competitor is bounded
above by the full objective evaluated at any full competitor with that first block. -/
lemma x1_partial_infimum_le_objective_at_competitor
    (y : E1 × E2) :
    phi1 y.1 ≤ F y := by
  rcases y with ⟨y1, y2⟩
  -- Insert the competitor's second block as one witness in the defining fiber of `phi1`.
  exact sInf_le ⟨y2, by simp⟩

/-- Helper for Lemma 14.4: the exact inactive `x₂`-minimization reduces the current objective gap
to the active `x₁` linearization term plus the `g₁` gap against `xStar.1`. -/
lemma x1_exact_inactive_block_gap_le_active_linearization
    (hF_convex : is_convex_function F)
    (hf_x1_convex : ConvexOn ℝ Set.univ f1)
    (hxStar : IsMinOn F Set.univ xStar)
    (hx2k : IsMinOn Fx2 Set.univ (x2 k)) :
    F xk ≤
      (((inner ℝ (∇ f1 (x1 k)) ((x1 k) - xStar.1) : ℝ) : EReal)) +
        (g1 (x1 k) - g1 xStar.1) + F xStar := by
  -- Route correction: pivot from the stalled owner-surface theorem to the source-faithful
  -- marginal object `phi1(y1) = inf_z2 F(y1, z2)`.
  have hphi_eq :
      phi1 (x1 k) = F xk :=
    x1_partial_infimum_eq_current_value
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) (k := k) hx2k
  have hphi_le :
      phi1 xStar.1 ≤ F xStar :=
    x1_partial_infimum_le_objective_at_competitor
      (f := f) (g1 := g1) (g2 := g2) xStar
  let _ := hF_convex
  let _ := hf_x1_convex
  let _ := hxStar
  let _ := hphi_eq
  let _ := hphi_le
  -- TODO: prove the marginal-support bridge
  -- `phi1 xStar.1 ≥ phi1 (x1 k) + ⟪∇ f1 (x1 k), xStar.1 - x1 k⟫ + g1 xStar.1 - g1 (x1 k)`.
  -- Exact attainment at `x₂^k` has already identified `phi1 (x1 k)` with `F xk`, and the
  -- competitor upper bound `hphi_le` already compares `phi1 xStar.1` to `F xStar`.
  sorry

/-- Helper for Lemma 14.4: the frozen `x₁` prox step satisfies the Chapter 6 all-points support
inequality for the scaled penalty, specialized at `xStar.1`. -/
lemma x1_scaled_prox_support_inequality :
    let t1 := T[L1; f1, g1] (x1 k)
    (((inner ℝ
        ((x1 k - (1 / L1 : ℝ) • ∇ f1 (x1 k)) - t1)
        (xStar.1 - t1) : ℝ)) : EReal) ≤
      ((((1 / L1 : PosReal) : EReal) • g1) xStar.1 -
        ((((1 / L1 : PosReal) : EReal) • g1) t1)) := by
  dsimp
  let t1 := T[L1; f1, g1] (x1 k)
  let scaledG1 : E1 → EReal := (((1 / L1 : PosReal) : EReal) • g1)
  let hg1_scaled :=
    scaled_function_proper_closed_convex_of_pos
      g1 inferInstance (Fact.out : LowerSemicontinuous g1)
      (Fact.out : is_convex_function g1) (1 / L1)
  have hprox :
      prox[scaledG1] (x1 k - (1 / L1 : ℝ) • ∇ f1 (x1 k)) = {t1} := by
    -- The Chapter 10 prox-gradient operator is exactly the singleton proximal step for the
    -- scaled penalty at the forward-gradient point.
    simpa [t1, scaledG1, proximal_gradient_step] using
      (prox_grad_operator_eq_singleton (f := Function.toEReal f1) (g := g1) L1
        (interior_effective_domain_point_of_real f1 (x1 k)))
  rcases prox_singleton_implies_effective_domain_and_inner_support
      scaledG1 hg1_scaled.1 hg1_scaled.2.2
      (x1 k - (1 / L1 : ℝ) • ∇ f1 (x1 k)) t1 hprox with
    ⟨ht1_eff, hsupport⟩
  by_cases hxStar_eff : xStar.1 ∈ effective_domain scaledG1
  · -- On the effective domain, Theorem 6.39 already gives the desired support inequality.
    simpa [scaledG1] using hsupport xStar.1 hxStar_eff
  · -- Outside the effective domain, the scaled penalty value is `⊤`, so the inequality is trivial.
    have hxStar_top : scaledG1 xStar.1 = ⊤ := by
      have hnot : ¬ scaledG1 xStar.1 < ⊤ := by
        simpa [effective_domain] using hxStar_eff
      exact le_antisymm le_top (not_lt.mp hnot)
    have ht1_ne_top : scaledG1 t1 ≠ ⊤ := (mem_effective_domain.mp ht1_eff).ne
    have h_rhs_top :
        (↑↑(1 / L1) * g1 xStar.1 - ↑↑(1 / L1) * g1 t1 : EReal) = ⊤ := by
      calc
        (↑↑(1 / L1) * g1 xStar.1 - ↑↑(1 / L1) * g1 t1 : EReal)
            = scaledG1 xStar.1 - scaledG1 t1 := by
              simp [scaledG1, smul_eq_mul]
        _ = ⊤ - scaledG1 t1 := by rw [hxStar_top]
        _ = ⊤ := EReal.top_sub ht1_ne_top
    rw [h_rhs_top]
    exact le_top

/-- Helper for Lemma 14.4: the block descent lemma controls the smooth first-block slice at the
prox-gradient test point by its quadratic model at `x₁^k`. -/
lemma x1_smooth_descent_to_prox_test_point
    (hf_x1_smooth : is_l_smooth_on f1 Set.univ (PosReal.toNNReal L1)) :
    let t1 := T[L1; f1, g1] (x1 k)
    f (t1, x2 k) ≤
      f (x1 k, x2 k) +
        inner ℝ (∇ f1 (x1 k)) (t1 - x1 k) +
          ((L1 : ℝ) / 2) * ‖t1 - x1 k‖ ^ (2 : ℕ) := by
  dsimp
  -- Apply Lemma 5.7 on the frozen `x₁` slice with domain `Set.univ`.
  simpa [norm_sub_rev] using
    is_l_smooth_on_descent_lemma
      (D := Set.univ)
      (f := f1)
      (by simpa using convex_univ)
      hf_x1_smooth
      (x := x1 k)
      (y := T[L1; f1, g1] (x1 k))
      (by simp)
      (by simp)

/-- Helper for Lemma 14.4: after rewriting the prox step through the gradient mapping, the
remaining quadratic residual on the active first block is bounded by the product of the
gradient-mapping norm and the full iterate-to-solution distance. -/
lemma x1_gradient_mapping_residual_term_le_norm_product :
    let t1 := T[L1; f1, g1] (x1 k)
    (L1 : ℝ) * inner ℝ (x1 k - t1) ((x1 k) - xStar.1) -
        ((L1 : ℝ) / 2) * ‖x1 k - t1‖ ^ (2 : ℕ) ≤
      ‖G[L1; f1, g1] (x1 k)‖ * ‖xk - xStar‖ := by
  dsimp
  let G1 := G[L1; f1, g1] (x1 k)
  have ht1 :
      T[L1; f1, g1] (x1 k) = x1 k - (1 / (L1 : ℝ)) • G1 := by
    -- Rewrite the prox point as the identity minus the scaled Chapter 10 gradient mapping.
    simpa [G1] using
      prox_gradient_operator_eq_sub_gradient_mapping
        (f := f1) (g := g1) (L := L1) (x := x1 k)
  have hstep :
      x1 k - T[L1; f1, g1] (x1 k) = (1 / (L1 : ℝ)) • G1 := by
    -- Solve the residual `x₁^k - t₁` from the prox-step identity above.
    rw [ht1]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hL_pos : 0 < (L1 : ℝ) := L1.2
  have hL_ne : (L1 : ℝ) ≠ 0 := hL_pos.ne'
  have hrewrite :
      (L1 : ℝ) * inner ℝ (x1 k - T[L1; f1, g1] (x1 k)) ((x1 k) - xStar.1) -
          ((L1 : ℝ) / 2) * ‖x1 k - T[L1; f1, g1] (x1 k)‖ ^ (2 : ℕ) =
        inner ℝ G1 ((x1 k) - xStar.1) -
          ((1 : ℝ) / (2 * (L1 : ℝ))) * ‖G1‖ ^ (2 : ℕ) := by
    -- Normalize the quadratic term to the exact scalar shape appearing in the textbook proof.
    rw [hstep, inner_smul_left, norm_smul, Real.norm_eq_abs, abs_of_pos hL_pos]
    rw [pow_two]
    field_simp [hL_ne]
    ring
  have hquad_nonneg :
      0 ≤ ((1 : ℝ) / (2 * (L1 : ℝ))) * ‖G1‖ ^ (2 : ℕ) := by
    positivity
  have hcoord :
      ‖(x1 k) - xStar.1‖ ≤ ‖xk - xStar‖ := by
    -- The first coordinate norm is dominated by the product-space norm.
    simpa [xk] using (norm_fst_le (xk - xStar))
  calc
    (L1 : ℝ) * inner ℝ (x1 k - T[L1; f1, g1] (x1 k)) ((x1 k) - xStar.1) -
        ((L1 : ℝ) / 2) * ‖x1 k - T[L1; f1, g1] (x1 k)‖ ^ (2 : ℕ) =
      inner ℝ G1 ((x1 k) - xStar.1) -
        ((1 : ℝ) / (2 * (L1 : ℝ))) * ‖G1‖ ^ (2 : ℕ) := hrewrite
    _ ≤ inner ℝ G1 ((x1 k) - xStar.1) := by
      exact sub_le_self _ hquad_nonneg
    _ ≤ ‖G1‖ * ‖(x1 k) - xStar.1‖ := by
      exact real_inner_le_norm _ _
    _ ≤ ‖G1‖ * ‖xk - xStar‖ := by
      exact mul_le_mul_of_nonneg_left hcoord (norm_nonneg _)
    _ = ‖G[L1; f1, g1] (x1 k)‖ * ‖xk - xStar‖ := by
      rfl

/-- Helper for Lemma 14.4: the unresolved x₁-side gap estimate is exactly the prox-gradient
comparison bound for the frozen first-block slice. -/
lemma x1_prox_test_point_gap_le_gradient_mapping_bound
    (hF_convex : is_convex_function F)
    (hf_x1_convex : ConvexOn ℝ Set.univ f1)
    (hf_x1_smooth : is_l_smooth_on f1 Set.univ (PosReal.toNNReal L1))
    (hxStar : IsMinOn F Set.univ xStar)
    (hx2k : IsMinOn Fx2 Set.univ (x2 k)) :
    F (T[L1; f1, g1] (x1 k), x2 k) ≤
      (((‖G[L1; f1, g1] (x1 k)‖ * ‖xk - xStar‖ : ℝ) : EReal)) + F xStar := by
  let t1 := T[L1; f1, g1] (x1 k)
  have hbridge :=
    x1_exact_inactive_block_gap_le_active_linearization
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) (xStar := xStar) (k := k)
      hF_convex hf_x1_convex hxStar hx2k
  have hprox_support :=
    x1_scaled_prox_support_inequality
      (f := f) (g1 := g1) (x1 := x1) (x2 := x2) (xStar := xStar)
      (k := k) (L1 := L1)
  have hdescent :=
    x1_smooth_descent_to_prox_test_point
      (f := f) (g1 := g1) (x1 := x1) (x2 := x2) (k := k) (L1 := L1)
      hf_x1_smooth
  -- Route correction: the remaining work is now only the source-faithful bridge algebra. The
  -- prox-support and smooth-descent steps have been isolated above, and the final closure should
  -- combine them with the inactive-block bridge `hbridge`.
  -- TODO: rewrite `hprox_support` into the unscaled `g₁`-support form, combine it with
  -- `hdescent` for the `f₁` slice and the bridge `hbridge`, and then finish by the standard
  -- gradient-mapping/Cauchy-Schwarz algebra from the textbook proof.
  sorry

/-- Lemma 14.4 (1): if the full pair objective
`F(x₁, x₂) = f(x₁, x₂) + g₁(x₁) + g₂(x₂)` is convex, the frozen first-block slice
`x₁ ↦ f(x₁, x₂^k)` is convex and `L₁`-smooth, the current second block `x₂^k` already minimizes
`x₂ ↦ f(x₁^k, x₂) + g₁(x₁^k) + g₂(x₂)`, and the first block update minimizes
`x₁ ↦ f(x₁, x₂^k) + g₁(x₁) + g₂(x₂^k)`, then the half-step objective gap satisfies
`F(x^{k+1/2}) - F(x^*) ≤ ‖G^1_{L₁}(x^k)‖ ‖x^k - x^*‖`, where
`x^{k+1/2} = (x₁^{k+1}, x₂^k)`. Along a full alternating-minimization trajectory, the extra
`x₂^k` optimality is the previous exact second-block update, with the initialization supplying the
`k = 0` case. -/
theorem two_block_half_step_objective_gap_le_x1_gradient_mapping
    (hF_convex : is_convex_function F)
    (hf_x1_convex : ConvexOn ℝ Set.univ f1)
    (hf_x1_smooth : is_l_smooth_on f1 Set.univ (PosReal.toNNReal L1))
    (hxStar : IsMinOn F Set.univ xStar)
    (hx2k : IsMinOn Fx2 Set.univ (x2 k))
    (hstep1 : IsMinOn Fx1 Set.univ (x1 (k + 1))) :
    F xHalf - F xStar ≤
      (((‖G[L1; f1, g1] (x1 k)‖ * ‖xk - xStar‖ : ℝ) : EReal)) := by
  let rhs : EReal := (((‖G[L1; f1, g1] (x1 k)‖ * ‖xk - xStar‖ : ℝ) : EReal))
  have hrhs_top : rhs ≠ ⊤ := by
    change (((‖G[L1; f1, g1] (x1 k)‖ * ‖xk - xStar‖ : ℝ) : EReal)) ≠ ⊤
    exact EReal.coe_ne_top _
  have hrhs_bot : rhs ≠ ⊥ := by
    change (((‖G[L1; f1, g1] (x1 k)‖ * ‖xk - xStar‖ : ℝ) : EReal)) ≠ ⊥
    exact EReal.coe_ne_bot _
  -- Rewrite the target subtraction inequality as a direct upper bound on the half-step value.
  apply (EReal.sub_le_iff_le_add (Or.inr hrhs_top) (Or.inr hrhs_bot)).2
  -- First compare the exact half-step against the prox-gradient test point.
  refine le_trans (two_block_half_step_le_x1_prox_test_point (f := f) (g1 := g1) (g2 := g2)
    (x1 := x1) (x2 := x2) (k := k) (L1 := L1) hstep1) ?_
  -- Then use the dedicated prox-test-point gap estimate.
  simpa [rhs, add_comm] using
    x1_prox_test_point_gap_le_gradient_mapping_bound
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) (xStar := xStar)
      (k := k) (L1 := L1) hF_convex hf_x1_convex hf_x1_smooth hxStar hx2k

end X1ObjectiveGap

-- Proof sketch: first use the exact `x₁`-minimization to identify the first-block prox residual
-- with zero at the half-step `x^{k+1/2}`. Then compare the exact next iterate with the
-- second-block prox-gradient slice using the exact `x₂`-minimization hypothesis, apply the
-- one-block convex proximal-gradient gap estimate, and finish with Cauchy-Schwarz.
section X2ObjectiveGap

variable (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (g2 : E2 → EReal)
variable [InnerProductSpace ℝ E2] [ProperSpace E2]
variable [NormedSpace ℝ E1]
variable [IsProperExtendedRealFunction g2] [Fact (LowerSemicontinuous g2)]
  [Fact (is_convex_function g2)]
variable (x1 : ℕ → E1) (x2 : ℕ → E2) (xStar : E1 × E2) (k : ℕ)
variable (L2 : PosReal)

local notation "F" => two_block_alternating_minimization_objective f.toEReal g1 g2
local notation "xHalf" => two_block_alternating_minimization_half_step x1 x2 k
local notation "xNext" => (x1 (k + 1), x2 (k + 1))
local notation "f2" => fun y2 ↦ f (x1 (k + 1), y2)
local notation "Fx1" => two_block_alternating_minimization_x1_objective f.toEReal g1 g2 (x2 k)
local notation "Fx2" => two_block_alternating_minimization_x2_objective f.toEReal g1 g2 (x1 (k + 1))
local notation "phi2" => fun y2 : E2 ↦ sInf (Set.range (fun z1 : E1 ↦ F (z1, y2)))

/-- Helper for Lemma 14.4: the exact second-block iterate cannot exceed the value of the
frozen-slice prox-gradient comparison point. -/
lemma two_block_next_iterate_le_x2_prox_test_point
    (hstep2 : IsMinOn Fx2 Set.univ (x2 (k + 1))) :
    F xNext ≤ F (x1 (k + 1), T[L2; f2, g2] (x2 k)) := by
  -- Compare the exact second-block minimizer against the prox-gradient test point on the frozen
  -- `x₁ = x₁^{k+1}` slice.
  have hmin := (isMinOn_iff.mp hstep2) (T[L2; f2, g2] (x2 k)) (by simp)
  simpa using hmin

/-- Helper for Lemma 14.4: exact minimization of the inactive first block compares the half-step
directly against the competitor obtained by replacing only the first block with `xStar.1`. -/
lemma current_x1_slice_minimizer_le_xStar_first_block
    (hstep1 : IsMinOn Fx1 Set.univ (x1 (k + 1))) :
    F xHalf ≤ F (xStar.1, x2 k) := by
  -- Freeze the active second block at `x₂^k` and compare the exact `x₁`-minimizer to the
  -- competitor whose first block is `xStar.1`.
  have hmin := (isMinOn_iff.mp hstep1) xStar.1 (by simp)
  simpa [two_block_alternating_minimization_half_step] using hmin

/-- Helper for Lemma 14.4: exact minimization of the current `x₁` slice identifies the marginal
partial-infimum value at `x₂^k` with the half-step objective value. -/
lemma x2_partial_infimum_eq_current_value
    (hstep1 : IsMinOn Fx1 Set.univ (x1 (k + 1))) :
    phi2 (x2 k) = F xHalf := by
  apply le_antisymm
  · -- The updated first block realizes one point in the fiber defining `phi2`.
    exact sInf_le ⟨x1 (k + 1), by simp [two_block_alternating_minimization_half_step]⟩
  · -- Exact slice minimality shows that no other first block gives a smaller fiber value.
    refine le_sInf ?_
    rintro _ ⟨z1, rfl⟩
    simpa [two_block_alternating_minimization_half_step] using
      (isMinOn_iff.mp hstep1) z1 (by simp)

/-- Helper for Lemma 14.4: the marginal partial infimum at a second-block competitor is bounded
above by the full objective evaluated at any full competitor with that second block. -/
lemma x2_partial_infimum_le_objective_at_competitor
    (y : E1 × E2) :
    phi2 y.2 ≤ F y := by
  rcases y with ⟨y1, y2⟩
  -- Insert the competitor's first block as one witness in the defining fiber of `phi2`.
  exact sInf_le ⟨y1, by simp⟩

/-- Helper for Lemma 14.4: the exact inactive `x₁`-minimization reduces the half-step objective
gap to the active `x₂` linearization term plus the `g₂` gap against `xStar.2`. -/
lemma x2_exact_inactive_block_gap_le_active_linearization
    (hF_convex : is_convex_function F)
    (hf_x2_convex : ConvexOn ℝ Set.univ f2)
    (hxStar : IsMinOn F Set.univ xStar)
    (hstep1 : IsMinOn Fx1 Set.univ (x1 (k + 1))) :
    F xHalf ≤
      (((inner ℝ (∇ f2 (x2 k)) ((x2 k) - xStar.2) : ℝ) : EReal)) +
        (g2 (x2 k) - g2 xStar.2) + F xStar := by
  -- Route correction: pivot from the stalled owner-surface theorem to the source-faithful
  -- marginal object `phi2(y2) = inf_z1 F(z1, y2)`.
  have hphi_eq :
      phi2 (x2 k) = F xHalf :=
    x2_partial_infimum_eq_current_value
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) (k := k) hstep1
  have hphi_le :
      phi2 xStar.2 ≤ F xStar :=
    x2_partial_infimum_le_objective_at_competitor
      (f := f) (g1 := g1) (g2 := g2) xStar
  let _ := hF_convex
  let _ := hf_x2_convex
  let _ := hxStar
  let _ := hphi_eq
  let _ := hphi_le
  -- TODO: prove the marginal-support bridge
  -- `phi2 xStar.2 ≥ phi2 (x2 k) + ⟪∇ f2 (x2 k), xStar.2 - x2 k⟫ + g2 xStar.2 - g2 (x2 k)`.
  -- Exact attainment at `x₁^{k+1}` has already identified `phi2 (x2 k)` with `F xHalf`, and the
  -- competitor upper bound `hphi_le` already compares `phi2 xStar.2` to `F xStar`.
  sorry

/-- Helper for Lemma 14.4: the frozen `x₂` prox step satisfies the Chapter 6 all-points support
inequality for the scaled penalty, specialized at `xStar.2`. -/
lemma x2_scaled_prox_support_inequality :
    let t2 := T[L2; f2, g2] (x2 k)
    (((inner ℝ
        ((x2 k - (1 / L2 : ℝ) • ∇ f2 (x2 k)) - t2)
        (xStar.2 - t2) : ℝ)) : EReal) ≤
      ((((1 / L2 : PosReal) : EReal) • g2) xStar.2 -
        ((((1 / L2 : PosReal) : EReal) • g2) t2)) := by
  dsimp
  let t2 := T[L2; f2, g2] (x2 k)
  let scaledG2 : E2 → EReal := (((1 / L2 : PosReal) : EReal) • g2)
  let hg2_scaled :=
    scaled_function_proper_closed_convex_of_pos
      g2 inferInstance (Fact.out : LowerSemicontinuous g2)
      (Fact.out : is_convex_function g2) (1 / L2)
  have hprox :
      prox[scaledG2] (x2 k - (1 / L2 : ℝ) • ∇ f2 (x2 k)) = {t2} := by
    -- The symmetric `x₂` prox-gradient test point is the singleton proximal step of the scaled
    -- penalty at the forward-gradient point.
    simpa [t2, scaledG2, proximal_gradient_step] using
      (prox_grad_operator_eq_singleton (f := Function.toEReal f2) (g := g2) L2
        (interior_effective_domain_point_of_real f2 (x2 k)))
  rcases prox_singleton_implies_effective_domain_and_inner_support
      scaledG2 hg2_scaled.1 hg2_scaled.2.2
      (x2 k - (1 / L2 : ℝ) • ∇ f2 (x2 k)) t2 hprox with
    ⟨ht2_eff, hsupport⟩
  by_cases hxStar_eff : xStar.2 ∈ effective_domain scaledG2
  · -- On the effective domain, the Chapter 6 support inequality applies directly.
    simpa [scaledG2] using hsupport xStar.2 hxStar_eff
  · -- If `xStar.2` is outside the effective domain, the right-hand side is `⊤`.
    have hxStar_top : scaledG2 xStar.2 = ⊤ := by
      have hnot : ¬ scaledG2 xStar.2 < ⊤ := by
        simpa [effective_domain] using hxStar_eff
      exact le_antisymm le_top (not_lt.mp hnot)
    have ht2_ne_top : scaledG2 t2 ≠ ⊤ := (mem_effective_domain.mp ht2_eff).ne
    have h_rhs_top :
        (↑↑(1 / L2) * g2 xStar.2 - ↑↑(1 / L2) * g2 t2 : EReal) = ⊤ := by
      calc
        (↑↑(1 / L2) * g2 xStar.2 - ↑↑(1 / L2) * g2 t2 : EReal)
            = scaledG2 xStar.2 - scaledG2 t2 := by
              simp [scaledG2, smul_eq_mul]
        _ = ⊤ - scaledG2 t2 := by rw [hxStar_top]
        _ = ⊤ := EReal.top_sub ht2_ne_top
    rw [h_rhs_top]
    exact le_top

/-- Helper for Lemma 14.4: the block descent lemma controls the smooth second-block slice at the
prox-gradient test point by its quadratic model at `x₂^k`. -/
lemma x2_smooth_descent_to_prox_test_point
    (hf_x2_smooth : is_l_smooth_on f2 Set.univ (PosReal.toNNReal L2)) :
    let t2 := T[L2; f2, g2] (x2 k)
    f (x1 (k + 1), t2) ≤
      f (x1 (k + 1), x2 k) +
        inner ℝ (∇ f2 (x2 k)) (t2 - x2 k) +
          ((L2 : ℝ) / 2) * ‖t2 - x2 k‖ ^ (2 : ℕ) := by
  dsimp
  -- Apply Lemma 5.7 on the frozen `x₂` slice with domain `Set.univ`.
  simpa [norm_sub_rev] using
    is_l_smooth_on_descent_lemma
      (D := Set.univ)
      (f := f2)
      (by simpa using convex_univ)
      hf_x2_smooth
      (x := x2 k)
      (y := T[L2; f2, g2] (x2 k))
      (by simp)
      (by simp)

/-- Helper for Lemma 14.4: after rewriting the prox step through the gradient mapping, the
remaining quadratic residual on the active second block is bounded by the product of the
gradient-mapping norm and the half-step-to-solution distance. -/
lemma x2_gradient_mapping_residual_term_le_norm_product :
    let t2 := T[L2; f2, g2] (x2 k)
    (L2 : ℝ) * inner ℝ (x2 k - t2) ((x2 k) - xStar.2) -
        ((L2 : ℝ) / 2) * ‖x2 k - t2‖ ^ (2 : ℕ) ≤
      ‖G[L2; f2, g2] (x2 k)‖ * ‖xHalf - xStar‖ := by
  dsimp
  let G2 := G[L2; f2, g2] (x2 k)
  have ht2 :
      T[L2; f2, g2] (x2 k) = x2 k - (1 / (L2 : ℝ)) • G2 := by
    -- Rewrite the second-block prox point as the identity minus the scaled gradient mapping.
    simpa [G2] using
      prox_gradient_operator_eq_sub_gradient_mapping
        (f := f2) (g := g2) (L := L2) (x := x2 k)
  have hstep :
      x2 k - T[L2; f2, g2] (x2 k) = (1 / (L2 : ℝ)) • G2 := by
    -- Solve the residual `x₂^k - t₂` from the prox-step identity above.
    rw [ht2]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hL_pos : 0 < (L2 : ℝ) := L2.2
  have hL_ne : (L2 : ℝ) ≠ 0 := hL_pos.ne'
  have hrewrite :
      (L2 : ℝ) * inner ℝ (x2 k - T[L2; f2, g2] (x2 k)) ((x2 k) - xStar.2) -
          ((L2 : ℝ) / 2) * ‖x2 k - T[L2; f2, g2] (x2 k)‖ ^ (2 : ℕ) =
        inner ℝ G2 ((x2 k) - xStar.2) -
          ((1 : ℝ) / (2 * (L2 : ℝ))) * ‖G2‖ ^ (2 : ℕ) := by
    -- Normalize the quadratic term to the exact scalar shape used in the symmetric branch.
    rw [hstep, inner_smul_left, norm_smul, Real.norm_eq_abs, abs_of_pos hL_pos]
    rw [pow_two]
    field_simp [hL_ne]
    ring
  have hquad_nonneg :
      0 ≤ ((1 : ℝ) / (2 * (L2 : ℝ))) * ‖G2‖ ^ (2 : ℕ) := by
    positivity
  have hcoord :
      ‖(x2 k) - xStar.2‖ ≤ ‖xHalf - xStar‖ := by
    -- The second coordinate norm is dominated by the product-space norm at the half-step.
    simpa [xHalf] using (norm_snd_le (xHalf - xStar))
  calc
    (L2 : ℝ) * inner ℝ (x2 k - T[L2; f2, g2] (x2 k)) ((x2 k) - xStar.2) -
        ((L2 : ℝ) / 2) * ‖x2 k - T[L2; f2, g2] (x2 k)‖ ^ (2 : ℕ) =
      inner ℝ G2 ((x2 k) - xStar.2) -
        ((1 : ℝ) / (2 * (L2 : ℝ))) * ‖G2‖ ^ (2 : ℕ) := hrewrite
    _ ≤ inner ℝ G2 ((x2 k) - xStar.2) := by
      exact sub_le_self _ hquad_nonneg
    _ ≤ ‖G2‖ * ‖(x2 k) - xStar.2‖ := by
      exact real_inner_le_norm _ _
    _ ≤ ‖G2‖ * ‖xHalf - xStar‖ := by
      exact mul_le_mul_of_nonneg_left hcoord (norm_nonneg _)
    _ = ‖G[L2; f2, g2] (x2 k)‖ * ‖xHalf - xStar‖ := by
      rfl

/-- Helper for Lemma 14.4: the unresolved x₂-side gap estimate is exactly the prox-gradient
comparison bound for the frozen second-block slice. -/
lemma x2_prox_test_point_gap_le_gradient_mapping_bound
    (hF_convex : is_convex_function F)
    (hf_x2_convex : ConvexOn ℝ Set.univ f2)
    (hf_x2_smooth : is_l_smooth_on f2 Set.univ (PosReal.toNNReal L2))
    (hxStar : IsMinOn F Set.univ xStar)
    (hstep1 : IsMinOn Fx1 Set.univ (x1 (k + 1))) :
    F (x1 (k + 1), T[L2; f2, g2] (x2 k)) ≤
      (((‖G[L2; f2, g2] (x2 k)‖ * ‖xHalf - xStar‖ : ℝ) : EReal)) + F xStar := by
  let t2 := T[L2; f2, g2] (x2 k)
  have hbridge :=
    x2_exact_inactive_block_gap_le_active_linearization
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) (xStar := xStar) (k := k)
      hF_convex hf_x2_convex hxStar hstep1
  have hprox_support :=
    x2_scaled_prox_support_inequality
      (f := f) (g2 := g2) (x1 := x1) (x2 := x2) (xStar := xStar)
      (k := k) (L2 := L2)
  have hdescent :=
    x2_smooth_descent_to_prox_test_point
      (f := f) (g2 := g2) (x1 := x1) (x2 := x2) (k := k) (L2 := L2)
      hf_x2_smooth
  -- Route correction: the remaining work is now only the symmetric inactive-block bridge
  -- algebra. The prox-support and smooth-descent steps have been isolated above.
  -- TODO: rewrite `hprox_support` into the unscaled `g₂`-support form, combine it with
  -- `hdescent` for the `f₂` slice and the bridge `hbridge`, and then finish by the same
  -- gradient-mapping/Cauchy-Schwarz argument as in the `x₁` branch.
  sorry

/-- Lemma 14.4 (2): if the full pair objective
`F(x₁, x₂) = f(x₁, x₂) + g₁(x₁) + g₂(x₂)` is convex, the frozen second-block slice
`x₂ ↦ f(x₁^{k+1}, x₂)` is convex and `L₂`-smooth, the preceding first block update minimizes
`x₁ ↦ f(x₁, x₂^k) + g₁(x₁) + g₂(x₂^k)`, and the second block update after the half-step
minimizes `x₂ ↦ f(x₁^{k+1}, x₂) + g₁(x₁^{k+1}) + g₂(x₂)`, then the next-iterate
objective gap satisfies
`F(x^{k+1}) - F(x^*) ≤ ‖G^2_{L₂}(x^{k+1/2})‖ ‖x^{k+1/2} - x^*‖`. -/
theorem two_block_next_iterate_objective_gap_le_x2_gradient_mapping
    (hF_convex : is_convex_function F)
    (hf_x2_convex : ConvexOn ℝ Set.univ f2)
    (hf_x2_smooth : is_l_smooth_on f2 Set.univ (PosReal.toNNReal L2))
    (hxStar : IsMinOn F Set.univ xStar)
    (hstep1 : IsMinOn Fx1 Set.univ (x1 (k + 1)))
    (hstep2 : IsMinOn Fx2 Set.univ (x2 (k + 1))) :
    F xNext - F xStar ≤
      (((‖G[L2; f2, g2] (x2 k)‖ * ‖xHalf - xStar‖ : ℝ) : EReal)) := by
  let rhs : EReal := (((‖G[L2; f2, g2] (x2 k)‖ * ‖xHalf - xStar‖ : ℝ) : EReal))
  have hrhs_top : rhs ≠ ⊤ := by
    change (((‖G[L2; f2, g2] (x2 k)‖ * ‖xHalf - xStar‖ : ℝ) : EReal)) ≠ ⊤
    exact EReal.coe_ne_top _
  have hrhs_bot : rhs ≠ ⊥ := by
    change (((‖G[L2; f2, g2] (x2 k)‖ * ‖xHalf - xStar‖ : ℝ) : EReal)) ≠ ⊥
    exact EReal.coe_ne_bot _
  -- Rewrite the target subtraction inequality as a direct upper bound on the next iterate value.
  apply (EReal.sub_le_iff_le_add (Or.inr hrhs_top) (Or.inr hrhs_bot)).2
  -- First compare the exact second-block iterate against the prox-gradient test point.
  refine le_trans (two_block_next_iterate_le_x2_prox_test_point (f := f) (g1 := g1) (g2 := g2)
    (x1 := x1) (x2 := x2) (k := k) (L2 := L2) hstep2) ?_
  -- Then use the dedicated prox-test-point gap estimate.
  simpa [rhs, add_comm] using
    x2_prox_test_point_gap_le_gradient_mapping_bound
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) (xStar := xStar)
      (k := k) (L2 := L2) hF_convex hf_x2_convex hf_x2_smooth hxStar hstep1

end X2ObjectiveGap

end ObjectiveGap

end

/-! ### Theorem_14_4 (from Chap14) -/
noncomputable section

universe u

section

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace ℝ (Ei i)]

/- `prompt_add/` is absent in this workspace, so the statement design is sampled directly from the
nearby Chapter 3, 11, and 14 owners.

This item is `source-facing`: it is a convergence corollary for sequences generated by the
composite alternating-minimization method. Domain sampling in the Chapter 14 API shows that the
trajectory owner already exists upstream:
- `is_alternating_minimization_trajectory` from Algorithm 14.1 for generated iterate sequences;
- `IsAlternatingMinimizationCompositeModel` from Algorithm 14.3 for the standing composite-model
  regularity assumptions in Assumption 14.6;
- `isMinOn_alternating_minimization_full_objective_iff_isMinOn_composite_block_objective` from
  Proposition 14.2 for the bridge from the Algorithm 14.3 displayed one-block objective to the
  owner blockwise `IsMinOn` clauses for the full composite objective;
- `alternating_minimization_trajectory_range_bounded` and
  `alternating_minimization_cluster_points_coordinatewise_minima` from Theorem 14.3 for the two
  convergence conclusions on the owner trajectory; and
- `is_stationary_point_of_coordinatewise_minimum` from Lemma 14.2 for the bridge from
  coordinatewise minimality to the Chapter 3 stationary-point owner `is_stationary_point`.

Accordingly, this file no longer keeps a parallel local trajectory predicate. The only local
`bridge/view` is the translation from the Algorithm 14.3 one-step data, through Proposition 14.2,
to the canonical Algorithm 14.1 trajectory for the full composite objective
`composite_model_objective f (separableSum g)`. The public theorems stay source-facing on the
Algorithm 14.3 step data and use that owner trajectory only internally.

Route correction: the remaining validation blocker for this file is upstream, not in the proof
route below. A direct
`lake env lean FirstOrderMethodsOptimization_Beck_2017/Chap14/Theorem_14_4.lean` currently stops at the
missing object file for `FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4`, so the
Chapter 14 proof skeleton is left unchanged until that canonical Chapter 11 owner rebuilds. -/

-- Proof sketch: for each outer iteration and block, start from the owner clause
-- `(hstep k).block_isMinOn i` on `alternating_minimization_composite_block_objective f g ...`,
-- then use Proposition 14.2 to transfer that minimizer statement to the full composite objective.
-- Together with the initial-domain assumption, this yields exactly the defining clauses of
-- `is_alternating_minimization_trajectory` for the composite objective.
/-- If every successive pair `(x^k, x^{k+1})` satisfies the composite Algorithm 14.3 step
conditions and `x^0 ∈ dom(F)`, then `x` is the canonical alternating-minimization trajectory for
the composite objective `F(x) = f(x) + ∑ i, g_i(x_i)`. -/
theorem is_alternating_minimization_trajectory_of_composite_steps
    {f : ((i : Fin p) → Ei i) → EReal}
    {g : (i : Fin p) → Ei i → EReal}
    {x : ℕ → (i : Fin p) → Ei i}
    (hx0 : x 0 ∈ effective_domain (composite_model_objective f (separableSum g)))
    (hstep : ∀ k : ℕ, IsAlternatingMinimizationCompositeStep f g (x k) (x (k + 1))) :
    is_alternating_minimization_trajectory (composite_model_objective f (separableSum g)) x := by
  let F : ((i : Fin p) → Ei i) → EReal := composite_model_objective f (separableSum g)
  have hprefix_old_eq (k : ℕ) (i : Fin p) :
      (fun j : Fin p ↦ if j.1 < i.1 then x (k + 1) j else x k j) =
        alternating_minimization_partial_state (x k) (x (k + 1)) i (x k i) := by
    funext j
    by_cases hj : j.1 < i.1
    · simp [alternating_minimization_partial_state, hj]
    · by_cases hji : j = i
      · subst hji
        simp [alternating_minimization_partial_state, Function.update]
      · simp [alternating_minimization_partial_state, hj, Function.update, hji]
  have hprefix_new_eq (k : ℕ) (i : Fin p) :
      (fun j : Fin p ↦ if j.1 < i.1 + 1 then x (k + 1) j else x k j) =
        alternating_minimization_partial_state (x k) (x (k + 1)) i (x (k + 1) i) := by
    funext j
    by_cases hj : j.1 < i.1
    · simp [alternating_minimization_partial_state, hj, Nat.lt_succ_of_lt hj]
    · by_cases hji : j = i
      · subst hji
        simp [alternating_minimization_partial_state, Function.update]
      · have hnot : ¬ j.1 < i.1 + 1 := by
          intro hlt
          have hle : i.1 ≤ j.1 := Nat.le_of_not_lt hj
          have hge : j.1 ≤ i.1 := Nat.lt_succ_iff.mp hlt
          exact hji (Fin.ext (le_antisymm hge hle))
        simp [alternating_minimization_partial_state, hj, hji, hnot, Function.update]
  have hprefix_mem :
      ∀ k : ℕ, x k ∈ effective_domain F →
        ∀ n ≤ p, (fun j : Fin p ↦ if j.1 < n then x (k + 1) j else x k j) ∈ effective_domain F := by
    intro k hxk n hn
    let hmodel : IsAlternatingMinimizationCompositeModel f g :=
      (hstep k).toIsAlternatingMinimizationCompositeModel
    induction n with
    | zero =>
        simpa [F] using hxk
    | succ n ihn =>
        have hn_lt : n < p := Nat.lt_of_succ_le hn
        let i : Fin p := ⟨n, hn_lt⟩
        have hold :
            (fun j : Fin p ↦ if j.1 < n then x (k + 1) j else x k j) ∈ effective_domain F :=
          ihn (Nat.le_of_lt hn_lt)
        have hold_old :
            alternating_minimization_partial_state (x k) (x (k + 1)) i (x k i) ∈
              effective_domain F := by
          rw [← hprefix_old_eq k i]
          exact hold
        have hinactive_ne_bot :
            (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then x (k + 1) j else x k j)) ≠ ⊥ := by
          exact ereal_sum_ne_bot (Finset.univ.erase i)
            (fun j ↦ g j (if j.1 < i.1 then x (k + 1) j else x k j))
            (fun j _ ↦ (hmodel.g_proper j).ne_bot _)
        have hdisplay_ne_bot :
            alternating_minimization_composite_block_objective
              f g (x k) (x (k + 1)) i (x k i) ≠ ⊥ := by
          rw [alternating_minimization_composite_block_objective_apply, EReal.add_ne_bot_iff]
          exact ⟨hmodel.f_ne_bot _, (hmodel.g_proper i).ne_bot (x k i)⟩
        have hinactive :
            (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then x (k + 1) j else x k j)) =
              (((∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then x (k + 1) j else x k j)).toReal
                : ℝ) : EReal) := by
          exact inactive_penalty_eq_coe_toReal_of_ne_bot_of_mem_effective_domain
            f g (x k) (x (k + 1)) i hinactive_ne_bot hdisplay_ne_bot hold_old
        have hiff :
            IsMinOn
              (alternating_minimization_block_objective
                (composite_model_objective f (separableSum g))
                (x k)
                (x (k + 1))
                i)
              Set.univ
              (x (k + 1) i) ↔
            IsMinOn
              (alternating_minimization_composite_block_objective f g (x k) (x (k + 1)) i)
              Set.univ
              (x (k + 1) i) :=
          isMinOn_alternating_minimization_full_objective_iff_isMinOn_composite_block_objective
            f g (x k) (x (k + 1)) i hinactive (x (k + 1) i)
        have hfull :
            IsMinOn
              (alternating_minimization_block_objective
                (composite_model_objective f (separableSum g))
                (x k)
                (x (k + 1))
                i)
              Set.univ
              (x (k + 1) i) :=
          hiff.2 ((hstep k).block_isMinOn i)
        have hcompare := (isMinOn_iff.mp hfull) (x k i) (by simp)
        have hold_top :
            alternating_minimization_block_objective
                (composite_model_objective f (separableSum g))
                (x k)
                (x (k + 1))
                i
                (x k i) <
              ⊤ := by
          simpa [F, alternating_minimization_block_objective_apply] using
            (mem_effective_domain.mp hold_old)
        have hnew_top :
            alternating_minimization_block_objective
                (composite_model_objective f (separableSum g))
                (x k)
                (x (k + 1))
                i
                (x (k + 1) i) <
              ⊤ :=
          lt_of_le_of_lt hcompare hold_top
        rw [hprefix_new_eq k i]
        exact mem_effective_domain.mpr <|
          by
            simpa [F, alternating_minimization_block_objective_apply] using hnew_top
  have hx_mem : ∀ k : ℕ, x k ∈ effective_domain F := by
    intro k
    induction k with
    | zero =>
        simpa [F] using hx0
    | succ k ih =>
        simpa [F] using hprefix_mem k ih p (le_rfl : p ≤ p)
  refine ⟨by simpa [F] using hx0, ?_⟩
  intro k i
  let hmodel : IsAlternatingMinimizationCompositeModel f g :=
    (hstep k).toIsAlternatingMinimizationCompositeModel
  have hiff :
      IsMinOn
        (alternating_minimization_block_objective
          (composite_model_objective f (separableSum g))
          (x k)
          (x (k + 1))
          i)
        Set.univ
        (x (k + 1) i) ↔
      IsMinOn
        (alternating_minimization_composite_block_objective f g (x k) (x (k + 1)) i)
        Set.univ
        (x (k + 1) i) :=
    by
      have hold_old :
          alternating_minimization_partial_state (x k) (x (k + 1)) i (x k i) ∈
            effective_domain F := by
        rw [← hprefix_old_eq k i]
        exact hprefix_mem k (hx_mem k) i.1 (Nat.le_of_lt i.2)
      have hinactive_ne_bot :
          (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then x (k + 1) j else x k j)) ≠ ⊥ := by
        exact ereal_sum_ne_bot (Finset.univ.erase i)
          (fun j ↦ g j (if j.1 < i.1 then x (k + 1) j else x k j))
          (fun j _ ↦ (hmodel.g_proper j).ne_bot _)
      have hdisplay_ne_bot :
          alternating_minimization_composite_block_objective
            f g (x k) (x (k + 1)) i (x k i) ≠ ⊥ := by
        rw [alternating_minimization_composite_block_objective_apply, EReal.add_ne_bot_iff]
        exact ⟨hmodel.f_ne_bot _, (hmodel.g_proper i).ne_bot (x k i)⟩
      have hinactive :
          (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then x (k + 1) j else x k j)) =
            (((∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then x (k + 1) j else x k j)).toReal
              : ℝ) : EReal) := by
        exact inactive_penalty_eq_coe_toReal_of_ne_bot_of_mem_effective_domain
          f g (x k) (x (k + 1)) i hinactive_ne_bot hdisplay_ne_bot hold_old
      exact
        isMinOn_alternating_minimization_full_objective_iff_isMinOn_composite_block_objective
          f g (x k) (x (k + 1)) i hinactive (x (k + 1) i)
  exact hiff.2 ((hstep k).block_isMinOn i)

section Boundedness

variable (f : ((i : Fin p) → Ei i) → EReal)
variable (g : (i : Fin p) → Ei i → EReal)
variable (x : ℕ → (i : Fin p) → Ei i)

local notation "F" => composite_model_objective f (separableSum g)

-- Proof sketch: convert the source-facing composite-step data to the canonical owner trajectory
-- for `F`, then apply Theorem 14.3 (1).
/-- Theorem 14.4 (1): under Assumption 14.6, if every real level set of the composite objective
`F(x) = f(x) + ∑ i, g_i(x_i)` is bounded and `x^k` is generated by Algorithm 14.3, then the
sequence `x^k` is bounded. -/
theorem alternating_minimization_composite_trajectory_bounded
    (hlevel :
      ∀ α : ℝ, Bornology.IsBounded {y | F y ≤ (α : EReal)})
    (hx0 : x 0 ∈ effective_domain F)
    (hstep : ∀ k : ℕ, IsAlternatingMinimizationCompositeStep f g (x k) (x (k + 1))) :
    Bornology.IsBounded (Set.range x) := by
  exact alternating_minimization_trajectory_range_bounded F x hlevel
    (is_alternating_minimization_trajectory_of_composite_steps hx0 hstep)

end Boundedness

end

section Stationarity

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace ℝ (Ei i)]

variable (f : ((i : Fin p) → Ei i) → EReal)
variable (g : (i : Fin p) → Ei i → EReal)
variable (x : ℕ → (i : Fin p) → Ei i)

local notation "F" => composite_model_objective f (separableSum g)

/-- Helper for Theorem 14.4: the block-separable penalty `x ↦ ∑ i, g_i(x_i)` never attains
`-∞` under Assumption 14.6. -/
lemma alternating_minimization_separableSum_ne_bot
    (hmodel : IsAlternatingMinimizationCompositeModel f g) :
    ∀ z : (i : Fin p) → Ei i, separableSum g z ≠ ⊥ := by
  intro z
  -- Properness of each block penalty rules out `-∞` termwise, hence also in the finite sum.
  simpa [separableSum_apply] using
    ereal_sum_ne_bot Finset.univ (fun i ↦ g i (z i))
      (fun i _ ↦ (hmodel.g_proper i).ne_bot (z i))

/-- Helper for Theorem 14.4: the composite objective `f + separableSum g` never attains `-∞`
under Assumption 14.6. -/
lemma alternating_minimization_composite_objective_ne_bot
    (hmodel : IsAlternatingMinimizationCompositeModel f g) :
    ∀ z : (i : Fin p) → Ei i, F z ≠ ⊥ := by
  intro z
  -- Both summands avoid `-∞`, so their sum does as well.
  rw [composite_model_objective_apply, EReal.add_ne_bot_iff]
  exact ⟨hmodel.f_ne_bot z,
    alternating_minimization_separableSum_ne_bot (f := f) (g := g) hmodel z⟩

/-- Helper for Theorem 14.4: any point where the composite objective is finite already lies in the
effective domain of the separable penalty. -/
lemma effective_domain_composite_model_objective_subset_separable
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {z : (i : Fin p) → Ei i} (hz : z ∈ effective_domain F) :
    z ∈ effective_domain (separableSum g) := by
  -- If the penalty were `⊤`, then adding the non-`⊥` smooth term would force `F z = ⊤`.
  refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
  intro hz_top
  have hF_top : F z = ⊤ := by
    rw [composite_model_objective_apply, hz_top]
    exact EReal.add_top_of_ne_bot (hmodel.f_ne_bot z)
  exact (lt_irrefl (⊤ : EReal)) (by simpa [hF_top] using mem_effective_domain.mp hz)

/-- Helper for Theorem 14.4: finiteness of the composite objective forces every block penalty
value to be finite. -/
lemma alternating_minimization_block_mem_effective_domain
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {z : (i : Fin p) → Ei i} (hz : z ∈ effective_domain F) (i : Fin p) :
    z i ∈ effective_domain (g i) := by
  -- First move from the composite effective domain to the separable one, then use the Chapter 11
  -- blockwise effective-domain lemma.
  have hz_separable :
      z ∈ effective_domain (separableSum g) :=
    effective_domain_composite_model_objective_subset_separable
      (f := f) (g := g) hmodel hz
  exact
    block_mem_effective_domain_of_mem_separableSum_effective_domain
      g hmodel.g_proper hz_separable i

/-- Helper for Theorem 14.4: on the composite effective domain, each block penalty value is a
real coercion in `EReal`. -/
lemma alternating_minimization_block_value_eq_coe_toReal
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {z : (i : Fin p) → Ei i} (hz : z ∈ effective_domain F) (i : Fin p) :
    g i (z i) = ((((g i (z i)).toReal : ℝ)) : EReal) := by
  -- The block-domain bridge gives finiteness, so `EReal.coe_toReal` recovers the original value.
  have hzi :
      z i ∈ effective_domain (g i) :=
    alternating_minimization_block_mem_effective_domain
      (f := f) (g := g) hmodel hz i
  exact
    (EReal.coe_toReal
      (mem_effective_domain.mp hzi).ne
      ((hmodel.g_proper i).ne_bot (z i))).symm

/-- Helper for Theorem 14.4: coercing a finite real sum into `EReal` matches summing the coerced
terms. -/
lemma ereal_coe_finset_sum {α : Type*} (s : Finset α) (a : α → ℝ) :
    (((Finset.sum s a : ℝ)) : EReal) = Finset.sum s (fun i ↦ ((a i : ℝ) : EReal)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp [Finset.sum_insert, hi, ih, EReal.coe_add]

/-- Helper for Theorem 14.4: the composite objective `f + separableSum g` is lower semicontinuous
and continuous on its effective domain under Assumption 14.6. -/
lemma alternating_minimization_composite_objective_regular
    (hmodel : IsAlternatingMinimizationCompositeModel f g) :
    LowerSemicontinuous F ∧ ContinuousOn F (effective_domain F) := by
  have hseparable_ne_bot :
      ∀ z : (i : Fin p) → Ei i, separableSum g z ≠ ⊥ :=
    alternating_minimization_separableSum_ne_bot (f := f) (g := g) hmodel
  have hf_cont :
      ContinuousOn (fun z ↦ ((f z).toReal : EReal)) (effective_domain F) := by
    -- Continuity of `f.toReal` comes from differentiability on the interior domain furnished by
    -- Assumption 14.6, restricted along the separable-domain inclusion.
    refine
      (continuous_coe_real_ereal.continuousOn : ContinuousOn ((↑) : ℝ → EReal) Set.univ).comp
        ?_ ?_
    · intro z hz
      have hz_separable :
          z ∈ effective_domain (separableSum g) :=
        effective_domain_composite_model_objective_subset_separable
          (f := f) (g := g) hmodel hz
      have hz_diff :
          DifferentiableWithinAt ℝ (fun x ↦ (f x).toReal) (interior (effective_domain f)) z :=
        hmodel.f_toReal_differentiableOn_interior_effective_domain z
          (hmodel.g_effective_domain_subset_interior_f_effective_domain hz_separable)
      have hz_cont :
          ContinuousWithinAt (fun x ↦ (f x).toReal) (interior (effective_domain f)) z :=
        hz_diff.continuousWithinAt
      -- Restrict continuity from the interior domain of `f` to the smaller composite effective
      -- domain provided by Assumption 14.6.
      exact hz_cont.mono fun y hy ↦
        hmodel.g_effective_domain_subset_interior_f_effective_domain
          (effective_domain_composite_model_objective_subset_separable
            (f := f) (g := g) hmodel hy)
    · intro z hz
      simp
  have hg_cont :
      ContinuousOn (separableSum g) (effective_domain F) := by
    classical
    have hcoord_cont :
        ∀ i : Fin p, ContinuousOn (fun z : (i : Fin p) → Ei i ↦ (g i (z i)).toReal)
          (effective_domain F) := by
      intro i
      -- Route correction: sum the real-valued coordinate functions first, because `EReal` lacks a
      -- global `ContinuousAdd` instance.
      refine EReal.continuousOn_toReal.comp ?_ ?_
      · refine (hmodel.g_continuousOn_effective_domain i).comp
          (continuous_apply i).continuousOn ?_
        intro z hz
        exact
          alternating_minimization_block_mem_effective_domain
            (f := f) (g := g) hmodel hz i
      · intro z hz
        have hzi :
            z i ∈ effective_domain (g i) :=
          alternating_minimization_block_mem_effective_domain
            (f := f) (g := g) hmodel hz i
        have hne_top : g i (z i) ≠ ⊤ := (mem_effective_domain.mp hzi).ne
        have hne_bot : g i (z i) ≠ ⊥ := (hmodel.g_proper i).ne_bot (z i)
        simp [hne_top, hne_bot]
    have hreal_sum_cont :
        ContinuousOn (fun z : (i : Fin p) → Ei i ↦ ∑ i : Fin p, (g i (z i)).toReal)
          (effective_domain F) := by
      -- The real-valued sum is continuous by the ordinary finite-sum API.
      simpa using continuousOn_finset_sum Finset.univ (fun i _ ↦ hcoord_cont i)
    have hcoe_sum_cont :
        ContinuousOn
          (fun z : (i : Fin p) → Ei i ↦
            (((∑ i : Fin p, (g i (z i)).toReal) : ℝ) : EReal))
          (effective_domain F) := by
      -- Coercing the continuous real sum back to `EReal` preserves continuity.
      refine
        (continuous_coe_real_ereal.continuousOn : ContinuousOn ((↑) : ℝ → EReal) Set.univ).comp
          hreal_sum_cont ?_
      intro z hz
      simp
    -- Rewrite the coerced real sum back to the separable penalty on the effective domain.
    refine hcoe_sum_cont.congr ?_
    intro z hz
    calc
      separableSum g z = ∑ i : Fin p, g i (z i) := by
        rw [separableSum_apply]
      _ = ∑ i : Fin p, ((((g i (z i)).toReal : ℝ)) : EReal) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact alternating_minimization_block_value_eq_coe_toReal
          (f := f) (g := g) hmodel hz i
      _ = (((∑ i : Fin p, (g i (z i)).toReal) : ℝ) : EReal) := by
        simpa using
          (ereal_coe_finset_sum
            (s := Finset.univ)
            (a := fun i : Fin p ↦ (g i (z i)).toReal)).symm
  have hcont_toReal :
      ContinuousOn
        (fun z : (i : Fin p) → Ei i ↦ ((f z).toReal : EReal) + separableSum g z)
        (effective_domain F) := by
    intro z hz
    have hz_left := hf_cont z hz
    have hz_right := hg_cont z hz
    have hadd :
        ContinuousAt
          (fun p : EReal × EReal ↦ p.1 + p.2)
          (((((f z).toReal : ℝ) : EReal), separableSum g z)) := by
      -- Addition is continuous because the left summand is always a finite real coercion.
      exact EReal.continuousAt_add (.inl (by simp)) (.inl (by simp))
    exact hadd.comp₂_continuousWithinAt hz_left hz_right
  have hcont : ContinuousOn F (effective_domain F) := by
    -- On the effective domain, the smooth term is finite, so the `toReal`-coerced model agrees
    -- pointwise with the original composite objective.
    refine hcont_toReal.congr ?_
    intro z hz
    have hz_separable :
        z ∈ effective_domain (separableSum g) :=
      effective_domain_composite_model_objective_subset_separable
        (f := f) (g := g) hmodel hz
    have hz_finite : z ∈ effective_domain f := by
      exact interior_subset
        (hmodel.g_effective_domain_subset_interior_f_effective_domain hz_separable)
    have hz_f_eq : f z = ((((f z).toReal : ℝ)) : EReal) := by
      exact
        (EReal.coe_toReal
          (mem_effective_domain.mp hz_finite).ne
          (hmodel.f_ne_bot z)).symm
    calc
      F z = f z + separableSum g z := by
        rw [composite_model_objective_apply]
      _ = (((f z).toReal : ℝ) : EReal) + separableSum g z := by
        exact congrArg (fun t : EReal ↦ t + separableSum g z) hz_f_eq
  have hclosed : LowerSemicontinuous F := by
    -- Lower semicontinuity is inherited from the two summands and continuity of `EReal` addition
    -- at the non-pathological points supplied above.
    refine hmodel.f_closed.add' (separableSum_closed g hmodel.g_closed) ?_
    intro z
    exact EReal.continuousAt_add (.inr (hseparable_ne_bot z)) (.inl (hmodel.f_ne_bot z))
  exact ⟨hclosed, hcont⟩

/-- Helper for Theorem 14.4: the composite-step hypotheses determine one fixed Assumption 14.6
owner that can be reused throughout the endgame. -/
lemma alternating_minimization_composite_model_of_steps
    (hstep : ∀ k : ℕ, IsAlternatingMinimizationCompositeStep f g (x k) (x (k + 1))) :
    IsAlternatingMinimizationCompositeModel f g := by
  -- Freeze the model witness from the first step so later applications reuse one canonical term.
  exact (hstep 0).toIsAlternatingMinimizationCompositeModel

end Stationarity

section StationarityCluster

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace ℝ (Ei i)]
variable [FiniteDimensional ℝ ((i : Fin p) → Ei i)]

variable (f : ((i : Fin p) → Ei i) → EReal)
variable (g : (i : Fin p) → Ei i → EReal)
variable (x : ℕ → (i : Fin p) → Ei i)

local notation "F" => composite_model_objective f (separableSum g)

/-- Helper for Theorem 14.4: every cluster point of the composite alternating-minimization
trajectory is a coordinate-wise minimum of the composite objective. -/
lemma alternating_minimization_composite_cluster_point_is_coordinatewise_minimum
    (hunique :
      ∀ xBar ∈ effective_domain F, ∀ i : Fin p,
        Set.Subsingleton (alternating_minimization_argmin F xBar i))
    (hlevel :
      ∀ α : ℝ, Bornology.IsBounded {y | F y ≤ (α : EReal)})
    (hx0 : x 0 ∈ effective_domain F)
    (hstep : ∀ k : ℕ, IsAlternatingMinimizationCompositeStep f g (x k) (x (k + 1)))
    (xBar : (i : Fin p) → Ei i)
    (hxBar : MapClusterPt xBar Filter.atTop x) :
    is_coordinatewise_minimum F xBar := by
  -- Route correction: package the Theorem 14.3 call under the local finite-dimensional
  -- `ProperSpace` bridge instead of rebuilding the cluster-point argument here.
  let hmodel : IsAlternatingMinimizationCompositeModel f g :=
    alternating_minimization_composite_model_of_steps (f := f) (g := g) (x := x) hstep
  letI : ProperSpace ((i : Fin p) → Ei i) := FiniteDimensional.proper ℝ ((i : Fin p) → Ei i)
  have htraj :
      is_alternating_minimization_trajectory F x :=
    is_alternating_minimization_trajectory_of_composite_steps
      (f := f) (g := g) (x := x) hx0 hstep
  have hregular :
      LowerSemicontinuous F ∧ ContinuousOn F (effective_domain F) :=
    alternating_minimization_composite_objective_regular (f := f) (g := g) hmodel
  -- Apply Theorem 14.3 to the canonical trajectory for the full composite objective.
  exact alternating_minimization_cluster_points_coordinatewise_minima
    F x
    (alternating_minimization_composite_objective_ne_bot
      (f := f) (g := g) hmodel)
    hregular.1 hregular.2 hunique hlevel htraj xBar hxBar

end StationarityCluster

section StationarityFinal

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, NormedAddCommGroup (Ei i)]
variable [∀ i, InnerProductSpace ℝ (Ei i)]
variable [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
variable [hfd : FiniteDimensional ℝ ((i : Fin p) → Ei i)]

variable (f : ((i : Fin p) → Ei i) → EReal)
variable (g : (i : Fin p) → Ei i → EReal)
variable (x : ℕ → (i : Fin p) → Ei i)

local notation "F" => composite_model_objective f (separableSum g)

/-- The Chapter 3 stationary-point owner uses the product-space module induced by the chosen
inner product on `Π i, E_i`. -/
local instance : Module ℝ ((i : Fin p) → Ei i) :=
  (inferInstance : InnerProductSpace ℝ ((i : Fin p) → Ei i)).toNormedSpace.toModule

/-- The finite-dimensional product hypothesis remains available after switching to the
inner-product-induced product module. -/
local instance : FiniteDimensional ℝ ((i : Fin p) → Ei i) := by
  simpa using hfd

/-- Helper for Theorem 14.4: in the current product Hilbert setting, coordinate-wise minimality
feeds directly into the Chapter 3 stationary-point owner via Lemma 14.2. -/
lemma alternating_minimization_coordinatewise_minimum_is_stationary
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {xStar : (i : Fin p) → Ei i}
    (hcoord : is_coordinatewise_minimum F xStar) :
    is_stationary_point f (separableSum g) xStar := by
  -- Freeze the current section instances and invoke the established coordinatewise-to-stationary
  -- bridge without introducing a new transport route.
  exact is_stationary_point_of_coordinatewise_minimum hmodel hcoord

-- Proof sketch: convert the Algorithm 14.3 step data to the canonical owner trajectory for `F`,
-- apply Theorem 14.3 (2) to get coordinate-wise minimality of any cluster point, and then use
-- Lemma 14.2 to translate that coordinate-wise minimality into the Chapter 3 stationarity
-- condition for `f + separableSum g`.
/-- Theorem 14.4 (2): under Assumption 14.6, if every one-block subproblem of the composite
objective `F(x) = f(x) + ∑ i, g_i(x_i)` has a unique minimizer on `dom(F)`, every real level set
of `F` is bounded, and `x^k` is generated by Algorithm 14.3, then every sequential limit point of
`x^k` is a stationary point of the composite problem. The properness input required by Theorem
14.3 is derived here from finite dimensionality of the product space. -/
theorem alternating_minimization_composite_cluster_point_is_stationary
    (hunique :
      ∀ xBar ∈ effective_domain F, ∀ i : Fin p,
        Set.Subsingleton (alternating_minimization_argmin F xBar i))
    (hlevel :
      ∀ α : ℝ, Bornology.IsBounded {y | F y ≤ (α : EReal)})
    (hx0 : x 0 ∈ effective_domain F)
    (hstep : ∀ k : ℕ, IsAlternatingMinimizationCompositeStep f g (x k) (x (k + 1)))
    (xBar : (i : Fin p) → Ei i)
    (hxBar : MapClusterPt xBar Filter.atTop x) :
    is_stationary_point f (separableSum g) xBar := by
  -- Route correction: finish with the source-faithful `Theorem 14.3 -> Lemma 14.2` handoff.
  have hmodel : IsAlternatingMinimizationCompositeModel f g :=
    alternating_minimization_composite_model_of_steps (f := f) (g := g) (x := x) hstep
  letI : ProperSpace ((i : Fin p) → Ei i) := FiniteDimensional.proper ℝ ((i : Fin p) → Ei i)
  have htraj :
      is_alternating_minimization_trajectory F x :=
    is_alternating_minimization_trajectory_of_composite_steps
      (f := f) (g := g) (x := x) hx0 hstep
  have hregular :
      LowerSemicontinuous F ∧ ContinuousOn F (effective_domain F) :=
    alternating_minimization_composite_objective_regular (f := f) (g := g) hmodel
  letI : ∀ i, NormedSpace ℝ (Ei i) := fun i ↦
    (inferInstance : InnerProductSpace ℝ (Ei i)).toNormedSpace
  have hcoord :
      is_coordinatewise_minimum F xBar :=
    alternating_minimization_cluster_points_coordinatewise_minima
      F x
      (alternating_minimization_composite_objective_ne_bot
        (f := f) (g := g) hmodel)
      hregular.1 hregular.2 hunique hlevel htraj xBar hxBar
  -- The cluster-point coordinatewise minimum is stationary for the composite problem.
  exact alternating_minimization_coordinatewise_minimum_is_stationary
    (f := f) (g := g) hmodel hcoord

end StationarityFinal

end
