import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_11
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_12
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_8

-- Declarations for this item will be appended below by the statement pipeline.

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
