import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap08.Algorithm_8_3
import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap08.Assumption_8_7
import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap08.Assumption_8_12
import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap08.Definition_8_8
import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap08.Lemma_8_24
import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap05.Proposition_5_13
import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap05.Theorem_5_26
import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap09.Definition_9_2
import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap09.Definition_9_3
import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap09.Text_9_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)
open WithLp (toLp)

noncomputable section

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Δ" => (toLp 2 '' (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ)) : Set E)
local notation "ω" => ((fun z : E ↦ ‖z‖ ^ (2 : ℕ) / 2) : E → ℝ)
local notation "ωₑ" => Function.toEReal ω

/- Text 9.8 is `source-facing`: the textbook specializes mirror descent on the simplex to the
Euclidean distance-generating function `ω(x) = ‖x‖₂² / 2`, initialized at the uniform point
`(1 / n) e`. The `core/canonical` owner for this rate statement is therefore the Chapter 9
trajectory predicate `is_mirror_descent_trajectory` together with the fixed-horizon rate theorem
`mirror_descent_best_value_gap_le_one_div_sqrt_of_constant_stepsizes`; the Euclidean
projected-subgradient formulation is only a `bridge/view`, supplied by Text 9.5. In the current
project the ambient Euclidean owner is `EuclideanSpace ℝ (Fin n)`, the simplex is the transported
set `toLp 2 '' stdSimplex ℝ (Fin n)`, and the uniform initial point is the transport of the
canonical simplex barycenter. -/

-- The coordinate-side owner is `stdSimplex.barycenter`; `uniform_simplex_point` is only its
-- Euclidean transported view in the image simplex `Δ`.
/-- The canonical uniform initial point `x⁰ = (1 / n) e` in the Euclidean simplex
`toLp 2 '' stdSimplex ℝ (Fin n)`, obtained by transporting `stdSimplex.barycenter`, for
`n > 0`. -/
abbrev uniform_simplex_point (hn : 0 < n) : Δ :=
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  ⟨toLp 2 (stdSimplex.barycenter : stdSimplex ℝ (Fin n)),
    ⟨stdSimplex.barycenter, stdSimplex.barycenter.2, rfl⟩⟩

-- Proof sketch: `stdSimplex.barycenter` has every coordinate equal to `(Fintype.card (Fin n))⁻¹`,
-- i.e. `1 / n`, and `uniform_simplex_point` is exactly its `toLp 2` transport into the ambient
-- Euclidean space.
/-- Coercing the uniform simplex point to the ambient Euclidean space gives the transported
constant vector with coordinates `1 / n`. -/
@[simp] theorem coe_uniform_simplex_point (hn : 0 < n) :
    (uniform_simplex_point hn : E) = toLp 2 (fun _ : Fin n ↦ 1 / (n : ℝ)) := by
  -- Unfold the transported barycenter and identify each simplex coordinate with `1 / n`.
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  ext i
  have hbary :
      ((stdSimplex.barycenter : stdSimplex ℝ (Fin n)) : Fin n → ℝ) i = (↑n : ℝ)⁻¹ := by
    simpa only [Fintype.card_fin] using
      (stdSimplex.barycenter_apply (𝕜 := ℝ) (X := Fin n) i)
  simpa [uniform_simplex_point] using hbary

/-- Helper for Text 9.8: for `ω(x) = ‖x‖² / 2`, the Bregman distance is
`‖x - y‖² / 2`. -/
lemma bregmanDistance_halfSquaredNorm_eq_half_norm_sub_sq (x y : E) :
    B[ωₑ] x y = ‖x - y‖ ^ (2 : ℕ) / 2 := by
  -- Expand the quadratic Bregman distance and collapse the cross-term with `norm_sub_sq_real`.
  rw [bregmanDistance_apply_real, gradient_half_squared_norm_div_two, inner_sub_right,
    real_inner_self_eq_norm_sq, real_inner_comm]
  nlinarith [norm_sub_sq_real x y]

/-- Helper for Text 9.8: two transported simplex points are at squared Euclidean distance at most
`2`. -/
lemma norm_sq_sub_le_two_of_mem_simplex {x y : E} (hx : x ∈ Δ) (hy : y ∈ Δ) :
    ‖x - y‖ ^ (2 : ℕ) ≤ 2 := by
  rcases hx with ⟨x', hx', rfl⟩
  rcases hy with ⟨y', hy', rfl⟩
  -- Rewrite the Euclidean norm in coordinates and compare each coordinate square by `a² ≤ a`.
  calc
    ‖toLp 2 x' - toLp 2 y'‖ ^ (2 : ℕ) = ∑ i, (x' i - y' i) ^ (2 : ℕ) := by
      simpa using (EuclideanSpace.real_norm_sq_eq (toLp 2 (x' - y')))
    _ ≤ ∑ i, (x' i + y' i) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hx0 : 0 ≤ x' i := hx'.1 i
      have hy0 : 0 ≤ y' i := hy'.1 i
      have hx1 : x' i ≤ 1 := (mem_Icc_of_mem_stdSimplex hx' i).2
      have hy1 : y' i ≤ 1 := (mem_Icc_of_mem_stdSimplex hy' i).2
      nlinarith
    _ = 2 := by
      rw [Finset.sum_add_distrib, hx'.2, hy'.2]
      norm_num

/-- Helper for Text 9.8: the quadratic mirror map is subdifferentiable everywhere. -/
lemma mem_subdifferential_domain_halfSquaredNorm (z : E) :
    z ∈ subdifferential_domain ωₑ := by
  have hconvex_real : ConvexOn ℝ Set.univ ω := by
    exact
      ((half_squared_norm_is_one_strongly_convex_on (C := Set.univ) convex_univ).strictConvexOn
        (by norm_num)).convexOn
  have hsub :
      fderiv ℝ ω z ∈ subdifferentialAt ω z := by
    -- The quadratic is convex and differentiable, so its Fréchet derivative is a subgradient.
    exact
      fderiv_mem_subdifferentialAt_of_convexOn_univ hconvex_real
        (hasGradientAt_half_squared_norm_div_two z).differentiableAt
  rw [mem_subdifferential_domain]
  exact ⟨fderiv ℝ ω z, by simpa [subdifferentialAt, Function.toEReal] using hsub⟩

/-- The Euclidean mirror map `ω(x) = ‖x‖² / 2` is a Bregman potential with modulus `1` on the
transported simplex `Δ`. -/
instance half_squared_norm_isBregmanPotentialOn_simplex :
    IsBregmanPotentialOn ωₑ Δ 1 := by
  -- Package the Euclidean quadratic with the canonical Chapter 9 Bregman-potential fields.
  refine
    { toIsProperExtendedRealFunction := Function.toEReal_isProper ω
      closed := ?_
      convex := ?_
      differentiableOn_subdifferential_domain := ?_
      subset_effective_domain := ?_
      sigma_pos := by norm_num
      strongConvexOn := ?_ }
  · -- The quadratic mirror map is continuous, hence lower semicontinuous after coercion to `EReal`.
    exact Function.toEReal_lowerSemicontinuous_of_continuous (by continuity : Continuous ω)
  · have hconvex_real : ConvexOn ℝ Set.univ ω := by
      exact
        ((half_squared_norm_is_one_strongly_convex_on (C := Set.univ) convex_univ).strictConvexOn
          (by norm_num)).convexOn
    exact Function.toEReal_isConvexFunction hconvex_real
  · -- The quadratic is differentiable everywhere, so in particular on `dom(∂ ω)`.
    intro x hx
    exact (hasGradientAt_half_squared_norm_div_two x).differentiableAt.differentiableWithinAt
  · -- A real-valued mirror map is finite everywhere.
    intro x hx
    simp [effective_domain, Function.toEReal]
  · have hΔ_convex : Convex ℝ (Δ : Set E) := by
      change Convex ℝ
        (((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap) ''
          (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ)))
      exact
        (convex_stdSimplex ℝ (Fin n)).linear_image
          ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap)
    exact half_squared_norm_is_one_strongly_convex_on (C := Δ) hΔ_convex

-- Proof sketch: for the Euclidean mirror map, the Bregman distance is
-- `(1 / 2) ‖x - x₀‖²`. Two points of the simplex lie in the unit `ℓ₂` ball and differ by at most
-- `√2`, so the resulting Bregman diameter from the uniform initialization is at most `1`.
/-- On the simplex, the Euclidean Bregman distance to the uniform initialization `x⁰ = (1 / n)e`
is bounded by `1`. This is the simplex specialization of the textbook constant `Θ₀ = 1`. -/
theorem half_squared_norm_bregman_le_one_of_mem_simplex
    (hn : 0 < n) {x : E} (hx : x ∈ Δ) :
    B[ωₑ] x (uniform_simplex_point hn) ≤ 1 := by
  -- Normalize the Bregman term to a squared Euclidean distance and apply the simplex diameter bound.
  calc
    B[ωₑ] x (uniform_simplex_point hn)
        = ‖x - uniform_simplex_point hn‖ ^ (2 : ℕ) / 2 := by
            exact bregmanDistance_halfSquaredNorm_eq_half_norm_sub_sq x (uniform_simplex_point hn)
    _ ≤ 2 / 2 := by
          gcongr
          exact norm_sq_sub_le_two_of_mem_simplex hx (uniform_simplex_point hn).property
    _ = 1 := by norm_num

section Rate

variable {f : E → EReal} {XStar : Set E} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem f Δ XStar fOpt)
variable (h_bound : SubgradientNormBoundOn f Δ)

-- Proof sketch: apply Theorem 9.16 to the Euclidean mirror map `ω(x) = ‖x‖² / 2` on the simplex
-- `Δ`, use `half_squared_norm_isBregmanPotentialOn_simplex` for the Bregman-potential owner, and
-- bound the initial Bregman term by `1` via
-- `half_squared_norm_bregman_le_one_of_mem_simplex` at the optimal point `xStar ∈ XStar ⊆ Δ`.
-- With `σ = 1`, `Θ₀ = 1`, and the constant stepsize
-- `t_k = √2 / (L_{f,2} √(N + 1))`, Theorem 9.16 reduces exactly to the displayed estimate.
/-- Text 9.8: for mirror descent on the Euclidean simplex with mirror map
`ω(x) = ‖x‖₂² / 2`, uniform initialization `x⁰ = (1 / n)e`, and constant stepsizes
`t_k = √2 / (L_{f,2} √(N + 1))` on the first `N + 1` iterations, the running-best objective gap
is bounded by `√2 L_{f,2} / √(N + 1)`, with `L_{f,2}` represented here by `h_bound.L_f`. -/
theorem euclidean_simplex_mirror_descent_best_value_gap_le
    (hn : 0 < n) {x g : ℕ → E} {t : ℕ → ℝ}
    (h_problem : IsConstrainedConvexProblem f Δ XStar fOpt)
    (h_traj : is_mirror_descent_trajectory (fun y ↦ (f y).toReal) ω Δ x g t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    (hx0 : x 0 = (uniform_simplex_point hn : E))
    {N : ℕ}
    (h_stepsize :
      ∀ k : Fin (N + 1),
        t k = Real.sqrt 2 / (h_bound.L_f * Real.sqrt (N + 1 : ℝ))) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt ≤
      Real.sqrt 2 * h_bound.L_f / Real.sqrt (N + 1 : ℝ) := by
  let x0 : Δ := uniform_simplex_point hn
  let gSeq : ℕ → Δ → E := fun k _ ↦ g k
  let xSeq : ℕ → Δ :=
    projected_subgradient_method Δ h_problem.feasible_nonempty h_problem.feasible_closed
      h_problem.feasible_convex gSeq t x0
  let xBar : ℕ → E :=
    projected_subgradient_method_iterate Δ h_problem.feasible_nonempty h_problem.feasible_closed
      h_problem.feasible_convex gSeq t x0
  let η : ℝ := Real.sqrt 2 / (h_bound.L_f * Real.sqrt (N + 1 : ℝ))
  have hη_pos : 0 < η := by
    -- The prescribed constant stepsize is positive because both `L_f` and `√(N + 1)` are.
    dsimp [η]
    exact
      div_pos (Real.sqrt_pos.2 (by norm_num))
        (mul_pos h_bound.L_f_pos (Real.sqrt_pos.2 (by positivity)))
  have hxStar_data : xStar ∈ Δ ∧ IsMinOn f Δ xStar := by
    -- Optimal points are exactly the feasible minimizers recorded by `IsConstrainedConvexProblem`.
    simpa [h_problem.optimal_set_eq] using hxStar
  have hxEq : ∀ k, x k = xBar k := by
    intro k
    induction k with
    | zero =>
        -- The mirror-descent and projected-subgradient sequences share the same initialization.
        calc
          x 0 = (uniform_simplex_point hn : E) := hx0
          _ = xBar 0 := by
              simpa [x0, xBar] using
                (projected_subgradient_method_iterate_zero
                  Δ h_problem.feasible_nonempty h_problem.feasible_closed
                  h_problem.feasible_convex gSeq t x0).symm
    | succ k ih =>
        have hxkp1_mem : x (k + 1) ∈ Δ := h_traj.mem_feasible_set (k + 1)
        have hproj :
            x (k + 1) =
              Pp[Δ, h_problem.feasible_nonempty, h_problem.feasible_closed,
                h_problem.feasible_convex] (x k - t k • g k) := by
          -- Text 9.5 rewrites the Euclidean mirror-descent minimizer as the projection update.
          exact
            (mirror_descent_half_squared_norm_step_iff_eq_projection
              Δ h_problem.feasible_nonempty h_problem.feasible_closed
              h_problem.feasible_convex (x k) (g k) (x (k + 1)) (t k) hxkp1_mem).mp
              (h_traj.isMinOn k)
        have hsucc :
            xBar (k + 1) =
              Pp[Δ, h_problem.feasible_nonempty, h_problem.feasible_closed,
                h_problem.feasible_convex] (xBar k - t k • g k) := by
          -- The Chapter 8 recursion has the same projection form for the constant selector `gSeq`.
          simpa [gSeq, x0, xSeq, xBar, projectionPoint] using
            projected_subgradient_method_iterate_succ
              Δ h_problem.feasible_nonempty h_problem.feasible_closed
              h_problem.feasible_convex gSeq t x0 k
        calc
          x (k + 1) =
              Pp[Δ, h_problem.feasible_nonempty, h_problem.feasible_closed,
                h_problem.feasible_convex] (x k - t k • g k) := hproj
          _ =
              Pp[Δ, h_problem.feasible_nonempty, h_problem.feasible_closed,
                h_problem.feasible_convex] (xBar k - t k • g k) := by
                rw [ih]
          _ = xBar (k + 1) := hsucc.symm
  have hxEqFun : x = xBar := by
    -- Package the pointwise identification for rewriting sequence-level quantities.
    funext k
    exact hxEq k
  have h_subgrad :
      ∀ k, toDualMap ℝ E (gSeq k (xSeq k)) ∈ strongDualSubdifferential f (xBar k) := by
    intro k
    -- The projected selector `gSeq` inherits strong-dual subgradient membership from the mirror
    -- trajectory subgradient clause after rewriting the iterate by `hxEq`.
    simpa [gSeq, xSeq, xBar, hxEq k, mem_euclideanSubdifferentialAt_iff, subdifferentialAt,
      mem_strongDualSubdifferential] using h_traj.subgradient_mem k
  have h_weighted :
      Finset.sum (Finset.range (N + 1)) (fun k ↦ t k * ((f (xBar k)).toReal - fOpt)) ≤
        (1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            Finset.sum (Finset.range (N + 1)) (fun k ↦ (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ)) := by
    -- Summing the Chapter 8 one-step projected-subgradient inequality gives the weighted gap bound.
    simpa [gSeq, x0, xSeq, xBar] using
      projected_subgradient_method_weighted_objective_gap_sum_le
        (f := f) (C := Δ) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
        (g := gSeq) (t := t) (x0 := x0)
        h_subgrad (fun k ↦ (h_traj.stepsize_pos k).le) hxStar N
  have h_initial : (1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ) ≤ 1 := by
    -- The simplex Euclidean diameter estimate supplies the textbook initial constant `Θ₀ = 1`.
    simpa [x0, norm_sub_rev, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (half_squared_norm_bregman_le_one_of_mem_simplex hn hxStar_data.1)
  have h_gnorm : ∀ k, ‖g k‖ ≤ h_bound.L_f := by
    intro k
    have hgk :
        toDualMap ℝ E (g k) ∈ strongDualSubdifferential f (x k) := by
      simpa [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential]
        using h_traj.subgradient_mem k
    simpa using h_bound.norm_le (h_traj.mem_feasible_set k) hgk
  have h_quad_term : (1 / 2 : ℝ) *
      Finset.sum (Finset.range (N + 1)) (fun k ↦ (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ)) ≤ 1 := by
    have hterm :
        ∀ k ∈ Finset.range (N + 1),
          (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) ≤ 2 / (N + 1 : ℝ) := by
      intro k hk
      have hk_step : t k = η := h_stepsize ⟨k, Finset.mem_range.mp hk⟩
      have hη_nonneg : 0 ≤ η := hη_pos.le
      have hsqrtN_pos : 0 < Real.sqrt (N + 1 : ℝ) := by
        positivity
      have hprod_le : t k * ‖g k‖ ≤ Real.sqrt 2 / Real.sqrt (N + 1 : ℝ) := by
        -- The constant stepsize and `‖g_k‖ ≤ L_f` collapse the mixed product to the textbook cap.
        rw [hk_step]
        have hmul := mul_le_mul_of_nonneg_left (h_gnorm k) hη_nonneg
        simpa [η, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, h_bound.L_f_pos.ne',
          hsqrtN_pos.ne'] using hmul
      have hlhs_nonneg : 0 ≤ t k * ‖g k‖ := by
        exact mul_nonneg (le_of_lt (h_traj.stepsize_pos k)) (norm_nonneg _)
      have hrhs_nonneg : 0 ≤ Real.sqrt 2 / Real.sqrt (N + 1 : ℝ) := by
        exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hsq :
          (t k * ‖g k‖) ^ (2 : ℕ) ≤ (Real.sqrt 2 / Real.sqrt (N + 1 : ℝ)) ^ (2 : ℕ) := by
        exact
          (sq_le_sq).2 <|
            by simpa [abs_of_nonneg hlhs_nonneg, abs_of_nonneg hrhs_nonneg] using hprod_le
      have hleft :
          (t k * ‖g k‖) ^ (2 : ℕ) = (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) := by
        ring
      have hright :
          (Real.sqrt 2 / Real.sqrt (N + 1 : ℝ)) ^ (2 : ℕ) = 2 / (N + 1 : ℝ) := by
        field_simp [pow_two, hsqrtN_pos.ne']
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ N + 1 by positivity)]
      calc
        (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) = (t k * ‖g k‖) ^ (2 : ℕ) := by
          rw [hleft]
        _ ≤ (Real.sqrt 2 / Real.sqrt (N + 1 : ℝ)) ^ (2 : ℕ) := hsq
        _ = 2 / (N + 1 : ℝ) := hright
    have hsum :
        Finset.sum (Finset.range (N + 1)) (fun k ↦ (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ)) ≤
          Finset.sum (Finset.range (N + 1)) (fun _ : ℕ ↦ 2 / (N + 1 : ℝ)) := by
      exact Finset.sum_le_sum hterm
    calc
      (1 / 2 : ℝ) *
          Finset.sum (Finset.range (N + 1)) (fun k ↦ (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ))
          ≤
        (1 / 2 : ℝ) * Finset.sum (Finset.range (N + 1)) (fun _ : ℕ ↦ 2 / (N + 1 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hsum (by norm_num : 0 ≤ (1 / 2 : ℝ))
      _ = 1 := by
          have hN_ne : (N + 1 : ℝ) ≠ 0 := by positivity
          calc
            (1 / 2 : ℝ) * Finset.sum (Finset.range (N + 1)) (fun _ : ℕ ↦ 2 / (N + 1 : ℝ))
                = (1 / 2 : ℝ) * ((N + 1 : ℝ) * (2 / (N + 1 : ℝ))) := by
                    simp [Finset.card_range]
            _ = 1 := by
                  field_simp [hN_ne]
  let bestGap : ℝ := best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt
  have hbest_weighted :
      (Finset.sum (Finset.range (N + 1)) (fun k ↦ t k)) * bestGap ≤
        Finset.sum (Finset.range (N + 1)) (fun k ↦ t k * ((f (x k)).toReal - fOpt)) := by
    -- The running-best gap is bounded by each prefix objective gap, and the steps are nonnegative.
    calc
      (Finset.sum (Finset.range (N + 1)) (fun k ↦ t k)) * bestGap =
          Finset.sum (Finset.range (N + 1)) (fun k ↦ t k * bestGap) := by
            rw [Finset.sum_mul]
      _ ≤ Finset.sum (Finset.range (N + 1)) (fun k ↦ t k * ((f (x k)).toReal - fOpt)) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            have hbest_le :
                best_achieved_function_value (fun y ↦ (f y).toReal) x N ≤ (f (x k)).toReal :=
              best_achieved_function_value_le_objective_value
                (fun y ↦ (f y).toReal) x N k hk
            exact mul_le_mul_of_nonneg_left
              (sub_le_sub_right hbest_le fOpt)
              (le_of_lt (h_traj.stepsize_pos k))
  have h_sum_steps :
      Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) = (N + 1 : ℝ) * η := by
    -- The first `N + 1` steps are constant by hypothesis.
    calc
      Finset.sum (Finset.range (N + 1)) (fun k ↦ t k)
          = Finset.sum (Finset.range (N + 1)) (fun _ : ℕ ↦ η) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              exact h_stepsize ⟨k, Finset.mem_range.mp hk⟩
      _ = (N + 1 : ℝ) * η := by
            simp [Finset.card_range]
  have h_rate_aux : bestGap ≤ 2 / ((N + 1 : ℝ) * η) := by
    have hsum_pos : 0 < (N + 1 : ℝ) * η := by
      exact mul_pos (by positivity) hη_pos
    have hweighted_x :
        Finset.sum (Finset.range (N + 1)) (fun k ↦ t k * ((f (x k)).toReal - fOpt)) ≤ 2 := by
      -- Rewrite the projected-subgradient bound back to `x` and use the unit initial/quadratic
      -- controls.
      have hweighted_xBar :
          Finset.sum (Finset.range (N + 1)) (fun k ↦ t k * ((f (x k)).toReal - fOpt)) ≤
            (1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ) +
              (1 / 2 : ℝ) *
                Finset.sum (Finset.range (N + 1)) (fun k ↦ (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ)) := by
        simpa [hxEqFun] using h_weighted
      nlinarith [hweighted_xBar, h_initial, h_quad_term]
    have hmul :
        ((N + 1 : ℝ) * η) * bestGap ≤ 2 := by
      rw [← h_sum_steps]
      exact hbest_weighted.trans hweighted_x
    rw [le_div_iff₀ hsum_pos]
    simpa [bestGap, mul_comm, mul_left_comm, mul_assoc] using hmul
  have h_eta_closed :
      2 / ((N + 1 : ℝ) * η) = Real.sqrt 2 * h_bound.L_f / Real.sqrt (N + 1 : ℝ) := by
    -- Simplify the constant-step denominator to the displayed Euclidean rate constant.
    have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have hsqrtN_pos : 0 < Real.sqrt (N + 1 : ℝ) := by
      positivity
    have hsqrtN_ne : Real.sqrt (N + 1 : ℝ) ≠ 0 := hsqrtN_pos.ne'
    have hsqrt2_div : 2 / Real.sqrt 2 = Real.sqrt 2 := by
      field_simp [hsqrt2_ne]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hsqrtN_ratio : Real.sqrt (N + 1 : ℝ) / (N + 1 : ℝ) = 1 / Real.sqrt (N + 1 : ℝ) := by
      field_simp [hsqrtN_ne]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ N + 1 by positivity)]
    calc
      2 / ((N + 1 : ℝ) * η)
          = 2 / ((N + 1 : ℝ) * (Real.sqrt 2 / (h_bound.L_f * Real.sqrt (N + 1 : ℝ)))) := by
              rfl
      _ = 2 * (h_bound.L_f * Real.sqrt (N + 1 : ℝ)) / ((N + 1 : ℝ) * Real.sqrt 2) := by
            field_simp [η, h_bound.L_f_pos.ne', hsqrtN_ne]
      _ = (2 / Real.sqrt 2) * (h_bound.L_f * (Real.sqrt (N + 1 : ℝ) / (N + 1 : ℝ))) := by
            field_simp [hsqrt2_ne, show (N + 1 : ℝ) ≠ 0 by positivity]
      _ = Real.sqrt 2 * (h_bound.L_f * (1 / Real.sqrt (N + 1 : ℝ))) := by
            rw [hsqrt2_div, hsqrtN_ratio]
      _ = Real.sqrt 2 * h_bound.L_f / Real.sqrt (N + 1 : ℝ) := by
            ring
  rw [h_eta_closed] at h_rate_aux
  simpa [bestGap] using h_rate_aux

section Bridge

variable (hn : 0 < n)
variable (g : ℕ → Δ → E) (t : ℕ → ℝ)

local notation "x[" k "]" =>
  projected_subgradient_method Δ h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t (uniform_simplex_point hn) k
local notation "x̄" =>
  projected_subgradient_method_iterate Δ h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t (uniform_simplex_point hn)
local notation "x̄[" k "]" => x̄ k

-- Proof sketch: feasibility of each iterate is automatic because `projected_subgradient_method`
-- is `Δ`-valued, the strong-dual subgradient hypothesis rewrites to the Euclidean subgradient
-- clause in `is_mirror_descent_trajectory`, `h_stepsize_pos` supplies positivity, and Text 9.5
-- identifies the projected-subgradient minimization with the Euclidean mirror-descent one-step
-- minimization.
/-- The projected-subgradient iterates on the Euclidean simplex, started at the uniform point,
form the specialized mirror-descent trajectory for `ω(x) = ‖x‖₂² / 2`. This is the explicit
Text 9.5 bridge between the Chapter 8 recursive iterates and the Chapter 9 owner
`is_mirror_descent_trajectory`. -/
theorem projected_subgradient_method_is_mirror_descent_trajectory
    (hn : 0 < n)
    (h_problem : IsConstrainedConvexProblem f Δ XStar fOpt)
    (h_subgrad :
      ∀ k,
        toDualMap ℝ E
            (g k
              (projected_subgradient_method Δ h_problem.feasible_nonempty
                h_problem.feasible_closed h_problem.feasible_convex g t
                (uniform_simplex_point (n := n) hn) k)) ∈
          strongDualSubdifferential f
            (projected_subgradient_method_iterate Δ h_problem.feasible_nonempty
              h_problem.feasible_closed h_problem.feasible_convex g t
              (uniform_simplex_point (n := n) hn) k))
    (h_stepsize_pos : ∀ k, 0 < t k) :
    is_mirror_descent_trajectory
      (fun y ↦ (f y).toReal)
      ω
      Δ
      (projected_subgradient_method_iterate Δ h_problem.feasible_nonempty
        h_problem.feasible_closed h_problem.feasible_convex g t
        (uniform_simplex_point (n := n) hn))
      (fun k ↦
        g k
          (projected_subgradient_method Δ h_problem.feasible_nonempty h_problem.feasible_closed
            h_problem.feasible_convex g t (uniform_simplex_point (n := n) hn) k))
      t := by
  let x0 : Δ := uniform_simplex_point (n := n) hn
  let xSeq : ℕ → Δ :=
    projected_subgradient_method Δ h_problem.feasible_nonempty h_problem.feasible_closed
      h_problem.feasible_convex g t x0
  let xBar : ℕ → E :=
    projected_subgradient_method_iterate Δ h_problem.feasible_nonempty h_problem.feasible_closed
      h_problem.feasible_convex g t x0
  intro k
  change
    xBar k ∈ Δ ∩ subdifferential_domain ωₑ ∧
      g k (xSeq k) ∈ euclideanSubdifferentialAt (fun y ↦ (f y).toReal) (xBar k) ∧
      0 < t k ∧
      IsMinOn (mirror_descent_update_objective ω (xBar k) (g k (xSeq k)) (t k)) Δ
        (xBar (k + 1))
  have hxk_mem : xBar k ∈ Δ := by
    -- Every projected-subgradient iterate is simplex-valued by construction.
    simpa [xBar, projected_subgradient_method_iterate, xSeq] using (xSeq k).property
  have hxkp1_mem : xBar (k + 1) ∈ Δ := by
    -- The next iterate is again simplex-valued for the same subtype reason.
    simpa [xBar, projected_subgradient_method_iterate, xSeq] using (xSeq (k + 1)).property
  have hgk_mem :
      g k (xSeq k) ∈ euclideanSubdifferentialAt (fun y ↦ (f y).toReal) (xBar k) := by
    -- Rewrite the strong-dual subgradient hypothesis through the Euclidean bridge.
    simpa [xSeq, xBar, projected_subgradient_method_iterate, mem_euclideanSubdifferentialAt_iff,
      subdifferentialAt, mem_strongDualSubdifferential]
      using h_subgrad k
  have hstep_eq :
      xBar (k + 1) =
        Pp[Δ, h_problem.feasible_nonempty, h_problem.feasible_closed, h_problem.feasible_convex]
          (xBar k - t k • g k (xSeq k)) := by
    -- The Chapter 8 recursive update is exactly the projection formula used by Text 9.5.
    simpa [xBar, xSeq, projected_subgradient_method_iterate, projectionPoint] using
      projected_subgradient_method_iterate_succ Δ h_problem.feasible_nonempty
        h_problem.feasible_closed h_problem.feasible_convex g t x0 k
  refine ⟨⟨hxk_mem, mem_subdifferential_domain_halfSquaredNorm (xBar k)⟩, hgk_mem,
    h_stepsize_pos k, ?_⟩
  -- Text 9.5 turns the projection update into the Euclidean mirror-descent minimizer condition.
  exact
    (mirror_descent_half_squared_norm_step_iff_eq_projection
      Δ h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex
      (xBar k) (g k (xSeq k)) (xBar (k + 1)) (t k) hxkp1_mem).2 hstep_eq

end Bridge

end Rate

end
