import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Lemma_9_4
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Theorem_9_12
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Algorithm_10_67
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Algorithm_10_68
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Algorithm_10_69
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Definition_10_67
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Definition_10_69
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Remark_10_19
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Theorem_10_72.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g ω : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
variable {x : ℕ → E} {L : ℕ → PosReal} {α : ℝ} {xStar : E}

local notation "F" => composite_model_objective f g

/- Theorem 10.72 is `source-facing` in the non-Euclidean proximal-gradient analysis.

Domain sampling against the existing Chapter 9 and Chapter 10 API points to:
- `is_non_euclidean_proximal_gradient_trajectory` from Algorithm 10.68 as the owner of the
  iterate sequence `x^k`;
- `non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_rule` and
  `non_euclidean_proximal_gradient_sublinear_rate_stepsize_rule` from this item as the source
  stepsize owners for the constant/B5 regimes;
- `hproblem.upper_model_of_constantOrBacktrackingB5Rule` from Definition 10.69 as the accepted
  upper-model inequality at the realized step;
- `non_euclidean_proximal_gradient_step_iff_isMinOn_non_euclidean_proximal_gradient_model` from
  Algorithm 10.67 as the canonical bridge from the step predicate to the textbook model;
- Chapter 9's Bregman owner `B[ω]` and its lower quadratic bound from Lemma 9.4.

The source proof route is therefore:
1. establish clause (a) by comparing the accepted upper model at `x^(k+1)` with the same model
   evaluated at the comparator `x^k`;
2. retain clause (b) on the source-faithful Chapter 9 route through the non-Euclidean second prox
   theorem, the three-point identity, and a Bregman telescope. -/

-- Proof sketch: Definition 10.69 gives the accepted upper-model inequality at the realized next
-- iterate `x^(k+1)`. Lemma 9.4 upgrades the quadratic term `(L_k / 2) ‖x^(k+1) - x^k‖²` to the
-- Bregman term `L_k B_ω(x^(k+1), x^k)`, so `F(x^(k+1))` is bounded by the textbook local model at
-- `x^(k+1)`. The Algorithm 10.67 step predicate says that this local model is minimized at
-- `x^(k+1)`, and evaluating the same model at `x^k` collapses it to `F(x^k)`.
/-- Theorem 10.72 (1): clause (a). Under the displayed `g`-regularity, smoothness, domain, and
Bregman-potential hypotheses, if the non-Euclidean proximal-gradient trajectory uses either the
constant stepsize rule `L_k = L_f` or backtracking procedure B5, then the objective sequence
`F(x^k)` is nonincreasing. -/
theorem non_euclidean_proximal_gradient_objective_values_antitone
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : hproblem.ConstantOrBacktrackingB5StepsizeRule hω x L) :
    Antitone (fun k ↦ F (x k)) := by
  refine antitone_nat_of_succ_le ?_
  intro k
  have hfxk :
      is_differentiable_at f (x k) :=
    is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj k
  have hstep :
      non_euclidean_proximal_gradient_step f g ω (x k) (L k) (x (k + 1)) :=
    is_non_euclidean_proximal_gradient_trajectory_mem_step htraj k
  have hmodel_min :
      IsMinOn (non_euclidean_textbook_model f g ω (x k) (L k)) Set.univ (x (k + 1)) := by
    -- The realized successor minimizes the textbook Chapter 10 local model.
    exact
      (non_euclidean_proximal_gradient_step_iff_isMinOn_non_euclidean_proximal_gradient_model
        (f := f) (g := g) (ω := ω) (xk := x k) (xNext := x (k + 1)) (Lk := L k) hfxk).mp
        hstep
  have hupper :
      f (x (k + 1)) ≤
        f (x k) +
          ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
            ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) :=
    hproblem.upper_model_of_constantOrBacktrackingB5Rule hω htraj hrule k
  have hxk_domains :
      x k ∈ effective_domain g ∩ subdifferential_domain ω :=
    is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj k
  have hxk1_domains :
      x (k + 1) ∈ effective_domain g ∩ subdifferential_domain ω :=
    is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj (k + 1)
  have hquad_le_bregman :
      ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) ≤
        (L k : ℝ) * B[ω] (x (k + 1)) (x k) := by
    have hbregman :
        (1 / 2 : ℝ) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) ≤
          B[ω] (x (k + 1)) (x k) := by
      -- The Chapter 9 lower quadratic bound is the source route from (10.94).
      simpa using
        (bregmanDistance_lower_quadratic_bound
          (hω := hω) (x := x (k + 1)) (y := x k)
          hxk1_domains.1 hxk_domains.1 hxk_domains.2)
    have hLk_nonneg : 0 ≤ (L k : ℝ) := le_of_lt (PosReal.coe_pos (L k))
    have hmul := mul_le_mul_of_nonneg_left hbregman hLk_nonneg
    nlinarith
  have hquad_le_bregmanE :
      ((((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        ((((L k : ℝ) * B[ω] (x (k + 1)) (x k) : ℝ) : EReal)) := by
    exact_mod_cast hquad_le_bregman
  have hmodel_upper :
      F (x (k + 1)) ≤ non_euclidean_textbook_model f g ω (x k) (L k) (x (k + 1)) := by
    -- Replace the quadratic term from the accepted upper model by the stronger Bregman term.
    calc
      F (x (k + 1)) = f (x (k + 1)) + g (x (k + 1)) := by
        simp [F, composite_model_objective]
      _ ≤
          (f (x k) +
            ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
              ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal)) +
            g (x (k + 1)) := by
          exact add_le_add_right hupper (g (x (k + 1)))
      _ ≤
          (f (x k) +
            ((((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) : ℝ) : EReal)) +
              ((((L k : ℝ) * B[ω] (x (k + 1)) (x k) : ℝ) : EReal)))) +
            g (x (k + 1)) := by
          have hsplit :
              (((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
                  ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤
                ((((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) : ℝ) : EReal)) +
                  ((((L k : ℝ) * B[ω] (x (k + 1)) (x k) : ℝ) : EReal))) := by
            rw [EReal.coe_add]
            exact add_le_add_left hquad_le_bregmanE
              (((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) : ℝ) : EReal))
          exact add_le_add_right hsplit (g (x (k + 1)))
      _ = non_euclidean_textbook_model f g ω (x k) (L k) (x (k + 1)) := by
        simp [non_euclidean_textbook_model, F, composite_model_objective, add_assoc, add_left_comm,
          add_comm]
  have hmodel_self :
      non_euclidean_textbook_model f g ω (x k) (L k) (x k) = F (x k) := by
    -- Evaluating the local model at the base point removes both the linear and Bregman terms.
    have hbregman_self : B[ω] (x k) (x k) = 0 :=
      bregmanDistance_eq_zero_of_eq ω rfl
    simp [non_euclidean_textbook_model, F, composite_model_objective, hbregman_self]
  -- Minimize the textbook local model at `x^(k+1)` and compare it with the comparator `x^k`.
  exact le_trans hmodel_upper <| by
    simpa [hmodel_self] using hmodel_min (x k) (by simp)

/-- Helper for Theorem 10.72: the pointwise sum of two convex extended-real-valued functions is
again convex. -/
lemma is_convex_function_add
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (f₁ f₂ : V → EReal) (hf₁ : is_convex_function f₁) (hf₂ : is_convex_function f₂) :
    is_convex_function (f₁ + f₂) := by
  let F : Fin 2 → V → EReal := fun i ↦ if i = 0 then f₁ else f₂
  have hF : ∀ i : Fin 2, is_convex_function (F i) := by
    intro i
    fin_cases i
    · -- The first summand is `f₁`.
      simpa [F] using hf₁
    · -- The second summand is `f₂`.
      simpa [F] using hf₂
  -- Express the sum as the two-term nonnegative weighted sum from Theorem 2.6.
  simpa [F, Fin.sum_univ_two, Pi.add_apply] using
    (is_convex_function_finset_nonneg_weighted_sum (m := 2) hF fun _ ↦ 1)

/-- Helper for Theorem 10.72: the Chapter 9 penalty `ψ_n` used in the source proof of clause (b).
It is the scaled linearization of `f` at `x^n` plus the scaled nonsmooth term `(1 / L_n) g`. -/
abbrev non_euclidean_linearized_scaled_penalty
    (n : ℕ) : E → EReal :=
  fun u ↦
    (((mirror_c_problem_functional ω (x n)
        (fderiv ℝ (fun y ↦ (f y).toReal) (x n))
        (((1 / L n : PosReal) : ℝ)) u : ℝ) : EReal) +
      ((((1 / L n : PosReal) : EReal) • g) u))

/-- Helper for Theorem 10.72: adding the finite linearization term to the scaled penalty does not
change its effective domain, so `ψ_n` has the same effective domain as `g`. -/
lemma non_euclidean_linearized_scaled_penalty_effective_domain_eq
    (n : ℕ) :
    effective_domain (non_euclidean_linearized_scaled_penalty
      (f := f) (g := g) (ω := ω) (x := x) (L := L) n) =
      effective_domain g := by
  let ψpen : E → EReal := (((1 / L n : PosReal) : EReal) • g)
  have hscaled_proper :
      IsProperExtendedRealFunction ψpen :=
    (scaled_backtracking_penalty_proper_closed_convex (g := g) (Lk := L n)).1
  ext u
  constructor
  · intro hu
    have hu_ne_top :
        non_euclidean_linearized_scaled_penalty
          (f := f) (g := g) (ω := ω) (x := x) (L := L) n u ≠ ⊤ :=
      (mem_effective_domain.mp hu).ne
    have hpen_ne_bot : ψpen u ≠ ⊥ := hscaled_proper.ne_bot u
    have hpen_ne_top : ψpen u ≠ ⊤ := by
      intro htop
      have hsum_top :
          non_euclidean_linearized_scaled_penalty
              (f := f) (g := g) (ω := ω) (x := x) (L := L) n u =
            ⊤ := by
        simp [non_euclidean_linearized_scaled_penalty, ψpen, htop, hpen_ne_bot]
      exact hu_ne_top hsum_top
    have hu_scaled : u ∈ effective_domain ψpen := mem_effective_domain.mpr <| by
      exact lt_top_iff_ne_top.mpr hpen_ne_top
    rwa [scaled_backtracking_penalty_effective_domain_eq (g := g) (Lk := L n)] at hu_scaled
  · intro hu
    have hu_scaled : u ∈ effective_domain ψpen := by
      rwa [scaled_backtracking_penalty_effective_domain_eq (g := g) (Lk := L n)]
    -- A finite linear perturbation cannot destroy finiteness of the scaled penalty.
    exact mem_effective_domain.mpr <| by
      simpa [non_euclidean_linearized_scaled_penalty, ψpen] using
        EReal.add_lt_top (EReal.coe_ne_top _)
          (mem_effective_domain.mp hu_scaled).ne

/-- Helper for Theorem 10.72: the Chapter 9 penalty `ψ_n` is proper and convex, exactly as needed
to specialize Theorem 9.12 in the source proof of clause (b). -/
lemma non_euclidean_linearized_scaled_penalty_proper_convex
    (n : ℕ) :
    IsProperExtendedRealFunction (non_euclidean_linearized_scaled_penalty
      (f := f) (g := g) (ω := ω) (x := x) (L := L) n) ∧
      is_convex_function (non_euclidean_linearized_scaled_penalty
        (f := f) (g := g) (ω := ω) (x := x) (L := L) n) := by
  let ψlin : E → EReal := fun u ↦
    (((mirror_c_problem_functional ω (x n)
        (fderiv ℝ (fun y ↦ (f y).toReal) (x n))
        (((1 / L n : PosReal) : ℝ)) u : ℝ) : EReal)
  let ψpen : E → EReal := (((1 / L n : PosReal) : EReal) • g)
  have hscaled := scaled_backtracking_penalty_proper_closed_convex (g := g) (Lk := L n)
  have hlin_convex : is_convex_function ψlin := by
    -- A continuous linear functional is convex on the whole space, and its `EReal` lift preserves
    -- that convexity.
    refine Function.toEReal_isConvexFunction ?_
    simpa [ψlin] using
      (((mirror_c_problem_functional ω (x n)
          (fderiv ℝ (fun y ↦ (f y).toReal) (x n))
          (((1 / L n : PosReal) : ℝ))).toLinearMap).convexOn (s := Set.univ) convex_univ)
  have hproper :
      IsProperExtendedRealFunction (non_euclidean_linearized_scaled_penalty
        (f := f) (g := g) (ω := ω) (x := x) (L := L) n) := by
    refine ⟨?_, ?_⟩
    · intro u
      -- The scaled penalty never takes `⊥`, and adding a finite real term preserves that.
      simpa [non_euclidean_linearized_scaled_penalty, ψlin, ψpen] using
        EReal.add_ne_bot (EReal.coe_ne_bot _) (hscaled.1.ne_bot u)
    · rcases hscaled.1.effective_domain_nonempty with ⟨u, hu⟩
      -- Any finite point of the scaled penalty remains finite after adding the linear term.
      refine ⟨u, ?_⟩
      exact mem_effective_domain.mpr <| by
        simpa [non_euclidean_linearized_scaled_penalty, ψlin, ψpen] using
          EReal.add_lt_top (EReal.coe_ne_top _)
            (mem_effective_domain.mp hu).ne
  have hconvex :
      is_convex_function (non_euclidean_linearized_scaled_penalty
        (f := f) (g := g) (ω := ω) (x := x) (L := L) n) := by
    -- Convexity is preserved when we add the affine linearization to the convex scaled penalty.
    simpa [non_euclidean_linearized_scaled_penalty, ψlin, ψpen, Pi.add_apply] using
      is_convex_function_add ψlin ψpen hlin_convex hscaled.2.2
  exact ⟨hproper, hconvex⟩

/-- Helper for Theorem 10.72: the source linearized objective
`u ↦ (⟨∇f(x^n), u⟩ + g(u)) / L_n` appearing in `(10.u400)`, before the Bregman term is added
back. -/
abbrev non_euclidean_scaled_linearized_objective
    (n : ℕ) : E → EReal :=
  fun u ↦
    ((((L n : ℝ)⁻¹ * fderiv ℝ (fun y ↦ (f y).toReal) (x n) u : ℝ) : EReal) +
      (((L n : ℝ)⁻¹ : EReal) * g u))

/-- Helper for Theorem 10.72: adding the finite linearization term
`u ↦ ⟪∇f(x^n), u⟫ / L_n` does not change the effective domain of the scaled penalty, so the source
linearized objective has the same effective domain as `g`. -/
lemma non_euclidean_scaled_linearized_objective_effective_domain_eq
    (n : ℕ) :
    effective_domain (non_euclidean_scaled_linearized_objective
      (f := f) (g := g) (x := x) (L := L) n) =
      effective_domain g := by
  let ψpen : E → EReal := fun u ↦ (((L n : ℝ)⁻¹ : EReal) * g u)
  have hscaled_proper :
      IsProperExtendedRealFunction ψpen := by
    simpa [ψpen, Pi.smul_apply, smul_eq_mul] using
      (scaled_backtracking_penalty_proper_closed_convex (g := g) (Lk := L n)).1
  ext u
  constructor
  · intro hu
    have hu_ne_top :
        non_euclidean_scaled_linearized_objective
          (f := f) (g := g) (x := x) (L := L) n u ≠ ⊤ :=
      (mem_effective_domain.mp hu).ne
    have hpen_ne_bot : ψpen u ≠ ⊥ := hscaled_proper.ne_bot u
    have hpen_ne_top : ψpen u ≠ ⊤ := by
      intro htop
      have hsum_top :
          non_euclidean_scaled_linearized_objective
              (f := f) (g := g) (x := x) (L := L) n u =
            ⊤ := by
        simp [non_euclidean_scaled_linearized_objective, ψpen, htop]
      exact hu_ne_top hsum_top
    have hu_scaled : u ∈ effective_domain ψpen := mem_effective_domain.mpr <| by
      exact lt_top_iff_ne_top.mpr hpen_ne_top
    simpa [ψpen, Pi.smul_apply, smul_eq_mul] using
      (mem_effective_domain_scaled_function_iff g (1 / L n) inferInstance u).mp hu_scaled
  · intro hu
    have hu_scaled :
        u ∈ effective_domain ψpen := by
      exact (mem_effective_domain_scaled_function_iff g (1 / L n) inferInstance u).mpr hu
    -- A finite linear perturbation preserves finiteness of the scaled penalty.
    exact mem_effective_domain.mpr <| by
      simpa [non_euclidean_scaled_linearized_objective, ψpen] using
        EReal.add_lt_top (EReal.coe_ne_top _)
          (mem_effective_domain.mp hu_scaled).ne

/-- Helper for Theorem 10.72: the source linearized objective is proper and convex, so it can be
used as the `ψ_n` input of Theorem 9.12 on the exact textbook route. -/
lemma non_euclidean_scaled_linearized_objective_proper_convex
    (n : ℕ) :
    IsProperExtendedRealFunction (non_euclidean_scaled_linearized_objective
      (f := f) (g := g) (x := x) (L := L) n) ∧
      is_convex_function (non_euclidean_scaled_linearized_objective
        (f := f) (g := g) (x := x) (L := L) n) := by
  let ψlin : E → EReal := fun u ↦
    ((((L n : ℝ)⁻¹ * fderiv ℝ (fun y ↦ (f y).toReal) (x n) u : ℝ) : EReal))
  let ψpen : E → EReal := fun u ↦ (((L n : ℝ)⁻¹ : EReal) * g u)
  have hscaled :
      IsProperExtendedRealFunction ψpen ∧ LowerSemicontinuous ψpen ∧
        is_convex_function ψpen := by
    simpa [ψpen, Pi.smul_apply, smul_eq_mul] using
      scaled_backtracking_penalty_proper_closed_convex (g := g) (Lk := L n)
  have hlin_convex : is_convex_function ψlin := by
    -- A continuous linear functional stays convex after the `EReal` lift.
    refine Function.toEReal_isConvexFunction ?_
    simpa [ψlin] using
      (((((L n : ℝ)⁻¹) • fderiv ℝ (fun y ↦ (f y).toReal) (x n)).convexOn (s := Set.univ))
        convex_univ)
  have hproper :
      IsProperExtendedRealFunction (non_euclidean_scaled_linearized_objective
        (f := f) (g := g) (x := x) (L := L) n) := by
    refine ⟨?_, ?_⟩
    · intro u
      -- The scaled penalty never takes `⊥`, and the linear term is finite.
      simpa [non_euclidean_scaled_linearized_objective, ψlin, ψpen] using
        EReal.add_ne_bot (EReal.coe_ne_bot _) (hscaled.1.ne_bot u)
    · rcases hscaled.1.effective_domain_nonempty with ⟨u, hu⟩
      -- Any finite point of the scaled penalty remains finite after adding the linear term.
      refine ⟨u, ?_⟩
      exact mem_effective_domain.mpr <| by
        simpa [non_euclidean_scaled_linearized_objective, ψlin, ψpen] using
          EReal.add_lt_top (EReal.coe_ne_top _)
            (mem_effective_domain.mp hu).ne
  have hconvex :
      is_convex_function (non_euclidean_scaled_linearized_objective
        (f := f) (g := g) (x := x) (L := L) n) := by
    -- Convexity is preserved under addition of the affine linearization term.
    simpa [non_euclidean_scaled_linearized_objective, ψlin, ψpen, Pi.add_apply] using
      is_convex_function_add ψlin ψpen hlin_convex hscaled.2.2
  exact ⟨hproper, hconvex⟩

/-- Helper for Theorem 10.72: convexity of the smooth term gives the supporting-hyperplane
inequality for the finite-valued restriction `x ↦ (f x).toReal` at a differentiability point. -/
lemma non_euclidean_convex_support_toReal_at_basepoint
    {xBase y : E}
    (hxBase : xBase ∈ effective_domain f)
    (hxDiff : DifferentiableAt ℝ (fun z ↦ (f z).toReal) xBase)
    (hy : y ∈ effective_domain f) :
    (f y).toReal ≥ (f xBase).toReal +
      inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase) := by
  let line : ℝ → E := AffineMap.lineMap xBase y
  let φ : ℝ → ℝ := fun t ↦ (f (line t)).toReal
  have hconv :
      ConvexOn ℝ (effective_domain f) (fun z ↦ (f z).toReal) :=
    convexOn_toReal_of_is_convex_function hproblem.f_convex
      (fun z _ ↦ hproblem.f_ne_bot z)
  have hφ_convex :
      ConvexOn ℝ (line ⁻¹' effective_domain f) φ := by
    -- Restrict the finite-valued convex model to the segment from `xBase` to `y`.
    simpa [φ, line] using
      hconv.comp_affineMap (AffineMap.lineMap (k := ℝ) xBase y)
  have hφ_zero :
      (0 : ℝ) ∈ line ⁻¹' effective_domain f := by
    simpa [line] using hxBase
  have hφ_one :
      (1 : ℝ) ∈ line ⁻¹' effective_domain f := by
    simpa [line] using hy
  have hφ_deriv :
      HasDerivAt φ
        (inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase)) 0 := by
    -- Differentiate the segment restriction and identify the derivative with the gradient pairing.
    have hcomp :
        HasDerivAt φ (fderiv ℝ (fun z ↦ (f z).toReal) xBase (y - xBase)) 0 := by
      have hbase :
          HasFDerivAt (fun z ↦ (f z).toReal)
            (fderiv ℝ (fun z ↦ (f z).toReal) xBase) (line 0) := by
        simpa [line] using hxDiff.hasFDerivAt
      have hline : HasDerivAt line (y - xBase) 0 := by
        simpa [line] using
          (AffineMap.hasDerivAt_lineMap (a := xBase) (b := y) (x := (0 : ℝ)))
      simpa [φ, line] using
        HasFDerivAt.comp_hasDerivAt (x := 0) hbase hline
    have hgrad :
        fderiv ℝ (fun z ↦ (f z).toReal) xBase (y - xBase) =
          inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase) := by
      simpa using HasGradientAt.fderiv_apply (y := y - xBase) hxDiff.hasGradientAt
    simpa [hgrad] using hcomp
  have hsecant :
      inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase) ≤ slope φ 0 1 := by
    -- Convexity bounds the derivative at the left endpoint by the secant slope.
    exact hφ_convex.le_slope_of_hasDerivAt hφ_zero hφ_one zero_lt_one hφ_deriv
  have hsecant' :
      inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase) ≤
        (f y).toReal - (f xBase).toReal := by
    simpa [φ, line, slope] using hsecant
  linarith

/-- Helper for Theorem 10.72: the accepted upper-model inequality together with the minimizing
property of the realized step bounds the successor objective by the textbook model at any
comparator `u`. This is the source `(10.94)` and `(10.u399)` package. -/
lemma non_euclidean_successor_le_textbook_model
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : hproblem.ConstantOrBacktrackingB5StepsizeRule hω x L)
    (n : ℕ) (u : E) :
    F (x (n + 1)) ≤ non_euclidean_textbook_model f g ω (x n) (L n) u := by
  have hfxn :
      is_differentiable_at f (x n) :=
    is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj n
  have hstep :
      non_euclidean_proximal_gradient_step f g ω (x n) (L n) (x (n + 1)) :=
    is_non_euclidean_proximal_gradient_trajectory_mem_step htraj n
  have hmodel_min :
      IsMinOn (non_euclidean_textbook_model f g ω (x n) (L n)) Set.univ (x (n + 1)) := by
    -- The realized successor minimizes the Chapter 10 local model at step `n`.
    exact
      (non_euclidean_proximal_gradient_step_iff_isMinOn_non_euclidean_proximal_gradient_model
        (f := f) (g := g) (ω := ω) (xk := x n) (xNext := x (n + 1)) (Lk := L n) hfxn).mp
        hstep
  have hupper :
      f (x (n + 1)) ≤
        f (x n) +
          ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (x (n + 1) - x n) +
            ((L n : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ) : ℝ) : EReal) :=
    hproblem.upper_model_of_constantOrBacktrackingB5Rule hω htraj hrule n
  have hxn_domains :
      x n ∈ effective_domain g ∩ subdifferential_domain ω :=
    is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj n
  have hxn1_domains :
      x (n + 1) ∈ effective_domain g ∩ subdifferential_domain ω :=
    is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj (n + 1)
  have hquad_le_bregman :
      ((L n : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ) ≤
        (L n : ℝ) * B[ω] (x (n + 1)) (x n) := by
    have hbregman :
        (1 / 2 : ℝ) * ‖x (n + 1) - x n‖ ^ (2 : ℕ) ≤
          B[ω] (x (n + 1)) (x n) := by
      -- Lemma 9.4 gives the source lower quadratic bound for the Bregman term.
      simpa using
        (bregmanDistance_lower_quadratic_bound
          (hω := hω) (x := x (n + 1)) (y := x n)
          hxn1_domains.1 hxn_domains.1 hxn_domains.2)
    have hLn_nonneg : 0 ≤ (L n : ℝ) := le_of_lt (PosReal.coe_pos (L n))
    have hmul := mul_le_mul_of_nonneg_left hbregman hLn_nonneg
    nlinarith
  have hquad_le_bregmanE :
      ((((L n : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        ((((L n : ℝ) * B[ω] (x (n + 1)) (x n) : ℝ) : EReal)) := by
    exact_mod_cast hquad_le_bregman
  have hmodel_upper :
      F (x (n + 1)) ≤ non_euclidean_textbook_model f g ω (x n) (L n) (x (n + 1)) := by
    -- Upgrade the accepted quadratic upper model to the stronger Bregman upper model.
    calc
      F (x (n + 1)) = f (x (n + 1)) + g (x (n + 1)) := by
        simp [F, composite_model_objective]
      _ ≤
          (f (x n) +
            ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (x (n + 1) - x n) +
              ((L n : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ) : ℝ) : EReal)) +
            g (x (n + 1)) := by
          exact add_le_add_right hupper (g (x (n + 1)))
      _ ≤
          (f (x n) +
            ((((inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (x (n + 1) - x n) : ℝ) : EReal)) +
              ((((L n : ℝ) * B[ω] (x (n + 1)) (x n) : ℝ) : EReal)))) +
            g (x (n + 1)) := by
          have hsplit :
              (((inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (x (n + 1) - x n) +
                  ((L n : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤
                ((((inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (x (n + 1) - x n) : ℝ) : EReal)) +
                  ((((L n : ℝ) * B[ω] (x (n + 1)) (x n) : ℝ) : EReal))) := by
            rw [EReal.coe_add]
            exact add_le_add_left hquad_le_bregmanE
              (((inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (x (n + 1) - x n) : ℝ) : EReal))
          exact add_le_add_right hsplit (g (x (n + 1)))
      _ = non_euclidean_textbook_model f g ω (x n) (L n) (x (n + 1)) := by
        simp [non_euclidean_textbook_model, F, composite_model_objective, add_assoc, add_left_comm,
          add_comm]
  -- Compare the model at the minimizer `x^(n+1)` with the same model at the external comparator.
  exact le_trans hmodel_upper <| hmodel_min u (by simp)

/-- Helper for Theorem 10.72: convexity of `f` replaces the local linear model at a comparator by
the true objective value, leaving only the Bregman penalty. This is the source passage from
`m(u, x^n)` to `f(u)`. -/
lemma non_euclidean_textbook_model_le_objective_add_bregman
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    {n : ℕ} {u : E} (hu : u ∈ effective_domain g) :
    non_euclidean_textbook_model f g ω (x n) (L n) u ≤
      F u + ((((L n : ℝ) * B[ω] u (x n) : ℝ) : EReal)) := by
  have hfxn :
      is_differentiable_at f (x n) :=
    is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj n
  have hxn_finite : x n ∈ finite_domain f := interior_subset hfxn.1
  have hxn_eff : x n ∈ effective_domain f := (mem_finite_domain.mp hxn_finite).1
  have hu_eff : u ∈ effective_domain f := by
    exact interior_subset (hproblem.g_effective_domain_subset_interior_f_effective_domain hu)
  have hxn_val :
      f (x n) = ((((f (x n)).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxn_eff).ne
        (hproblem.f_ne_bot (x n))).symm
  have hu_val :
      f u = ((((f u).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne
        (hproblem.f_ne_bot u)).symm
  have hsupport :
      (f u).toReal ≥ (f (x n)).toReal +
        inner ℝ (∇ (fun z ↦ (f z).toReal) (x n)) (u - x n) :=
    non_euclidean_convex_support_toReal_at_basepoint
      (xBase := x n) (y := u) hxn_eff hfxn.2 hu_eff
  have hlinear_le :
      f (x n) +
        (((inner ℝ (∇ (fun z ↦ (f z).toReal) (x n)) (u - x n) : ℝ)) : EReal) ≤
      f u := by
    -- Rewrite both finite `f`-values as real coercions and transport the real support inequality.
    rw [hxn_val, hu_val, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr hsupport
  -- Replace the linearized smooth term by the true smooth value at the comparator.
  calc
    non_euclidean_textbook_model f g ω (x n) (L n) u
        =
        ((f (x n) +
            (((inner ℝ (∇ (fun z ↦ (f z).toReal) (x n)) (u - x n) : ℝ)) : EReal)) +
          g u) +
          ((((L n : ℝ) * B[ω] u (x n) : ℝ) : EReal)) := by
            simp [non_euclidean_textbook_model, add_assoc]
    _ ≤ ((f u + g u) + ((((L n : ℝ) * B[ω] u (x n) : ℝ) : EReal))) := by
      exact add_le_add_right (add_le_add_right hlinear_le (g u)) _
    _ = F u + ((((L n : ℝ) * B[ω] u (x n) : ℝ) : EReal)) := by
      simp [F, composite_model_objective, add_assoc]

/-- Helper for Theorem 10.72: the optimal value is a lower bound for every objective value along
the non-Euclidean proximal-gradient trajectory. -/
lemma non_euclidean_objective_gap_nonneg (n : ℕ) :
    (FOpt : EReal) ≤ F (x n) := by
  -- This is exactly the greatest-lower-bound clause from Assumption 10.77.
  exact hproblem.optimal_value_isGLB.1 ⟨x n, rfl⟩

/-- Helper for Theorem 10.72: every optimizer has finite nonsmooth value, so it belongs to
`effective_domain g`. -/
lemma non_euclidean_optimizer_mem_effective_domain_g
    (hxStar : xStar ∈ XStar) :
    xStar ∈ effective_domain g := by
  have hobj : F xStar = (FOpt : EReal) :=
    hproblem.objective_eq_optimalValue_of_mem_optimalSet hxStar
  by_contra hxg
  have hg_top : g xStar = ⊤ := by
    exact le_antisymm le_top <| not_lt.mp <| by
      simpa [effective_domain] using hxg
  have hF_top : F xStar = ⊤ := by
    rw [composite_model_objective_apply, hg_top]
    exact EReal.add_top_of_ne_bot (hproblem.f_ne_bot xStar)
  exact EReal.coe_ne_top FOpt (hobj.symm.trans hF_top)

/-- Helper for Theorem 10.72: specializing Theorem 9.12 to the source penalty `ψ_n` and then
rewriting its left side with the three-point identity gives the textbook inequality `(10.u401)`. -/
lemma non_euclidean_linearized_penalty_three_point_ineq
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (n : ℕ) {u : E} (hu : u ∈ effective_domain g) :
    (((B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) - B[ω] u (x n) : ℝ)) : EReal) ≤
      non_euclidean_linearized_scaled_penalty
          (f := f) (g := g) (ω := ω) (x := x) (L := L) n u -
        non_euclidean_linearized_scaled_penalty
          (f := f) (g := g) (ω := ω) (x := x) (L := L) n (x (n + 1)) := by
  let ψ := non_euclidean_linearized_scaled_penalty
    (f := f) (g := g) (ω := ω) (x := x) (L := L) n
  have hxn_domains :
      x n ∈ effective_domain g ∩ subdifferential_domain ω :=
    is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj n
  have hxn1_domains :
      x (n + 1) ∈ effective_domain g ∩ subdifferential_domain ω :=
    is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj (n + 1)
  have hcurvature :
      ((L n : ℝ)⁻¹) = (((1 / L n : PosReal) : ℝ)) := by
    simp
  have hmin_bregman :
      IsMinOn (fun z ↦ ψ z + ((B[ω] z (x n) : ℝ) : EReal)) Set.univ (x (n + 1)) := by
    -- Rewrite the realized step minimizer from the Mirror-C objective to the Bregman-form
    -- objective `ψ_n + B[ω](·, x^n)`.
    have hmirror :
        IsMinOn
          (mirror_c_update_objective g ω (x n)
            (fderiv ℝ (fun y ↦ (f y).toReal) (x n)) ((L n : ℝ)⁻¹))
          Set.univ (x (n + 1)) :=
      is_non_euclidean_proximal_gradient_trajectory_isMinOn htraj n
    simpa [ψ, non_euclidean_linearized_scaled_penalty, hcurvature, Pi.smul_apply, smul_eq_mul,
      add_assoc] using
      (isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_update_objective
        g ω (x n) (x (n + 1))
        (fderiv ℝ (fun y ↦ (f y).toReal) (x n)) ((L n : ℝ)⁻¹)).mp hmirror
  have hψ_data :=
    non_euclidean_linearized_scaled_penalty_proper_convex
      (f := f) (g := g) (ω := ω) (x := x) (L := L) n
  have hωψ : IsBregmanPotentialOn ω (effective_domain ψ) (1 : ℝ) := by
    rw [non_euclidean_linearized_scaled_penalty_effective_domain_eq
      (f := f) (g := g) (ω := ω) (x := x) (L := L) n]
    exact hω
  have huψ : u ∈ effective_domain ψ := by
    rwa [non_euclidean_linearized_scaled_penalty_effective_domain_eq
      (f := f) (g := g) (ω := ω) (x := x) (L := L) n]
  have hopt :
      (inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x n)) -
            (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
          (u - x (n + 1)) : EReal) ≤
        ψ u - ψ (x (n + 1)) :=
    non_euclidean_second_prox_optimality_ineq
      (ψ := ψ) (ω := ω) (σ := (1 : ℝ))
      hωψ hψ_data.1 hψ_data.2 hxn_domains.2 hmin_bregman u huψ
  have hthree_point :
      inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x n)) -
            (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
          (u - x (n + 1)) =
        B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) - B[ω] u (x n) := by
    -- The Bregman three-point identity rewrites the gradient pairing into the textbook
    -- difference-of-distances expression.
    simpa using
      (bregman_three_point_identity
        (ω := ω) (c := u) (a := x (n + 1)) (b := x n)
        ((hω.differentiableOn_subdifferential_domain hxn1_domains.2).hasGradientAt)
        ((hω.differentiableOn_subdifferential_domain hxn_domains.2).hasGradientAt)).symm
  calc
    (((B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) - B[ω] u (x n) : ℝ)) : EReal) =
        (inner ℝ
            ((∇ (fun z ↦ (ω z).toReal) (x n)) -
              (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
            (u - x (n + 1)) : EReal) := by
          exact (congrArg (fun r : ℝ ↦ (r : EReal)) hthree_point).symm
    _ ≤ ψ u - ψ (x (n + 1)) := hopt

/-- Helper for Theorem 10.72: route correction for clause (b). Instead of forcing the Chapter 9
inequality through the mirror-functional form, apply Theorem 9.12 directly to the source
linearized objective `(m(·, x^n) + g) / L_n`, so the conclusion is already the plus-form
equation `(10.96)` in `scaled_bregman_objective` language. -/
lemma non_euclidean_scaled_objective_successor_add_bregman_le_comparator
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (n : ℕ) {u : E} (hu : u ∈ effective_domain g) :
    scaled_bregman_objective f g ω (x n) (L n) (x (n + 1)) +
      (((B[ω] u (x (n + 1)) : ℝ)) : EReal) ≤
    scaled_bregman_objective f g ω (x n) (L n) u := by
  let ψ := non_euclidean_scaled_linearized_objective
    (f := f) (g := g) (x := x) (L := L) n
  have hxn_domains :
      x n ∈ effective_domain g ∩ subdifferential_domain ω :=
    is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj n
  have hxn1_domains :
      x (n + 1) ∈ effective_domain g ∩ subdifferential_domain ω :=
    is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj (n + 1)
  have hψ_data :
      IsProperExtendedRealFunction ψ ∧ is_convex_function ψ :=
    non_euclidean_scaled_linearized_objective_proper_convex
      (f := f) (g := g) (x := x) (L := L) n
  have hωψ : IsBregmanPotentialOn ω (effective_domain ψ) (1 : ℝ) := by
    rw [non_euclidean_scaled_linearized_objective_effective_domain_eq
      (f := f) (g := g) (x := x) (L := L) n]
    exact hω
  have huψ : u ∈ effective_domain ψ := by
    rwa [non_euclidean_scaled_linearized_objective_effective_domain_eq
      (f := f) (g := g) (x := x) (L := L) n]
  have hmin_scaled :
      IsMinOn (fun z ↦ ψ z + ((B[ω] z (x n) : ℝ) : EReal)) Set.univ (x (n + 1)) := by
    -- The realized step minimizes the exact Chapter 9 objective `ψ_n + B_ω(·, x^n)`.
    have hmirror :
        IsMinOn
          (mirror_c_update_objective g ω (x n)
            (fderiv ℝ (fun y ↦ (f y).toReal) (x n)) ((L n : ℝ)⁻¹))
          Set.univ (x (n + 1)) :=
      is_non_euclidean_proximal_gradient_trajectory_isMinOn htraj n
    simpa [ψ, non_euclidean_scaled_linearized_objective, scaled_bregman_objective, add_assoc] using
      (isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_update_objective
        g ω (x n) (x (n + 1))
        (fderiv ℝ (fun y ↦ (f y).toReal) (x n)) ((L n : ℝ)⁻¹)).mp hmirror
  have hopt :
      (inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x n)) -
            (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
          (u - x (n + 1)) : EReal) ≤
        ψ u - ψ (x (n + 1)) :=
    non_euclidean_second_prox_optimality_ineq
      (ψ := ψ) (ω := ω) (σ := (1 : ℝ))
      hωψ hψ_data.1 hψ_data.2 hxn_domains.2 hmin_scaled u huψ
  have hthree_point :
      inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x n)) -
            (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
          (u - x (n + 1)) =
        B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) - B[ω] u (x n) := by
    -- The Bregman three-point identity is exactly the source bridge to `(10.u401)`.
    simpa using
      (bregman_three_point_identity
        (ω := ω) (c := u) (a := x (n + 1)) (b := x n)
        ((hω.differentiableOn_subdifferential_domain hxn1_domains.2).hasGradientAt)
        ((hω.differentiableOn_subdifferential_domain hxn_domains.2).hasGradientAt)).symm
  have hgap :
      (((B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) - B[ω] u (x n) : ℝ)) : EReal) ≤
        ψ u - ψ (x (n + 1)) := by
    calc
      (((B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) - B[ω] u (x n) : ℝ)) : EReal) =
          (inner ℝ
              ((∇ (fun z ↦ (ω z).toReal) (x n)) -
                (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
              (u - x (n + 1)) : EReal) := by
            exact (congrArg (fun r : ℝ ↦ (r : EReal)) hthree_point).symm
      _ ≤ ψ u - ψ (x (n + 1)) := hopt
  have hψ_succ_ne_bot : ψ (x (n + 1)) ≠ ⊥ := hψ_data.1.ne_bot _
  have hψ_u_ne_top : ψ u ≠ ⊤ := (mem_effective_domain.mp huψ).ne
  have hgap_add :
      (((B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) : ℝ)) : EReal) +
        ψ (x (n + 1)) ≤
      ψ u + (((B[ω] u (x n) : ℝ)) : EReal) := by
    -- Move `ψ(x^(n+1))` across the subtraction and then cancel the trailing `-B_ω(u, x^n)`.
    have hshift :
        (((B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) - B[ω] u (x n) : ℝ)) : EReal) +
          ψ (x (n + 1)) ≤ ψ u := by
      exact
        (EReal.le_sub_iff_add_le (.inl hψ_succ_ne_bot) (.inl hψ_u_ne_top)).1 hgap
    have hshift' := add_le_add_right hshift ((((B[ω] u (x n) : ℝ)) : EReal))
    have hsum_real :
        (B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) - B[ω] u (x n)) + B[ω] u (x n) =
          B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) := by
      ring
    simpa [hsum_real, add_assoc, add_left_comm, add_comm, EReal.coe_add] using hshift'
  -- Reassemble the left and right sides into `scaled_bregman_objective`.
  simpa [ψ, non_euclidean_scaled_linearized_objective, scaled_bregman_objective,
    add_assoc, add_left_comm, add_comm, EReal.coe_add] using hgap_add

-- Proof sketch: keep the source-faithful Chapter 9 route. The missing bridge is the one-step
-- inequality obtained by specializing Theorem 9.12 to the scaled linearized objective,
-- rewriting with the three-point identity, and telescoping the resulting Bregman differences.
/-- Theorem 10.72 (2): clause (b). Under the same assumptions as clause (1), every positive
iterate satisfies the non-Euclidean sublinear objective-gap estimate
`F(x^k) - F_opt ≤ α L_f B[ω] x* x^0 / k` for every optimizer `x* ∈ X^*`. -/
theorem non_euclidean_proximal_gradient_objective_gap_le
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : hproblem.NonEuclideanSublinearRateStepsizeRule hω x L α)
    (hxStar : xStar ∈ XStar) (k : ℕ) (hk : 1 ≤ k) :
    F (x k) - (FOpt : EReal) ≤
      (((α * (Lf : ℝ) * B[ω] xStar (x 0) / (k : ℝ) : ℝ)) : EReal) := by
  have hmono :
      Antitone (fun n ↦ F (x n)) :=
    non_euclidean_proximal_gradient_objective_values_antitone
      (hω := hω) (htraj := htraj)
      (hrule := hproblem.sublinearRateStepsizeRule_constantOrBacktrackingB5 hrule)
  have hLf_pos : 0 < (Lf : ℝ) :=
    hproblem.sublinearRateStepsizeRule_lf_pos_of_nonEuclidean hrule
  have hxStar_value : F xStar = (FOpt : EReal) :=
    hproblem.objective_eq_optimalValue_of_mem_optimalSet hxStar
  have hxStar_eff : xStar ∈ effective_domain g :=
    non_euclidean_optimizer_mem_effective_domain_g
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) hxStar
  have hsuccessor_model :
      ∀ n : ℕ, F (x (n + 1)) ≤ non_euclidean_textbook_model f g ω (x n) (L n) xStar := by
    intro n
    -- This is the source `(10.94)` plus model minimality at the realized step.
    exact
      non_euclidean_successor_le_textbook_model
        (hω := hω) (htraj := htraj)
        (hrule := hproblem.sublinearRateStepsizeRule_constantOrBacktrackingB5 hrule)
        n xStar
  have hcomparator_bound :
      ∀ n : ℕ,
        non_euclidean_textbook_model f g ω (x n) (L n) xStar ≤
          F xStar + ((((L n : ℝ) * B[ω] xStar (x n) : ℝ) : EReal)) := by
    intro n
    -- Convexity upgrades the local linear model at `xStar` to the true objective value `F xStar`.
    exact
      non_euclidean_textbook_model_le_objective_add_bregman
        (htraj := htraj) (n := n) hxStar_eff
  have hscaled_objective_drop :
      ∀ n : ℕ,
        scaled_bregman_objective f g ω (x n) (L n) (x (n + 1)) +
          (((B[ω] xStar (x (n + 1)) : ℝ)) : EReal) ≤
        scaled_bregman_objective f g ω (x n) (L n) xStar := by
    intro n
    -- Route correction: use the source plus-form inequality `(10.96)` directly.
    exact
      non_euclidean_scaled_objective_successor_add_bregman_le_comparator
        (hω := hω) (htraj := htraj) (n := n) hxStar_eff
  -- Route correction: clause (b) must stay on the source Chapter 9 route.
  -- The source plus-form inequality `(10.96)` is now in place. The remaining work is the single
  -- rescaling rewrite from `scaled_bregman_objective` to the Chapter 10 textbook model, followed
  -- by the B5/constant stepsize bound and the telescope-to-average conversion already prepared
  -- above.
  -- TODO: rewrite `hscaled_objective_drop` into the one-step model drop
  -- `F (x (n + 1)) - FOpt ≤ (L n) * (B[ω] xStar (x n) - B[ω] xStar (x (n + 1)))`,
  -- prove `L n ≤ α * Lf`, and then sum the recurrence over `Finset.range k`.
  clear hmono hLf_pos hxStar_value hk
  sorry

end
