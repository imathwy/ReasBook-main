import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_72.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g ω : E → EReal} {Lf : NNReal}
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

/- `lean_leansearch` was unavailable in this run, so the local Chapter 5 and Chapter 10 files
were used directly for API recall.

Definition 10.69 is a `source-facing` bridge in the non-Euclidean proximal-gradient section. The
source item does not introduce a new owner abstraction; it restates the shared quadratic
upper-model inequality at one iterate under the admissible constant-or-B5 stepsize regime. The
relevant domain owners already present in the project are:
- `uses_proximal_gradient_Lf_stepsize_rule` from Remark 10.19 for the constant branch;
- `uses_non_euclidean_proximal_gradient_backtracking_B5_rule` from Algorithm 10.69 for the B5
  branch;
- `non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_rule` from Theorem 10.72
  as the source-facing Chapter 10 owner of that exact disjunction;
- `is_l_smooth_on_descent_lemma` from Lemma 5.7 for the smoothness-based derivation of the
  constant branch on the segment joining consecutive iterates.

Primitive data are the smoothness/domain hypotheses, the Bregman potential hypothesis, the
non-Euclidean trajectory, and the canonical Chapter 10 stepsize owner. The displayed quadratic
upper-model inequality is derived API, so this file should first bridge to the canonical owner
`non_euclidean_proximal_gradient_backtracking_B5_accepts` from Algorithm 10.69 instead of
keeping the expanded inequality as the primary owner-facing output. -/

omit [FiniteDimensional ℝ E] [IsProperExtendedRealFunction g]
  [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] in
/-- Helper for Definition 10.69: every iterate of a non-Euclidean proximal-gradient trajectory
lies in `interior (effective_domain f)` once `effective_domain g` is contained there. -/
lemma non_euclidean_proximal_gradient_trajectory_mem_interior_effective_domain
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (k : ℕ) :
    x k ∈ interior (effective_domain f) := by
  -- The trajectory stays in `effective_domain g`, and the standing inclusion moves it into the
  -- interior of `effective_domain f`.
  exact
    hg_effective_domain_subset_interior_f_effective_domain
      (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj k).1

/-- Bridge/view layer: along a non-Euclidean proximal-gradient trajectory, the next iterate is
the canonical non-Euclidean proximal-gradient operator value `V[L_k, f, g, ω] (x^k)`. -/
theorem is_non_euclidean_proximal_gradient_trajectory_succ_eq_operator
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (k : ℕ) :
    x (k + 1) = V[L k, f, g, ω] (x k) := by
  -- The trajectory successor and the operator output solve the same unique step problem.
  have hfxk :
      is_differentiable_at f (x k) :=
    is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj k
  refine
    (existsUnique_non_euclidean_proximal_gradient_step_mem_domains
      f g ω (x k) (L k) hfxk).unique ?_ ?_
  · -- The realized successor is a valid step and stays in the required domains.
    exact
      ⟨is_non_euclidean_proximal_gradient_trajectory_mem_step htraj k,
        is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj (k + 1)⟩
  · -- The canonical operator value satisfies the same step and domain conditions.
    exact
      ⟨non_euclidean_proximal_gradient_operator_mem_step f g ω (x k) (L k) hfxk,
        non_euclidean_proximal_gradient_operator_mem_domains f g ω (x k) (L k) hfxk⟩

/-- Helper for Definition 10.69: a real-valued descent estimate upgrades to the `EReal`
upper-model inequality once the current iterate lies in the finite domain and the next iterate
stays in `interior (effective_domain f)`. -/
lemma non_euclidean_upper_model_of_toReal_le
    {xk xNext : E} {Lk : PosReal}
    (hfxk : is_differentiable_at f xk)
    (hxNext : xNext ∈ interior (effective_domain f))
    (hdescent :
      (f xNext).toReal ≤
        (f xk).toReal +
          inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
          ((Lk : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ)) :
    f xNext ≤
      f xk +
        ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
          ((Lk : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- The differentiability owner records that `xk` lies in the finite domain of `f`.
  have hxk_finite : xk ∈ finite_domain f := interior_subset hfxk.1
  have hxk_eff : xk ∈ effective_domain f := (mem_finite_domain.mp hxk_finite).1
  have hxk_ne_bot : f xk ≠ ⊥ := (mem_finite_domain.mp hxk_finite).2
  by_cases hxNext_bot : f xNext = ⊥
  · -- If `f xNext = ⊥`, the `EReal` upper model is immediate.
    simp [hxNext_bot]
  · -- Otherwise both endpoints can be rewritten as real coercions and the real estimate lifts.
    have hxNext_eff : xNext ∈ effective_domain f := interior_subset hxNext
    have hxk_val : f xk = (((f xk).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxk_eff).ne hxk_ne_bot).symm
    have hxNext_val : f xNext = (((f xNext).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxNext_eff).ne hxNext_bot).symm
    have hdescentE :
        (((f xNext).toReal : ℝ) : EReal) ≤
          (((f xk).toReal +
              inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
              ((Lk : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      exact_mod_cast hdescent
    rw [hxNext_val, hxk_val]
    simpa [EReal.coe_add, add_assoc] using hdescentE

/-- Bridge/view layer: under the standing smoothness and domain hypotheses, the canonical
constant-or-B5 stepsize owner implies that the chosen curvature estimate `L_k` satisfies the
canonical B5 acceptance predicate at iteration `k`. -/
theorem non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_accepts
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule :
      non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_rule
        f g ω Lf hω x L)
    (k : ℕ) :
    non_euclidean_proximal_gradient_backtracking_B5_accepts f g ω (L k) (x k) := by
  rcases hrule with hLf_rule | ⟨s, η, hB5⟩
  · -- In the constant-stepsize branch, use the descent lemma on the segment joining
    -- consecutive iterates.
    have hfxk :
        is_differentiable_at f (x k) :=
      is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj k
    have hxk_int :
        x k ∈ interior (effective_domain f) :=
      non_euclidean_proximal_gradient_trajectory_mem_interior_effective_domain
        hg_effective_domain_subset_interior_f_effective_domain htraj k
    have hxk1_int :
        x (k + 1) ∈ interior (effective_domain f) :=
      non_euclidean_proximal_gradient_trajectory_mem_interior_effective_domain
        hg_effective_domain_subset_interior_f_effective_domain htraj (k + 1)
    have hnext :
        x (k + 1) = V[L k, f, g, ω] (x k) :=
      is_non_euclidean_proximal_gradient_trajectory_succ_eq_operator hω htraj k
    have hdescent :
        (f (x (k + 1))).toReal ≤
          (f (x k)).toReal +
            inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
            ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) := by
      -- Lemma 5.7 applies on the convex interior of `effective_domain f`.
      simpa [hLf_rule k, norm_sub_rev] using
        (is_l_smooth_on_descent_lemma
          (L := Lf)
          (D := interior (effective_domain f))
          (f := fun y ↦ (f y).toReal)
          hf_effective_domain_convex.interior
          hf_toReal_smooth_on_interior_effective_domain
          hxk_int
          hxk1_int)
    refine ⟨hfxk, ?_⟩
    -- Rewrite the realized successor as the canonical operator output and lift the real descent
    -- estimate to the `EReal` acceptance inequality.
    simpa [hnext] using
      non_euclidean_upper_model_of_toReal_le
        (f := f)
        (xk := x k)
        (xNext := x (k + 1))
        (Lk := L k)
        hfxk
        hxk1_int
        hdescent
  · exact uses_non_euclidean_proximal_gradient_backtracking_B5_rule_accepts f g ω hB5 k

/-- Definition 10.69: [Remark 10.79] if `effective_domain f` is convex,
`effective_domain g ⊆ interior (effective_domain f)`, `(fun y ↦ (f y).toReal)` is `L_f`-smooth
on `interior (effective_domain f)`, and the
non-Euclidean proximal-gradient trajectory satisfies the canonical constant-or-B5 stepsize owner,
then at every iteration `k` the quadratic upper-model inequality
`f(x^(k+1)) ≤ f(x^k) + ⟪∇ f(x^k), x^(k+1) - x^k⟫ + (L_k / 2) ‖x^(k+1) - x^k‖²` holds. -/
theorem non_euclidean_proximal_gradient_upper_model_of_constant_or_backtracking_B5_rule
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule :
      non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_rule
        f g ω Lf hω x L)
    (k : ℕ) :
    f (x (k + 1)) ≤
      f (x k) +
        ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
          ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  have haccepts :=
    non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_accepts
      hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      hω htraj hrule k
  have hnext :
      x (k + 1) = V[L k, f, g, ω] (x k) :=
    is_non_euclidean_proximal_gradient_trajectory_succ_eq_operator hω htraj k
  simpa [non_euclidean_proximal_gradient_backtracking_B5_accepts, hnext] using haccepts.2

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g ω : E → EReal} {Lf : NNReal}
variable {XStar : Set E} {FOpt : ℝ}

namespace IsConvexCompositeSmoothMinimizationProblem

/-- Bridge/view layer: Assumption 10.77 specializes the primitive Definition 10.69 upper-model
theorem to the source-facing constant-or-B5 stepsize rule from Theorem 10.72. -/
theorem upper_model_of_constantOrBacktrackingB5Rule
    [hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : hproblem.ConstantOrBacktrackingB5StepsizeRule hω x L)
    (k : ℕ) :
    f (x (k + 1)) ≤
      f (x k) +
        ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
          ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  simpa [ConstantOrBacktrackingB5StepsizeRule] using
    non_euclidean_proximal_gradient_upper_model_of_constant_or_backtracking_B5_rule
      hproblem.f_effective_domain_convex
      hproblem.g_effective_domain_subset_interior_f_effective_domain
      hproblem.f_toReal_smooth_on_interior_effective_domain
      hω htraj hrule k

end IsConvexCompositeSmoothMinimizationProblem

end
