import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology
open Module.Dual

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 3.10 is a `bridge/view` reformulation of the Chapter 3 max formula from
`Definition_3_9`: the owner notions remain `directional_derivative` and `extendedRealSubdifferential`, while
the support-function expression is the Chapter 2 canonical reformulation. -/
recall support_function
recall directional_derivative
recall is_convex_function
recall extendedRealSubdifferential
recall finite_domain
recall directional_derivative_isGreatest_subgradient_pairings_at_interior_point
recall support_function_eq_of_isGreatest_image

-- Proof sketch: apply the owner theorem
-- `directional_derivative_isGreatest_subgradient_pairings_at_interior_point` from
-- `Definition_3_9`, then rewrite the resulting maximum formula through the canonical support
-- function owner lemma `support_function_eq_of_isGreatest_image`. The chapter's owner-side
-- qualification is `x ∈ interior (finite_domain f)`, from which the older global no-`⊥`
-- hypothesis and the effective-domain interior hypothesis are derived internally.
/-- Proposition 3.10: for a convex extended-real-valued function, at a point in the interior of
its finite domain the directional derivative equals the support function of the extendedRealSubdifferential
evaluated at the canonical functional `Module.Dual.eval ℝ E d`. -/
theorem directional_derivative_eq_support_function_subdifferential_at_interior_point
    {f : E → EReal} {x d : E} (hconvex : is_convex_function f)
    (hx : x ∈ interior (finite_domain f)) :
    directional_derivative f x d = support_function (extendedRealSubdifferential f x) (eval ℝ E d) := by
  have hx_effective : x ∈ interior (effective_domain f) :=
    interior_mono (fun _ hz ↦ hz.1) hx
  have h_ne_bot : ∀ y, f y ≠ ⊥ := by
    intro y
    by_contra hy_bot
    have hxfd : x ∈ finite_domain f := interior_subset hx
    have hy_effective : y ∈ effective_domain f := by
      simp [effective_domain, hy_bot]
    by_cases hxy : y = x
    · exact hxfd.2 (hxy ▸ hy_bot)
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
    let t : ℝ := min (ε / (2 * ‖y - x‖)) (1 / 2)
    have hnorm_pos : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have ht_pos : 0 < t := by
      dsimp [t]
      refine lt_min ?_ (by norm_num)
      exact div_pos hε_pos (by positivity)
    have ht_le_half : t ≤ 1 / 2 := by
      dsimp [t]
      exact min_le_right _ _
    have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact le_of_lt ht_pos
      · linarith
    let z : E := x + t • (y - x)
    have hz_ball : z ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      dsimp [z]
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (le_of_lt ht_pos)]
      have ht_le : t ≤ ε / (2 * ‖y - x‖) := by
        dsimp [t]
        exact min_le_left _ _
      have ht_mul : t * (2 * ‖y - x‖) ≤ ε := by
        exact (le_div_iff₀ (by positivity)).mp ht_le
      have htnorm : t * ‖y - x‖ ≤ ε / 2 := by
        nlinarith
      linarith
    have hz_finite : z ∈ finite_domain f := interior_subset (hε_ball hz_ball)
    have hz_eq : z = t • y + (1 - t) • x := by
      dsimp [z]
      calc
        x + t • (y - x) = x + (t • y - t • x) := by rw [smul_sub]
        _ = x + (t • y + -(t • x)) := by rw [sub_eq_add_neg]
        _ = x + (t • y + (-t) • x) := by
          exact congrArg (fun s ↦ x + (t • y + s)) (neg_smul t x).symm
        _ = t • y + ((-t) + 1) • x := by
          rw [add_smul, one_smul]
          abel
        _ = t • y + (1 - t) • x := by ring_nf
    have hz_le :
        f z ≤ (t : EReal) * f y + ((1 - t : ℝ) : EReal) * f x := by
      simpa [hz_eq] using
        (is_convex_function_iff_segment_ineq.mp hconvex) y hy_effective x hxfd.1 ht_mem
    have h_rhs_bot :
        (t : EReal) * f y + ((1 - t : ℝ) : EReal) * f x = ⊥ := by
      rw [hy_bot, EReal.mul_bot_of_pos (by exact_mod_cast ht_pos)]
      simp
    exact hz_finite.2 (le_bot_iff.mp <| h_rhs_bot ▸ hz_le)
  symm
  refine support_function_eq_of_isGreatest_image (extendedRealSubdifferential f x) (eval ℝ E d) ?_
  simpa [eval_apply] using
    directional_derivative_isGreatest_subgradient_pairings_at_interior_point
      h_ne_bot hconvex hx_effective

end
