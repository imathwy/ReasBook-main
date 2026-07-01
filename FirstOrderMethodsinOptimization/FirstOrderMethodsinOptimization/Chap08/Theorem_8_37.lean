import FirstOrderMethodsinOptimization.Chap08.Algorithm_8_10
import FirstOrderMethodsinOptimization.Chap08.Assumption_8_7
import FirstOrderMethodsinOptimization.Chap08.Assumption_8_34
import FirstOrderMethodsinOptimization.Chap08.Definition_8_8
import FirstOrderMethodsinOptimization.Chap08.Lemma_8_11
import FirstOrderMethodsinOptimization.Chap05.Theorem_5_4
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped BigOperators ProbabilityTheory
open MeasureTheory
open InnerProductSpace (toDualMap)

noncomputable section

section

variable {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt σ : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (g : ℕ → C → Ω → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  stochastic_projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k

/- Theorem 8.37 is `source-facing`: it states the stochastic strongly-convex `O(1 / k)` rate for
the actual stochastic projected-subgradient iterates and for their weighted averages. The owner
abstractions already present in the chapter are the pathwise iterate sequence
`stochastic_projected_subgradient_method`, the running-best objective value
`best_achieved_function_value`, the stochastic oracle package
`StochasticProjectedSubgradientOracle`, the standing constrained problem class
`IsConstrainedConvexProblem`, and the canonical strong-convexity predicate
`StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)`. The only new data object needed by
the source is the averaged random iterate `x^(k)`, so it is exposed directly as a concrete weighted
sum of the sampled iterates rather than via a surrogate wrapper. -/

/-- The weighted average random iterate `x^(k)` used in the strongly convex stochastic
projected-subgradient rate. It uses the canonical weight convention from Theorem 8.31, so
`x^(0) = x^0` and for `k > 0` the coefficients are `α_n^k = 2 n / (k (k + 1))`. -/
def stochastic_projected_subgradient_strongly_convex_average_iterate
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (g : ℕ → C → Ω → E) (t : ℕ → ℝ) (x0 : C) (k : ℕ) : Ω → E :=
  let x :=
    stochastic_projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
      h_problem.feasible_convex g t x0
  fun ω ↦
    Finset.sum (Finset.range (k + 1)) fun n ↦
      (if k = 0 then
          if n = 0 then 1 else 0
        else
          (2 : ℝ) * n / (k * (k + 1) : ℝ)) •
        (x n ω : E)

-- Proof sketch: unfold
-- `stochastic_projected_subgradient_strongly_convex_average_iterate` at `k = 0`; the range has
-- only the index `0`, and the degenerate branch in the weight formula makes the unique
-- coefficient equal to `1`.
/-- The stochastic strongly convex weighted average at `k = 0` is the initial random iterate
`x^0`. -/
theorem stochastic_projected_subgradient_strongly_convex_average_iterate_zero (ω : Ω) :
    stochastic_projected_subgradient_strongly_convex_average_iterate h_problem g t x0 0 ω =
      (x[0] ω : E) := by
  -- Unfold the degenerate weighted average; only the index `0` survives with coefficient `1`.
  simp [stochastic_projected_subgradient_strongly_convex_average_iterate]

/-- Helper for Theorem 8.37: a Euclidean subgradient of the real-valued restriction
`x ↦ (f x).toReal` at a finite point yields a genuine subgradient of the original extended-real
objective. -/
lemma toDualMap_mem_subdifferential_of_mem_euclideanSubdifferentialAt_toReal
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    {x v : E} (hx : x ∈ effective_domain f)
    (hv : v ∈ euclideanSubdifferentialAt (fun y ↦ (f y).toReal) x) :
    (toDualMap ℝ E v : Module.Dual ℝ E) ∈ subdifferential f x := by
  -- Rewrite the Euclidean membership into the real-valued subgradient inequality.
  rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
    mem_subdifferential, is_subgradient_at_coe_iff] at hv
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨hx, ?_⟩
  intro y hy
  -- Finite values on the feasible domain let the real inequality lift back to `EReal`.
  have hx_top : f x ≠ ⊤ := ne_of_lt hx
  have hy_top : f y ≠ ⊤ := ne_of_lt hy
  have hx_bot : f x ≠ ⊥ := h_problem.ne_bot x
  have hy_bot : f y ≠ ⊥ := h_problem.ne_bot y
  have hvy : (f y).toReal ≥ (f x).toReal + inner ℝ v (y - x) := hv y
  have hvyE :
      ((((f x).toReal + inner ℝ v (y - x) : ℝ) : EReal) ≤ (((f y).toReal : ℝ) : EReal)) := by
    exact EReal.coe_le_coe (by simpa [ge_iff_le] using hvy)
  simpa [InnerProductSpace.toDualMap_apply_apply, EReal.coe_toReal hx_top hx_bot,
    EReal.coe_toReal hy_top hy_bot, EReal.coe_add, ge_iff_le] using hvyE

/-- Helper for Theorem 8.37: every Euclidean subgradient at a feasible point supports the
strongly convex objective at an optimal point with the quadratic correction term. -/
lemma strongly_convex_support_at_optimal_point
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ) {x xStar v : E} (hxC : x ∈ C) (hxStar : xStar ∈ XStar)
    (hv : v ∈ euclideanSubdifferentialAt (fun y ↦ (f y).toReal) x) :
    ((f x).toReal - fOpt) + (σ / 2) * ‖x - xStar‖ ^ (2 : ℕ) ≤ inner ℝ v (x - xStar) := by
  -- Route correction: avoid the broken Chapter 5 first-order-support file by shifting `f` by the
  -- affine functional `y ↦ -⟪v, y⟫`. The Euclidean subgradient inequality then says `x`
  -- minimizes the shifted objective on all of `E`, so Theorem 5.25 applies directly.
  let fShift : E → EReal := fun y ↦ f y + (((-inner ℝ v y : ℝ) : EReal))
  have hx_dom : x ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hxC)
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hxStar_dom : xStar ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hxStar_data.1)
  have hv_support : ∀ y : E, (f y).toReal ≥ (f x).toReal + inner ℝ v (y - x) := by
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
      mem_subdifferential, is_subgradient_at_coe_iff] at hv
    exact hv
  -- The affine shift preserves the effective domain because the added term is always finite.
  have hdomShift : effective_domain fShift = effective_domain f := by
    ext y
    constructor
    · intro hy
      change f y < ⊤
      refine lt_top_iff_ne_top.mpr ?_
      exact
        (EReal.add_ne_top_iff_of_ne_bot_of_ne_top (EReal.coe_ne_bot _) (EReal.coe_ne_top _)).1
          (ne_of_lt hy)
    · intro hy
      simpa [fShift] using EReal.add_lt_top (ne_of_lt hy) (EReal.coe_ne_top _)
  have hne_bot_shift : ∀ y, fShift y ≠ ⊥ := by
    intro y
    simpa [fShift, EReal.add_ne_bot_iff] using
      (show f y ≠ ⊥ ∧ (((-inner ℝ v y : ℝ) : EReal) ≠ ⊥) from
        ⟨h_problem.ne_bot y, EReal.coe_ne_bot _⟩)
  -- On the finite domain, the shifted real-valued objective is `y ↦ (f y).toReal - ⟪v, y⟫`.
  have htoRealShift :
      ∀ {y : E}, y ∈ effective_domain fShift → (fShift y).toReal = (f y).toReal - inner ℝ v y := by
    intro y hy
    have hy_dom : y ∈ effective_domain f := by
      simpa [hdomShift] using hy
    have hy_top : f y ≠ ⊤ := ne_of_lt hy_dom
    have hy_bot : f y ≠ ⊥ := h_problem.ne_bot y
    rw [show fShift y = f y + (((-inner ℝ v y : ℝ) : EReal)) by rfl,
      EReal.toReal_add hy_top hy_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp [EReal.coe_toReal hy_top hy_bot, sub_eq_add_neg]
  -- The strong-convexity modulus is unchanged because affine terms cancel in the Jensen defect.
  have hstrongShift :
      StrongConvexOn (effective_domain fShift) σ (fun y ↦ (fShift y).toReal) := by
    refine ⟨?_, ?_⟩
    · simpa [hdomShift] using h_strong.1
    · intro y hy z hz a b ha hb hab
      have hy_dom : y ∈ effective_domain f := by
        simpa [hdomShift] using hy
      have hz_dom : z ∈ effective_domain f := by
        simpa [hdomShift] using hz
      have hyz_dom : a • y + b • z ∈ effective_domain f := h_strong.1 hy_dom hz_dom ha hb hab
      have hyz_shift : a • y + b • z ∈ effective_domain fShift := by
        simpa [hdomShift] using hyz_dom
      have hbase := h_strong.2 hy_dom hz_dom ha hb hab
      have hinner :
          inner ℝ v (a • y + b • z) = a * inner ℝ v y + b * inner ℝ v z := by
        rw [inner_add_right, inner_smul_right, inner_smul_right]
      calc
        (fShift (a • y + b • z)).toReal =
            (f (a • y + b • z)).toReal - inner ℝ v (a • y + b • z) := by
              exact htoRealShift hyz_shift
        _ ≤ a * (f y).toReal + b * (f z).toReal -
            a * b * ((σ / 2) * ‖y - z‖ ^ (2 : ℕ)) - inner ℝ v (a • y + b • z) := by
              exact sub_le_sub_right hbase _
        _ = a * ((fShift y).toReal) + b * ((fShift z).toReal) -
            a * b * ((σ / 2) * ‖y - z‖ ^ (2 : ℕ)) := by
              rw [htoRealShift hy, htoRealShift hz, hinner]
              ring
  -- The Euclidean subgradient inequality exactly says that `x` minimizes the shifted objective.
  have hminShift : IsMinOn fShift Set.univ x := by
    rw [isMinOn_univ_iff]
    intro y
    by_cases hy_dom : y ∈ effective_domain f
    · have hx_top : f x ≠ ⊤ := ne_of_lt hx_dom
      have hx_bot : f x ≠ ⊥ := h_problem.ne_bot x
      have hy_top : f y ≠ ⊤ := ne_of_lt hy_dom
      have hy_bot : f y ≠ ⊥ := h_problem.ne_bot y
      have hsub : (f y).toReal ≥ (f x).toReal + inner ℝ v (y - x) := hv_support y
      have hinner_sub : inner ℝ v (y - x) = inner ℝ v y - inner ℝ v x := by
        rw [inner_sub_right]
      have hreal :
          (f x).toReal - inner ℝ v x ≤ (f y).toReal - inner ℝ v y := by
        nlinarith [hsub, hinner_sub]
      have hcoe :
          ((((f x).toReal - inner ℝ v x : ℝ) : EReal) ≤
            (((f y).toReal - inner ℝ v y : ℝ) : EReal)) := EReal.coe_le_coe hreal
      simpa [fShift, EReal.coe_toReal hx_top hx_bot, EReal.coe_toReal hy_top hy_bot,
        EReal.coe_add, sub_eq_add_neg] using hcoe
    · have hy_top : f y = ⊤ := le_antisymm le_top (not_lt.mp hy_dom)
      simpa [fShift, hy_top] using (le_top : fShift x ≤ (⊤ : EReal))
  have hxShift_dom : x ∈ effective_domain fShift := by
    simpa [hdomShift] using hx_dom
  have hxStarShift_dom : xStar ∈ effective_domain fShift := by
    simpa [hdomShift] using hxStar_dom
  let φ : E → ℝ := fun y ↦ (fShift y).toReal
  have hminReal : ∀ {y : E}, y ∈ effective_domain fShift → φ x ≤ φ y := by
    intro y hy
    have hle : fShift x ≤ fShift y := (isMinOn_iff.mp hminShift) y (by simp)
    exact EReal.toReal_le_toReal hle (hne_bot_shift x) (ne_of_lt hy)
  let c : ℝ := (σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)
  have happrox :
      ∀ n : ℕ, φ xStar - φ x ≥ (n : ℝ) / (n + 1 : ℝ) * c := by
    intro n
    let a : ℝ := (n : ℝ) / (n + 1 : ℝ)
    let b : ℝ := 1 / (n + 1 : ℝ)
    have ha : 0 ≤ a := by
      positivity
    have hb : 0 ≤ b := by
      positivity
    have hab : a + b = 1 := by
      dsimp [a, b]
      field_simp
    have hm_dom : a • x + b • xStar ∈ effective_domain fShift :=
      hstrongShift.1 hxShift_dom hxStarShift_dom ha hb hab
    have hmin_mid : φ x ≤ φ (a • x + b • xStar) :=
      hminReal hm_dom
    have hstrong_mid :
        φ (a • x + b • xStar) ≤
          a * φ x + b * φ xStar - a * b * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) :=
      hstrongShift.2 hxShift_dom hxStarShift_dom ha hb hab
    have hcombine :
        φ x ≤ a * φ x + b * φ xStar - a * b * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) :=
      le_trans hmin_mid hstrong_mid
    have hb_pos : 0 < b := by
      positivity
    have hscaled :
        0 ≤ b * (φ xStar - φ x - a * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ))) := by
      have hcombine' : 0 ≤ a * φ x + b * φ xStar - a * b * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) - φ x := by
        linarith
      have hrewrite :
          a * φ x + b * φ xStar - a * b * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) - φ x =
            b * (φ xStar - φ x - a * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ))) := by
        have ha' : a = 1 - b := by
          linarith
        rw [ha']
        ring
      simpa [hrewrite] using hcombine'
    have hgoal_nonneg :
        0 ≤ φ xStar - φ x - a * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) := by
      by_contra hneg
      have hneg' : φ xStar - φ x - a * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) < 0 :=
        lt_of_not_ge hneg
      have : b * (φ xStar - φ x - a * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ))) < 0 := by
        exact mul_neg_of_pos_of_neg hb_pos hneg'
      linarith
    simpa [a, c] using hgoal_nonneg
  -- A contradiction argument upgrades the `n / (n + 1)` approximations to the full coefficient.
  have hquadReal :
      φ xStar ≥ φ x + c := by
    by_cases hxxStar : x = xStar
    · subst hxxStar
      simp [c]
    · have hc : 0 < c := by
        have hnorm_pos : 0 < ‖x - xStar‖ ^ (2 : ℕ) := by
          positivity [norm_pos_iff.mpr (sub_ne_zero.mpr hxxStar)]
        positivity
      by_contra hlt
      have hgap_pos : 0 < (c - (φ xStar - φ x)) / c := by
        have : 0 < c - (φ xStar - φ x) := by
          linarith
        exact div_pos this hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgap_pos
      have hfrac :
          (φ xStar - φ x) / c < (n : ℝ) / (n + 1 : ℝ) := by
        have hleft :
            1 - (1 / (n + 1 : ℝ)) > 1 - ((c - (φ xStar - φ x)) / c) := by
          linarith
        have hleft' : (n : ℝ) / (n + 1 : ℝ) = 1 - 1 / (n + 1 : ℝ) := by
          field_simp
          ring
        have hright' : 1 - ((c - (φ xStar - φ x)) / c) = (φ xStar - φ x) / c := by
          have hc_ne : (c : ℝ) ≠ 0 := ne_of_gt hc
          field_simp [hc_ne]
          ring
        linarith
      have hlt' : φ xStar - φ x < (n : ℝ) / (n + 1 : ℝ) * c := by
        have hmul := mul_lt_mul_of_pos_right hfrac hc
        have hc_ne : (c : ℝ) ≠ 0 := ne_of_gt hc
        field_simp [hc_ne] at hmul
        have hn1pos : 0 < (n + 1 : ℝ) := by
          positivity
        have hmul' : (φ xStar - φ x) * (n + 1 : ℝ) < (n : ℝ) * c := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
        have hdiv : φ xStar - φ x < ((n : ℝ) * c) / (n + 1 : ℝ) := by
          have hmul'' :
              (φ xStar - φ x) * (n + 1 : ℝ) <
                (((n : ℝ) * c) / (n + 1 : ℝ)) * (n + 1 : ℝ) := by
            simpa [hn1pos.ne', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul'
          have hdiv' :
              ((φ xStar - φ x) * (n + 1 : ℝ)) / (n + 1 : ℝ) <
                ((n : ℝ) * c) / (n + 1 : ℝ) := by
            exact (div_lt_iff₀ hn1pos).2 hmul''
          simpa [hn1pos.ne', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv'
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
      have hge' := happrox n
      linarith
  -- Rewrite the shifted inequality back to the original objective and isolate the desired term.
  have hquadReal' :
      fOpt - inner ℝ v xStar ≥
        (f x).toReal - inner ℝ v x + (σ / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    simpa [φ, c, htoRealShift hxStarShift_dom, htoRealShift hxShift_dom,
      optimal_point_toReal_eq_fOpt (f := f) (C := C) (XStar := XStar) (fOpt := fOpt)
        h_problem hxStar] using hquadReal
  have hinner_diff : inner ℝ v (x - xStar) = inner ℝ v x - inner ℝ v xStar := by
    rw [inner_sub_right]
  nlinarith [hquadReal', hinner_diff]

/-- Helper for Theorem 8.37: the oracle unbiasedness clause lifts the deterministic strong
support inequality to the conditional expectation subgradient almost surely. -/
lemma ae_condexp_inner_ge_gap_add_strong_term
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    ∀ᵐ ω ∂μ,
      ((f (x[n] ω : E)).toReal - fOpt) + (σ / 2) * ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) ≤
        inner ℝ
          (μ[fun ω ↦ g n (x[n] ω) ω |
            MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω)
          ((x[n] ω : E) - xStar) := by
  -- Specialize the deterministic support inequality to the random iterate and conditional mean.
  filter_upwards [h_oracle.unbiased n] with ω hω
  exact strongly_convex_support_at_optimal_point
    (h_problem := h_problem) (h_strong := h_strong) (hσ := hσ)
    ((x[n] ω).property) hxStar hω

/-- Helper for Theorem 8.37: for `k > 0`, the coefficients `2n / (k (k + 1))` form a simplex on
`{0, ..., k}`. -/
lemma strongly_convex_average_weights_form_simplex {k : ℕ} (hk : 0 < k) :
    (∀ n ∈ Finset.range (k + 1), 0 ≤ (2 : ℝ) * n / (k * (k + 1) : ℝ)) ∧
      Finset.sum (Finset.range (k + 1))
        (fun n ↦ (2 : ℝ) * n / (k * (k + 1) : ℝ)) = 1 := by
  -- The denominator is positive for `k > 0`, so every coefficient is nonnegative.
  have hkden : (k * (k + 1) : ℝ) ≠ 0 := by
    positivity
  have hsum_two_nat :
      (Finset.sum (Finset.range (k + 1)) fun n ↦ n) * 2 = k * (k + 1) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Finset.sum_range_id_mul_two (k + 1)
  have hsum_two :
      (Finset.sum (Finset.range (k + 1)) fun n ↦ (n : ℝ)) * 2 = k * (k + 1) := by
    simpa using congrArg (fun m : ℕ ↦ (m : ℝ)) hsum_two_nat
  constructor
  · intro n hn
    positivity
  · calc
      Finset.sum (Finset.range (k + 1)) (fun n ↦ (2 : ℝ) * n / (k * (k + 1) : ℝ)) =
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ ((2 : ℝ) / (k * (k + 1) : ℝ)) * n) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          ring_nf
      _ = ((2 : ℝ) / (k * (k + 1) : ℝ)) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ)) := by
        rw [Finset.mul_sum]
      _ = (((Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ))) * 2) /
          (k * (k + 1) : ℝ)) := by
        field_simp [hkden]
      _ = 1 := by
        rw [hsum_two]
        field_simp [hkden]

/-- Helper for Theorem 8.37: once the right factor is measurable with respect to the conditioning
sigma-algebra, the conditional expectation of the inner product pulls through that factor. -/
lemma condexp_inner_of_aestronglyMeasurable_right
    {m : MeasurableSpace Ω} {u v : Ω → E}
    (hv : AEStronglyMeasurable[m] v μ)
    (huv : Integrable (fun ω ↦ inner ℝ (u ω) (v ω)) μ)
    (hu : Integrable u μ) :
    μ[(fun ω ↦ inner ℝ (u ω) (v ω)) | m] =ᵐ[μ]
      fun ω ↦ inner ℝ (μ[u | m] ω) (v ω) := by
  -- This is exactly the Mathlib pull-out theorem specialized to the real inner product.
  simpa [innerSL_apply_apply] using
    (MeasureTheory.condExp_bilin_of_aestronglyMeasurable_right
      (μ := μ) (m := m) (B := innerSL ℝ) hv huv hu)

/-- Helper for Theorem 8.37: points already lying in the feasible set are fixed by the metric
projection onto `C`. -/
lemma metricProjection_eq_self_of_mem {y : E} (hy : y ∈ C) :
    (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed.isComplete
      h_problem.feasible_convex y : E) = y := by
  -- The projection variational inequality with test point `y` forces the residual to vanish.
  have hineq :=
    inner_sub_metricProjection_le_zero C h_problem.feasible_nonempty
      h_problem.feasible_closed.isComplete h_problem.feasible_convex y y hy
  have hnorm_sq_le_zero :
      ‖y -
          (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed.isComplete
            h_problem.feasible_convex y : E)‖ ^ (2 : ℕ) ≤ 0 := by
    simpa [real_inner_self_eq_norm_sq] using hineq
  have hnorm_zero :
      ‖y -
          (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed.isComplete
            h_problem.feasible_convex y : E)‖ = 0 := by
    nlinarith [sq_nonneg
      ‖y -
          (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed.isComplete
            h_problem.feasible_convex y : E)‖, hnorm_sq_le_zero]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)).symm

/-- Helper for Theorem 8.37: each stochastic iterate is almost surely strongly measurable. -/
lemma stochastic_iterate_aestronglyMeasurable
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    (n : ℕ) :
    AEStronglyMeasurable (fun ω ↦ (x[n] ω : E)) μ := by
  induction n with
  | zero =>
      -- The initial iterate is the constant feasible starting point.
      simpa [stochastic_projected_subgradient_method_zero] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω ↦ (x0 : E)) μ)
  | succ n ih =>
      let P : E → E := fun y ↦
        (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed.isComplete
          h_problem.feasible_convex y : E)
      have hg :
          AEStronglyMeasurable (fun ω ↦ g n (x[n] ω) ω) μ :=
        (h_oracle.integrable_subgradient n).aestronglyMeasurable
      have hupdate :
          AEStronglyMeasurable
            (fun ω ↦ (x[n] ω : E) - t n • g n (x[n] ω) ω) μ :=
        ih.sub (hg.const_smul (t n))
      have hproj :
          AEStronglyMeasurable
            (fun ω ↦ P ((x[n] ω : E) - t n • g n (x[n] ω) ω)) μ :=
        (metricProjection_nonexpansive C h_problem.feasible_nonempty h_problem.feasible_closed
          h_problem.feasible_convex).continuous.comp_aestronglyMeasurable hupdate
      -- Rewrite the recursive update into the measurable projection map applied above.
      refine hproj.congr ?_
      filter_upwards with ω
      simpa [P] using congrArg (fun z : C ↦ (z : E))
        (stochastic_projected_subgradient_method_succ
          (C := C) (hC_nonempty := h_problem.feasible_nonempty)
          (hC_closed := h_problem.feasible_closed) (hC_convex := h_problem.feasible_convex)
          (g := g) (t := t) (x0 := x0) n ω)

/-- Helper for Theorem 8.37: one stochastic projection step has a coarse quadratic growth bound,
used only to bootstrap square-integrability of the iterates. -/
lemma projected_sqdist_step_growth_bound
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    ∀ ω,
      ‖(x[n + 1] ω : E) - xStar‖ ^ (2 : ℕ) ≤
        2 * ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) +
          2 * (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
  intro ω
  let P : E → E := fun y ↦
    (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed.isComplete
      h_problem.feasible_convex y : E)
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hfix : P xStar = xStar := by
    simpa [P] using
      metricProjection_eq_self_of_mem (h_problem := h_problem) hxStar_data.1
  have hstep :
      (x[n + 1] ω : E) =
        P ((x[n] ω : E) - t n • g n (x[n] ω) ω) := by
    simpa [P] using congrArg (fun z : C ↦ (z : E))
      (stochastic_projected_subgradient_method_succ
        (C := C) (hC_nonempty := h_problem.feasible_nonempty)
        (hC_closed := h_problem.feasible_closed) (hC_convex := h_problem.feasible_convex)
        (g := g) (t := t) (x0 := x0) n ω)
  have hnonexp :
      ‖(x[n + 1] ω : E) - xStar‖ ≤
        ‖((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar‖ := by
    -- Firm nonexpansiveness against the fixed feasible point `xStar` yields the norm contraction.
    have hfirm :
        inner ℝ ((x[n + 1] ω : E) - xStar)
            (((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar) ≥
          ‖(x[n + 1] ω : E) - xStar‖ ^ (2 : ℕ) := by
      simpa [P, hstep, hfix, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        metricProjection_firmly_nonexpansive C h_problem.feasible_nonempty
          h_problem.feasible_closed h_problem.feasible_convex
          (((x[n] ω : E) - t n • g n (x[n] ω) ω)) xStar
    have habs :
        inner ℝ ((x[n + 1] ω : E) - xStar)
            (((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar) ≤
          ‖(x[n + 1] ω : E) - xStar‖ *
            ‖((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar‖ := by
      exact le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
    nlinarith [hfirm, habs, norm_nonneg ((x[n + 1] ω : E) - xStar),
      norm_nonneg (((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar)]
  have htriangle :
      ‖((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar‖ ≤
        ‖(x[n] ω : E) - xStar‖ + ‖t n • g n (x[n] ω) ω‖ := by
    -- Rewrite the update vector as the iterate offset minus the stochastic step.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      norm_sub_le ((x[n] ω : E) - xStar) (t n • g n (x[n] ω) ω)
  have hnonexp_sq :
      ‖(x[n + 1] ω : E) - xStar‖ ^ (2 : ℕ) ≤
        ‖((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar‖ ^ (2 : ℕ) := by
    nlinarith [hnonexp, norm_nonneg ((x[n + 1] ω : E) - xStar),
      norm_nonneg (((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar)]
  have htriangle_sq :
      ‖((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar‖ ^ (2 : ℕ) ≤
        (‖(x[n] ω : E) - xStar‖ + ‖t n • g n (x[n] ω) ω‖) ^ (2 : ℕ) := by
    nlinarith [htriangle, norm_nonneg (((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar),
      add_nonneg (norm_nonneg ((x[n] ω : E) - xStar))
        (norm_nonneg (t n • g n (x[n] ω) ω))]
  have hsq_sum :
      (‖(x[n] ω : E) - xStar‖ + ‖t n • g n (x[n] ω) ω‖) ^ (2 : ℕ) ≤
        2 * ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) +
          2 * ‖t n • g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (‖(x[n] ω : E) - xStar‖ - ‖t n • g n (x[n] ω) ω‖)]
  calc
    ‖(x[n + 1] ω : E) - xStar‖ ^ (2 : ℕ) ≤
        ‖((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar‖ ^ (2 : ℕ) := hnonexp_sq
    _ ≤ (‖(x[n] ω : E) - xStar‖ + ‖t n • g n (x[n] ω) ω‖) ^ (2 : ℕ) := htriangle_sq
    _ ≤ 2 * ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) +
          2 * ‖t n • g n (x[n] ω) ω‖ ^ (2 : ℕ) := hsq_sum
    _ =
        2 * ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) +
          2 * (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
        have habs_sq :
            (|t n| * ‖g n (x[n] ω) ω‖) ^ (2 : ℕ) =
              (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
          calc
            (|t n| * ‖g n (x[n] ω) ω‖) ^ (2 : ℕ) =
                |t n| ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by ring
            _ = (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
                rw [sq_abs]
        rw [norm_smul, Real.norm_eq_abs, habs_sq]
        ring

/-- Helper for Theorem 8.37: the squared distance to the optimal point is integrable at every
iterate, obtained from the coarse quadratic growth recursion. -/
lemma stochastic_iterate_sqdist_integrable
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    Integrable (fun ω ↦ ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ)) μ := by
  induction n with
  | zero =>
      -- The initial squared distance is a constant random variable.
      simpa [stochastic_projected_subgradient_method_zero] using
        (integrable_const (‖(x0 : E) - xStar‖ ^ (2 : ℕ)) : Integrable (fun _ : Ω ↦
          ‖(x0 : E) - xStar‖ ^ (2 : ℕ)) μ)
  | succ n ih =>
      have hbound_int :
          Integrable
            (fun ω ↦
              2 * ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) +
                2 * (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) μ := by
        -- The rough growth bound is controlled by the previous square distance plus the oracle
        -- second-moment bound.
        exact (ih.const_mul 2).add ((h_oracle.integrable_sqnorm_subgradient n).const_mul
          (2 * (t n) ^ (2 : ℕ)))
      have hmeas :
          AEStronglyMeasurable (fun ω ↦ ‖(x[n + 1] ω : E) - xStar‖ ^ (2 : ℕ)) μ := by
        -- Measurability comes from the iterate measurability established above and the continuity
        -- of the squared norm.
        exact
          ((continuous_norm.comp_aestronglyMeasurable
              ((stochastic_iterate_aestronglyMeasurable
                (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle (n + 1)).sub
                  aestronglyMeasurable_const)).pow 2)
      refine Integrable.mono' hbound_int hmeas ?_
      filter_upwards with ω
      have hgrowth :=
        projected_sqdist_step_growth_bound
          (h_problem := h_problem) (g := g) (t := t) (x0 := x0) hxStar n ω
      have hnonneg : 0 ≤ ‖(x[n + 1] ω : E) - xStar‖ ^ (2 : ℕ) := by positivity
      simpa [abs_of_nonneg hnonneg] using hgrowth

/-- Helper for Theorem 8.37: the pathwise projection step satisfies the exact squared-distance
expansion from equation `(8.55)` before conditioning. -/
lemma projected_sqdist_step_pointwise
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    ∀ ω,
      ‖(x[n + 1] ω : E) - xStar‖ ^ (2 : ℕ) ≤
        ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) -
          2 * t n * inner ℝ (g n (x[n] ω) ω) ((x[n] ω : E) - xStar) +
          (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
  intro ω
  let P : E → E := fun y ↦
    (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed.isComplete
      h_problem.feasible_convex y : E)
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hfix : P xStar = xStar := by
    simpa [P] using
      metricProjection_eq_self_of_mem (h_problem := h_problem) hxStar_data.1
  have hstep :
      (x[n + 1] ω : E) =
        P ((x[n] ω : E) - t n • g n (x[n] ω) ω) := by
    simpa [P] using congrArg (fun z : C ↦ (z : E))
      (stochastic_projected_subgradient_method_succ
        (C := C) (hC_nonempty := h_problem.feasible_nonempty)
        (hC_closed := h_problem.feasible_closed) (hC_convex := h_problem.feasible_convex)
        (g := g) (t := t) (x0 := x0) n ω)
  have hnonexp :
      ‖(x[n + 1] ω : E) - xStar‖ ≤
        ‖((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar‖ := by
    -- Firm nonexpansiveness against `xStar` again gives the exact one-step norm contraction.
    have hfirm :
        inner ℝ ((x[n + 1] ω : E) - xStar)
            (((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar) ≥
          ‖(x[n + 1] ω : E) - xStar‖ ^ (2 : ℕ) := by
      simpa [P, hstep, hfix, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        metricProjection_firmly_nonexpansive C h_problem.feasible_nonempty
          h_problem.feasible_closed h_problem.feasible_convex
          (((x[n] ω : E) - t n • g n (x[n] ω) ω)) xStar
    have habs :
        inner ℝ ((x[n + 1] ω : E) - xStar)
            (((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar) ≤
          ‖(x[n + 1] ω : E) - xStar‖ *
            ‖((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar‖ := by
      exact le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
    nlinarith [hfirm, habs, norm_nonneg ((x[n + 1] ω : E) - xStar),
      norm_nonneg (((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar)]
  have hnonexp_sq :
      ‖(x[n + 1] ω : E) - xStar‖ ^ (2 : ℕ) ≤
        ‖((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar‖ ^ (2 : ℕ) := by
    nlinarith [hnonexp, norm_nonneg ((x[n + 1] ω : E) - xStar),
      norm_nonneg (((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar)]
  -- Expand the exact squared norm of the iterate offset after one stochastic step.
  calc
    ‖(x[n + 1] ω : E) - xStar‖ ^ (2 : ℕ) ≤
        ‖((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar‖ ^ (2 : ℕ) := hnonexp_sq
    _ = ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) -
          2 * t n * inner ℝ (g n (x[n] ω) ω) ((x[n] ω : E) - xStar) +
          (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
        have hrewrite :
            ((x[n] ω : E) - t n • g n (x[n] ω) ω) - xStar =
              ((x[n] ω : E) - xStar) - t n • g n (x[n] ω) ω := by
          abel
        have habs_sq :
            (|t n| * ‖g n (x[n] ω) ω‖) ^ (2 : ℕ) =
              (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
          calc
            (|t n| * ‖g n (x[n] ω) ω‖) ^ (2 : ℕ) =
                |t n| ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by ring
            _ = (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
                rw [sq_abs]
        rw [hrewrite, norm_sub_sq_real]
        rw [real_inner_smul_right, real_inner_comm, norm_smul, Real.norm_eq_abs, habs_sq]
        ring

/-- Helper for Theorem 8.37: composing the iterate with a continuous scalar observable stays
measurable with respect to the sigma-algebra generated by that iterate, so conditional expectation
fixes it as soon as the generated sigma-algebra is known to sit inside the ambient one. -/
lemma condexp_iterate_scalar_comp_eq_self
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    {φ : E → ℝ} (hφ : Continuous φ) (n : ℕ)
    (hm :
      MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance ≤ ‹MeasurableSpace Ω›)
    (h_int : Integrable (fun ω ↦ φ ((x[n] ω : E))) μ) :
    μ[(fun ω ↦ φ ((x[n] ω : E))) |
        MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] =ᵐ[μ]
      fun ω ↦ φ ((x[n] ω : E)) := by
  have hx_ae : AEMeasurable (fun ω ↦ (x[n] ω : E)) μ := by
    exact
      (stochastic_iterate_aestronglyMeasurable
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle n).aemeasurable
  have hcomp_meas :
      AEStronglyMeasurable[MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance]
        (fun ω ↦ φ ((x[n] ω : E))) μ := by
    -- Re-express the scalar observable as a composition through the iterate-generated sigma
    -- algebra, so the conditional expectation can be identified with the observable itself.
    simpa [Function.comp] using
      (hφ.aestronglyMeasurable.comp_ae_measurable' hx_ae)
  simpa using
    (MeasureTheory.condExp_of_aestronglyMeasurable'
      (m := MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance)
      (m₀ := inferInstance) hm hcomp_meas h_int)

/-- Helper for Theorem 8.37: the iterate offset `x[n] - xStar` is almost surely strongly
measurable with respect to the sigma-algebra generated by `x[n]`. -/
lemma iterate_offset_aestronglyMeasurable_comap
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    (n : ℕ)
    (hm :
      MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance ≤ ‹MeasurableSpace Ω›)
    {xStar : E} :
    AEStronglyMeasurable[
        MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance]
      (fun ω ↦ (x[n] ω : E) - xStar) μ := by
  let offset : Ω → E := fun ω ↦ (x[n] ω : E) - xStar
  have hoffset_ae : AEStronglyMeasurable offset μ := by
    -- The iterate is a.e. strongly measurable in the ambient space, and translating by `xStar`
    -- preserves that ambient measurability.
    exact
      (stochastic_iterate_aestronglyMeasurable
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle n).sub
        aestronglyMeasurable_const
  have hmeas_offset :
      Measurable[
        MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] offset := by
    -- Over the pullback sigma-algebra, the iterate map is measurable by definition.
    have hx_meas :
        Measurable[
          MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance]
          (fun ω ↦ (x[n] ω : E)) :=
      measurable_iff_comap_le.mpr le_rfl
    exact (continuous_id.sub continuous_const).measurable.comp hx_meas
  rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 hoffset_ae).2 with
    ⟨s, hs_sep, hs_ae⟩
  obtain ⟨s₀, hs₀_subset, hs₀_count, hs_subset_closure⟩ :=
    hs_sep.exists_countable_dense_subset
  have hs_closure_ae : ∀ᵐ ω ∂μ, offset ω ∈ closure s₀ := by
    filter_upwards [hs_ae] with ω hω
    exact hs_subset_closure hω
  have hs_meas :
      MeasurableSet[
        MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance]
        {ω | offset ω ∈ closure s₀} := by
    exact hmeas_offset isClosed_closure.measurableSet
  have hs_trim : ∀ᵐ ω ∂μ.trim hm, offset ω ∈ closure s₀ := by
    have hs_meas_compl :
        MeasurableSet[
          MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance]
          {ω | offset ω ∉ closure s₀} := hs_meas.compl
    rw [ae_iff]
    rw [trim_measurableSet_eq hm hs_meas_compl]
    simpa [ae_iff] using hs_closure_ae
  have htrim :
      @AEStronglyMeasurable Ω E _ 
        (MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance)
        (MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance)
        offset (μ.trim hm) := by
    -- On the trimmed measure, measurability in the pullback sigma-algebra plus the ambient
    -- a.e. separable range gives the desired relative strong measurability.
    exact
      (aestronglyMeasurable_iff_aemeasurable_separable).2
        ⟨hmeas_offset.aemeasurable, ⟨closure s₀, hs₀_count.isSeparable.closure, hs_trim⟩⟩
  exact MeasureTheory.AEStronglyMeasurable.of_trim hm htrim

/-- Helper for Theorem 8.37: conditioning on the sigma-algebra generated by `x[n]` pulls the
iterate offset out of the inner product. -/
lemma condexp_inner_iterate_offset_comap_pullout
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    (n : ℕ)
    (hm :
      MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance ≤ ‹MeasurableSpace Ω›)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    μ[(fun ω ↦ inner ℝ (g n (x[n] ω) ω) ((x[n] ω : E) - xStar)) |
        MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] =ᵐ[μ]
      fun ω ↦
        inner ℝ
          (μ[fun ω ↦ g n (x[n] ω) ω |
            MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω)
          ((x[n] ω : E) - xStar) := by
  let gFun : Ω → E := fun ω ↦ g n (x[n] ω) ω
  let offset : Ω → E := fun ω ↦ (x[n] ω : E) - xStar
  have hg_ae : AEStronglyMeasurable gFun μ := by
    -- The oracle integrability hypothesis already supplies almost-everywhere measurability of the
    -- sampled stochastic subgradient.
    exact (h_oracle.integrable_subgradient n).aestronglyMeasurable
  have hoffset_ae : AEStronglyMeasurable offset μ := by
    -- The iterate itself is a.e. strongly measurable, and translating by `xStar` preserves that.
    exact
      (stochastic_iterate_aestronglyMeasurable
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle n).sub
        aestronglyMeasurable_const
  have hg_memLp : MemLp gFun 2 μ := by
    -- The oracle's squared-norm integrability is exactly the `L²` membership criterion.
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hg_ae).2
      (h_oracle.integrable_sqnorm_subgradient n)
  have hoffset_memLp : MemLp offset 2 μ := by
    -- The offset has integrable squared norm by the iterate square-distance bootstrap.
    simpa [offset] using
      (MeasureTheory.memLp_two_iff_integrable_sq_norm hoffset_ae).2
        (stochastic_iterate_sqdist_integrable
          (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle hxStar n)
  have hinner_lp :
      Integrable
        (fun ω ↦ inner ℝ ((hg_memLp.toLp gFun) ω) ((hoffset_memLp.toLp offset) ω)) μ := by
    -- The pointwise inner product of two `L²` functions is integrable.
    exact MeasureTheory.L2.integrable_inner (hg_memLp.toLp gFun) (hoffset_memLp.toLp offset)
  have hinner_eq :
      (fun ω ↦ inner ℝ ((hg_memLp.toLp gFun) ω) ((hoffset_memLp.toLp offset) ω)) =ᵐ[μ]
        fun ω ↦ inner ℝ (g n (x[n] ω) ω) ((x[n] ω : E) - xStar) := by
    filter_upwards [MemLp.coeFn_toLp hg_memLp, MemLp.coeFn_toLp hoffset_memLp] with ω hg hoffset
    simp [gFun, offset, hg, hoffset]
  have hinner_int :
      Integrable (fun ω ↦ inner ℝ (g n (x[n] ω) ω) ((x[n] ω : E) - xStar)) μ := by
    exact (integrable_congr hinner_eq).1 hinner_lp
  -- Pull the measurable iterate offset through the conditional expectation in one step.
  exact condexp_inner_of_aestronglyMeasurable_right
    (μ := μ)
    (m := MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance)
    (u := gFun) (v := offset)
    (iterate_offset_aestronglyMeasurable_comap
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle n hm)
    hinner_int
    (h_oracle.integrable_subgradient n)

/-- Helper for Theorem 8.37: the inner-product term in the projected-square expansion is
integrable, because both the stochastic subgradient and the iterate offset belong to `L²`. -/
lemma integrable_inner_iterate_offset
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    (n : ℕ)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    Integrable (fun ω ↦ inner ℝ (g n (x[n] ω) ω) ((x[n] ω : E) - xStar)) μ := by
  let gFun : Ω → E := fun ω ↦ g n (x[n] ω) ω
  let offset : Ω → E := fun ω ↦ (x[n] ω : E) - xStar
  have hg_ae : AEStronglyMeasurable gFun μ := by
    -- The oracle integrability hypothesis already supplies almost-everywhere measurability of the
    -- sampled stochastic subgradient.
    exact (h_oracle.integrable_subgradient n).aestronglyMeasurable
  have hoffset_ae : AEStronglyMeasurable offset μ := by
    -- The iterate itself is a.e. strongly measurable, and translating by `xStar` preserves that.
    exact
      (stochastic_iterate_aestronglyMeasurable
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle n).sub
        aestronglyMeasurable_const
  have hg_memLp : MemLp gFun 2 μ := by
    -- The oracle's squared-norm integrability is exactly the `L²` membership criterion.
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hg_ae).2
      (h_oracle.integrable_sqnorm_subgradient n)
  have hoffset_memLp : MemLp offset 2 μ := by
    -- The offset has integrable squared norm by the iterate square-distance bootstrap.
    simpa [offset] using
      (MeasureTheory.memLp_two_iff_integrable_sq_norm hoffset_ae).2
        (stochastic_iterate_sqdist_integrable
          (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle hxStar n)
  have hinner_lp :
      Integrable
        (fun ω ↦ inner ℝ ((hg_memLp.toLp gFun) ω) ((hoffset_memLp.toLp offset) ω)) μ := by
    -- The pointwise inner product of two `L²` functions is integrable.
    exact MeasureTheory.L2.integrable_inner (hg_memLp.toLp gFun) (hoffset_memLp.toLp offset)
  have hinner_eq :
      (fun ω ↦ inner ℝ ((hg_memLp.toLp gFun) ω) ((hoffset_memLp.toLp offset) ω)) =ᵐ[μ]
        fun ω ↦ inner ℝ (g n (x[n] ω) ω) ((x[n] ω : E) - xStar) := by
    filter_upwards [MemLp.coeFn_toLp hg_memLp, MemLp.coeFn_toLp hoffset_memLp] with ω hg hoffset
    simp [gFun, offset, hg, hoffset]
  exact (integrable_congr hinner_eq).1 hinner_lp

/-- Helper for Theorem 8.37: under the measurable `comap(x[n])` branch, conditioning the raw
right-hand side of the projected-square expansion normalizes exactly into the target form with the
inner-product factor pulled through the conditional expectation. -/
lemma condexp_projected_sqdist_step_rhs_eq
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    (n : ℕ)
    (hm :
      MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance ≤ ‹MeasurableSpace Ω›)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    μ[(fun ω ↦
        ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) -
          2 * t n * inner ℝ (g n (x[n] ω) ω) ((x[n] ω : E) - xStar) +
          (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
        MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] =ᵐ[μ]
      fun ω ↦
        ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) -
          2 * t n *
            inner ℝ
              (μ[fun ω ↦ g n (x[n] ω) ω |
                MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω)
              ((x[n] ω : E) - xStar) +
          (t n) ^ (2 : ℕ) *
            μ[(fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
              MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω := by
  let sqdist : Ω → ℝ := fun ω ↦ ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ)
  let innerTerm : Ω → ℝ := fun ω ↦ inner ℝ (g n (x[n] ω) ω) ((x[n] ω : E) - xStar)
  let sqnorm : Ω → ℝ := fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)
  have hsqdist_int : Integrable sqdist μ := by
    simpa [sqdist] using
      stochastic_iterate_sqdist_integrable
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle hxStar n
  have hinner_int : Integrable innerTerm μ := by
    simpa [innerTerm] using
      integrable_inner_iterate_offset
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle n hxStar
  have hsqnorm_int : Integrable sqnorm μ := by
    simpa [sqnorm] using h_oracle.integrable_sqnorm_subgradient n
  have hsqdist_ce :
      μ[sqdist | MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] =ᵐ[μ]
        sqdist := by
    -- The squared-distance term depends only on the current iterate, so conditioning fixes it.
    exact condexp_iterate_scalar_comp_eq_self
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle
      (φ := fun y ↦ ‖y - xStar‖ ^ (2 : ℕ))
      ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2)
      n hm hsqdist_int
  have hinner_ce :
      μ[innerTerm | MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] =ᵐ[μ]
        fun ω ↦
          inner ℝ
            (μ[fun ω ↦ g n (x[n] ω) ω |
              MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω)
            ((x[n] ω : E) - xStar) := by
    -- Pull the iterate offset through the conditional expectation in the inner-product term.
    simpa [innerTerm] using
      condexp_inner_iterate_offset_comap_pullout
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle n hm hxStar
  have hscaled_inner_ce :
      μ[(fun ω ↦ (2 * t n) * innerTerm ω) |
          MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] =ᵐ[μ]
        fun ω ↦
          (2 * t n) *
            inner ℝ
              (μ[fun ω ↦ g n (x[n] ω) ω |
                MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω)
              ((x[n] ω : E) - xStar) := by
    -- The deterministic scalar `2 * t n` commutes with conditional expectation.
    refine (MeasureTheory.condExp_smul (2 * t n) innerTerm
      (MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance)).trans ?_
    filter_upwards [hinner_ce] with ω hω
    simp [hω]
  have hscaled_sqnorm_ce :
      μ[(fun ω ↦ (t n) ^ (2 : ℕ) * sqnorm ω) |
          MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] =ᵐ[μ]
        fun ω ↦
          (t n) ^ (2 : ℕ) *
            μ[sqnorm | MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω := by
    -- The squared-norm term is also just a deterministic scalar multiple.
    refine (MeasureTheory.condExp_smul ((t n) ^ (2 : ℕ)) sqnorm
      (MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance)).trans ?_
    filter_upwards with ω
    simp
  have hsub_ce :
      μ[(fun ω ↦ sqdist ω - (2 * t n) * innerTerm ω) |
          MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] =ᵐ[μ]
        fun ω ↦
          sqdist ω -
            (2 * t n) *
              inner ℝ
                (μ[fun ω ↦ g n (x[n] ω) ω |
                  MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω)
                ((x[n] ω : E) - xStar) := by
    -- First normalize the difference `sqdist - 2 t_n innerTerm`.
    exact (MeasureTheory.condExp_sub hsqdist_int (hinner_int.const_mul (2 * t n))
      (MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance)).trans
        (hsqdist_ce.sub hscaled_inner_ce)
  -- Combine the normalized difference with the conditioned squared-norm term.
  calc
    μ[(fun ω ↦
        ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) -
          2 * t n * inner ℝ (g n (x[n] ω) ω) ((x[n] ω : E) - xStar) +
          (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
        MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] =ᵐ[μ]
      μ[(fun ω ↦ sqdist ω - (2 * t n) * innerTerm ω + (t n) ^ (2 : ℕ) * sqnorm ω) |
        MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] := by
          exact MeasureTheory.condExp_congr_ae <| Filter.Eventually.of_forall fun ω ↦ by
            simp [sqdist, innerTerm, sqnorm]
    _ =ᵐ[μ]
      (fun ω ↦
        sqdist ω -
          (2 * t n) *
            inner ℝ
              (μ[fun ω ↦ g n (x[n] ω) ω |
                MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω)
              ((x[n] ω : E) - xStar) +
          (t n) ^ (2 : ℕ) *
            μ[sqnorm | MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω) := by
          exact (MeasureTheory.condExp_add
            (hsqdist_int.sub (hinner_int.const_mul (2 * t n)))
            (hsqnorm_int.const_mul ((t n) ^ (2 : ℕ)))
            _).trans
            (hsub_ce.add hscaled_sqnorm_ce)
    _ =ᵐ[μ]
      fun ω ↦
        ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) -
          2 * t n *
            inner ℝ
              (μ[fun ω ↦ g n (x[n] ω) ω |
                MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω)
              ((x[n] ω : E) - xStar) +
          (t n) ^ (2 : ℕ) *
            μ[(fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
              MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω := by
          exact Filter.Eventually.of_forall fun ω ↦ by simp [sqdist, sqnorm]

/-- Helper for Theorem 8.37: the conditional projected-square estimate at the sigma-algebra
generated by `x[n]`. This is the source-faithful `(8.55) + (8.u196)` bridge before any
integration or telescoping. -/
lemma conditional_projected_sqdist_le_of_strongly_convex_support
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    ∀ᵐ ω ∂μ,
      μ[(fun ω ↦ ‖(x[n + 1] ω : E) - xStar‖ ^ (2 : ℕ)) |
          MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω ≤
        ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) -
          2 * t n *
            (((f (x[n] ω : E)).toReal - fOpt) +
              (σ / 2) * ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ)) +
          (t n) ^ (2 : ℕ) *
            μ[(fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
              MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω := by
  let sqdistNext : Ω → ℝ := fun ω ↦ ‖(x[n + 1] ω : E) - xStar‖ ^ (2 : ℕ)
  let rawRhs : Ω → ℝ := fun ω ↦
    ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) -
      2 * t n * inner ℝ (g n (x[n] ω) ω) ((x[n] ω : E) - xStar) +
      (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)
  have hsqdistNext_int : Integrable sqdistNext μ := by
    simpa [sqdistNext] using
      stochastic_iterate_sqdist_integrable
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle hxStar (n + 1)
  have hinner_int :
      Integrable (fun ω ↦ inner ℝ (g n (x[n] ω) ω) ((x[n] ω : E) - xStar)) μ := by
    exact integrable_inner_iterate_offset
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle n hxStar
  have hrawRhs_int : Integrable rawRhs μ := by
    -- Every term in the raw pathwise square expansion is integrable.
    simpa [rawRhs] using
      (stochastic_iterate_sqdist_integrable
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle hxStar n).sub
        (hinner_int.const_mul (2 * t n)) |>.add
        ((h_oracle.integrable_sqnorm_subgradient n).const_mul ((t n) ^ (2 : ℕ)))
  have hmono :
      μ[sqdistNext | MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ≤ᵐ[μ]
        μ[rawRhs | MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] := by
    -- Condition the pointwise projection inequality from `projected_sqdist_step_pointwise`.
    refine MeasureTheory.condExp_mono hsqdistNext_int hrawRhs_int ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [sqdistNext, rawRhs] using
        projected_sqdist_step_pointwise
          (h_problem := h_problem) (g := g) (t := t) (x0 := x0) hxStar n ω
  have ht_nonneg : 0 ≤ t n := by
    rw [h_stepsize n]
    positivity
  by_cases hm :
      MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance ≤ ‹MeasurableSpace Ω›
  · have hrhs_eq :=
      condexp_projected_sqdist_step_rhs_eq
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle n hm hxStar
    have hsupport :=
      ae_condexp_inner_ge_gap_add_strong_term
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        (h_strong := h_strong) hσ h_oracle hxStar n
    -- In the measurable branch, the new rewrite lemma reduces everything to one monotonicity step.
    filter_upwards [hmono, hrhs_eq, hsupport] with ω hωmono hωrhs hωsupport
    have hstep :
        μ[sqdistNext | MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω ≤
          ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) -
            2 * t n *
              inner ℝ
                (μ[fun ω ↦ g n (x[n] ω) ω |
                  MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω)
                ((x[n] ω : E) - xStar) +
            (t n) ^ (2 : ℕ) *
              μ[(fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
                MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω := by
      exact hωrhs ▸ hωmono
    have hreplace :
        ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) -
            2 * t n *
              inner ℝ
                (μ[fun ω ↦ g n (x[n] ω) ω |
                  MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω)
                ((x[n] ω : E) - xStar) +
            (t n) ^ (2 : ℕ) *
              μ[(fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
                MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω ≤
          ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) -
            2 * t n *
              (((f (x[n] ω : E)).toReal - fOpt) +
                (σ / 2) * ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ)) +
            (t n) ^ (2 : ℕ) *
              μ[(fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
                MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] ω := by
      nlinarith
    exact le_trans hstep hreplace
  · have hsqdistNext_zero :
      μ[sqdistNext | MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] = 0 := by
      exact MeasureTheory.condExp_of_not_le hm
    have hsqnorm_zero :
      μ[(fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
          MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] = 0 := by
      exact MeasureTheory.condExp_of_not_le hm
    have hcond_zero :
      μ[fun ω ↦ g n (x[n] ω) ω |
          MeasurableSpace.comap (fun ω ↦ (x[n] ω : E)) inferInstance] = 0 := by
      exact MeasureTheory.condExp_of_not_le hm
    have hsupport :=
      ae_condexp_inner_ge_gap_add_strong_term
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        (h_strong := h_strong) hσ h_oracle hxStar n
    -- In the non-measurable branch every conditional expectation is definitionally zero.
    filter_upwards [hsupport] with ω hωsupport
    have hsupport_zero :
        ((f (x[n] ω : E)).toReal - fOpt) +
            (σ / 2) * ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) ≤ 0 := by
      simpa [hcond_zero] using hωsupport
    have htarget_nonneg :
        0 ≤
          ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) -
            2 * t n *
              (((f (x[n] ω : E)).toReal - fOpt) +
                (σ / 2) * ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ)) := by
      have hsq_nonneg : 0 ≤ ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) := by positivity
      nlinarith
    simpa [sqdistNext, hsqdistNext_zero, hsqnorm_zero] using htarget_nonneg

/-- Helper for Theorem 8.37: the integrated one-step inequality in the exact `(8.u199)` form
after substituting the stepsize `t_n = 2 / (σ (n + 1))`. -/
lemma expected_one_step_gap_le_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    ((∫ ω, (f (x[n] ω : E)).toReal ∂μ) - fOpt) ≤
      (σ * (n - 1 : ℝ) / 4) * (∫ ω, ‖(x[n] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) -
        (σ * (n + 1 : ℝ) / 4) * (∫ ω, ‖(x[n + 1] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) +
        h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)) := by
  -- TODO: integrate `conditional_projected_sqdist_le_of_strongly_convex_support` with
  -- `integral_condExp`, use `h_oracle.sqnorm_condexp_le n`, and rewrite the stepsize coefficients
  -- into the displayed `σ (n ± 1) / 4` form.
  sorry

/-- Helper for Theorem 8.37: the weighted telescope keeps the negative squared-distance tail before
it is discarded in the final bound. -/
lemma weighted_expected_gap_sum_with_tail_le_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    Finset.sum (Finset.range (k + 1))
        (fun n ↦ (n : ℝ) * (((∫ ω, (f (x[n] ω : E)).toReal ∂μ) - fOpt))) ≤
      -(σ * k * (k + 1 : ℝ) / 4) * (∫ ω, ‖(x[k + 1] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) +
        h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ := by
  -- Induct on the prefix length so the squared-distance coefficients cancel one step at a time.
  induction k with
  | zero =>
      -- The `n = 0` weighted term vanishes, so the tail form is exact at the base case.
      simp
  | succ k hk =>
      have hstep :=
        expected_one_step_gap_le_of_strongly_convex_stepsize
          (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
          (h_strong := h_strong) (hσ := hσ) (h_stepsize := h_stepsize)
          (h_oracle := h_oracle) hxStar (k + 1)
      have hk_sub : (((k + 1 : ℕ) : ℝ) - 1) = k := by
        norm_num
      have hk_add : (k : ℝ) + 1 + 1 = k + 2 := by
        ring
      have hstep' :
          ((∫ ω, (f (x[k + 1] ω : E)).toReal ∂μ) - fOpt) ≤
            (σ * k / 4) * (∫ ω, ‖(x[k + 1] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) -
              (σ * (k + 2 : ℝ) / 4) *
                (∫ ω, ‖(x[k + 2] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) +
              h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (k + 2 : ℝ)) := by
        -- Rewrite the `n = k + 1` one-step estimate into the coefficient form used by the
        -- telescope.
        simpa [Nat.add_assoc, hk_sub, hk_add, sub_eq_add_neg] using hstep
      have hstep_mul :=
        mul_le_mul_of_nonneg_left hstep' (show 0 ≤ (k + 1 : ℝ) by positivity)
      have hstep_mul' :
          ((k + 1 : ℝ) * (((∫ ω, (f (x[k + 1] ω : E)).toReal ∂μ) - fOpt))) ≤
            (σ * k * (k + 1 : ℝ) / 4) *
                (∫ ω, ‖(x[k + 1] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) -
              (σ * (k + 1) * (k + 2 : ℝ) / 4) *
                (∫ ω, ‖(x[k + 2] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) +
              h_oracle.L_tilde_f ^ (2 : ℕ) * ((k + 1 : ℝ) / (σ * (k + 2 : ℝ))) := by
        -- This is exactly the one-step estimate at index `k + 1`, multiplied by `k + 1`.
        have htmp := hstep_mul
        ring_nf at htmp ⊢
        simpa using htmp
      have hfrac_le :
          h_oracle.L_tilde_f ^ (2 : ℕ) * ((k + 1 : ℝ) / (σ * (k + 2 : ℝ))) ≤
            h_oracle.L_tilde_f ^ (2 : ℕ) / σ := by
        have hk2_ne : ((k + 2 : ℕ) : ℝ) ≠ 0 := by
          positivity
        have hL_nonneg : 0 ≤ h_oracle.L_tilde_f ^ (2 : ℕ) := by
          positivity
        have hfrac_raw : ((k + 1 : ℝ) / (σ * (k + 2 : ℝ))) ≤ 1 / σ := by
          field_simp [hσ.ne', hk2_ne]
          nlinarith
        have hscaled := mul_le_mul_of_nonneg_left hfrac_raw hL_nonneg
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
      rw [Finset.sum_range_succ]
      have hsum :=
        add_le_add hk hstep_mul'
      have hLsum :
          h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ +
              h_oracle.L_tilde_f ^ (2 : ℕ) * ((k + 1 : ℝ) / (σ * (k + 2 : ℝ))) ≤
            h_oracle.L_tilde_f ^ (2 : ℕ) * (k + 1) / σ := by
        have haux :=
          add_le_add_left hfrac_le (h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ)
        calc
          h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ +
              h_oracle.L_tilde_f ^ (2 : ℕ) * ((k + 1 : ℝ) / (σ * (k + 2 : ℝ))) ≤
              h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ + h_oracle.L_tilde_f ^ (2 : ℕ) / σ := by
                simpa [add_comm, add_left_comm, add_assoc] using haux
          _ = h_oracle.L_tilde_f ^ (2 : ℕ) * (k + 1) / σ := by
            ring
      have hcombine :
          -(σ * k * (k + 1 : ℝ) / 4) *
              (∫ ω, ‖(x[k + 1] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) +
            h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ +
              ((σ * k * (k + 1 : ℝ) / 4) *
                  (∫ ω, ‖(x[k + 1] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) -
                (σ * (k + 1) * (k + 2 : ℝ) / 4) *
                (∫ ω, ‖(x[k + 2] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) +
                h_oracle.L_tilde_f ^ (2 : ℕ) * ((k + 1 : ℝ) / (σ * (k + 2 : ℝ))) ) ≤
            -(σ * (k + 1) * (k + 2 : ℝ) / 4) *
                (∫ ω, ‖(x[k + 2] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) +
              h_oracle.L_tilde_f ^ (2 : ℕ) * (k + 1) / σ := by
        -- The squared-distance tail cancels, and the remaining fraction is bounded by `1 / σ`.
        nlinarith [hLsum]
      simpa [Nat.cast_add, Nat.add_assoc, hk_add] using (le_trans hsum hcombine)

/-- Helper for Theorem 8.37: the `n`-weighted telescope obtained by summing the integrated
one-step inequalities. -/
lemma weighted_expected_gap_sum_le_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    Finset.sum (Finset.range (k + 1))
        (fun n ↦ (n : ℝ) * (((∫ ω, (f (x[n] ω : E)).toReal ∂μ) - fOpt))) ≤
      h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ := by
  -- First keep the explicit negative squared-distance tail from the telescope.
  have htail :=
    weighted_expected_gap_sum_with_tail_le_of_strongly_convex_stepsize
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
      (h_strong := h_strong) (hσ := hσ) (h_stepsize := h_stepsize)
      (h_oracle := h_oracle) hxStar k
  have hsqdist_nonneg :
      0 ≤ (∫ ω, ‖(x[k + 1] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) := by
    -- Squared norms are pointwise nonnegative, so their integral is nonnegative as well.
    exact integral_nonneg fun ω ↦ by positivity
  have htail_nonpos :
      -(σ * k * (k + 1 : ℝ) / 4) *
          (∫ ω, ‖(x[k + 1] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) ≤ 0 := by
    have hcoef_nonneg : 0 ≤ σ * k * (k + 1 : ℝ) / 4 := by
      positivity
    nlinarith
  linarith

/-- Helper for Theorem 8.37: normalizing the weighted telescope gives the exact simplex-weighted
objective-gap estimate used in the ergodic part of the proof. -/
lemma normalized_strongly_convex_weighted_gap_le
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) {k : ℕ} (hk : 0 < k) :
    Finset.sum (Finset.range (k + 1))
        (fun n ↦
          ((2 : ℝ) * n / (k * (k + 1) : ℝ)) *
            (((∫ ω, (f (x[n] ω : E)).toReal ∂μ) - fOpt))) ≤
      2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
  -- Normalize the weighted telescope by the deterministic denominator `k (k + 1)`.
  have hweighted :=
    weighted_expected_gap_sum_le_of_strongly_convex_stepsize
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
      (h_strong := h_strong) (hσ := hσ) (h_stepsize := h_stepsize)
      (h_oracle := h_oracle) hxStar k
  have hkden_ne : (k * (k + 1) : ℝ) ≠ 0 := by
    positivity
  have hfactor_nonneg : 0 ≤ (2 : ℝ) / (k * (k + 1) : ℝ) := by
    positivity
  calc
    Finset.sum (Finset.range (k + 1))
        (fun n ↦
          ((2 : ℝ) * n / (k * (k + 1) : ℝ)) *
            (((∫ ω, (f (x[n] ω : E)).toReal ∂μ) - fOpt))) =
      ((2 : ℝ) / (k * (k + 1) : ℝ)) *
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ (n : ℝ) * (((∫ ω, (f (x[n] ω : E)).toReal ∂μ) - fOpt))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro n hn
        field_simp [hkden_ne]
    _ ≤ ((2 : ℝ) / (k * (k + 1) : ℝ)) * (h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ) := by
      exact mul_le_mul_of_nonneg_left hweighted hfactor_nonneg
    _ = 2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
      have hk_ne : (k : ℝ) ≠ 0 := by
        positivity
      field_simp [hkden_ne, hk_ne, hσ.ne']

/-- Helper for Theorem 8.37: for `k > 0`, the weighted average iterate is a convex combination of
feasible iterates, hence it remains in `C` pathwise. -/
lemma strongly_convex_average_iterate_mem_feasible
    {k : ℕ} (hk : 0 < k) :
    ∀ ω,
      stochastic_projected_subgradient_strongly_convex_average_iterate h_problem g t x0 k ω ∈ C := by
  intro ω
  rcases strongly_convex_average_weights_form_simplex (k := k) hk with ⟨h_nonneg, h_sum⟩
  have hmem :
      (Finset.sum (Finset.range (k + 1)) fun n ↦
        ((2 : ℝ) * n / (k * (k + 1) : ℝ)) • ((x[n] ω : C) : E)) ∈ C := by
    -- Each iterate already lies in `C`, so convexity closes the weighted finite sum.
    exact h_problem.feasible_convex.sum_mem h_nonneg h_sum fun n hn ↦ (x[n] ω).property
  -- Unfold the average iterate and use the nondegenerate weight formula valid for `k > 0`.
  simpa [stochastic_projected_subgradient_strongly_convex_average_iterate, hk.ne'] using hmem

-- Proof sketch: combine the conditional one-step estimate from Lemma 8.11 with the unbiased
-- oracle hypothesis from Assumption 8.34 and the strong-convexity lower support inequality from
-- Theorem 5.24. Substituting the stepsizes `t_n = 2 / (σ (n + 1))`, taking expectations, and
-- summing the weighted inequalities from `n = 0` to `k` telescopes the squared-distance terms and
-- yields the stated `O(1 / k)` bound for the expected running minimum.
/-- Theorem 8.37 (1): under Assumptions 8.7 and 8.34, if `f` is `σ`-strongly convex with
`σ > 0`, the stochastic projected subgradient method uses the stepsizes
`t_k = 2 / (σ (k + 1))`, and the sampled directions satisfy the oracle assumptions along the
generated iterates, then the expected best objective value attained among the first `k + 1`
stochastic iterates satisfies
`E(f_best^k) - fOpt ≤ 2 L_tilde_f^2 / (σ (k + 1))`. -/
theorem stochastic_projected_subgradient_best_value_gap_le_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    (k : ℕ) :
    (∫ ω,
        best_achieved_function_value (fun x : E ↦ (f x).toReal) (fun n ↦ (x[n] ω : E)) k ∂μ) -
      fOpt ≤
      2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
  -- Route correction: the proof is now organized exactly as in the source:
  -- conditional one-step descent, integrated one-step estimate, weighted telescope, then prefix
  -- minimum. The unresolved frontier is no longer the theorem endgame but the conditional
  -- projection-square estimate isolated above.
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  by_cases hk : k = 0
  · subst k
    have hbest0 :
        (∫ ω,
            best_achieved_function_value (fun x : E ↦ (f x).toReal)
              (fun n ↦ (x[n] ω : E)) 0 ∂μ) =
          ∫ ω, (f (x[0] ω : E)).toReal ∂μ := by
      -- At `k = 0`, the running best is the unique initial objective value.
      refine integral_congr_ae ?_
      filter_upwards with ω
      simp [best_achieved_function_value]
    have hstep0 :=
      expected_one_step_gap_le_of_strongly_convex_stepsize
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        (h_strong := h_strong) (hσ := hσ) (h_stepsize := h_stepsize)
        (h_oracle := h_oracle) hxStar 0
    have hstep0' :
        ((∫ ω, (f (x[0] ω : E)).toReal ∂μ) - fOpt) ≤
          (-σ / 4) * (∫ ω, ‖(x[0] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) -
            (σ / 4) * (∫ ω, ‖(x[1] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) +
              h_oracle.L_tilde_f ^ (2 : ℕ) / σ := by
      -- Evaluate the exact coefficients appearing in the `n = 0` one-step estimate.
      simpa [sub_eq_add_neg, hσ.ne'] using hstep0
    have hsq0_nonneg :
        0 ≤ (∫ ω, ‖(x[0] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) := by
      exact integral_nonneg fun ω ↦ by positivity
    have hsq1_nonneg :
        0 ≤ (∫ ω, ‖(x[1] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) := by
      exact integral_nonneg fun ω ↦ by positivity
    have hbound0 :
        ((∫ ω, (f (x[0] ω : E)).toReal ∂μ) - fOpt) ≤
          h_oracle.L_tilde_f ^ (2 : ℕ) / σ := by
      -- The two squared-distance terms appear with nonpositive coefficients when `n = 0`.
      nlinarith [hstep0', hsq0_nonneg, hsq1_nonneg]
    have hL_nonneg : 0 ≤ h_oracle.L_tilde_f ^ (2 : ℕ) / σ := by
      positivity
    have hdouble :
        h_oracle.L_tilde_f ^ (2 : ℕ) / σ ≤
          2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * ((0 : ℝ) + 1)) := by
      field_simp [hσ.ne']
      nlinarith [hL_nonneg, hσ]
    rw [hbest0]
    simpa using (le_trans hbound0 hdouble)
  · have hk_pos : 0 < k := Nat.pos_iff_ne_zero.mpr hk
    have hnormalized :=
      normalized_strongly_convex_weighted_gap_le
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        (h_strong := h_strong) (hσ := hσ) (h_stepsize := h_stepsize)
        (h_oracle := h_oracle) hxStar hk_pos
    -- TODO: compare the simplex-weighted expected objective values with the expectation of the
    -- prefix minimum, using `best_achieved_function_value_le_objective_value` pathwise and then
    -- divide by `∑_{n=0}^k n = k (k + 1) / 2`.
    sorry

-- Proof sketch: start from the weighted estimate proved for the expected iterate values in the
-- proof of part (1), divide by `k (k + 1) / 2`, and rewrite the normalized coefficients as the
-- canonical strong-convexity weights. Jensen's inequality for the convex restriction of `f` then
-- transfers the estimate to the averaged random iterate `x^(k)`.
/-- Theorem 8.37 (2): with the same assumptions as in part (1), the weighted average random
iterate
`x^(k) = ∑_{n=0}^k α_n^k x^n`, where `α_n^k = 2 n / (k (k + 1))` for `k > 0` and `x^(0) = x^0`,
satisfies the same expected objective-gap bound
`E(f(x^(k))) - fOpt ≤ 2 L_tilde_f^2 / (σ (k + 1))`. -/
theorem stochastic_projected_subgradient_average_value_gap_le_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        (fun n ω ↦ (x[n] ω : E)) (fun n ω ↦ g n (x[n] ω) ω))
    (k : ℕ) :
    (∫ ω,
        (f (stochastic_projected_subgradient_strongly_convex_average_iterate h_problem g t x0 k
          ω)).toReal ∂μ) -
      fOpt ≤
      2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
  -- The ergodic clause reuses the same weighted telescope, so only the Jensen endgame remains
  -- after the source-faithful stochastic descent backbone is in place.
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  by_cases hk : k = 0
  · subst k
    have havg0 :
        (∫ ω,
            (f (stochastic_projected_subgradient_strongly_convex_average_iterate
              h_problem g t x0 0 ω)).toReal ∂μ) =
          ∫ ω, (f (x[0] ω : E)).toReal ∂μ := by
      -- The degenerate average iterate is exactly the initial random iterate.
      refine integral_congr_ae ?_
      filter_upwards with ω
      simp [stochastic_projected_subgradient_strongly_convex_average_iterate_zero]
    have hstep0 :=
      expected_one_step_gap_le_of_strongly_convex_stepsize
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        (h_strong := h_strong) (hσ := hσ) (h_stepsize := h_stepsize)
        (h_oracle := h_oracle) hxStar 0
    have hstep0' :
        ((∫ ω, (f (x[0] ω : E)).toReal ∂μ) - fOpt) ≤
          (-σ / 4) * (∫ ω, ‖(x[0] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) -
            (σ / 4) * (∫ ω, ‖(x[1] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) +
              h_oracle.L_tilde_f ^ (2 : ℕ) / σ := by
      -- Evaluate the exact coefficients appearing in the `n = 0` one-step estimate.
      simpa [sub_eq_add_neg, hσ.ne'] using hstep0
    have hsq0_nonneg :
        0 ≤ (∫ ω, ‖(x[0] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) := by
      exact integral_nonneg fun ω ↦ by positivity
    have hsq1_nonneg :
        0 ≤ (∫ ω, ‖(x[1] ω : E) - xStar‖ ^ (2 : ℕ) ∂μ) := by
      exact integral_nonneg fun ω ↦ by positivity
    have hbound0 :
        ((∫ ω, (f (x[0] ω : E)).toReal ∂μ) - fOpt) ≤
          h_oracle.L_tilde_f ^ (2 : ℕ) / σ := by
      -- The initial-step estimate is already stronger than the target `2 / σ` bound.
      nlinarith [hstep0', hsq0_nonneg, hsq1_nonneg]
    have hL_nonneg : 0 ≤ h_oracle.L_tilde_f ^ (2 : ℕ) / σ := by
      positivity
    have hdouble :
        h_oracle.L_tilde_f ^ (2 : ℕ) / σ ≤
          2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * ((0 : ℝ) + 1)) := by
      field_simp [hσ.ne']
      nlinarith [hL_nonneg, hσ]
    rw [havg0]
    simpa using (le_trans hbound0 hdouble)
  · have hk_pos : 0 < k := Nat.pos_iff_ne_zero.mpr hk
    have hnormalized :=
      normalized_strongly_convex_weighted_gap_le
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        (h_strong := h_strong) (hσ := hσ) (h_stepsize := h_stepsize)
        (h_oracle := h_oracle) hxStar hk_pos
    have hweights := strongly_convex_average_weights_form_simplex (k := k) hk_pos
    -- TODO: obtain the convex restriction of `x ↦ (f x).toReal` from `h_strong`, prove the
    -- weighted average iterate stays in `C`, and apply `ConvexOn.map_sum_le` pathwise with the
    -- simplex data `hweights`, then integrate and combine with `hnormalized`.
    sorry

end
