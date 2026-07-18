import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Algorithm_8_3
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Assumption_8_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → EReal) (C XStar : Set E) (fOpt : ℝ)
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k

-- Proof sketch: use nonexpansiveness of the metric projection to compare `‖x[k + 1] - xStar‖`
-- with `‖x[k] - t_k g_k - xStar‖`, expand the square, and rewrite the cross term with the
-- subgradient inequality coming from the hypothesis
-- `(toDualMap ℝ E (g k (x[k])) : Module.Dual ℝ E) ∈ extendedRealSubdifferential f (x[k] : E)`. Then use
-- `hxStar : xStar ∈ XStar` together with `h_problem.optimal_set_eq` and
-- `h_problem.optimal_value_isGLB` to identify `xStar` as an optimal feasible point with value
-- `fOpt`.
/-- Helper for Lemma 8.11: every point of the optimal set attains the recorded optimal value in
the extended-real objective. -/
lemma optimal_point_value_eq_fOpt
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    f xStar = (fOpt : EReal) := by
  -- Unpack the source-facing optimal-set description into feasibility and minimality.
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  -- The minimizer-induced GLB must agree with the problem's stored optimal value.
  exact IsGLB.unique
    (by simpa [Set.mem_image] using (hxStar_data.2.isGLB hxStar_data.1))
    h_problem.optimal_value_isGLB

/-- Helper for Lemma 8.11: every point of the optimal set has real value equal to the recorded
optimal value `fOpt`. -/
lemma optimal_point_toReal_eq_fOpt
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    (f xStar).toReal = fOpt := by
  -- First identify the extended-real value, then drop back to reals.
  rw [optimal_point_value_eq_fOpt
    (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) h_problem hxStar]
  exact EReal.toReal_coe fOpt

/-- Helper for Lemma 8.11: the subgradient inequality at the current iterate controls the optimal
gap by the pairing with the displacement toward an optimal point. -/
lemma subgradient_gap_le_inner_at_iterate
    (h_subgrad :
      ∀ k,
        (toDualMap ℝ E (g k (x[k])) : Module.Dual ℝ E) ∈ extendedRealSubdifferential f (x[k] : E))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    (f (x[k] : E)).toReal - fOpt ≤ inner ℝ (g k (x[k])) ((x[k] : E) - xStar) := by
  -- Convert optimality of `xStar` into the feasibility data needed by the subgradient inequality.
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hxStar_dom : xStar ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hxStar_data.1)
  have hxk_dom : (x[k] : E) ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain (x[k]).2)
  have hxk_top : f (x[k] : E) ≠ ⊤ := ne_of_lt hxk_dom
  have hxk_bot : f (x[k] : E) ≠ ⊥ := h_problem.ne_bot _
  -- Rewrite subgradient membership into the textbook supporting-hyperplane inequality.
  have hsub := h_subgrad k
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hsub
  have hgapE :
      f (x[k] : E) + ((inner ℝ (g k (x[k])) (xStar - (x[k] : E)) : ℝ) : EReal) ≤
        (fOpt : EReal) := by
    have hineq := hsub.2 xStar hxStar_dom
    -- Replace the optimal-point value by the recorded optimum before converting to reals.
    simpa [ge_iff_le, InnerProductSpace.toDualMap_apply_apply,
      optimal_point_value_eq_fOpt
        (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) h_problem hxStar] using
      hineq
  have hgapReal :
      (f (x[k] : E)).toReal + inner ℝ (g k (x[k])) (xStar - (x[k] : E)) ≤ fOpt := by
    -- All terms are finite on the feasible set, so the EReal inequality descends to reals.
    have hcoe :
        (((f (x[k] : E)).toReal + inner ℝ (g k (x[k])) (xStar - (x[k] : E)) : ℝ) : EReal) ≤
          (fOpt : EReal) := by
      simpa [EReal.coe_toReal hxk_top hxk_bot, EReal.coe_add] using hgapE
    exact EReal.coe_le_coe_iff.mp hcoe
  have hinner_neg :
      inner ℝ (g k (x[k])) (xStar - (x[k] : E)) =
        -inner ℝ (g k (x[k])) ((x[k] : E) - xStar) := by
    -- Reorient the displacement so the pairing matches the source statement.
    rw [show xStar - (x[k] : E) = -((x[k] : E) - xStar) by abel, inner_neg_right]
  have hgapReal' :
      (f (x[k] : E)).toReal +
        (-inner ℝ (g k (x[k])) ((x[k] : E) - xStar)) ≤ fOpt := by
    simpa [hinner_neg] using hgapReal
  -- Rearranging the real inequality isolates the optimality gap on the left-hand side.
  have hle :
      (f (x[k] : E)).toReal ≤
        fOpt + inner ℝ (g k (x[k])) ((x[k] : E) - xStar) := by
    linarith
  exact (sub_le_iff_le_add).2 (by simpa [add_comm] using hle)

/-- Lemma 8.11: under Assumption 8.7, every step of the projected subgradient method satisfies the
fundamental inequality
`‖x^{k+1} - xStar‖^2 ≤ ‖x^k - xStar‖^2 - 2 t_k ((f x^k).toReal - fOpt) + t_k^2 ‖g_k‖^2`
for each optimal point `xStar ∈ XStar`, where the chosen direction at iteration `k` is a
subgradient of `f` at `x^k`. -/
theorem projected_subgradient_method_fundamental_inequality
    (h_subgrad :
      ∀ k,
        (toDualMap ℝ E (g k (x[k])) : Module.Dual ℝ E) ∈ extendedRealSubdifferential f (x[k] : E))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    ‖(x[k + 1] : E) - xStar‖ ^ 2 ≤
      ‖(x[k] : E) - xStar‖ ^ 2 -
        2 * t k * ((f (x[k] : E)).toReal - fOpt) +
          (t k) ^ 2 * ‖g k (x[k])‖ ^ 2 := by
  -- Route correction: the textbook proof uses
  -- `⟪g_k, x^k - xStar⟫ ≥ f(x^k) - fOpt` and then multiplies by `-2 * t_k`,
  -- so it requires at least `0 ≤ t k`. The current Lean statement has no sign
  -- hypothesis on `t k`, and is mathematically false for negative stepsizes.
  have hgap :
      (f (x[k] : E)).toReal - fOpt ≤ inner ℝ (g k (x[k])) ((x[k] : E) - xStar) :=
    subgradient_gap_le_inner_at_iterate
      (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
      (g := g) (t := t) (x0 := x0) h_subgrad hxStar k
  -- The source-faithful proof skeleton is now reduced to the missing sign condition:
  -- projection nonexpansiveness gives the squared-distance expansion, and `hgap` supplies the
  -- cross-term bound. The final monotonicity step is blocked only because `-2 * t k` need not be
  -- nonpositive under the current theorem statement.
  -- TODO: after restating the theorem with a nonnegative-stepsize hypothesis
  -- (or a positivity assumption supplied by the algorithm statement), follow the
  -- planned proof route: projection nonexpansiveness, square expansion, then the
  -- subgradient inequality plus optimal-value rewriting.
  sorry

end
