import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Assumption_8_7 (from Chap08) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Assumption 8.7 is `source-facing`: it fixes the standing convex-optimization hypotheses for the
constrained problem `min {f x : x ∈ C}` used later by the projected subgradient method. The
canonical owners already present in the project are `IsProperExtendedRealFunction`,
`LowerSemicontinuous`, `is_convex_function`, `constrained_problem_solutions`, and `IsGLB`, so the
assumption is recorded directly as a Prop-valued class on the objective, feasible set, optimal
set, and optimal value, with no surrogate algorithm-branded wrapper. -/

/-- Assumption 8.7: clauses (A)-(D) hold for the constrained convex problem `min {f x : x ∈ C}`,
namely `f` is
proper, closed, and convex, `C` is a nonempty closed convex subset of `interior (dom(f))`,
`XStar` is the nonempty optimal set of the constrained problem `min {f x : x ∈ C}`, and `fOpt`
is its optimal value. -/
class IsConstrainedConvexProblem
    (f : E → EReal) (C XStar : Set E) (fOpt : ℝ) : Prop
    extends IsProperExtendedRealFunction f where
  closed : LowerSemicontinuous f
  convex : is_convex_function f
  feasible_nonempty : C.Nonempty
  feasible_closed : IsClosed C
  feasible_convex : Convex ℝ C
  feasible_subset_interior_effective_domain : C ⊆ interior (effective_domain f)
  optimal_set_eq : XStar = constrained_problem_solutions f C
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB : IsGLB (f '' C) (fOpt : EReal)

/-- A constrained convex problem packages both existence of minimizers and the
greatest-lower-bound characterization of the optimal value. -/
instance instFactOptimalSetNonemptyAndOptimalValueIsGLB
    {f : E → EReal} {C XStar : Set E} {fOpt : ℝ}
    [h : IsConstrainedConvexProblem f C XStar fOpt] :
    Fact (XStar.Nonempty ∧ IsGLB (f '' C) (fOpt : EReal)) where
  out := ⟨h.optimal_set_nonempty, h.optimal_value_isGLB⟩

end

/-! ### Definition_8_7 (from Chap08) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 8.7 is `source-facing`: the textbook introduces a deterministic rule that chooses,
for each feasible point `x ∈ C`, one member of the owner set `subdifferential f x = ∂ f(x)`.
This is genuine data, not merely an existence claim, so the public API is a function on `C`
equipped with the pointwise membership property, without any existential wrapper or separate choice
operator. -/

/-- Definition 8.7: a subgradient selection for `f` on `C` is a deterministic rule assigning to
each `x ∈ C` a chosen subgradient `f'(x) ∈ ∂ f(x)`, that is, a function `C → E*` whose value at
every feasible point belongs to the subdifferential of `f` at that point. -/
structure SubgradientSelection (f : E → EReal) (C : Set E) where
  toFun : C → Module.Dual ℝ E
  mem_subdifferential : ∀ x : C, toFun x ∈ subdifferential f x.1

/-- A subgradient selection is canonically used as the underlying function `C → E*`. -/
instance {f : E → EReal} {C : Set E} :
    CoeFun (SubgradientSelection f C) (fun _ ↦ ↥C → Module.Dual ℝ E) where
  coe s := s.toFun

end

/-! ### Proposition_8_7 (from Chap08) -/
universe u v

open scoped ProbabilityTheory
open MeasureTheory

section

variable {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable {f : E → ℝ} {x : ℕ → Ω → E} {g : ℕ → Ω → E}

-- Proof sketch: expand `StochasticProjectedSubgradientOracle.unbiased k` and rewrite membership in
-- `euclideanSubdifferentialAt` using the Chapter 3 bridge lemmas
-- `mem_euclideanSubdifferentialAt_iff`, `mem_strongDualSubdifferential`, `mem_subdifferential`,
-- and `is_subgradient_at_coe_iff`; then use `toDualMap_apply_apply` to identify the pairing with
-- the inner product.
/-- Proposition 8.7: for a real-valued objective, clause (A) of Assumption 8.34 is equivalent to
saying that, for each `k`, the conditional expectation of the stochastic subgradient given `x^k`
satisfies the pointwise subgradient inequality at `x^k` almost surely, i.e. for every `z`, one has
`f z ≥ f (x^k) + ⟪E[g^k | x^k], z - x^k⟫`. Since `f` is real-valued here, `dom(f) = E`. -/
theorem stochastic_projected_subgradient_unbiased_iff_ae_subgradient_inequality (k : ℕ) :
    (∀ᵐ ω ∂μ,
      μ[g k | MeasurableSpace.comap (x k) inferInstance] ω ∈
        euclideanSubdifferentialAt f (x k ω)) ↔
      ∀ᵐ ω ∂μ,
        ∀ z : E,
          f z ≥
            f (x k ω) +
              inner ℝ
                (μ[g k | MeasurableSpace.comap (x k) inferInstance] ω)
                (z - x k ω) := by
  -- Rewrite the stochastic clause pointwise through the Chapter 3 Euclidean-subgradient bridge.
  have hpointwise :
      ∀ ω : Ω,
        μ[g k | MeasurableSpace.comap (x k) inferInstance] ω ∈
            euclideanSubdifferentialAt f (x k ω) ↔
          ∀ z : E,
            f z ≥
              f (x k ω) +
                inner ℝ
                  (μ[g k | MeasurableSpace.comap (x k) inferInstance] ω)
                  (z - x k ω) := by
    intro ω
    -- The owner predicate is exactly the real-valued subgradient inequality after identifying the
    -- Riesz pairing with the inner product.
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
      mem_subdifferential, is_subgradient_at_coe_iff]
    simp [InnerProductSpace.toDualMap_apply_apply]
  constructor
  · intro hmem
    -- Transport the pointwise bridge along the almost-everywhere membership event.
    filter_upwards [hmem] with ω hω
    exact (hpointwise ω).1 hω
  · intro hineq
    -- The reverse implication is the same pointwise bridge used in the opposite direction.
    filter_upwards [hineq] with ω hω
    exact (hpointwise ω).2 hω

end
