import Mathlib
import FirstOrderMethodsinOptimization.Chap03.Definition_3_10
import FirstOrderMethodsinOptimization.Chap06.Definition_6_10
import FirstOrderMethodsinOptimization.Chap06.Theorem_6_30
import FirstOrderMethodsinOptimization.Chap09.Definition_9_2
import FirstOrderMethodsinOptimization.Chap09.Definition_9_6
import FirstOrderMethodsinOptimization.Chap09.Lemma_9_7
import FirstOrderMethodsinOptimization.Chap09.Theorem_9_24
import FirstOrderMethodsinOptimization.Chap10.Algorithm_10_2
import FirstOrderMethodsinOptimization.Chap10.Algorithm_10_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (f g ω : E → EReal)
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)] [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]

attribute [local instance] Classical.propDecidable

/-- Helper for Algorithm 10.69: the canonical one-step non-Euclidean proximal-gradient update
predicate used by the B5 backtracking construction. -/
def non_euclidean_proximal_gradient_backtracking_step
    (f g ω : E → EReal) (xk : E) (Lk : PosReal) (xNext : E) : Prop :=
  is_differentiable_at f xk ∧
    IsMinOn
      (mirror_c_update_objective g ω xk
        (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹))
      Set.univ xNext

/- `prompt_add/` is absent in this workspace, so the nearby Chapter 9 and Chapter 10 files supply
the local API guidance.

Algorithm 10.69 is `source-facing` in the non-Euclidean proximal-gradient API.

Domain sampling against the existing project code identifies:
- `proximal_gradient_backtracking_trial_stepsize` and
  `ProximalGradientBacktrackingGrowthFactor` from Algorithm 10.2 as the canonical owner of the
  geometric trial family `LPrev η^i`;
- `non_euclidean_proximal_gradient_step` from Algorithm 10.67 as the canonical owner of the
  non-Euclidean one-step update predicate;
- `IsBregmanPotentialOn` from Definition 9.2 and the unique-minimizer theorem
  `existsUnique_composite_minimizer_mem_domains` from Lemma 9.7 as the canonical bridge turning
  the source symbol `V_L(x)` into a point-valued operator.

The clean public interface therefore keeps the B5-specific content at the same level as B2, B3,
and B4: a canonical point-valued one-step operator `V_L`, the B5 acceptance predicate, the local
class saying that an index is the first accepted geometric trial, and the sequence-level rule
recording `L_k = L_{k-1} η^{i_k}` at the current iterate `x^k`. The chapter already owns the
recursion `L_{-1} = s`, `L_prev(k + 1) = L_k` as
`proximal_gradient_backtracking_B2_previous_stepsize`, so this file should reuse that owner
directly instead of threading an extra trajectory witness merely to recover the point `x^k`.

Because Algorithm 10.67 no longer hides the Chapter 3 differentiability hypothesis inside a
totalized set-valued owner, the point-valued update and the B5 acceptance data in this file must
keep that hypothesis explicit on theorem surfaces, rather than reviving a hidden fallback
derivative through totalization. -/

/-- Helper for Algorithm 10.69: positive scaling by the reciprocal curvature leaves the effective
domain of `g` unchanged. -/
lemma scaled_backtracking_penalty_effective_domain_eq
    (g : E → EReal) [IsProperExtendedRealFunction g] (Lk : PosReal) :
    effective_domain ((((1 / Lk : PosReal) : EReal) • g)) = effective_domain g := by
  ext x
  -- Domain membership is invariant under positive scaling.
  exact mem_effective_domain_scaled_function_iff g (1 / Lk) inferInstance x

/-- Helper for Algorithm 10.69: the standing Bregman-potential hypothesis transports to the
scaled penalty domain. -/
lemma bregman_potential_on_scaled_penalty_domain
    (g ω : E → EReal) [IsProperExtendedRealFunction g]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)] (Lk : PosReal) :
    IsBregmanPotentialOn ω
      (effective_domain ((((1 / Lk : PosReal) : EReal) • g))) (1 : ℝ) := by
  have hdomain :
      effective_domain ((((1 / Lk : PosReal) : EReal) • g)) = effective_domain g :=
    scaled_backtracking_penalty_effective_domain_eq (g := g) Lk
  -- Rewrite the target domain to the original one and reuse the standing instance.
  rw [hdomain]
  exact inferInstance

omit [FiniteDimensional ℝ E] in
/-- Helper for Algorithm 10.69: the Algorithm 10.67 step objective is exactly the Chapter 9
Mirror-C objective for the scaled penalty `(1 / Lk) g`. -/
lemma mirror_c_step_objective_eq_scaled_auxiliary_objective
    (f g ω : E → EReal) (xk : E) (Lk : PosReal) :
    mirror_c_update_objective g ω xk
      (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹) =
      fun x ↦
        (((mirror_c_problem_functional ω xk
            (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((1 / Lk : PosReal) : ℝ) x : ℝ) : EReal) +
          ((((1 / Lk : PosReal) : EReal) • g) x)) +
          ω x := by
  funext x
  have hcurvature : ((Lk : ℝ)⁻¹) = ((1 / Lk : PosReal) : ℝ) := by
    simp
  -- Rewrite the reciprocal curvature into the positive-scaling owner used by Chapter 9.
  rw [hcurvature, mirror_c_update_objective_apply, Pi.smul_apply, smul_eq_mul]

/-- Helper for Algorithm 10.69: positive scaling by the reciprocal curvature preserves the proper,
closed, and convex hypotheses on `g`. -/
lemma scaled_backtracking_penalty_proper_closed_convex
    (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] (Lk : PosReal) :
    IsProperExtendedRealFunction ((((1 / Lk : PosReal) : EReal) • g)) ∧
      LowerSemicontinuous ((((1 / Lk : PosReal) : EReal) • g)) ∧
      is_convex_function ((((1 / Lk : PosReal) : EReal) • g)) := by
  let hg_closed : LowerSemicontinuous g := Fact.out
  let hg_convex : is_convex_function g := Fact.out
  -- Chapter 6 already proves stability of these hypotheses under positive scaling.
  exact scaled_function_proper_closed_convex_of_pos g inferInstance hg_closed hg_convex (1 / Lk)

/-- The canonical non-Euclidean proximal-gradient step predicate from Algorithm 10.67 has a unique
realizer, and that point lies in `dom(g) ∩ dom(∂ ω)`. -/
theorem existsUnique_non_euclidean_proximal_gradient_step_mem_domains
    (xk : E) (Lk : PosReal) (hfxk : is_differentiable_at f xk) :
    ∃! xNext : E,
      non_euclidean_proximal_gradient_backtracking_step f g ω xk Lk xNext ∧
        xNext ∈ effective_domain g ∩ subdifferential_domain ω := by
  have hω_scaled :
      IsBregmanPotentialOn ω
        (effective_domain ((((1 / Lk : PosReal) : EReal) • g))) (1 : ℝ) :=
    bregman_potential_on_scaled_penalty_domain (g := g) (ω := ω) Lk
  have hg_scaled :
      IsProperExtendedRealFunction ((((1 / Lk : PosReal) : EReal) • g)) ∧
        LowerSemicontinuous ((((1 / Lk : PosReal) : EReal) • g)) ∧
        is_convex_function ((((1 / Lk : PosReal) : EReal) • g)) :=
    scaled_backtracking_penalty_proper_closed_convex (g := g) Lk
  -- Reduce Algorithm 10.67 to the Chapter 9 unique Mirror-C minimizer for the scaled penalty.
  rcases existsUnique_mirror_c_problem_minimizer_mem_domains
      (a := mirror_c_problem_functional ω xk
        (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((1 / Lk : PosReal) : ℝ))
      hω_scaled hg_scaled.1 hg_scaled.2.1 hg_scaled.2.2 with
    ⟨xNext, hxNext, hxNext_unique⟩
  refine ⟨xNext, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · -- Package the differentiability hypothesis with the rewritten minimizer clause.
      refine ⟨hfxk, ?_⟩
      simpa [mirror_c_step_objective_eq_scaled_auxiliary_objective (f := f) (g := g) (ω := ω)
        xk Lk] using hxNext.1
    · -- Transport the Chapter 9 domain conclusion back to `effective_domain g`.
      refine ⟨?_, hxNext.2.2⟩
      exact
        (mem_effective_domain_scaled_function_iff g (1 / Lk) inferInstance xNext).mp
          hxNext.2.1
  · intro y hy
    have hy_scaled :
        IsMinOn
            (fun x ↦
              ((mirror_c_problem_functional ω xk
                  (fderiv ℝ (fun z ↦ (f z).toReal) xk) ((1 / Lk : PosReal) : ℝ) x : ℝ) :
                EReal) +
                ((((1 / Lk : PosReal) : EReal) • g) x) + ω x)
            Set.univ y ∧
          y ∈ effective_domain ((((1 / Lk : PosReal) : EReal) • g)) ∩
            subdifferential_domain ω := by
      refine ⟨?_, ?_⟩
      · -- Any competing Algorithm 10.67 step yields a competing scaled Mirror-C minimizer.
        simpa [mirror_c_step_objective_eq_scaled_auxiliary_objective (f := f) (g := g) (ω := ω)
          xk Lk] using hy.1.2
      · -- Positive scaling preserves the effective domain component of the witness.
        refine ⟨?_, hy.2.2⟩
        exact
          (mem_effective_domain_scaled_function_iff g (1 / Lk) inferInstance y).mpr
            hy.2.1
    exact hxNext_unique y hy_scaled

/-- The totalized point-valued non-Euclidean prox-gradient update `V_L(xk)`. On the
Chapter 3 differentiability locus it is the unique point satisfying the canonical step predicate
from Algorithm 10.67; away from that locus it returns the harmless default `xk`, while all
source-facing theorem surfaces below keep differentiability explicit. -/
def non_euclidean_proximal_gradient_operator
    (f g ω : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    (Lk : PosReal) : E → E :=
  fun xk ↦
    if hfxk : is_differentiable_at f xk then
      Classical.choose <|
        existsUnique_non_euclidean_proximal_gradient_step_mem_domains f g ω xk Lk hfxk
    else
      xk

@[inherit_doc] scoped[Gradient] notation:max "V[" L ", " f ", " g ", " ω "]" =>
  non_euclidean_proximal_gradient_operator f g ω L

private theorem non_euclidean_proximal_gradient_operator_spec
    (f g ω : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    (xk : E) (Lk : PosReal) (hfxk : is_differentiable_at f xk) :
    non_euclidean_proximal_gradient_backtracking_step f g ω xk Lk (V[Lk, f, g, ω] xk) ∧
      V[Lk, f, g, ω] xk ∈ effective_domain g ∩ subdifferential_domain ω := by
  simp [non_euclidean_proximal_gradient_operator, hfxk]
  rcases Classical.choose_spec
      (existsUnique_non_euclidean_proximal_gradient_step_mem_domains f g ω xk Lk hfxk) with
    ⟨hspec, _⟩
  simpa [non_euclidean_proximal_gradient_backtracking_step, hfxk] using hspec

/-- The point-valued non-Euclidean prox-gradient update satisfies the canonical step predicate
from Algorithm 10.67. -/
theorem non_euclidean_proximal_gradient_operator_mem_step
    (f g ω : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    (xk : E) (Lk : PosReal) (hfxk : is_differentiable_at f xk) :
    non_euclidean_proximal_gradient_backtracking_step f g ω xk Lk (V[Lk, f, g, ω] xk) :=
  (non_euclidean_proximal_gradient_operator_spec f g ω xk Lk hfxk).1

/-- The point-valued non-Euclidean prox-gradient update belongs to
`dom(g) ∩ dom(∂ ω)`. -/
theorem non_euclidean_proximal_gradient_operator_mem_domains
    (f g ω : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    (xk : E) (Lk : PosReal) (hfxk : is_differentiable_at f xk) :
    V[Lk, f, g, ω] xk ∈ effective_domain g ∩ subdifferential_domain ω :=
  (non_euclidean_proximal_gradient_operator_spec f g ω xk Lk hfxk).2

/-- The B5 acceptance test accepts a trial curvature `L` at the current iterate `xk` exactly when
the Chapter 3 differentiability condition holds at `xk` and the canonical update `V_L(xk)`
satisfies the quadratic upper-model inequality from the textbook. -/
def non_euclidean_proximal_gradient_backtracking_B5_accepts
    (f g ω : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    (L : PosReal) (xk : E) : Prop :=
  is_differentiable_at f xk ∧
    let xNext := V[L, f, g, ω] xk
    f xNext ≤
      f xk +
        ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
          ((L : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ) : ℝ) : EReal)

/-- The B5 acceptance predicate is exactly the displayed inequality
`f(V_L(xk)) ≤ f(xk) + ⟪∇ f(xk), V_L(xk) - xk⟫ + (L / 2) ‖V_L(xk) - xk‖²`. -/
theorem non_euclidean_proximal_gradient_backtracking_B5_accepts_iff
    (f g ω : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    (L : PosReal) (xk : E) :
    non_euclidean_proximal_gradient_backtracking_B5_accepts f g ω L xk ↔
      is_differentiable_at f xk ∧
        let xNext := V[L, f, g, ω] xk
        f xNext ≤
          f xk +
            ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
              ((L : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ) : ℝ) : EReal) :=
  Iff.rfl

/-- A trial index `i` is valid for B5 at `xk` when the geometric trial `LPrev η^i` is the first
trial curvature satisfying the B5 acceptance inequality. -/
class is_backtracking_procedure_B5_index
    (f g ω : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    (LPrev : PosReal) (η : ProximalGradientBacktrackingGrowthFactor)
    (xk : E) (i : ℕ) : Prop where
  accepts :
    non_euclidean_proximal_gradient_backtracking_B5_accepts
      f g ω (proximal_gradient_backtracking_trial_stepsize LPrev η i) xk
  minimal (j : ℕ) (hj : j < i) :
    ¬ non_euclidean_proximal_gradient_backtracking_B5_accepts
        f g ω (proximal_gradient_backtracking_trial_stepsize LPrev η j) xk

/-- An accepted B5 backtracking index yields the corresponding acceptance fact as a `Fact`
instance. -/
instance is_backtracking_procedure_B5_index_accepts_fact
    {LPrev : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    {xk : E} {i : ℕ}
    [h : is_backtracking_procedure_B5_index f g ω LPrev η xk i] :
    Fact
      (non_euclidean_proximal_gradient_backtracking_B5_accepts
        f g ω (proximal_gradient_backtracking_trial_stepsize LPrev η i) xk) :=
  ⟨h.accepts⟩

/-- A valid B5 backtracking index records that `f` is differentiable at the current iterate
`xk`. -/
theorem is_backtracking_procedure_B5_index_differentiable_at
    (f g ω : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    {LPrev : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    {xk : E} {i : ℕ} (hi : is_backtracking_procedure_B5_index f g ω LPrev η xk i) :
    is_differentiable_at f xk :=
  hi.accepts.1

/-- A valid B5 backtracking index has an accepted trial curvature `LPrev η^i`. -/
theorem is_backtracking_procedure_B5_index_accepts
    (f g ω : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    {LPrev : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    {xk : E} {i : ℕ} (hi : is_backtracking_procedure_B5_index f g ω LPrev η xk i) :
    non_euclidean_proximal_gradient_backtracking_B5_accepts
      f g ω (proximal_gradient_backtracking_trial_stepsize LPrev η i) xk :=
  hi.accepts

/-- A valid B5 backtracking index is minimal among the accepted geometric trials based on
`LPrev`. -/
theorem is_backtracking_procedure_B5_index_minimal
    (f g ω : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    {LPrev : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    {xk : E} {i j : ℕ} (hi : is_backtracking_procedure_B5_index f g ω LPrev η xk i)
    (hj : j < i) :
    ¬ non_euclidean_proximal_gradient_backtracking_B5_accepts
        f g ω (proximal_gradient_backtracking_trial_stepsize LPrev η j) xk :=
  hi.minimal j hj

/-- Algorithm 10.69: a non-Euclidean proximal-gradient run uses backtracking procedure B5 with
parameters `(s, η)` when `L_{-1} = s` and, at every iteration `k`, the accepted curvature
estimate `L_k` is the first geometric trial `L_{k-1} η^{i_k}` whose canonical update
`V_{L_{k-1} η^{i_k}}(x^k)` satisfies the quadratic upper-model inequality
`f(V_L(x^k)) ≤ f(x^k) + ⟪∇ f(x^k), V_L(x^k) - x^k⟫ + (L / 2) ‖V_L(x^k) - x^k‖²`. -/
def uses_non_euclidean_proximal_gradient_backtracking_B5_rule
    (f g ω : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    (x : ℕ → E) (L : ℕ → PosReal)
    (s : PosReal) (η : ProximalGradientBacktrackingGrowthFactor) : Prop :=
  ∀ k : ℕ, ∃ i : ℕ,
    is_backtracking_procedure_B5_index
      f g ω (proximal_gradient_backtracking_B2_previous_stepsize s L k) η
      (x k) i ∧
    L k =
      proximal_gradient_backtracking_trial_stepsize
        (proximal_gradient_backtracking_B2_previous_stepsize s L k) η i

/-- Under B5, the current iterate `x^k` is a differentiability point of `f`. -/
theorem uses_non_euclidean_proximal_gradient_backtracking_B5_rule_differentiable_at
    (f g ω : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    {x : ℕ → E} {L : ℕ → PosReal}
    {s : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    (hrule : uses_non_euclidean_proximal_gradient_backtracking_B5_rule
      f g ω x L s η)
    (k : ℕ) :
    is_differentiable_at f (x k) := by
  rcases hrule k with ⟨i, hi, _⟩
  exact hi.accepts.1

/-- Under B5, the chosen curvature estimate `L_k` satisfies the B5 acceptance inequality at
iteration `k`. -/
theorem uses_non_euclidean_proximal_gradient_backtracking_B5_rule_accepts
    (f g ω : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    {x : ℕ → E} {L : ℕ → PosReal}
    {s : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    (hrule : uses_non_euclidean_proximal_gradient_backtracking_B5_rule
      f g ω x L s η)
    (k : ℕ) :
    non_euclidean_proximal_gradient_backtracking_B5_accepts f g ω (L k) (x k) := by
  rcases hrule k with ⟨i, hi, hLk⟩
  simpa [hLk] using hi.accepts

end
