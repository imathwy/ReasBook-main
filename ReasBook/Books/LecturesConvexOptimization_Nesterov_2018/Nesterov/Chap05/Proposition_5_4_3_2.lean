import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_3_4_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_3_4
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open QuadraticallyConstrainedQuadraticOptimizationProblem

variable {n m : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Proposition 5.4.3.2 lies in the Chapter 5 QCQP / logarithmic-barrier / short-step
path-following domain.

Sampled owner declarations in this domain:
* `QuadraticallyConstrainedQuadraticOptimizationProblem.strictEpigraphFeasibleSet`,
  `StrictEpigraphFeasiblePoint`, `epigraphLogarithmicBarrier`, and
  `epigraphLogarithmicBarrierAmbient` from `Definition_5_4_3_5`, the QCQP owner API for the
  strict epigraph barrier;
* `BarrierPathFollowingScheme` from `Definition_5_3_4_1`, the chapter owner for short-step
  barrier path-following data;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for
  self-concordant barriers on an ambient domain;
* the chapter `RealProdL2` pattern, used in nearby files to keep raw pair owners on the public
  surface while realizing the ambient Euclidean structure through the canonical `WithLp 2`
  `L²` model only internally.

Source/core/bridge triage:
* source-facing: the QCQP strict epigraph feasible region and its logarithmic barrier;
* core/canonical: `BarrierPathFollowingScheme` together with `IsSelfConcordantBarrierOnWith`;
* bridge/view: the local `L²` inner-product structure on the raw pair space `Eₙ × ℝ`,
  implemented through `WithLp.toLp`.

Primitive data:
* the QCQP owner `problem`.

Derived API:
* the strict-to-nonstrict epigraph-feasibility inclusion;
* the closure bridge identifying the closure of the strict QCQP epigraph domain with the
  nonstrict QCQP epigraph feasible set;
* the raw-pair self-concordant-barrier instance needed by `BarrierPathFollowingScheme`, with the
  `WithLp` realization kept internal to this file;
* the common short-step existence package theorem and its source-facing projections.

The refined file therefore removes the redundant public `WithLp`-surface wrappers from
Proposition 5.4.3.2. The QCQP owner barrier remains primary, and the `WithLp` model is used only
internally to equip the raw epigraph pair space with its `L²` ambient structure. -/

section

variable (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)

noncomputable local instance : SeminormedAddCommGroup (Eₙ × ℝ) :=
  WithLp.seminormedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance : NormedAddCommGroup (Eₙ × ℝ) :=
  WithLp.normedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance : NormedSpace ℝ (Eₙ × ℝ) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance : InnerProductSpace ℝ (Eₙ × ℝ) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 Eₙ ℝ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance : CompleteSpace (Eₙ × ℝ) := inferInstance

local notation "𝒟" =>
  problem.strictEpigraphFeasibleSet
local notation "F" =>
  problem.epigraphLogarithmicBarrierAmbient
local notation "P" =>
  problem.epigraphOptimizationProblem
local notation "ℱ" =>
  problem.epigraphFeasibleSet
local notation "cτ" =>
  ((0 : Eₙ), (1 : ℝ))

-- Proof sketch: a strict inequality implies the corresponding weak inequality, so the strict
-- epigraph domain is contained in the nonstrict epigraph feasible set of the same QCQP.
/-- Every point of the strict QCQP epigraph domain is feasible for the nonstrict epigraph
reformulation of the same QCQP. -/
theorem qcqpStrictEpigraphDomain_subset_epigraphFeasibleSet :
    𝒟 ⊆ problem.epigraphFeasibleSet := sorry

-- Proof sketch: if `(x, τ)` is feasible for the closed QCQP epigraph problem and `(x̄, τ̄)` is a
-- strict feasible point, then every convex combination `(1 - s) • (x, τ) + s • (x̄, τ̄)` with
-- `0 < s < 1` satisfies the strict inequalities because the QCQP objective and constraints are
-- convex. Sending `s → 0⁺` shows that every feasible epigraph point is a limit of strict ones.
/-- If the strict QCQP epigraph domain is nonempty, every feasible epigraph point is a limit of
strictly feasible epigraph points. -/
theorem epigraphFeasibleSet_subset_closure_strictEpigraphFeasibleSet
    (hstrict : Set.Nonempty 𝒟) :
    ℱ ⊆ closure 𝒟 := sorry

-- Proof sketch: the strict QCQP epigraph domain is contained in the nonstrict feasible set by
-- `qcqpStrictEpigraphDomain_subset_epigraphFeasibleSet`, while the converse closure inclusion is
-- the theorem above.
/-- If the strict QCQP epigraph domain is nonempty, its closure is exactly the nonstrict QCQP
epigraph feasible set. -/
theorem closure_strictEpigraphFeasibleSet_eq_epigraphFeasibleSet
    (hstrict : Set.Nonempty 𝒟) :
    closure 𝒟 = ℱ := sorry

-- Proof sketch: each slack function `τ - q₀(x)` and `βᵢ - qᵢ(x)` is concave on the strict
-- epigraph domain because the corresponding `qᵢ` is convex. The logarithmic barrier of the
-- `m + 1` positive scalar slacks is therefore the standard `(m + 1)`-self-concordant barrier for
-- the QCQP epigraph domain.
/-- The QCQP epigraph logarithmic barrier is an `(m + 1)`-self-concordant barrier on the strict
epigraph domain. The raw pair ambient space `Eₙ × ℝ` carries the canonical `L²` inner-product
structure locally inside this file, so the public theorem surface stays on the QCQP epigraph
owner itself rather than on an exposed `WithLp` transport. -/
theorem qcqpStrictEpigraphLogarithmicBarrier_isSelfConcordantBarrierOnWith :
    IsSelfConcordantBarrierOnWith 𝒟 (m + 1) F := sorry

local instance : IsSelfConcordantBarrierOnWith 𝒟 (m + 1) F :=
  qcqpStrictEpigraphLogarithmicBarrier_isSelfConcordantBarrierOnWith problem

-- Proof sketch: identify `closure 𝒟` with the owner feasible set `ℱ` using
-- `closure_strictEpigraphFeasibleSet_eq_epigraphFeasibleSet`, then specialize the generic
-- short-step existence and complexity theory for self-concordant barriers to the QCQP epigraph
-- barrier. The resulting common witnesses `β`, `γ`, `C`, `x₀`, and `scheme` simultaneously
-- satisfy the six source-facing clauses of Proposition 5.4.3.2.
/-- Proposition 5.4.3.2: if a convex QCQP in epigraph form has nonempty strict feasible region,
admits an epigraph-optimal feasible point `xOpt`, and `ε > 0`, then there exist common
parameters `β`, `γ`, `C`, a starting point `x₀`, and a short-step path-following scheme for the
QCQP epigraph barrier such that:
`β < 1 / 2`, `γ > 0`, `C > 0`, the stopping iterate is feasible for the epigraph
reformulation, its epigraph objective value is within `ε` of the epigraph-optimal reference
value `P (xOpt : Eₙ × ℝ)`, and its stopping index satisfies the stated logarithmic iteration
bound. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ C : NNRealˣ,
          ∃ x0 : problem.StrictEpigraphFeasiblePoint,
            ∃ scheme : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
              beta < 1 / 2 ∧
                0 < gamma ∧
                scheme scheme.stopIndex ∈ ℱ ∧
                P (scheme scheme.stopIndex) ≤ P (xOpt : Eₙ × ℝ) + ε ∧
                scheme.stopIndex ≤
                  ⌈((C : NNReal) : ℝ) * Real.sqrt (m + 1 : ℝ) *
                      Real.log ((m + 1 : ℝ) / ε)⌉₊ := sorry

-- Proof sketch: project the `β < 1 / 2` clause from the common witness package theorem above.
/-- Proposition 5.4.3.2 (1): under the hypotheses of Proposition 5.4.3.2, the common short-step
scheme can be chosen with initial centering parameter `β < 1 / 2`. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph_beta_lt_half
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ x0 : problem.StrictEpigraphFeasiblePoint,
          ∃ _ : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
            beta < 1 / 2 := by
  rcases exists_shortStepPathFollowingScheme_for_qcqpEpigraph problem hstrict xOpt hopt hε with
    ⟨beta, gamma, C, x0, scheme, hβ, -, -, -, -⟩
  exact ⟨beta, gamma, x0, scheme, hβ⟩

-- Proof sketch: specialize the general short-step path-following existence theorem for the
-- QCQP epigraph logarithmic barrier and extract the positive stepsize parameter `γ`.
/-- Proposition 5.4.3.2 (2): under the same hypotheses, there exists such a short-step scheme
with a positive update parameter `γ`. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph_gamma_pos
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ x0 : problem.StrictEpigraphFeasiblePoint,
          ∃ _ : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
            0 < gamma := by
  rcases exists_shortStepPathFollowingScheme_for_qcqpEpigraph problem hstrict xOpt hopt hε with
    ⟨beta, gamma, C, x0, scheme, -, hγ, -, -, -⟩
  exact ⟨beta, gamma, x0, scheme, hγ⟩

-- Proof sketch: the same existence theorem yields a positive absolute constant controlling the
-- complexity bound in the QCQP epigraph setting.
/-- Proposition 5.4.3.2 (3): under the same hypotheses, there exists such a short-step scheme
with a positive iteration-bound constant `C`. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph_constant_pos
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ C : NNRealˣ,
          ∃ x0 : problem.StrictEpigraphFeasiblePoint,
            ∃ _ : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
              0 < ((C : NNReal) : ℝ) := by
  rcases exists_shortStepPathFollowingScheme_for_qcqpEpigraph problem hstrict xOpt hopt hε with
    ⟨beta, gamma, C, x0, scheme, -, -, -, -, -⟩
  refine ⟨beta, gamma, C, x0, scheme, ?_⟩
  have hC : (0 : NNReal) < (C : NNReal) := by
    exact pos_iff_ne_zero.mpr (Units.ne_zero C)
  exact_mod_cast hC

-- Proof sketch: the short-step existence theory produces a stopping iterate that remains in the
-- strict barrier domain, hence is feasible for the nonstrict QCQP epigraph problem.
/-- Proposition 5.4.3.2 (4): under the same hypotheses, there exists a short-step QCQP epigraph
scheme whose stopping iterate is feasible for the epigraph reformulation. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph_stop_feasible
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ x0 : problem.StrictEpigraphFeasiblePoint,
          ∃ scheme : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
            scheme scheme.stopIndex ∈ ℱ := by
  rcases exists_shortStepPathFollowingScheme_for_qcqpEpigraph problem hstrict xOpt hopt hε with
    ⟨beta, gamma, C, x0, scheme, -, -, hfeas, -, -⟩
  exact ⟨beta, gamma, x0, scheme, hfeas⟩

-- Proof sketch: specialize the generic `ε`-accuracy guarantee for short-step path-following on
-- self-concordant barriers to the QCQP epigraph owner `P`, whose objective is the slack
-- coordinate `τ`, and compare the stopping iterate with the epigraph-optimal reference point
-- `xOpt`.
/-- Proposition 5.4.3.2 (5): under the same hypotheses, there exists a short-step QCQP epigraph
scheme whose stopping iterate has epigraph-objective value within `ε` of the epigraph-optimal
reference value `P (xOpt : Eₙ × ℝ)`. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph_stop_tau_le_add_epsilon
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ x0 : problem.StrictEpigraphFeasiblePoint,
          ∃ scheme : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
            P (scheme scheme.stopIndex) ≤ P (xOpt : Eₙ × ℝ) + ε := by
  rcases exists_shortStepPathFollowingScheme_for_qcqpEpigraph problem hstrict xOpt hopt hε with
    ⟨beta, gamma, C, x0, scheme, -, -, -, hgap, -⟩
  exact ⟨beta, gamma, x0, scheme, hgap⟩

-- Proof sketch: combine the source-facing `xOpt` comparison with the owner-level optimality
-- property of `xOpt` on the feasible set `ℱ` to compare the stopping iterate with any feasible
-- epigraph point.
/-- Companion corollary: under the same hypotheses, the stopping iterate from Proposition
5.4.3.2 also has `τ`-value within `ε` of every feasible epigraph value. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph_stop_tau_le_feasible_add_epsilon
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ x0 : problem.StrictEpigraphFeasiblePoint,
          ∃ scheme : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
            ∀ y ∈ ℱ, P (scheme scheme.stopIndex) ≤ P y + ε := by
  rcases exists_shortStepPathFollowingScheme_for_qcqpEpigraph problem hstrict xOpt hopt hε with
    ⟨beta, gamma, C, x0, scheme, -, -, -, hgap, -⟩
  refine ⟨beta, gamma, x0, scheme, ?_⟩
  intro y hy
  have hopt' : ∀ z ∈ ℱ, P (xOpt : Eₙ × ℝ) ≤ P z :=
    isMinOn_iff.mp hopt
  have hxOpt_le : P (xOpt : Eₙ × ℝ) ≤ P y := by
    exact hopt' y hy
  have hxOpt_le_add : P (xOpt : Eₙ × ℝ) + ε ≤ P y + ε := by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hxOpt_le ε
  exact le_trans hgap hxOpt_le_add

-- Proof sketch: apply the standard short-step iteration complexity estimate for
-- `ν = m + 1` self-concordant barriers to the QCQP epigraph barrier.
/-- Proposition 5.4.3.2 (6): under the same hypotheses, there exists a short-step QCQP epigraph
scheme whose stopping index satisfies the bound
`O(√(m + 1) log ((m + 1) / ε))` with an explicit constant `C`. -/
theorem exists_shortStepPathFollowingScheme_for_qcqpEpigraph_iteration_bound
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ C : NNRealˣ,
          ∃ x0 : problem.StrictEpigraphFeasiblePoint,
            ∃ scheme : BarrierPathFollowingScheme cτ F (m + 1) x0 beta gamma ε,
              scheme.stopIndex ≤
                ⌈((C : NNReal) : ℝ) * Real.sqrt (m + 1 : ℝ) *
                    Real.log ((m + 1 : ℝ) / ε)⌉₊ := by
  rcases exists_shortStepPathFollowingScheme_for_qcqpEpigraph problem hstrict xOpt hopt hε with
    ⟨beta, gamma, C, x0, scheme, -, -, -, -, hbound⟩
  exact ⟨beta, gamma, C, x0, scheme, hbound⟩

end
