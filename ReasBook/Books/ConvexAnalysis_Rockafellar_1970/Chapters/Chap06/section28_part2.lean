import Mathlib
import Mathlib.Order.Filter.Extr
import Mathlib.Order.SaddlePoint
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_6_28_3 (from Chap06) -/
universe u v

noncomputable section

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜] [DecidableLT 𝕜] [AddCommGroup 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.28.3 states that for each fixed primal point `x`, the
  Lagrangian slice in the multiplier variable `u⋆` is concave.
- `core/canonical`: the Lagrangian owner is `OrdinaryConvexProgram.saddleLagrangian` from
  `Definition_6_28_3`, with the multiplier-set and branch lemmas supplied by
  `Definition_6_28_6`.
- `bridge/view`: the chapter's canonical owner for global extended-valued concavity is
  `Function.IsConcave`, while `Function.IsConcave.convex_neg` remains the internal sign-dual
  bridge to convexity of the negated slice.

Domain-style sampling used here:
- `OrdinaryConvexProgram.saddleLagrangian` from `Definition_6_28_3`;
- `OrdinaryConvexProgram.multiplierSet` and its branch lemmas from `Definition_6_28_6`;
- `Function.IsConcave` from `Definition_6_30_2`;
- `Function.IsConcave.convex_neg` from `Definition_6_30_2`.

Primitive data vs derived API:
- primitive source data: the program `P` and the fixed primal point `x`;
- core owner statement: the dual slice `P.saddleLagrangian · x`;
- derived curvature API: `(P.saddleLagrangian · x).IsConcave`.

Layer target: `bridge/view`. The proposition adds a curvature property of the existing
Lagrangian owner; it should not introduce a second Lagrangian wrapper or a surrogate multiplier
owner.
-/

variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

-- Proof sketch: split on whether the fixed primal point lies in `P.constraintSet`. Off the
-- constraint set the dual slice is constantly `⊤`, hence concave. On the constraint set,
-- Definition 6.28.6 makes the slice equal to an affine function on `multiplierSet` and equal
-- to `⊥` off that convex set, so the negated slice is the pointwise supremum of convex affine
-- minorants and is therefore globally convex.
/-- Proposition 6.28.3: for each fixed primal point `x`, the Lagrangian slice in the multiplier
variable is concave on the whole multiplier space. The chapter's canonical owner for that
conclusion is `Function.IsConcave`. -/
theorem lagrangianDualSlice_isConcave
    (x : E) :
    (P.saddleLagrangian · x).IsConcave 𝕜 := sorry

end OrdinaryConvexProgram

end

/-! ### Theorem_6_28_3 (from Chap06) -/
noncomputable section

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {ι κ : Type} [Fintype ι] [Fintype κ]

open scoped Rockafellar

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.28.3 is Rockafellar's Kuhn--Tucker existence theorem for an ordinary
  convex program under the qualification that the nonaffine inequality constraints are satisfied
  strictly at some feasible point.
- `core/canonical`: the Chapter 6 owners already present are `P.feasibleSet`,
  `P.optimalValue`, and `P.IsKuhnTuckerVector`.
- `bridge/view`: the source set `I` of indices of nonaffine inequality constraints is expressed
  intrinsically by `¬ affOn[𝕜](extendZero (P.inequality i), P.constraintSet)`, while the source
  phrase “there is a feasible solution strict in `i ∈ I`” is packaged as a single qualification
  predicate on `P`.

Domain-style sampling used here:
- `OrdinaryConvexProgram` and `affOn[𝕜](·, ·)` (on `extendZero` realizations) from
  `Definition_6_28_1`;
- `P.feasibleSet`, `P.optimalValue`, and `P.IsKuhnTuckerVector` from `Definition_6_28_3`;
- intrinsic constrained-data evaluation `P.inequality i x` for `x : P.constraintSet`.

Primitive data vs derived API:
- primitive source data: the existing program owner `P`;
- source-facing qualification: existence of a feasible point where every nonaffine inequality
  constraint is strict;
- derived theorem: existence of multiplier blocks `(lam, μ)` forming a Kuhn--Tucker vector.

Layer target: `source-facing`. The theorem is stated directly on the existing program and
Kuhn--Tucker owners, with the source qualification isolated as one reusable predicate rather than
as an existential package or surrogate program wrapper.
-/

variable {r s : ℕ}
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

/-- A feasible point of `P` is strictly feasible on the nonaffine inequalities if every
inequality constraint that is not affine on `P.constraintSet` is satisfied strictly there. The
owner is stated on the canonical feasible-set layer of `P`. -/
def HasStrictlyFeasiblePointOnNonaffineInequalities : Prop :=
  ∃ x : P.feasibleSet,
    ∀ i, ¬ affOn[𝕜](extendZero (P.inequality i), P.constraintSet) →
      extendZero (P.inequality i) x.1 < 0

-- Proof sketch: this is the definitional expansion of
-- `HasStrictlyFeasiblePointOnNonaffineInequalities` at the canonical feasible-set owner layer.
/-- The nonaffine strict-feasibility qualification is exactly the existence of a feasible point
whose nonaffine inequalities are strict. -/
theorem hasStrictlyFeasiblePointOnNonaffineInequalities_iff_exists_feasiblePoint :
    P.HasStrictlyFeasiblePointOnNonaffineInequalities ↔
      ∃ x : P.feasibleSet,
        ∀ i, ¬ affOn[𝕜](extendZero (P.inequality i), P.constraintSet) →
          extendZero (P.inequality i) x.1 < 0 :=
  Iff.rfl

-- Proof sketch: expand feasibility through the intrinsic split owner
-- `P.mem_feasibleSet`, then use `extendZero_apply` only as a bridge for the strict-inequality
-- clause stated in ambient form.
/-- Bridge form of nonaffine strict feasibility: this recovers the fully expanded constrained-data
surface with weak feasibility plus strictness on nonaffine inequalities. -/
theorem hasStrictlyFeasiblePointOnNonaffineInequalities_iff :
    P.HasStrictlyFeasiblePointOnNonaffineInequalities ↔
      ∃ x : P.constraintSet,
        (∀ i, P.inequality i x ≤ 0) ∧
          (∀ j, P.equality j x = 0) ∧
          (∀ i, ¬ affOn[𝕜](extendZero (P.inequality i), P.constraintSet) →
            P.inequality i x < 0) := by
  constructor
  · rintro ⟨x, hxStrict⟩
    rcases (P.mem_feasibleSet x.1).1 x.2 with ⟨hxC, hxI, hxE⟩
    refine ⟨⟨x.1, hxC⟩, hxI, hxE, ?_⟩
    · intro i hnonaffine
      have hxI : extendZero (P.inequality i) x.1 < 0 := hxStrict i hnonaffine
      have hxIeq :
          extendZero (P.inequality i) x.1 =
            P.inequality i ⟨x.1, hxC⟩ := by
        simpa using (extendZero_apply (P.inequality i) ⟨x.1, hxC⟩)
      exact hxIeq ▸ hxI
  · rintro ⟨x, hxIneq, hxEq, hxStrict⟩
    have hxFeasible : x.1 ∈ P.feasibleSet := by
      exact (P.mem_feasibleSet x.1).2 ⟨x.2, hxIneq, hxEq⟩
    refine ⟨⟨x.1, hxFeasible⟩, ?_⟩
    intro i hnonaffine
    simpa [extendZero_apply] using hxStrict i hnonaffine

-- Proof sketch: in the pure-inequality case, apply the mixed strict/weak separation theorem from
-- Chapter 21 to the optimal-value-shifted system consisting of the strict nonaffine block and the
-- weak affine block, then normalize the objective coefficient to `1` and read off a
-- Kuhn--Tucker vector. When equality constraints are present, replace each affine equality by the
-- pair of weak inequalities `h ≤ 0` and `-h ≤ 0`, apply the already proved inequality case, and
-- combine the two resulting coefficient blocks into the unrestricted equality multipliers.
/-- Theorem 6.28.3: if the optimal value of an ordinary convex program is not `-∞` and the
program has a feasible point at which every nonaffine inequality constraint is strict, then a
Kuhn--Tucker vector exists for the program. -/
theorem exists_kuhnTuckerVector_of_nonaffine_strict_feasibility
    (hopt : P.optimalValue ≠ ⊥)
    (hstrict : P.HasStrictlyFeasiblePointOnNonaffineInequalities) :
    ∃ lam : ι → 𝕜, ∃ μ : κ → 𝕜, P.IsKuhnTuckerVector lam μ := sorry

end OrdinaryConvexProgram

end

/-! ### Corollary_6_28_4 (from Chap06) -/
noncomputable section

universe u v

open scoped Rockafellar

section

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.28.4 is the linear-constraint specialization of the Kuhn--Tucker
  existence theorem for ordinary convex programs.
- `core/canonical`: the existing Chapter 6 owners are `OrdinaryConvexProgram`, `P.optimalValue`,
  `P.feasibleSet`, and `P.IsKuhnTuckerVector`.
- `bridge/view`: the source phrase “only linear constraints” is expressed canonically by requiring
  each inequality constraint to be affine on `P.constraintSet`, now at the intrinsic
  owner `affOn[𝕜](·, ·)` on the canonical ambient extension `extendZero (P.inequality i)`; the
  equality block is already affine by the defining data of `OrdinaryConvexProgram`.

Domain-style sampling used here:
- `OrdinaryConvexProgram` and `affOn[𝕜](·, ·)` (on `extendZero` realizations) from
  `Definition_6_28_1`;
- `P.feasibleSet`, `P.optimalValue`, and `P.IsKuhnTuckerVector` from
  `Definition_6_28_3`;
- `P.HasStrictlyFeasiblePointOnNonaffineInequalities` and
  `exists_kuhnTuckerVector_of_nonaffine_strict_feasibility` from `Theorem_6_28_3`;
- the relative-interior owner notation `ri[𝕜](·)` from `Chap02.Text_6_8`.

Primitive data vs derived API:
- primitive source-facing data: an ordinary convex program `P`, affine inequality constraints,
  and a feasible point;
- derived qualification: nonaffine strict feasibility (vacuous when every inequality is affine);
- derived conclusion: existence of a Kuhn--Tucker multiplier pair for `P`.

Layer target: `source-facing`, with the canonical intrinsic constrained-data affine owner on the
theorem surface.
-/

variable {r s : ℕ} (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s)

-- Proof sketch: if every inequality is affine on the constraint-set owner layer, there are no
-- nonaffine inequalities. Hence any feasible point witnesses
-- `HasStrictlyFeasiblePointOnNonaffineInequalities`.
/-- If all inequality constraints are affine on `P.constraintSet`, then any feasible point of `P`
induces the nonaffine strict-feasibility qualification from Theorem 6.28.3. -/
theorem hasStrictlyFeasiblePointOnNonaffineInequalities_of_affine_inequalities_and_feasiblePoint
    (haffine : ∀ i, affOn[𝕜](extendZero (P.inequality i), P.constraintSet))
    (hfeas : ∃ x : E, x ∈ P.feasibleSet) :
    P.HasStrictlyFeasiblePointOnNonaffineInequalities := by
  rcases hfeas with ⟨x, hxFeas⟩
  refine ⟨⟨x, hxFeas⟩, ?_⟩
  intro i hnonaffine
  exact False.elim (hnonaffine (haffine i))

-- Proof sketch: affine inequalities and a feasible point give the nonaffine strict-feasibility
-- qualification via
-- `hasStrictlyFeasiblePointOnNonaffineInequalities_of_affine_inequalities_and_feasiblePoint`,
-- then apply `exists_kuhnTuckerVector_of_nonaffine_strict_feasibility`.
/-- Primitive owner form of Corollary 6.28.4: if every inequality of `P` is affine on
`P.constraintSet`, `P.optimalValue ≠ ⊥`, and `P.feasibleSet` is nonempty, then `P` admits a
Kuhn--Tucker vector. -/
theorem exists_kuhnTuckerVector_of_affine_inequalities_and_feasiblePoint
    (hopt : P.optimalValue ≠ ⊥)
    (haffine : ∀ i, affOn[𝕜](extendZero (P.inequality i), P.constraintSet))
    (hfeas : ∃ x : E, x ∈ P.feasibleSet) :
    ∃ lam : Fin r → 𝕜, ∃ μ : Fin s → 𝕜, P.IsKuhnTuckerVector lam μ := by
  have hstrict : P.HasStrictlyFeasiblePointOnNonaffineInequalities :=
    P.hasStrictlyFeasiblePointOnNonaffineInequalities_of_affine_inequalities_and_feasiblePoint
      haffine hfeas
  exact P.exists_kuhnTuckerVector_of_nonaffine_strict_feasibility hopt hstrict

end OrdinaryConvexProgram

end

section

variable {𝕜 : Type v} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]

namespace OrdinaryConvexProgram

variable {r s : ℕ} (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s)

-- Proof sketch: `hri` immediately yields a feasible point, so the primitive owner theorem
-- `exists_kuhnTuckerVector_of_affine_inequalities_and_feasiblePoint` applies directly.
/-- Corollary 6.28.4 (source-facing form): if an ordinary convex program has only linear
constraints, formalized by the intrinsic affineness of every inequality on `P.constraintSet`, its
optimal value is not `-∞`, and the feasible set meets `ri[𝕜](P.constraintSet)`, then a Kuhn--Tucker
vector exists. The equality constraints are already affine by the defining data of
`OrdinaryConvexProgram`. -/
theorem exists_kuhnTuckerVector_of_affine_inequalities_and_ri_feasiblePoint
    (hopt : P.optimalValue ≠ ⊥)
    (haffine : ∀ i, affOn[𝕜](extendZero (P.inequality i), P.constraintSet))
    (hri : ∃ x : E, x ∈ P.feasibleSet ∩ ri[𝕜](P.constraintSet)) :
    ∃ lam : Fin r → 𝕜, ∃ μ : Fin s → 𝕜, P.IsKuhnTuckerVector lam μ := by
  refine P.exists_kuhnTuckerVector_of_affine_inequalities_and_feasiblePoint hopt haffine ?_
  rcases hri with ⟨x, hx, -⟩
  exact ⟨x, hx⟩

end OrdinaryConvexProgram

end

/-! ### Definition_6_28_4 (from Chap06) -/
universe u v w

noncomputable section

attribute [local instance] Classical.propDecidable

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]

namespace OrdinaryConvexProgram

variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.4 introduces, for a fixed ordinary convex program `P`, the
  perturbed problem obtained by replacing the zero right-hand sides of the inequality and equality
  constraints by prescribed perturbation levels.
- `core/canonical`: in the project, a constrained minimization problem is most naturally encoded
  as the finite objective extended by `+∞` off its feasible set, via
  `Function.toWithTopBotOn`.
- `bridge/view`: because `OrdinaryConvexProgram` already represents the textbook indices
  `1, …, r` and `r + 1, …, m` by the canonical owner `P.ConstraintIndex`, the perturbation vector
  is represented intrinsically as one map `u : P.ConstraintIndex → β`.

Domain-style sampling used here:
- `OrdinaryConvexProgram` and `extendZero` from `Definition_6_28_1`;
- `OrdinaryConvexProgram.relation`, `OrdinaryConvexProgram.constraint`,
  and `LinearConstraintRelation.feasibleSet`;
- `Function.toWithTopBotOn` from `Remark_4_4_5`.

Primitive data vs derived API:
- primitive source data: the base program `P` and one perturbation vector
  `u : P.ConstraintIndex → β`;
- supporting source-facing data: the perturbed feasible set cut out by that perturbation vector;
- main owner: the perturbed problem as the canonical `WithTopBot β`-valued extension of the
  objective to the perturbed feasible set, with the mixed relation and constraint family reused
  from `Definition_6_28_2`.

Layer target: `source-facing` with a canonical extended-value owner. This item defines a genuine
perturbed problem attached to `P`, so it should stay public; the feasible-set description is a
supporting bridge, not a separate wrapper owner.
-/

/-- The feasible set of the perturbed problem attached to `P` with perturbation vector
`u : P.ConstraintIndex → β`. -/
def perturbedFeasibleSet (u : P.ConstraintIndex → β) : Set E :=
  P.constraintSet ∩
    LinearConstraintRelation.feasibleSet
      P.relation
      P.constraint
      u

/-- Definition 6.28.4: the perturbed problem `(P_u)` attached to an ordinary convex program `P`.
The textbook perturbation vector `u = (v₁, …, v_m)` is represented canonically as one map on the
disjoint index owner `P.ConstraintIndex`, where `u (Sum.inl i)` are inequality bounds and
`u (Sum.inr j)` are equality targets. The problem is encoded as the objective extended by `+∞`
off the perturbed feasible set. -/
def perturbedProblem (u : P.ConstraintIndex → β) : E → WithTopBot β :=
  Function.toWithTopBotOn (extendZero P.objective) (P.perturbedFeasibleSet u)

-- Proof sketch: unfold `perturbedFeasibleSet`; membership in the intersections is exactly the
-- ambient constraint together with the mixed relation family attached to `P`.
/-- Intrinsic owner-level membership characterization: `x` belongs to the perturbed feasible set
iff it belongs to the source constraint set and satisfies each mixed linear relation prescribed by
`P.relation` at level `u`. -/
@[simp] theorem mem_perturbedFeasibleSet
    {u : P.ConstraintIndex → β} {x : E} :
    x ∈ P.perturbedFeasibleSet u ↔
      x ∈ P.constraintSet ∧
        (∀ i, (P.relation i).holds (P.constraint i x) (u i)) := by
  constructor
  · rintro ⟨hxC, hx⟩
    refine ⟨hxC, ?_⟩
    exact (LinearConstraintRelation.mem_feasibleSet
      P.relation P.constraint u x).1 hx
  · rintro ⟨hxC, hx⟩
    refine ⟨hxC, ?_⟩
    exact (LinearConstraintRelation.mem_feasibleSet
      P.relation P.constraint u x).2 hx

-- Proof sketch: specialize `mem_perturbedFeasibleSet` to the left (`ι`) and right (`κ`)
-- blocks of `P.ConstraintIndex`, then unfold the intrinsic `Sum.elim` owners
-- `P.relation` and `P.constraint`.
/-- Source-facing split view of `mem_perturbedFeasibleSet`: membership means belonging to the
original constraint set, satisfying each perturbed inequality bound, and satisfying each perturbed
equality target. -/
theorem mem_perturbedFeasibleSet_split
    {u : P.ConstraintIndex → β} {x : E} :
    x ∈ P.perturbedFeasibleSet u ↔
      ∃ hxC : x ∈ P.constraintSet,
        (∀ i, P.inequality i ⟨x, hxC⟩ ≤ u (Sum.inl i)) ∧
        (∀ j, P.equality j ⟨x, hxC⟩ = u (Sum.inr j)) := by
  constructor
  · intro hx
    rcases (P.mem_perturbedFeasibleSet).1 hx with ⟨hxC, hrel⟩
    refine ⟨hxC, ?_, ?_⟩
    · intro i
      have hi : extendZero (P.inequality i) x ≤ u (Sum.inl i) := by
        simpa [OrdinaryConvexProgram.relation, OrdinaryConvexProgram.constraint] using
          hrel (Sum.inl i)
      have hix : extendZero (P.inequality i) x = P.inequality i ⟨x, hxC⟩ := by
        simpa using (extendZero_apply (P.inequality i) ⟨x, hxC⟩)
      exact hix ▸ hi
    · intro j
      have hj : extendZero (P.equality j) x = u (Sum.inr j) := by
        simpa [OrdinaryConvexProgram.relation, OrdinaryConvexProgram.constraint] using
          hrel (Sum.inr j)
      have hjx : extendZero (P.equality j) x = P.equality j ⟨x, hxC⟩ := by
        simpa using (extendZero_apply (P.equality j) ⟨x, hxC⟩)
      exact hjx ▸ hj
  · rintro ⟨hxC, hI, hE⟩
    refine (P.mem_perturbedFeasibleSet).2 ?_
    refine ⟨hxC, ?_⟩
    intro i
    cases i with
    | inl j =>
        have hix : extendZero (P.inequality j) x = P.inequality j ⟨x, hxC⟩ := by
          simpa using (extendZero_apply (P.inequality j) ⟨x, hxC⟩)
        have hi : extendZero (P.inequality j) x ≤ u (Sum.inl j) := by
          simpa [hix] using hI j
        simpa [OrdinaryConvexProgram.relation, OrdinaryConvexProgram.constraint] using hi
    | inr j =>
        have hjx : extendZero (P.equality j) x = P.equality j ⟨x, hxC⟩ := by
          simpa using (extendZero_apply (P.equality j) ⟨x, hxC⟩)
        have hj : extendZero (P.equality j) x = u (Sum.inr j) := by
          simpa [hjx] using hE j
        simpa [OrdinaryConvexProgram.relation, OrdinaryConvexProgram.constraint] using hj

-- Proof sketch: unfold `perturbedProblem` and rewrite `Function.toWithTopBotOn` as its
-- canonical two-branch piecewise definition on `P.perturbedFeasibleSet u`.
/-- The perturbed problem takes the original objective value on the perturbed feasible set and the
value `+∞` outside it. -/
@[simp] theorem perturbedProblem_apply
    (u : P.ConstraintIndex → β) (x : E) :
    P.perturbedProblem u x =
      if x ∈ P.perturbedFeasibleSet u
      then ((extendZero P.objective x : β) : WithTopBot β)
      else ⊤ := by
  by_cases hx : x ∈ P.perturbedFeasibleSet u
  · simp [perturbedProblem, hx]
  · simp [perturbedProblem, hx]

end OrdinaryConvexProgram

namespace OrdinaryConvexProgram

section PureInequality

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {δ : Type w} [AddCommMonoid δ] [PartialOrder δ] [SMul 𝕜 δ]
variable {m : ℕ} {ι : Type}
variable [Fintype ι] [Fact (Fintype.card ι = m)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithTopBot δ) m 0 ι)

/-- Bridge owner for `s = 0`: insert a perturbation vector `u : ι → δ` into the canonical
perturbation owner `P.ConstraintIndex → WithTopBot δ` by using `u` on the inequality block and
the unique function on the empty equality block. -/
abbrev pureInequalityPerturbation (u : ι → δ) : P.ConstraintIndex → WithTopBot δ :=
  Sum.elim (fun i ↦ (u i : WithTopBot δ)) Fin.elim0

/-- Bridge/view: in the pure-inequality case, the perturbed problem may be read as a bifunction on
the source perturbation space `δ^m`, represented intrinsically as `ι → δ`, by inserting the
perturbation vector into the inequality block and using the unique empty equality block. Since the
objective branch is already `WithTopBot δ`-valued, this bridge keeps that codomain and uses the
canonical two-branch
`Set.piecewise` owner rather than adding another `WithTopBot` layer. -/
abbrev pureInequalityPerturbedProblem
    : (ι → δ) → E → WithTopBot δ :=
  fun u ↦
    (P.perturbedFeasibleSet (P.pureInequalityPerturbation u)).piecewise
      (extendZero P.objective)
      ⊤

@[simp] theorem pureInequalityPerturbedProblem_apply (u : ι → δ) (x : E) :
    P.pureInequalityPerturbedProblem u x =
      if x ∈ P.perturbedFeasibleSet (P.pureInequalityPerturbation u) then
        extendZero P.objective x
      else
        ⊤ := by
  by_cases hx : x ∈ P.perturbedFeasibleSet (P.pureInequalityPerturbation u)
  · simp [pureInequalityPerturbedProblem, hx]
  · simp [pureInequalityPerturbedProblem, hx]

end PureInequality

end OrdinaryConvexProgram

end

/-! ### Proposition_6_28_4 (from Chap06) -/
universe u v w z

section

variable {𝕜 : Type w} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {I : Sort v}
variable {α : Type z} [AddCommGroup α] [SMul 𝕜 α]
variable [ConditionallyCompleteLattice α] [IsOrderedAddMonoid α]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 6.28.4 states that the pointwise infimum of concave functions is
  concave.
- `core/canonical`: the chapter owner for global concavity is `Function.IsConcave` from
  Definition 6.30.2, and the canonical infimum closure owner is the set form
  `Function.IsConcave.sInf`.
- `bridge/view`: the indexed-family theorem `Function.IsConcave.iInf` is the `iInf` bridge form,
  while the proof route uses the upstream convex owner theorem `Function.IsConvex.iSup`.
- Primitive data vs derived API: for `iInf`, the family `f : I → E → WithTopBot α` and the
  concavity of each `f i` are primitive; for `sInf`, the primitive data are a set family
  `F : Set (E → WithTopBot α)` and its memberwise concavity.

Domain-style sampling used here:
- `Function.IsConcave` and `Function.IsConcave.convex_neg`;
- `Function.IsConvex`;
- `Function.IsConvex.iSup`;
- `WithTopBot.negOrderIso.map_iInf`.

Layer target: `source-facing`. The public closure owner is exposed on `Function.IsConcave`,
with `sInf` as canonical owner form and `iInf` as the indexed bridge surface.
-/

/-- Proposition 6.28.4 (owner method form): concavity is closed under pointwise indexed
infima. The source states this on `R^m`; the chapter's canonical whole-space owner for that
conclusion is `Function.IsConcave`, and the proof uses the existing convex-owner closure theorem
on the negated family. -/
theorem IsConcave.iInf
    {f : I → E → WithTopBot α}
    (hf : ∀ i, (f i).IsConcave 𝕜) :
    (⨅ i, f i).IsConcave 𝕜 := by
  have hneg_iInf_point (g : I → WithTopBot α) : -(⨅ i, g i) = ⨆ i, -g i := by
    exact congrArg OrderDual.ofDual (WithTopBot.negOrderIso.map_iInf g)
  have hneg_iInf : -(⨅ i, f i) = ⨆ i, -f i := by
    ext x
    change -((⨅ i, f i) x) = (⨆ i, -f i) x
    simpa [iInf_apply, iSup_apply] using hneg_iInf_point (fun i ↦ f i x)
  change (-(⨅ i, f i)).IsConvex 𝕜
  rw [hneg_iInf]
  exact IsConvex.iSup (fun i ↦ (hf i).convex_neg)

/-- Proposition 6.28.4 (set-owner form): concavity is closed under pointwise set infima. This is
`Function.IsConcave.iInf` packaged on the intrinsic set-family owner `SupSet.sInf`, so downstream
items can use the canonical set form directly without introducing an auxiliary index type. -/
theorem IsConcave.sInf
    {F : Set (E → WithTopBot α)}
    (hF : ∀ f ∈ F, f.IsConcave 𝕜) :
    (SupSet.sInf F).IsConcave 𝕜 := by
  classical
  simpa [sInf_eq_iInf'] using
    (IsConcave.iInf (f := fun f : F ↦ (f : E → WithTopBot α))
      (hf := fun f ↦ hF f f.property))

end Function

end

/-! ### Theorem_6_28_4 (from Chap06) -/
noncomputable section

universe u v

namespace OrdinaryConvexProgram
open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.28.4 identifies Kuhn-Tucker multipliers and optimal points with
  saddle-points of the Lagrangian, and then rewrites that saddle condition in the source
  coordinatewise form.
- `core/canonical`: the already built Chapter 6 owners are `P.IsKuhnTuckerVector`,
  `P.feasibleSet`, `P.feasibleObjective`, `P.weightedObjective`, `P.IsOptimalSolution`,
  `P.saddleLagrangian`, the source multiplier domain `multiplierSet`, and the source-order
  saddle-point owner `Bifunction.IsSaddlePointOn`, together with the pairing-based Chapter 23
  owner `_root_.subdifferentialAt`.
- `bridge/view`: the source order `(u⋆, x)` is represented directly by
  `Bifunction.IsSaddlePointOn multiplierSet (Set.univ : Set E) (saddleLagrangian P) u⋆ x`,
  avoiding swapped-kernel ambient owner noise on theorem surfaces.

Domain-style sampling used here:
- `OrdinaryConvexProgram.IsKuhnTuckerVector` and `OrdinaryConvexProgram.weightedObjective`
  from `Definition_6_28_3`;
- `OrdinaryConvexProgram.multiplierSet` from `Definition_6_28_6`;
- `Bifunction.IsSaddlePointOn` from `Definition_6_28_7`;
- `_root_.subdifferentialAt` from `Chap05.Definition_23_0_6`.
-/

section Saddle

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

-- Proof sketch: rewrite the source supremum/infimum saddle condition for `P.saddleLagrangian`
-- into the equalities used in Definition 6.28.3. On the constraint set and for admissible
-- multipliers, the Lagrangian is exactly the weighted objective, while outside those source
-- domains the `⊥`/`⊤` branches force the dual and primal inequalities that recover
-- Kuhn-Tucker admissibility and primal optimality.
/-- Theorem 6.28.4 (1): a multiplier pair `(lam, μ)` is a Kuhn-Tucker vector for `P` and `x` is
an optimal solution of `P` if and only if `(lam, μ, x)` is a saddle-point of the source-order
Lagrangian of `P`. -/
theorem isKuhnTuckerVector_and_isOptimalSolution_iff_isSaddlePoint_saddleLagrangian
    (lam : ι → 𝕜) (μ : κ → 𝕜) (x : E) :
    P.IsKuhnTuckerVector lam μ ∧ P.IsOptimalSolution x ↔
      Bifunction.IsSaddlePointOn multiplierSet (Set.univ : Set E)
        (saddleLagrangian P) (lam, μ) x := sorry

end Saddle

section KuhnTuckerPoint

variable {𝕜 : Type v} [Semiring 𝕜] [LinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

/-- The source Kuhn-Tucker point conditions at `x`: feasibility of `x`, nonnegativity of the
inequality multipliers, complementary slackness, and primal minimization of the weighted
objective. For pairing ambient models, minimization yields the usual
`0 ∈ ∂(weightedObjective)` stationarity condition and is exposed below as a derived bridge. -/
structure IsKuhnTuckerPoint (lam : ι → 𝕜) (μ : κ → 𝕜) (x : E) : Prop where
  feasible : x ∈ P.feasibleSet
  nonneg : ∀ i, 0 ≤ lam i
  complementarySlackness :
    ∀ i, ((lam i : WithBotTop 𝕜) * extendZero (P.inequality i) x = 0)
  isMin : IsMinOn (P.weightedObjective lam μ) Set.univ x

-- Proof sketch: combine part (1) with the pointwise source description of the saddle inequalities.
-- Feasibility of `x` recovers the clauses `f_i(x) ≤ 0` and `h_j(x) = 0`, the maximization in the
-- multiplier variable forces `lam i ≥ 0` together with complementary slackness, and the
-- minimization in the primal variable is exactly `IsMinOn (P.weightedObjective lam μ) univ x`.
/-- Theorem 6.28.4 (2): the saddle-point condition for the Lagrangian is equivalent to the source
Kuhn-Tucker point conditions, packaged canonically as feasibility, nonnegative multipliers,
complementary slackness, and primal minimization of the weighted objective at `x`. -/
theorem isSaddlePoint_saddleLagrangian_iff_isKuhnTuckerPoint
    (lam : ι → 𝕜) (μ : κ → 𝕜) (x : E) :
    Bifunction.IsSaddlePointOn multiplierSet (Set.univ : Set E)
      (saddleLagrangian P) (lam, μ) x ↔
        P.IsKuhnTuckerPoint lam μ x := sorry

end KuhnTuckerPoint

section StationaryBridge

variable {𝕜 : Type v} [NormedField 𝕜] [LinearOrder 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

/-- Pairing-level bridge: if the distinguished zero dual element pairs to zero, then the minimizer
field in `P.IsKuhnTuckerPoint` gives the Chapter 23 stationarity form
`0 ∈ ∂(weightedObjective)` used in the source display. -/
theorem IsKuhnTuckerPoint.stationary_pairing
    {Y : Type (max u v)} [Zero Y] [HasPairing E Y 𝕜]
    (hpair_zero : ∀ z : E, (HasPairing.pairing z (0 : Y) : 𝕜) = 0)
    {lam : ι → 𝕜} {μ : κ → 𝕜} {x : E}
    (h : P.IsKuhnTuckerPoint lam μ x) :
    (0 : Y) ∈ _root_.subdifferentialAt (Y := Y) (P.weightedObjective lam μ) x := by
  rw [_root_.mem_subdifferentialAt_pairing]
  intro z
  have hz : P.weightedObjective lam μ x ≤ P.weightedObjective lam μ z :=
    (isMinOn_univ_iff.mp h.isMin) z
  simpa [hpair_zero (z - x)] using hz

/-- Canonical-dual specialization of `IsKuhnTuckerPoint.stationary_pairing`. -/
theorem IsKuhnTuckerPoint.stationary
    {lam : ι → 𝕜} {μ : κ → 𝕜} {x : E}
    (h : P.IsKuhnTuckerPoint lam μ x) :
    (0 : StrongDual 𝕜 E) ∈ (∂ (P.weightedObjective lam μ) at x) := by
  exact
    IsKuhnTuckerPoint.stationary_pairing (P := P) (Y := StrongDual 𝕜 E)
      (hpair_zero := fun z : E => rfl) h

end StationaryBridge

end OrdinaryConvexProgram

/-! ### Corollary_6_28_5 (from Chap06) -/
noncomputable section

universe u

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.28.5 is the Kuhn--Tucker optimality criterion for an ordinary
  convex program under the qualification hypothesis used in Theorem 6.28.3.
- `core/canonical`: the Chapter 6 owners already present are `P.IsOptimalSolution`,
  `P.HasStrictlyFeasiblePointOnNonaffineInequalities`, `P.IsKuhnTuckerPoint`,
  `multiplierSet`, and the source-order saddle-point owner `Bifunction.IsSaddlePointOn` applied to
  `saddleLagrangian P`.
- `bridge/view`: the source writes a single multiplier vector `u⋆`; in the local API this is the
  split multiplier data `(lam, μ)` with `lam : Fin r → 𝕜` for inequality constraints and
  `μ : Fin s → 𝕜` for equality constraints.

Domain-style sampling used here:
- `OrdinaryConvexProgram.HasStrictlyFeasiblePointOnNonaffineInequalities` and
  `exists_kuhnTuckerVector_of_nonaffine_strict_feasibility` from `Theorem_6_28_3`;
- `OrdinaryConvexProgram.IsOptimalSolution` and `OrdinaryConvexProgram.saddleLagrangian` from
  `Definition_6_28_3`;
- `OrdinaryConvexProgram.multiplierSet` from `Definition_6_28_6` through `Theorem_6_28_4`;
- `OrdinaryConvexProgram.IsKuhnTuckerPoint`,
  `isKuhnTuckerVector_and_isOptimalSolution_iff_isSaddlePoint_saddleLagrangian`, and
  `isSaddlePoint_saddleLagrangian_iff_isKuhnTuckerPoint` from `Theorem_6_28_4`;
- `Bifunction.IsSaddlePointOn` from `Definition_6_28_7` via `Theorem_6_28_4`.

Primitive data vs derived API:
- primitive source data: a program `P`, the qualification hypotheses from Theorem 6.28.3, and a
  candidate point `x`;
- main source-facing criterion: existence of multiplier blocks making `(lam, μ, x)` a saddle point
  of the source-order Lagrangian;
- derived equivalent criterion: existence of multiplier blocks making `x` a Kuhn--Tucker point.

Layer target: `source-facing`. This corollary stays on the existing Chapter 6 owners for optimal
solutions, saddle points, and Kuhn--Tucker points, without introducing a second optimality or
multiplier wrapper.
-/

section Saddle

variable {𝕜 : Type*} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {r s : ℕ} (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s)

-- Proof sketch: for the forward direction, apply
-- `exists_kuhnTuckerVector_of_nonaffine_strict_feasibility` to obtain multipliers `(lam, μ)`, and
-- then use `isKuhnTuckerVector_and_isOptimalSolution_iff_isSaddlePoint_saddleLagrangian` to turn
-- the Kuhn--Tucker vector together with optimality of `x` into a saddle-point statement. For the
-- reverse direction, a saddle point gives both a Kuhn--Tucker vector and optimality of `x` by the
-- same equivalence, so project the optimality component.
/-- Corollary 6.28.5: under the nonaffine strict-feasibility hypothesis of Theorem 6.28.3, a
point `x` is an optimal solution of an ordinary convex program `P` if and only if there exist
multiplier blocks `(lam, μ)` representing the source multiplier vector `u⋆` such that
`((lam, μ), x)` is a saddle-point of the `WithBotTop 𝕜`-valued Lagrangian used in
Theorem 6.28.4, with
the dual variable constrained to the multiplier set `Eᵣ = multiplierSet`. -/
theorem isOptimalSolution_iff_exists_isSaddlePoint_saddleLagrangian
    (hopt : P.optimalValue ≠ ⊥)
    (hstrict : P.HasStrictlyFeasiblePointOnNonaffineInequalities)
    (x : E) :
    P.IsOptimalSolution x ↔
      ∃ lam : Fin r → 𝕜, ∃ μ : Fin s → 𝕜,
        Bifunction.IsSaddlePointOn multiplierSet (Set.univ : Set E)
          (saddleLagrangian P) (lam, μ) x := sorry

end Saddle

section KuhnTuckerPoint

variable {𝕜 : Type*} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {r s : ℕ} (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s)

-- Proof sketch: combine
-- `isOptimalSolution_iff_exists_isSaddlePoint_saddleLagrangian` with
-- `isSaddlePoint_saddleLagrangian_iff_isKuhnTuckerPoint`; this rewrites the existential
-- saddle-point criterion as an existential Kuhn--Tucker point criterion with the same multiplier
-- blocks.
/-- Under the hypotheses of Theorem 6.28.3, optimality of `x` is equivalently the existence of
Lagrange multipliers `(lam, μ)` such that `x` is a Kuhn--Tucker point of `P`. -/
theorem isOptimalSolution_iff_exists_isKuhnTuckerPoint
    (hopt : P.optimalValue ≠ ⊥)
    (hstrict : P.HasStrictlyFeasiblePointOnNonaffineInequalities)
    (x : E) :
    P.IsOptimalSolution x ↔
      ∃ lam : Fin r → 𝕜, ∃ μ : Fin s → 𝕜, P.IsKuhnTuckerPoint lam μ x := sorry

end KuhnTuckerPoint

end OrdinaryConvexProgram

/-! ### Definition_6_28_5 (from Chap06) -/
universe u v w

noncomputable section

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]
variable [InfSet (WithBotTop β)]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.5 introduces the perturbation-value function of an ordinary
  convex program by taking, for each perturbation vector, the infimum of the corresponding
  perturbed problem.
- `core/canonical`: the existing Chapter 6 owner for such value functions is
  `Bifunction.perturbationFunction`.
- `bridge/view`: for an ordinary convex program `P`, the bifunction to which that owner is applied
  is the canonical extension by `+∞` of the objective to the perturbed feasible set, where the
  textbook vector `u = (v₁, …, v_m)` is represented on the canonical owner
  `P.ConstraintIndex`.

Domain-style sampling used here:
- `OrdinaryConvexProgram` and `extendZero` from `Definition_6_28_1`;
- `Function.toWithBotTopOn` from `Remark_4_4_5`;
- `Bifunction.perturbationFunction`;
- `Bifunction.perturbationFunction_apply`.

Primitive data vs derived API:
- primitive data: the ordinary convex program `P`;
- core/canonical owner: `Bifunction.perturbationFunction` applied directly to the perturbed-problem
  family attached to `P`;
- derived API: the pointwise value formula for that specialization, already owned upstream by
  `Bifunction.perturbationFunction_apply`.

Layer target: `source-facing` on top of the canonical owner. This item introduces the source
vocabulary `P.perturbationValue` as a thin owner-level specialization of
`Bifunction.perturbationFunction` to `P.perturbedProblem`, then reuses the canonical upstream
evaluation theorem.
-/

variable {r s : ℕ} (P : OrdinaryConvexProgram 𝕜 E β r s)

/-- Definition 6.28.5: the perturbation-value function of an ordinary convex program `P`,
obtained by specializing the chapter's canonical perturbation-function owner to
`P.perturbedProblem`. -/
abbrev perturbationValue : (P.ConstraintIndex → β) → WithBotTop β :=
  Bifunction.perturbationFunction P.perturbedProblem

/-- Evaluating the source-facing perturbation-value owner is the canonical row-infimum formula. -/
@[simp] theorem perturbationValue_apply
    (u : P.ConstraintIndex → β) :
    P.perturbationValue u = ⨅ x, P.perturbedProblem u x := by
  exact Bifunction.perturbationFunction_apply P.perturbedProblem u

end OrdinaryConvexProgram

end

/-! ### Theorem_6_28_5 (from Chap06) -/
noncomputable section

open scoped BigOperators Pointwise Rockafellar

universe u v

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.28.5 characterizes the subdifferential of the constrained objective
  from Definition 6.28.8 under the Slater condition, first by nonemptiness exactly on the feasible
  set and then by the usual multiplier formula with complementary slackness.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.toWithTopBotOn` on the finite feasible-set owner for the constrained objective and
  `dom∂(·)` / `Function.subdifferentialAt` for the subdifferential domain and subgradients of the
  resulting `WithTopBot ℝ`-valued function.
- `bridge/view`: Proposition 6.28.1 already identifies the subdifferential of the Definition
  6.28.8 constrained objective with the subdifferential of `f₀` plus the finite sum of the
  individual indicator-sublevel subdifferentials, while Proposition 6.28.2 gives the three
  source-facing cases for each individual indicator term. On the multiplier side, the owner
  abstraction is the canonical nonnegative cone `Set.Ici` on the finite function space
  `{i // i ∈ s} → ℝ`, with complementary slackness kept as the additional source predicate at `x`
  rather than repackaged as a second public subtype owner.

Domain-style sampling used here:
- the Definition 6.28.8 owner surface
  `Function.toWithTopBotOn f₀ (convexInequalitySolutionSetOn s (fun _ ↦ .le) f (fun _ ↦ 0))`;
- `dom∂(·)` and `mem_domSubdifferential` from `Chap05.Definition_5_24_1`;
- Proposition 6.28.1's constrained-subdifferential sum decomposition;
- `Function.subdifferentialAt_indicator_sublevel_eq_nonneg_smul_subdifferentialAt_of_eq_zero`;
- `Function.subdifferentialAt_indicator_sublevel_eq_singleton_zero_of_lt_zero`;
- `OrdinaryConvexProgram.multiplierSet`, whose `Set.Ici` owner is the chapter's canonical surface
  for nonnegative multiplier families.

Primitive data vs derived API:
- primitive source data: the finite-valued convex objective `f₀`, a finite subsystem `s`, the
  convex constraints `f i` on that subsystem, the Chapter 21 finite strict feasible-region owner
  on `s`, and the evaluation point `x`;
- primitive multiplier data for part (2): a family `μ : {i // i ∈ s} → ℝ` on the actual finite
  subsystem, together with nonnegativity from the canonical owner `Set.Ici` and the source
  complementary-slackness equalities;
- derived owner statements: membership in the constrained subdifferential domain `dom∂(·)` and
  the multiplier description of the constrained subdifferential set, both stated directly on the
  existing feasible-set owner rather than through local wrapper names.

Layer target: `source-facing`, stated directly on the existing constrained-objective and
subdifferential owners, with the Slater condition routed through the Chapter 21 owner instead of a
parallel subtype-indexed wrapper.
-/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type v}
variable (f₀ : E → ℝ) (s : Finset ι) (f : ι → E → ℝ)

variable (hf₀_convex : ConvexOn ℝ Set.univ f₀)
variable (hf_convex : ∀ i ∈ s, ConvexOn ℝ Set.univ (f i))
variable
    (hstrict :
      (strictConvexInequalitySolutionSetOn s f).Nonempty)

-- Proof sketch: use Proposition 6.28.1 to rewrite the constrained subdifferential as the sum of
-- the lifted objective subdifferential and the individual indicator-sublevel subdifferentials.
-- If some constraint is violated, Proposition 6.28.2 makes the corresponding indicator term
-- empty, so the whole sum is empty. Conversely, if every constraint is satisfied, each indicator
-- term is nonempty (`{0}` in the strict case and a nonnegative scalar hull in the active case),
-- and the finite-valued convex objective has a nonempty subdifferential at `x`.
/-- Theorem 6.28.5 (1): under the Slater condition, the constrained objective from Definition
6.28.8 lies in the Chapter 5 subdifferential-domain owner `dom∂(·)` exactly when `x` lies in the
Chapter 21 feasible-set owner `convexInequalitySolutionSetOn s (fun _ ↦ .le) f 0`, equivalently
when every inequality constraint is satisfied. -/
theorem mem_domSubdifferential_constrainedObjective_iff_feasible
    (x : E) :
    x ∈ dom∂(toWithTopBotOn f₀ (convexInequalitySolutionSetOn s (fun _ ↦ .le) f 0)) ↔
      x ∈ convexInequalitySolutionSetOn s (fun _ ↦ .le) f 0 := sorry

-- Proof sketch: start from the decomposition in Proposition 6.28.1. For each constraint index
-- `i`, apply the three-case formulas from Proposition 6.28.2: if `f i x < 0`, the indicator
-- subdifferential is `{0}`, and if `f i x = 0`, it is the nonnegative scalar hull of
-- `subdifferentialAt (f i).toWithTopBot x`. Feasibility rules out the empty case `0 < f i x`.
-- Expanding the finite Minkowski sum of those individual hulls yields the union over the
-- canonical nonnegative multiplier owner `Set.Ici (0 : {i // i ∈ s} → ℝ)` cut out by the
-- complementary-slackness equalities at `x`.
/-- Theorem 6.28.5 (2): at a point `x` of the Chapter 21 feasible-set owner
`convexInequalitySolutionSetOn s (fun _ ↦ .le) f 0`, the subdifferential of the constrained
objective is the union of the subdifferential sums obtained from the finite complementary
multiplier families on `s` satisfying `μᵢ * fᵢ(x) = 0`, indexed directly by the canonical
nonnegative owner `Set.Ici (0 : {i // i ∈ s} → ℝ)` cut out by those complementary-slackness
equalities. -/
theorem subdifferentialAt_constrainedObjective_eq_iUnion_multiplier_subdifferentialSums_of_feasible
    {x : E} (hfeasible : x ∈ convexInequalitySolutionSetOn s (fun _ ↦ .le) f 0) :
    subdifferentialAt
        (toWithTopBotOn f₀ (convexInequalitySolutionSetOn s (fun _ ↦ .le) f 0)) x =
      ⋃ μ ∈ Set.Ici (0 : {i // i ∈ s} → ℝ) ∩ { μ | ∀ i, μ i * f i.1 x = 0 },
        (subdifferentialAt f₀.toWithTopBot x +
          s.attach.sum (fun i ↦ μ i • subdifferentialAt (f i.1).toWithTopBot x)) := sorry

end

end Function

/-! ### Corollary_6_28_6 (from Chap06) -/
noncomputable section

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace OrdinaryConvexProgram

open Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.28.6 says that, once an ordinary convex program has at least one
  Kuhn--Tucker multiplier, the Kuhn--Tucker multipliers are exactly the maximizers of the dual
  function
  `g(u) = inf_x L(u, x)`.
- `core/canonical`: the existing Chapter 6 owners are `P.IsKuhnTuckerMultiplier`,
  `P.IsKuhnTuckerVector`, `P.saddleLagrangian`, `Bifunction.perturbationFunction`,
  `multiplierSet`, and `IsMaxOn`.
- `bridge/view`: the source multiplier vector is represented canonically by the split pair
  `u : (Fin r → 𝕜) × (Fin s → 𝕜)` already used throughout the ordinary-convex-program API.
- abstraction normalization: this corollary does not use real-specific structure or the concrete
  codomain `EReal`; it therefore lives at the Chapter 6 canonical layer
  `OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s`.

Domain-style sampling used here:
- `OrdinaryConvexProgram.IsKuhnTuckerMultiplier`, `OrdinaryConvexProgram.IsKuhnTuckerVector`, and
  `OrdinaryConvexProgram.saddleLagrangian` from `Definition_6_28_3`;
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `OrdinaryConvexProgram.multiplierSet` from `Definition_6_28_6`;
- `IsMaxOn` / `isMaxOn_univ_iff` from mathlib's extrema API;
- the Chapter 6 theorem style in `Theorem_31_3`, where dual attainment is expressed canonically
  via `IsMaxOn ... Set.univ`.

Primitive data vs derived API:
- primitive source data: the program `P` and the Lagrangian owner `P.saddleLagrangian`;
- primitive owner reused from upstream: `perturbationFunction P.saddleLagrangian`;
- derived API: the characterization of Kuhn--Tucker multipliers as the maximizers of that dual
  function on the source multiplier set.

Layer target: `source-facing`, stated directly on the existing Kuhn--Tucker and Lagrangian
owners without introducing a parallel ordinary-program alias for the row-infimum owner.
-/

variable {r s : ℕ} (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s)

local notation "dualObjective" => perturbationFunction P.saddleLagrangian

-- Proof sketch: if `u` is Kuhn--Tucker, Theorem 6.28.6 identifies
-- `(perturbationFunction P.saddleLagrangian) u` with the common maximin/minimax value, so `u` is
-- a global maximizer of the dual function. Conversely, choose `u₀` from `hExists`; the same
-- theorem makes `u₀` a maximizer with the common extremal value. Any maximizer `u` therefore has
-- the same row infimum as `u₀`, so the row infimum at `u` is finite and agrees with both global
-- extremal values. Applying Theorem 6.28.6 again yields `P.IsKuhnTuckerMultiplier u`.
/-- Corollary 6.28.6: assuming `P` has at least one Kuhn--Tucker multiplier, a split multiplier
pair `u` representing the source multiplier vector is a Kuhn--Tucker multiplier exactly when
the dual function `g(u) = inf_x L(u, x)`, rendered here by the chapter owner
`perturbationFunction P.saddleLagrangian`, attains its supremum over the canonical multiplier set
`Eᵣ = multiplierSet` at `u`. -/
theorem isKuhnTuckerMultiplier_iff_isMaxOn_dualObjective
    (hExists : ∃ u : (Fin r → 𝕜) × (Fin s → 𝕜), P.IsKuhnTuckerMultiplier u)
    (u : (Fin r → 𝕜) × (Fin s → 𝕜)) :
    P.IsKuhnTuckerMultiplier u ↔
      IsMaxOn dualObjective multiplierSet u := by
  constructor
  · intro hKT
    rcases
      (P.isKuhnTuckerMultiplier_iff_saddleLagrangian_rowInf_finite_eq_maximin_eq_minimax
        u).1 hKT with
      ⟨_, hmaximin, _⟩
    intro v hv
    calc
      dualObjective v = (⨅ x, P.saddleLagrangian v x) := by
        simpa using perturbationFunction_apply P.saddleLagrangian v
      _ ≤ (⨆ w, ⨅ x, P.saddleLagrangian w x) := by
        exact le_iSup (fun w => ⨅ x, P.saddleLagrangian w x) v
      _ = (⨅ x, P.saddleLagrangian u x) := hmaximin
      _ = dualObjective u := by
        simpa using (perturbationFunction_apply P.saddleLagrangian u).symm
  · intro hMax
    rcases hExists with ⟨u0, hKT0⟩
    rcases
      (P.isKuhnTuckerMultiplier_iff_saddleLagrangian_rowInf_finite_eq_maximin_eq_minimax
        u0).1 hKT0 with
      ⟨h0bot, h0maximin, h0minimax⟩
    have hu0_mem : u0 ∈ multiplierSet := by
      simpa using hKT0.nonneg
    have hrow0_le_row :
        (⨅ x, P.saddleLagrangian u0 x) ≤ (⨅ x, P.saddleLagrangian u x) := by
      simpa [perturbationFunction_apply] using hMax hu0_mem
    have hrow_le_maximin :
        (⨅ x, P.saddleLagrangian u x) ≤ (⨆ w, ⨅ x, P.saddleLagrangian w x) := by
      exact le_iSup (fun w => ⨅ x, P.saddleLagrangian w x) u
    have hmaximin_le_row :
        (⨆ w, ⨅ x, P.saddleLagrangian w x) ≤ (⨅ x, P.saddleLagrangian u x) := by
      calc
        (⨆ w, ⨅ x, P.saddleLagrangian w x) = (⨅ x, P.saddleLagrangian u0 x) := h0maximin
        _ ≤ (⨅ x, P.saddleLagrangian u x) := hrow0_le_row
    have hmaximin :
        (⨆ w, ⨅ x, P.saddleLagrangian w x) = (⨅ x, P.saddleLagrangian u x) :=
      le_antisymm hmaximin_le_row hrow_le_maximin
    have hrow_eq :
        (⨅ x, P.saddleLagrangian u0 x) = (⨅ x, P.saddleLagrangian u x) := by
      calc
        (⨅ x, P.saddleLagrangian u0 x) = (⨆ w, ⨅ x, P.saddleLagrangian w x) := h0maximin.symm
        _ = (⨅ x, P.saddleLagrangian u x) := hmaximin
    have hbot :
        ⊥ < (⨅ x, P.saddleLagrangian u x) := by
      simpa [hrow_eq] using h0bot
    have hminimax :
        (⨅ x, ⨆ w, P.saddleLagrangian w x) = (⨅ x, P.saddleLagrangian u x) := by
      calc
        (⨅ x, ⨆ w, P.saddleLagrangian w x) = (⨅ x, P.saddleLagrangian u0 x) := h0minimax
        _ = (⨅ x, P.saddleLagrangian u x) := hrow_eq
    exact
      (P.isKuhnTuckerMultiplier_iff_saddleLagrangian_rowInf_finite_eq_maximin_eq_minimax
        u).2
        ⟨hbot, hmaximin, hminimax⟩

end OrdinaryConvexProgram

end

/-! ### Definition_6_28_6 (from Chap06) -/
universe u w

noncomputable section

namespace OrdinaryConvexProgram
open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.6 introduces the multiplier set `E_r`.
- `core/canonical`: the Lagrangian owner for an ordinary convex program is already
  `OrdinaryConvexProgram.saddleLagrangian` from `Definition_6_28_3`, together with the existing
  weighted-objective owner `weightedObjective`.
- `bridge/view`: the textbook multiplier vector is represented canonically here by a pair of
  coordinate blocks `((ι → β) × τ)`, so that only the first block carries the nonnegativity
  condition defining `E_r`; the second block is unrestricted and specializes to the equality
  multiplier block `(κ → β)` in the program-facing lemmas below. The source piecewise formula is
  then restated by branch lemmas for the existing Lagrangian owner.

Domain-style sampling used here:
- `OrdinaryConvexProgram.saddleLagrangian` from `Chap06.Definition_6_28_3`;
- `OrdinaryConvexProgram.weightedObjective` from `Chap06.Definition_6_28_3`;
- `OrdinaryConvexProgram.weightedObjective_of_mem_constraintSet` from
  `Chap06.Definition_6_28_3`;
- the canonical order interval owner `Set.Ici` on the inequality-multiplier block `ι → β`,
  combined with an unrestricted companion block.

Primitive data vs derived API:
- primitive source-facing data: the multiplier set `multiplierSet`;
- core owner reused from upstream: `P.saddleLagrangian`;
- derived API: coordinatewise membership in the multiplier set and the three pointwise branch
  formulas for `P.saddleLagrangian`.

Layer target: `source-facing` for `multiplierSet`, and `bridge/view` for the branch lemmas that
restate the source formula on the existing Lagrangian owner.
-/

section MultiplierSet

variable {β : Type w} [Zero β] [Preorder β]
variable {ι τ : Type*}

/-- The multiplier set attached to an ordinary convex program: the inequality multipliers are
coordinatewise nonnegative, while the companion multiplier block is unrestricted. -/
def multiplierSet : Set ((ι → β) × τ) :=
  Set.Ici (0 : ι → β) ×ˢ Set.univ

scoped[Rockafellar] notation "Eᵣ" => multiplierSet

-- Proof sketch: unfold `multiplierSet`; membership in the defining set-builder is exactly the
-- coordinatewise nonnegativity condition on the inequality multiplier block.
/-- Coordinatewise characterization of the multiplier set of an ordinary convex program. -/
@[simp] theorem mem_multiplierSet (u : (ι → β) × τ) :
    u ∈ Eᵣ ↔ ∀ i, 0 ≤ u.1 i := by
  simp [multiplierSet]
  rfl

end MultiplierSet

section SaddleLagrangian

variable {𝕜 : Type w} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type*} [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β] [Top β] [Bot β]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

-- Proof sketch: `u ∈ multiplierSet` is exactly the nonnegativity branch used by
-- `P.saddleLagrangian`, so admissible multipliers force the weighted-objective branch globally.
/-- Admissible multipliers give the weighted-objective branch of `P.saddleLagrangian`. -/
theorem saddleLagrangian_apply_of_mem_multiplierSet
    {u : (ι → 𝕜) × (κ → 𝕜)} {x : E}
    (hu : u ∈ Eᵣ) :
    P.saddleLagrangian u x = P.weightedObjective u.1 u.2 x := by
  have hnonneg : ∀ i, 0 ≤ u.1 i := by simpa using hu
  simp [saddleLagrangian, hnonneg]

-- Proof sketch: `u ∉ multiplierSet` means the nonnegativity branch of
-- `P.saddleLagrangian` is unavailable; on `P.constraintSet` the remaining branch is `⊥`.
/-- On the constraint set, inadmissible multipliers make `P.saddleLagrangian` equal to `⊥`. -/
theorem saddleLagrangian_apply_of_mem_constraintSet_of_not_mem_multiplierSet
    {u : (ι → 𝕜) × (κ → 𝕜)} {x : E}
    (hx : x ∈ P.constraintSet) (hu : u ∉ Eᵣ) :
    P.saddleLagrangian u x = ⊥ := by
  have hnonneg : ¬ ∀ i, 0 ≤ u.1 i := by simpa using hu
  simp [saddleLagrangian, hnonneg, hx]

-- Proof sketch: off `P.constraintSet`, the extension branch of `P.saddleLagrangian` is `⊤` when
-- the multipliers are admissible, and the fallback branch is also `⊤` when they are not.
/-- Off the constraint set, `P.saddleLagrangian` is `⊤`. -/
theorem saddleLagrangian_apply_of_not_mem_constraintSet
    {u : (ι → 𝕜) × (κ → 𝕜)} {x : E}
    (hx : x ∉ P.constraintSet) :
    P.saddleLagrangian u x = ⊤ := by
  by_cases hu : u ∈ Eᵣ
  · have hnonneg : ∀ i, 0 ≤ u.1 i := by simpa using hu
    simpa [saddleLagrangian, hnonneg] using
      (P.weightedObjective_of_notMem_constraintSet u.1 u.2 hx)
  · have hnonneg : ¬ ∀ i, 0 ≤ u.1 i := by simpa using hu
    simp [saddleLagrangian, hnonneg, hx]

end SaddleLagrangian

end OrdinaryConvexProgram

/-! ### Theorem_6_28_6 (from Chap06) -/
noncomputable section

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.28.6 identifies Kuhn-Tucker multipliers by the source minimax formula
  for the Lagrangian and records the optimal-value interpretation of the resulting saddle value.
- `core/canonical`: the existing Chapter 6 owners are `P.IsKuhnTuckerMultiplier`,
  `P.IsKuhnTuckerVector`, `P.optimalValue`,
  `P.IsOptimalSolution`, and the Lagrangian `P.saddleLagrangian`.
- `bridge/view`: the already built owners `P.IsOptimalSolution` and `P.saddleLagrangian`,
  matching the bridge used in Theorem 6.28.4, connect the Kuhn-Tucker data to the displayed
  row-infimum / maximin / minimax formulas on the canonical extended-order codomain
  `WithBotTop 𝕜`.

Domain-style sampling used here:
- `OrdinaryConvexProgram.IsKuhnTuckerMultiplier`, `OrdinaryConvexProgram.IsKuhnTuckerVector`,
  `OrdinaryConvexProgram.optimalValue`, and `OrdinaryConvexProgram.saddleLagrangian` from the
  preceding Section 28 items;
- the source bridge owner `OrdinaryConvexProgram.IsOptimalSolution`, sampled from the nearby
  Section 28 development;
- `IsSaddlePointOn` and the row/column extremum API sampled through the Chapter 7 minimax files.
-/

variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

-- Proof sketch: Theorem 6.28.4 turns the Kuhn-Tucker and primal-optimality hypotheses into a
-- saddle-point of `P.saddleLagrangian`. Evaluating that saddle-point at the distinguished pair
-- `(u, x)` identifies the saddle value with the program's optimal value.
/-- The saddle value of the Lagrangian at a Kuhn-Tucker multiplier and an optimal solution equals
the optimal value of the ordinary convex program. -/
theorem saddleLagrangian_value_eq_optimalValue_of_isKuhnTuckerMultiplier_of_isOptimalSolution
    (u : (ι → 𝕜) × (κ → 𝕜)) (x : E)
    (hKT : P.IsKuhnTuckerMultiplier u) (hx : P.IsOptimalSolution x) :
    P.saddleLagrangian u x = P.optimalValue := sorry

-- Proof sketch: combine Theorem 6.28.4 with the preceding saddle-value lemma. The saddle-point
-- inequalities identify the row infimum at `u` with the global maximin value, and the
-- pointwise primal supremum of the Lagrangian gives the minimax value; all three then coincide
-- with `P.optimalValue`.
/-- For a Kuhn-Tucker multiplier, the row infimum at that multiplier pair, the global maximin
value, and the global minimax value of the Lagrangian all coincide with the optimal value of
`P`. -/
theorem saddleLagrangian_rowInf_maximin_minimax_eq_optimalValue_of_isKuhnTuckerMultiplier
    (u : (ι → 𝕜) × (κ → 𝕜)) (hKT : P.IsKuhnTuckerMultiplier u) :
    (⨅ x, P.saddleLagrangian u x) = P.optimalValue ∧
      (⨆ u, ⨅ x, P.saddleLagrangian u x) = P.optimalValue ∧
      (⨅ x, ⨆ u, P.saddleLagrangian u x) = P.optimalValue := sorry

-- Proof sketch: if `u` is Kuhn-Tucker, the previous theorem identifies the row infimum at
-- `u` with the common maximin/minimax value and gives the strict lower bound `⊥ < ...`
-- from the finiteness built into `P.IsKuhnTuckerMultiplier`. Conversely, strict lower boundedness
-- together with equality of both extremal values to that row infimum rules out the inadmissible
-- `⊥` branch of the
-- Lagrangian and recovers the defining Kuhn-Tucker conditions.
/-- Theorem 6.28.6: a multiplier pair `u = (lam, μ)` is a Kuhn-Tucker multiplier for an ordinary
convex program `P` exactly when the row infimum of the Lagrangian at `u` is strictly above
`⊥`, with both global values `sup_u inf_x L(u, x)` and `inf_x sup_u L(u, x)` equal to that row
infimum. -/
theorem isKuhnTuckerMultiplier_iff_saddleLagrangian_rowInf_finite_eq_maximin_eq_minimax
    (u : (ι → 𝕜) × (κ → 𝕜)) :
    P.IsKuhnTuckerMultiplier u ↔
      ⊥ < (⨅ x, P.saddleLagrangian u x) ∧
        (⨆ u, ⨅ x, P.saddleLagrangian u x) =
          (⨅ x, P.saddleLagrangian u x) ∧
        (⨅ x, ⨆ u, P.saddleLagrangian u x) =
          (⨅ x, P.saddleLagrangian u x) := sorry

end OrdinaryConvexProgram

end

/-! ### Corollary_6_28_7 (from Chap06) -/
noncomputable section

universe u
universe v
universe w

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {α : Type w} [AddCommGroup α] [SMul 𝕜 α]
variable [ConditionallyCompleteLattice α] [IsOrderedAddMonoid α]
variable {U : Type u} [AddCommMonoid U] [SMul 𝕜 U]
variable {X : Type*}

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.28.7 uses the dual-objective shape
  `g(u) = inf_x L(u, x)`, which is the Chapter 6 perturbation-function owner of a bifunction.
- `core/canonical`: the canonical row-infimum owner is `Bifunction.perturbationFunction`, and
  the canonical curvature owner is `Function.IsConcave`.
- `bridge/view`: if every slice `u ↦ F u x` is concave, then
  `perturbationFunction F = fun u ↦ inf_x F u x` is concave by `Function.IsConcave.iInf`.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` and `Bifunction.perturbationFunction_apply` from
  `Definition_6_29_1`;
- `Function.IsConcave.iInf` from `Proposition_6_28_4`;
- `Function.IsConcave` from `Definition_6_30_2`.

Primitive data vs derived API:
- primitive source data: a bifunction `F` and slice concavity hypotheses
  `∀ x, (F · x).IsConcave 𝕜`;
- derived API: concavity of the canonical row-infimum owner `perturbationFunction F`.

Layer target: `core/canonical`, so downstream source items can reuse this owner-level bridge
without introducing item-specific wrappers around the same pointwise-infimum argument.
-/

/-- Row-infimum concavity bridge: if every slice `u ↦ F u x` is concave, then the
perturbation function `u ↦ inf_x F u x` is concave. -/
theorem perturbationFunction_isConcave
    (F : U → X → WithBotTop α)
    (hSlice : ∀ x : X, (F · x).IsConcave 𝕜) :
    (perturbationFunction F).IsConcave 𝕜 := by
  have hpert : perturbationFunction F = fun u ↦ ⨅ x, F u x := by
    funext u
    simpa using (perturbationFunction_apply F u)
  have hslices :
      (fun u ↦ ⨅ x, F u x) = (⨅ x : X, fun u ↦ F u x) := by
    funext u
    simp [iInf_apply]
  rw [hpert, hslices]
  exact Function.IsConcave.iInf (fun x ↦ by simpa using hSlice x)

end Bifunction

end

section

variable {𝕜 : Type v} [Ring 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedAddMonoid 𝕜]
variable [DecidableLT 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace OrdinaryConvexProgram

open Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.28.7 states that the dual function attached to the Lagrangian,
  namely `g(u) = inf_x L(u, x)`, is concave.
- `core/canonical`: the Chapter 6 owner for a bifunction row-infimum `u ↦ inf_x F u x` is
  `Bifunction.perturbationFunction`, and the chapter owner for the conclusion is
  `Function.IsConcave`.
- `bridge/view`: specialize the canonical bifunction bridge
  `Bifunction.perturbationFunction_isConcave` to the Lagrangian owner
  `P.saddleLagrangian`.
- abstraction normalization: no step of this bridge needs the concrete codomain `EReal` or the
  concrete scalar `ℝ`; the source-facing corollary is exposed on
  `OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ` with only the primitive slice-concavity
  hypothesis.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` and `Bifunction.perturbationFunction_apply` from
  `Definition_6_29_1`;
- `OrdinaryConvexProgram.saddleLagrangian` from `Definition_6_28_3`;
- `Bifunction.perturbationFunction_isConcave` from this file;
- `Function.IsConcave.iInf` from `Proposition_6_28_4`;
- `Function.IsConcave` from `Definition_6_30_2`.

Primitive data vs derived API:
- primitive source data: the program `P` and its Lagrangian owner `P.saddleLagrangian`;
- primitive curvature hypothesis: `∀ x, (P.saddleLagrangian · x).IsConcave 𝕜`;
- derived API: concavity of the canonical row-infimum owner
  `perturbationFunction P.saddleLagrangian`.

Layer target: `bridge/view`, stated directly on the existing perturbation-function owner instead
of a parallel ordinary-program alias for the same row-infimum construction.
-/

variable {r s : ℕ} {ι : Type} {κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

/-- Corollary 6.28.7: the dual function of an ordinary convex program, defined by
`g(u) = inf_x L(u, x)`, is the perturbation function of the Lagrangian bifunction and is concave
on the multiplier space. The statement is expressed directly on the chapter owner
`(perturbationFunction P.saddleLagrangian).IsConcave`. In owner-normalized bridge form, the
assumption is exactly concavity of each Lagrangian slice in the multiplier variable. -/
theorem lagrangianDualObjective_isConcave
    (hSlice : ∀ x : E, (P.saddleLagrangian · x).IsConcave 𝕜) :
    (perturbationFunction P.saddleLagrangian).IsConcave 𝕜 := by
  simpa using
    (Bifunction.perturbationFunction_isConcave
      (F := P.saddleLagrangian) hSlice)

end OrdinaryConvexProgram

end
