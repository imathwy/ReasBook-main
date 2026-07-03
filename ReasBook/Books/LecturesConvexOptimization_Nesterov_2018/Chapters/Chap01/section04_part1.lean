import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Recall
import Mathlib.Topology.Order.MonotoneConvergence

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_4_1 (from Chap01) -/
/- Definition 1.4.1 is a source-facing recall in the order-theoretic monotonicity domain.

Layer targeted by this refinement:
* source-facing recall of the core/canonical owner predicate `Antitone`

Sampled owner-style declarations:
* `Antitone`, the owner notion of a decreasing sequence on a preorder
* `antitone_nat_of_succ_le`, the canonical `ℕ` constructor from the one-step decrease condition

Primitive data:
* the antitonicity condition `Antitone a`

Derived API:
* the textbook successor-step criterion `∀ k, a (k + 1) ≤ a k`, obtained by evaluating
  `Antitone a` on `Nat.le_succ` and conversely rebuilding `Antitone a` with
  `antitone_nat_of_succ_le`

This file therefore introduces no parallel wrapper API for relaxation sequences.
-/

#check (Antitone : (ℕ → ℝ) → Prop)
#check antitone_nat_of_succ_le

/-- On `ℕ`, the owner predicate `Antitone` is equivalent to the textbook one-step decrease
criterion. -/
theorem antitone_nat_iff_succ_le {α : Type*} [Preorder α] {f : ℕ → α} :
    Antitone f ↔ ∀ n : ℕ, f (n + 1) ≤ f n := by
  exact ⟨fun hf n ↦ hf (Nat.le_succ n), antitone_nat_of_succ_le⟩

/-! ### Definition_1_4_1 (from Items/Chap01) -/
/- Definition 1.4.1 is a source-facing recall in the order-theoretic monotonicity domain.

Layer targeted by this refinement:
* source-facing recall of the Chapter 1 owner theorem for decreasing sequences on `ℕ`

Primary domain:
* monotonicity of sequences on preorders, specialized here to real sequences on `ℕ`

Relevant owner-style declarations sampled before refining:
* `Antitone`, the canonical owner predicate for decreasing maps on a preorder;
* `antitone_nat_of_succ_le`, the canonical `ℕ` constructor from the one-step decrease condition;
* `antitone_nat_iff_succ_le` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_4_1.lean`, the chapter bridge
  theorem already packaging the textbook successor-step criterion;
* `bounded_relaxation_sequence_tendsto_infimum` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Proposition_1_4_2.lean`, the
  direct downstream theorem that consumes the chapter bridge instead of a local item-level copy.

Best owner abstraction:
* source-facing recall: `Antitone` specialized to sequences `ℕ → ℝ`;
* core/canonical owner: `Antitone`;
* bridge/view: `antitone_nat_iff_succ_le`.

Primitive data:
* a sequence `a : ℕ → ℝ`;
* the owner predicate `Antitone a`.

Derived API:
* the textbook one-step decrease criterion `∀ k, a (k + 1) ≤ a k`.

This item therefore reuses the exact Chapter 1 owner/bridge surface directly and introduces no
parallel local copy of the successor-step equivalence. -/

/- Definition 1.4.1: a relaxation sequence is exactly the canonical predicate `Antitone`
specialized to real sequences indexed by `ℕ`. -/
#check (Antitone : (ℕ → ℝ) → Prop)

/- On `ℕ`, the owner predicate `Antitone` is equivalent to the textbook one-step decrease
criterion for real sequences. -/
section

variable {a : ℕ → ℝ}

#check (antitone_nat_iff_succ_le : Antitone a ↔ ∀ n : ℕ, a (n + 1) ≤ a n)

end

/-! ### Proposition_1_4_2 (from Chap01) -/
open Filter

universe u

/- Proposition 1.4.2 lies in the order-theoretic monotone-convergence domain.

Relevant owner declarations sampled before refining:
* `Antitone`, the owner predicate for a decreasing sequence
* `antitone_nat_of_succ_le`, the canonical bridge from the textbook one-step decrease
  condition to the owner predicate on `ℕ`
* `tendsto_atTop_ciInf`, the owner monotone-convergence theorem for antitone nets
* `sInf_range`, the bridge from the indexed infimum `⨅ n, a n` to the textbook
  `sInf (Set.range a)`

Best owner abstraction:
* `tendsto_atTop_ciInf`

Primitive data:
* the source-facing one-step decrease condition `∀ n, a (n + 1) ≤ a n`
* `BddBelow (Set.range a)`

Derived API:
* `Antitone a`, via `antitone_nat_of_succ_le`
* convergence of `a` to `sInf (Set.range a)`

Source/core/bridge triage:
* source-facing: the proposition that a bounded-below relaxation sequence converges to the
  infimum of its range from the textbook one-step decrease hypothesis
* core/canonical: `tendsto_atTop_ciInf`
* bridge/view: `antitone_nat_of_succ_le` and `sInf_range`

This file therefore keeps only the source-facing theorem and targets the canonical proof route via
`antitone_nat_of_succ_le`, `tendsto_atTop_ciInf`, and `sInf_range` without introducing any local
wrapper around monotonicity or infimum convergence.
-/

/-- Proposition 1.4.2: A bounded-below relaxation sequence converges to the infimum of its
range. -/
-- Proof sketch: convert the successor-step decrease hypothesis to `Antitone a` via
-- `antitone_nat_of_succ_le`, then apply `tendsto_atTop_ciInf` and rewrite `⨅ n, a n` as
-- `sInf (Set.range a)` using `sInf_range`.
theorem relaxationSequence_tendsto_inf {α : Type u} [TopologicalSpace α]
    [ConditionallyCompletePartialOrderInf α] [InfConvergenceClass α] {a : ℕ → α}
    (ha : ∀ n : ℕ, a (n + 1) ≤ a n) (hbdd : BddBelow (Set.range a)) :
    Tendsto a atTop (nhds (sInf (Set.range a))) := by
  simpa [sInf_range] using tendsto_atTop_ciInf (antitone_nat_of_succ_le ha) hbdd

/-! ### Proposition_1_4_2 (from Items/Chap01) -/
open Filter

/- Proposition 1.4.2 lies in the order-theoretic monotone-convergence domain.

Relevant owner-style declarations sampled before refining:
* `Antitone`, the canonical owner predicate for decreasing sequences;
* `antitone_nat_iff_succ_le` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_4_1.lean`, the chapter bridge from
  the textbook one-step decrease condition to `Antitone`;
* `tendsto_atTop_ciInf`, the canonical monotone-convergence owner theorem for antitone
  bounded-below sequences;
* `relaxationSequence_tendsto_inf` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Proposition_1_4_2.lean`, the chapter
  source-facing owner already expressing this proposition.

Best owner abstraction:
* source-facing: a real relaxation sequence `a : ℕ → ℝ` with the textbook successor-step decrease
  hypothesis and a lower bound on its range;
* core/canonical: `relaxationSequence_tendsto_inf`, built from `Antitone` and
  `tendsto_atTop_ciInf`;
* bridge/view: `antitone_nat_iff_succ_le`.

Primitive data:
* a real sequence `a : ℕ → ℝ`;
* the one-step decrease hypothesis `∀ n, a (n + 1) ≤ a n`;
* the bounded-below hypothesis `BddBelow (Set.range a)`.

Derived API:
* convergence of `a` to `sInf (Set.range a)`.

This item is recall-first: the chapter file already owns the source-faithful proposition, so the
item file reuses that owner directly instead of keeping parallel local theorem copies specialized
to `ℝ`. -/

/- Proposition 1.4.2: a bounded-below relaxation sequence converges to the infimum of its
range. The textbook real-sequence statement is the specialization `α = ℝ`. -/
recall relaxationSequence_tendsto_inf {α : Type*} [TopologicalSpace α]
    [ConditionallyCompletePartialOrderInf α] [InfConvergenceClass α] {a : ℕ → α}
    (ha : ∀ n : ℕ, a (n + 1) ≤ a n) (hbdd : BddBelow (Set.range a)) :
    Tendsto a atTop (nhds (sInf (Set.range a)))

/-! ### Definition_1_4_3 (from Chap01) -/
namespace SetConstrainedMinimizationProblem

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

open FunctionalConstraintsMinimizationProblem
open GeneralMinimizationProblem

/- Definition 1.4.3 lies in the optimization-regularity domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem`, the owner of the feasible-set and objective data;
* `FunctionalConstraintsMinimizationProblem.IsConstrained` together with
  `FunctionalConstraintsMinimizationProblem.not_isConstrained_iff_feasibleSet_eq_univ` in
  `Definition_1_1_4_1`, the earlier Chapter 1 owner for unconstrainedness;
* `GeneralMinimizationProblem.IsSmooth`, the earlier Chapter 1 owner for smoothness;
* `SetConstrainedMinimizationProblem.toGeneralMinimizationProblem`, the canonical bridge from a
  set-constrained problem to that earlier owner.

Best owner abstraction:
* `problem.toGeneralMinimizationProblem`, together with the owner predicates
  `¬ problem.toGeneralMinimizationProblem.IsConstrained` and
  `problem.toGeneralMinimizationProblem.IsSmooth`.

Primitive data:
* `problem.feasibleSet`
* `problem.objective`

Derived API:
* the canonical owner conjunction
  `¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
    problem.toGeneralMinimizationProblem.IsSmooth`
* the smoothness bridge `isSmooth_iff_differentiable`, which turns owner smoothness into
  ordinary differentiability once the feasible set is known to be all of `ℝⁿ`
* the companion bridge `unconstrainedSmooth_iff`, which recovers the textbook formulation
  `problem.feasibleSet = Set.univ ∧ Differentiable ℝ problem`
* the direct consequences `feasibleSet_eq_univ_of_unconstrainedSmooth` and
  `differentiable_of_unconstrainedSmooth`

Source/core/bridge triage:
* source-facing: the canonical owner conjunction above
* core/canonical: `problem.toGeneralMinimizationProblem` with the owner predicates above
* bridge/view: `unconstrainedSmooth_iff`. -/

variable (problem : SetConstrainedMinimizationProblem E)

/- Definition 1.4.3: an unconstrained smooth minimization problem on `ℝⁿ` is a
set-constrained minimization problem whose canonical earlier Chapter 1 owner is both
unconstrained and smooth. -/
#check (
  ¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
    problem.toGeneralMinimizationProblem.IsSmooth
)

private theorem toGeneralMinimizationProblem_objectiveOnAmbient_eq_objective
    (problem : SetConstrainedMinimizationProblem E)
    (hfeasibleSet : problem.feasibleSet = Set.univ) :
    problem.toGeneralMinimizationProblem.objectiveOnAmbient = problem.objective := by
  ext x
  have hx : x ∈ problem.toGeneralMinimizationProblem.basicFeasibleSet := by
    change x ∈ problem.feasibleSet
    simp [hfeasibleSet]
  simpa [SetConstrainedMinimizationProblem.toGeneralMinimizationProblem,
    SetConstrainedMinimizationProblem.toFunctionalConstraintsMinimizationProblem] using
    FunctionalConstraintsMinimizationProblem.objectiveOnAmbient_apply
      problem.toGeneralMinimizationProblem hx

private theorem toGeneralMinimizationProblem_feasibleSet_eq_feasibleSet
    (problem : SetConstrainedMinimizationProblem E) :
    (problem.toGeneralMinimizationProblem.feasibleSet : Set E) = problem.feasibleSet := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact y.2
  · intro hx
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change problem.toGeneralMinimizationProblem.IsFeasible ⟨x, hx⟩
    intro i
    exact Fin.elim0 i

private theorem feasibleSet_eq_univ_of_toGeneralMinimizationProblem_not_isConstrained
    (problem : SetConstrainedMinimizationProblem E) :
    ¬ problem.toGeneralMinimizationProblem.IsConstrained → problem.feasibleSet = Set.univ := by
  intro hunconstrained
  refine Set.eq_univ_iff_forall.2 ?_
  intro x
  by_contra hx
  apply hunconstrained
  constructor
  · exact Set.subset_univ _
  · intro hsubset
    have hx' : x ∈ (problem.toGeneralMinimizationProblem.feasibleSet : Set E) := hsubset (by
      trivial)
    rw [toGeneralMinimizationProblem_feasibleSet_eq_feasibleSet problem] at hx'
    exact hx hx'

private theorem toGeneralMinimizationProblem_not_isConstrained_of_feasibleSet_eq_univ
    (problem : SetConstrainedMinimizationProblem E)
    (hfeasibleSet : problem.feasibleSet = Set.univ) :
    ¬ problem.toGeneralMinimizationProblem.IsConstrained := by
  intro hconstrained
  apply hconstrained.2
  intro x
  rw [toGeneralMinimizationProblem_feasibleSet_eq_feasibleSet problem, hfeasibleSet]
  intro _
  trivial

private theorem toGeneralMinimizationProblem_constraintVectorOnAmbient_eq_zero
    (problem : SetConstrainedMinimizationProblem E) :
    problem.toGeneralMinimizationProblem.constraintVectorOnAmbient =
      fun _ : E ↦ (0 : EuclideanSpace ℝ (Fin 0)) := by
  ext x i
  exact Fin.elim0 i

/-- If the feasible set is all of `ℝⁿ`, then the owner smoothness predicate is exactly ordinary
differentiability of the objective. -/
theorem isSmooth_iff_differentiable
    (problem : SetConstrainedMinimizationProblem E)
    (hfeasibleSet : problem.feasibleSet = Set.univ) :
    problem.toGeneralMinimizationProblem.IsSmooth ↔ Differentiable ℝ problem.objective := by
  constructor
  · intro hsmooth
    have hobjective :
        DifferentiableOn ℝ problem.toGeneralMinimizationProblem.objectiveOnAmbient
          problem.toGeneralMinimizationProblem.basicFeasibleSet := hsmooth.1
    change DifferentiableOn ℝ problem.toGeneralMinimizationProblem.objectiveOnAmbient
      problem.feasibleSet at hobjective
    rw [hfeasibleSet] at hobjective
    have hdiff : Differentiable ℝ problem.toGeneralMinimizationProblem.objectiveOnAmbient :=
      differentiableOn_univ.mp hobjective
    simpa [toGeneralMinimizationProblem_objectiveOnAmbient_eq_objective problem hfeasibleSet]
      using hdiff
  · intro hdiff
    refine ⟨?_, ?_⟩
    · change DifferentiableOn ℝ problem.toGeneralMinimizationProblem.objectiveOnAmbient
        problem.feasibleSet
      rw [hfeasibleSet]
      have hobjective : DifferentiableOn ℝ problem.objective Set.univ :=
        differentiableOn_univ.mpr hdiff
      have hobjective_eq :=
        toGeneralMinimizationProblem_objectiveOnAmbient_eq_objective problem hfeasibleSet
      rw [← hobjective_eq] at hobjective
      exact hobjective
    · change DifferentiableOn ℝ problem.toGeneralMinimizationProblem.constraintVectorOnAmbient
        problem.feasibleSet
      rw [hfeasibleSet]
      have hzero :
          DifferentiableOn ℝ (fun _ : E ↦ (0 : EuclideanSpace ℝ (Fin 0))) Set.univ := by
        rw [differentiableOn_univ]
        exact differentiable_const (0 : EuclideanSpace ℝ (Fin 0))
      rw [toGeneralMinimizationProblem_constraintVectorOnAmbient_eq_zero problem]
      exact hzero

/-- The canonical owner expression for Definition 1.4.3 is equivalent to the textbook
whole-space differentiability formulation. -/
theorem unconstrainedSmooth_iff
    (problem : SetConstrainedMinimizationProblem E) :
    (¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
      problem.toGeneralMinimizationProblem.IsSmooth) ↔
      problem.feasibleSet = Set.univ ∧ Differentiable ℝ problem.objective := by
  constructor
  · rintro ⟨hunconstrained, hsmooth⟩
    have hfeasibleSet : problem.feasibleSet = Set.univ :=
      feasibleSet_eq_univ_of_toGeneralMinimizationProblem_not_isConstrained problem hunconstrained
    exact ⟨hfeasibleSet, (isSmooth_iff_differentiable problem hfeasibleSet).mp hsmooth⟩
  · rintro ⟨hfeasibleSet, hdiff⟩
    exact
      ⟨toGeneralMinimizationProblem_not_isConstrained_of_feasibleSet_eq_univ problem hfeasibleSet,
        (isSmooth_iff_differentiable problem hfeasibleSet).mpr hdiff⟩

/-- The owner expression of Definition 1.4.3 forces the feasible set to be all of `ℝⁿ`. -/
theorem feasibleSet_eq_univ_of_unconstrainedSmooth
    (problem : SetConstrainedMinimizationProblem E)
    (h : ¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
      problem.toGeneralMinimizationProblem.IsSmooth) :
    problem.feasibleSet = Set.univ :=
  (unconstrainedSmooth_iff problem).mp h |>.1

/-- The owner expression of Definition 1.4.3 gives a differentiable objective on `ℝⁿ`. -/
theorem differentiable_of_unconstrainedSmooth
    (problem : SetConstrainedMinimizationProblem E)
    (h : ¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
      problem.toGeneralMinimizationProblem.IsSmooth) :
    Differentiable ℝ problem.objective :=
  (unconstrainedSmooth_iff problem).mp h |>.2

end SetConstrainedMinimizationProblem

/-! ### Definition_1_4_3 (from Items/Chap01) -/
/- Definition 1.4.3 lies in the unconstrained smooth minimization domain.

Relevant owner-style declarations sampled before refining:
* `SetConstrainedMinimizationProblem` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_3.lean`, the chapter
  owner of a feasible set together with a real-valued objective;
* `GeneralMinimizationProblem.IsConstrained` and
  `GeneralMinimizationProblem.not_isConstrained_iff_feasibleSet_eq_univ` in
  `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_1_4_1.lean`, the earlier owner of unconstrainedness;
* `GeneralMinimizationProblem.IsSmooth` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_1_4_3.lean`, the earlier
  owner of smoothness;
* `SetConstrainedMinimizationProblem.unconstrainedSmooth_iff` in
  `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_4_3.lean`, the chapter bridge back to the textbook whole-space
  differentiability formulation.

Best owner abstraction:
* source-facing: the chapter owner expression
  `¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
    problem.toGeneralMinimizationProblem.IsSmooth`;
* core/canonical: `problem.toGeneralMinimizationProblem`, together with the earlier owner
  predicates `IsConstrained` and `IsSmooth`;
* bridge/view: `SetConstrainedMinimizationProblem.unconstrainedSmooth_iff`.

Primitive data:
* `problem : SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n))`.

Derived API:
* the owner expression above;
* the bridge to `problem.feasibleSet = Set.univ ∧ Differentiable ℝ problem`;
* the consequences `feasibleSet_eq_univ_of_unconstrainedSmooth` and
  `differentiable_of_unconstrainedSmooth`.

The exact source-facing owner and companion bridge API already exist in the chapter file, so this
item is refined to a recall surface instead of keeping the unused parallel structure
`UnconstrainedSmoothMinimizationProblem`. -/

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable (problem : SetConstrainedMinimizationProblem E)

/- Definition 1.4.3: an unconstrained smooth minimization problem on `ℝⁿ` is the chapter owner
expression asserting that the associated general minimization problem is both unconstrained and
smooth. -/
#check (
  ¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
    problem.toGeneralMinimizationProblem.IsSmooth
)

end

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable {problem : SetConstrainedMinimizationProblem E}

/- The chapter owner expression is equivalent to the textbook whole-space differentiability
formulation. -/
recall SetConstrainedMinimizationProblem.unconstrainedSmooth_iff
    {problem : SetConstrainedMinimizationProblem E} :
    (¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
      problem.toGeneralMinimizationProblem.IsSmooth) ↔
      problem.feasibleSet = Set.univ ∧ Differentiable ℝ problem

/- The owner expression forces the feasible set to be all of `ℝⁿ`. -/
recall SetConstrainedMinimizationProblem.feasibleSet_eq_univ_of_unconstrainedSmooth
    {problem : SetConstrainedMinimizationProblem E}
    (h : ¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
      problem.toGeneralMinimizationProblem.IsSmooth) :
    problem.feasibleSet = Set.univ

/- The owner expression yields a differentiable objective on `ℝⁿ`. -/
recall SetConstrainedMinimizationProblem.differentiable_of_unconstrainedSmooth
    {problem : SetConstrainedMinimizationProblem E}
    (h : ¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
      problem.toGeneralMinimizationProblem.IsSmooth) :
    Differentiable ℝ problem

end

/-! ### Definition_1_4_4 (from Chap01) -/
open scoped BigOperators

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Definition 1.4.4 lies in the finite-dimensional Euclidean inner-product-space domain.

Relevant owner-style declarations sampled before refining:
* `inner ℝ`, the canonical inner product on `E`
* `(fun x : E ↦ ‖x‖)`, the inherited norm on `E`
* mathlib `EuclideanSpace.inner_eq_star_dotProduct`, the canonical coordinate bridge for the
  Euclidean inner product
* mathlib `EuclideanSpace.norm_eq`, the canonical sum-of-squares norm formula

Best owner abstraction:
* the canonical `InnerProductSpace` and `Norm` structure on `EuclideanSpace ℝ (Fin n)`

Primitive data:
* vectors `x y : E`

Derived API:
* `EuclideanSpace.inner_eq_star_dotProduct`, the coordinate formula for the Euclidean inner product
* `EuclideanSpace.norm_eq`, the coordinate formula for the Euclidean norm
* the real-specialized textbook rewrites below, where absolute values disappear and the dot
  product may be read in the usual order

Source/core/bridge triage:
* source-facing: the Euclidean inner product and norm on `ℝⁿ`
* core/canonical: `inner ℝ` and `‖·‖` on `EuclideanSpace ℝ (Fin n)`
* bridge/view: `EuclideanSpace.inner_eq_star_dotProduct` and `EuclideanSpace.norm_eq`

The canonical owner operations come from the `InnerProductSpace` and `Norm` structures on `E`,
and the coordinate bridges are the upstream mathlib `EuclideanSpace` theorems. This file
therefore reuses those owners directly instead of keeping parallel local copies.
-/

#check (inner ℝ : E → E → ℝ)
#check (‖·‖ : E → ℝ)

#check
  (EuclideanSpace.inner_eq_star_dotProduct :
    ∀ x y : E, inner ℝ x y = y ⬝ᵥ x)

#check
  (show ∀ x y : E, inner ℝ x y = x ⬝ᵥ y from
    fun x y ↦ by
      simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct x y))

#check
  (EuclideanSpace.norm_eq :
    ∀ x : E, ‖x‖ = Real.sqrt (∑ i, ‖x i‖ ^ 2))

#check
  (show ∀ x : E, ‖x‖ = Real.sqrt (∑ i, (x i) ^ 2) from
    fun x ↦ by
      simpa using (EuclideanSpace.norm_eq x))

/-! ### Definition_1_4_4 (from Items/Chap01) -/
open scoped BigOperators

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 1.4.4 lies in the finite-dimensional Euclidean inner-product-space domain.

Relevant owner-style declarations sampled before refining:
* `inner ℝ`, the canonical inner product on `E`
* `(fun x : E ↦ ‖x‖)`, the inherited norm on `E`
* mathlib `EuclideanSpace.inner_eq_star_dotProduct`, the canonical coordinate bridge for the
  Euclidean inner product
* mathlib `EuclideanSpace.norm_eq`, the canonical sum-of-squares norm formula

Best owner abstraction:
* the canonical `InnerProductSpace` and `Norm` structure on `EuclideanSpace ℝ (Fin n)`

Primitive data:
* vectors `x y : E`

Derived API:
* `EuclideanSpace.inner_eq_star_dotProduct`, the coordinate formula for the Euclidean inner product
* `EuclideanSpace.norm_eq`, the coordinate formula for the Euclidean norm
* the real-specialized textbook rewrites below, where absolute values disappear and the dot
  product may be read in the usual order

Source/core/bridge triage:
* source-facing: the Euclidean inner product and norm on `ℝⁿ`
* core/canonical: `inner ℝ` and `‖·‖` on `EuclideanSpace ℝ (Fin n)`
* bridge/view: `EuclideanSpace.inner_eq_star_dotProduct` and `EuclideanSpace.norm_eq`

The canonical owner operations come from the `InnerProductSpace` and `Norm` structures on `E`,
and the coordinate bridges are the upstream mathlib `EuclideanSpace` theorems already recalled in
the chapter file. This item therefore reuses those owners directly instead of keeping parallel
local copies or the unnecessary `EuclideanSpace.equiv` transport layer. -/

/- Definition 1.4.4: the Euclidean inner product on `ℝⁿ` is the inherited inner product. -/
#check (inner ℝ : E → E → ℝ)

/- The Euclidean norm on `ℝⁿ` is the inherited norm. -/
#check (norm : E → ℝ)

/- In coordinates, the Euclidean inner product is the standard dot product. -/
#check
  (EuclideanSpace.inner_eq_star_dotProduct :
    ∀ x y : E, inner ℝ x y = y ⬝ᵥ x)

/- Over `ℝ`, the coordinate formula can be read in the textbook order `xᵀ y`. -/
#check
  (show ∀ x y : E, inner ℝ x y = x ⬝ᵥ y from
    fun x y ↦ by
      simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct x y))

/- The Euclidean norm is the square root of the sum of the squares of the coordinates. -/
#check
  (EuclideanSpace.norm_eq :
    ∀ x : E, ‖x‖ = Real.sqrt (∑ i, ‖x i‖ ^ 2))

/- Over `ℝ`, the norm formula is the textbook square-root-of-sum-of-squares identity. -/
#check
  (show ∀ x : E, ‖x‖ = Real.sqrt (∑ i, (x i) ^ 2) from
    fun x ↦ by
      simpa using (EuclideanSpace.norm_eq x))

/-! ### Proposition_1_4_5 (from Chap01) -/
open Matrix

/-
Proposition 1.4.5 lies in the finite-dimensional inner-product linear algebra domain.

Relevant owner declarations sampled before refining:
* `LinearMap.adjoint`, the owner adjoint construction for linear maps on Euclidean spaces
* `LinearMap.adjoint_inner_right`, the canonical adjointness identity
* `Matrix.toEuclideanLin`, the owner matrix action on Euclidean space
* `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`, the canonical matrix-to-adjoint bridge

Best owner abstraction:
* `LinearMap.adjoint`

Primitive data:
* a real matrix `A`
* vectors `x` and `y`
* the induced linear map `A.toEuclideanLin`

Derived API:
* the adjointness identity from `A.toEuclideanLin.adjoint_inner_right`
* the matrix bridge `A.toEuclideanLin.adjoint = Aᵀ.toEuclideanLin`

Source/core/bridge triage:
* source-facing: the textbook transpose identity `⟨Ax, y⟩ = ⟨x, Aᵀ y⟩`
* core/canonical: `LinearMap.adjoint`
* bridge/view: `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`

This file therefore keeps only the source-facing theorem and reuses the owner adjoint API
directly, rather than rebuilding a parallel matrix-specific adjoint interface.
-/

variable {m n : ℕ}

-- Proof sketch: rewrite `⟪A x, y⟫` using the owner adjointness identity for `A.toEuclideanLin`,
-- then identify the adjoint with `(Aᵀ).toEuclideanLin`.
/-- Proposition 1.4.5: for a real `m × n` matrix, the standard Euclidean inner products on
`ℝ^n` and `ℝ^m` satisfy the adjointness identity `⟨Ax, y⟩ = ⟨x, Aᵀ y⟩`. -/
theorem matrix_transpose_adjointness
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (A.toEuclideanLin x) y =
      inner ℝ x (Aᵀ.toEuclideanLin y) := by
  rw [← A.toEuclideanLin.adjoint_inner_right]
  exact congrArg
    (fun z : EuclideanSpace ℝ (Fin n) ↦ inner ℝ x z)
    (congrArg
      (fun T : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) ↦ T y)
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm)

/-! ### Proposition_1_4_5 (from Items/Chap01) -/
open Matrix

/- Proposition 1.4.5 lies in the finite-dimensional inner-product linear algebra domain.

Relevant owner-style declarations sampled before refining:
* `LinearMap.adjoint`, the canonical adjoint owner for linear maps on Euclidean spaces
* `LinearMap.adjoint_inner_right`, the owner adjointness identity
* `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`, the canonical matrix-to-adjoint bridge
* `matrix_transpose_adjointness` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Proposition_1_4_5.lean`, the exact
  source-facing chapter theorem already owning this proposition

Best owner abstraction:
* source-facing owner in the project: `matrix_transpose_adjointness`
* core/canonical owner: `LinearMap.adjoint`
* bridge/view: `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`

Primitive data:
* a real matrix `A`
* vectors `x` and `y`

Derived API:
* the source-facing transpose identity `⟨Ax, y⟩ = ⟨x, Aᵀ y⟩`
* its canonical proof route through `LinearMap.adjoint`

Source/core/bridge triage:
* source-facing: the textbook transpose identity `⟨Ax, y⟩ = ⟨x, Aᵀ y⟩`
* core/canonical: `LinearMap.adjoint`
* bridge/view: `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`

The exact source-facing theorem already exists in the chapter file with the right interface, so
this item is recall-only rather than a second theorem body duplicating the same owner surface. -/

/- Proposition 1.4.5: for a real `m × n` matrix, the standard Euclidean inner products on
`ℝ^n` and `ℝ^m` satisfy the adjointness identity `⟨Ax, y⟩ = ⟨x, Aᵀ y⟩`. -/
recall matrix_transpose_adjointness
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (A.toEuclideanLin x) y =
      inner ℝ x (Aᵀ.toEuclideanLin y)

/-! ### Definition_1_4_6 (from Chap01) -/
open scoped Gradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Primary domain: first-order differential calculus on real inner-product spaces, specialized in the
source text to `ℝⁿ`.

Relevant owner-style declarations sampled before refining:
* `HasGradientAt`
* `DifferentiableAt.hasGradientAt`
* `HasGradientAt.differentiableAt`
* `hasGradientAt_iff_isLittleO`

Best owner abstraction:
* the canonical gradient predicate `HasGradientAt f g xBar`

Primitive data:
* the gradient witness `g`
* the owner predicate `HasGradientAt f g xBar`

Derived API:
* `DifferentiableAt ℝ f xBar`
* the little-o reformulation `hasGradientAt_iff_isLittleO`
* the affine-approximation reformulations below

Source/core/bridge triage:
* source-facing: `differentiableAt_iff_exists_sub_affineApproximation_isLittleO`
* core/canonical: `HasGradientAt f g xBar`
* bridge/view: `hasGradientAt_iff_sub_affineApproximation_isLittleO`

The file therefore keeps the textbook affine-approximation statement as a thin bridge over the
owner API, without introducing any parallel wrapper. Since neither the statement nor the proof
uses coordinates, the public bridge is stated at the canonical real Hilbert-space level and
specializes to `ℝⁿ`.
-/

/-- The canonical gradient predicate is equivalent to the textbook affine-approximation remainder
formulation. -/
theorem hasGradientAt_iff_sub_affineApproximation_isLittleO
    {f : E → ℝ} {xBar g : E} :
    HasGradientAt f g xBar ↔
      (fun y ↦ f y - (f xBar + inner ℝ g (y - xBar))) =o[nhds xBar] fun y ↦ ‖y - xBar‖ := by
  simpa [Asymptotics.isLittleO_norm_right, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm] using
    (hasGradientAt_iff_isLittleO : HasGradientAt f g xBar ↔
      (fun y : E ↦ f y - f xBar - inner ℝ g (y - xBar)) =o[nhds xBar] fun y ↦ y - xBar)

/-- Definition 1.4.6: for a scalar-valued function on a real inner-product space, and hence in
particular on `ℝⁿ`, differentiability at `xBar` is equivalent to the existence of a gradient
vector whose affine approximation at `xBar` differs from `f` by a term that is little-o of
`‖y - xBar‖` as `y → xBar`; equivalently, `g` is the vector representing the first-order linear
part of that affine approximation. -/
theorem differentiableAt_iff_exists_sub_affineApproximation_isLittleO
    {f : E → ℝ} {xBar : E} :
    DifferentiableAt ℝ f xBar ↔
      ∃ g : E,
        (fun y ↦ f y - (f xBar + inner ℝ g (y - xBar))) =o[nhds xBar] fun y ↦ ‖y - xBar‖ := by
  constructor
  · intro hf
    exact ⟨∇ f xBar, hasGradientAt_iff_sub_affineApproximation_isLittleO.mp hf.hasGradientAt⟩
  · rintro ⟨g, hg⟩
    exact (hasGradientAt_iff_sub_affineApproximation_isLittleO.mpr hg).differentiableAt

/-! ### Definition_1_4_6 (from Items/Chap01) -/
open scoped Gradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Primary domain: first-order differential calculus on real inner-product spaces, specialized in the
source text to `ℝⁿ`.

Relevant owner-style declarations sampled before refining:
* `HasGradientAt`
* `DifferentiableAt.hasGradientAt`
* `HasGradientAt.differentiableAt`
* `hasGradientAt_iff_isLittleO`

Best owner abstraction:
* the canonical gradient predicate `HasGradientAt f g xBar`

Primitive data:
* the gradient witness `g`
* the owner predicate `HasGradientAt f g xBar`

Derived API:
* `DifferentiableAt ℝ f xBar`
* the little-o reformulation `hasGradientAt_iff_isLittleO`
* the affine-approximation reformulations below

Source/core/bridge triage:
* source-facing: `differentiableAt_iff_exists_sub_affineApproximation_isLittleO`
* core/canonical: `HasGradientAt f g xBar`
* bridge/view: `hasGradientAt_iff_sub_affineApproximation_isLittleO`

The file therefore keeps the textbook affine-approximation statement as a thin bridge over the
owner API, without introducing any parallel wrapper. Since neither the statement nor the proof
uses coordinates, the public bridge is stated at the canonical real Hilbert-space level and
specializes to `ℝⁿ`.
-/

/-- The canonical gradient predicate is equivalent to the textbook affine-approximation remainder
formulation. -/
theorem hasGradientAt_iff_sub_affineApproximation_isLittleO
    {f : E → ℝ} {xBar g : E} :
    HasGradientAt f g xBar ↔
      (fun y ↦ f y - (f xBar + inner ℝ g (y - xBar))) =o[nhds xBar] fun y ↦ ‖y - xBar‖ := by
  simpa [Asymptotics.isLittleO_norm_right, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm] using
    (hasGradientAt_iff_isLittleO : HasGradientAt f g xBar ↔
      (fun y : E ↦ f y - f xBar - inner ℝ g (y - xBar)) =o[nhds xBar] fun y ↦ y - xBar)

/-- Definition 1.4.6: for a scalar-valued function on a real inner-product space, and hence in
particular on `ℝⁿ`, differentiability at `xBar` is equivalent to the existence of a gradient
vector whose affine approximation at `xBar` differs from `f` by a term that is little-o of
`‖y - xBar‖` as `y → xBar`; equivalently, `g` is the vector representing the first-order linear
part of that affine approximation. -/
theorem differentiableAt_iff_exists_sub_affineApproximation_isLittleO
    {f : E → ℝ} {xBar : E} :
    DifferentiableAt ℝ f xBar ↔
      ∃ g : E,
        (fun y ↦ f y - (f xBar + inner ℝ g (y - xBar))) =o[nhds xBar] fun y ↦ ‖y - xBar‖ := by
  constructor
  · intro hf
    exact ⟨∇ f xBar, hasGradientAt_iff_sub_affineApproximation_isLittleO.mp hf.hasGradientAt⟩
  · rintro ⟨g, hg⟩
    exact (hasGradientAt_iff_sub_affineApproximation_isLittleO.mpr hg).differentiableAt

/-! ### Definition_1_4_7 (from Chap01) -/
open scoped Gradient
open EuclideanSpace

noncomputable section

universe u v

/-
Definition 1.4.7 is a source-facing bridge in first-order differential calculus on Euclidean
space.

Source/core/bridge triage:
* source-facing: the coordinate formula for the gradient in the standard Euclidean basis
* core/canonical: mathlib's `gradient`
* bridge/view: identify each coordinate with the Fréchet derivative on the corresponding basis
  vector

Primary domain:
* first-order differential calculus on finite-dimensional Euclidean spaces

Relevant owner-style declarations sampled before refining:
* `gradient` from `Mathlib.Analysis.Calculus.Gradient.Basic`
* `inner_gradient_left`, which identifies `fderiv ℝ f xBar` with pairing against `∇ f xBar`
* `inner_basisFun_real`, which recovers standard coordinates from the Euclidean basis

Owner abstraction:
* the gradient vector `∇ f xBar`

Primitive data:
* a function `f`
* a point `xBar`

Derived API:
* the directional derivative along the `i`th standard basis vector
* the coordinate formula `gradient_eq_pi_fderiv_stdBasis` under differentiability at `xBar`

Accordingly, this file keeps the owner notion `gradient` and exposes only the thin Euclidean
coordinate bridge, rather than introducing any parallel local gradient definition.
-/
recall gradient {𝕜 : Type u} {F : Type v} [RCLike 𝕜] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] (f : F → 𝕜) (x : F) : F

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => basisFun (Fin n) ℝ

/-- At a differentiability point `xBar`, the `i`th coordinate of `∇ f xBar` in the standard
Euclidean basis is the directional derivative of `f` along the `i`th basis vector. -/
-- Proof sketch: rewrite the `i`th coordinate of `∇ f xBar` as the inner product against the
-- `i`th standard basis vector using `inner_basisFun_real`, then apply `inner_gradient_left`.
theorem gradient_eq_pi_fderiv_stdBasis
    (f : E → ℝ) (xBar : E) (hf : DifferentiableAt ℝ f xBar) :
    ∇ f xBar = fun i ↦ fderiv ℝ f xBar (e i) := by
  ext i
  rw [← inner_basisFun_real]
  exact inner_gradient_left hf

/-! ### Definition_1_4_7 (from Items/Chap01) -/
open scoped Gradient

noncomputable section

universe u v

/-
Definition 1.4.7 is a source-facing bridge in first-order differential calculus on Euclidean
space.

Source/core/bridge triage:
* source-facing: the coordinate formula for the gradient in the standard Euclidean basis
* core/canonical: mathlib's `gradient`
* bridge/view: identify each coordinate with the Fréchet derivative on the corresponding basis
  vector

Primary domain:
* first-order differential calculus on finite-dimensional Euclidean spaces

Relevant owner-style declarations sampled before refining:
* `gradient` from `Mathlib.Analysis.Calculus.Gradient.Basic`
* `inner_gradient_left`, which identifies `fderiv ℝ f xBar` with pairing against `∇ f xBar`
* `EuclideanSpace.inner_basisFun_real`, which recovers standard coordinates from the Euclidean
  basis
* `gradient_eq_pi_fderiv_stdBasis` from `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_4_7.lean`, the exact
  chapter-level source-facing bridge for this item

Owner abstraction:
* the gradient vector `∇ f xBar`

Primitive data:
* a function `f`
* a point `xBar`

Derived API:
* the directional derivative along the `i`th standard basis vector
* the coordinate formula `gradient_eq_pi_fderiv_stdBasis` under differentiability at `xBar`

The exact source-facing bridge already exists in the chapter owner file, so this item is refined
to a recall surface instead of reintroducing a parallel local theorem.
-/
recall gradient {𝕜 : Type u} {F : Type v} [RCLike 𝕜] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] (f : F → 𝕜) (x : F) : F

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

/- Definition 1.4.7: at a differentiability point `xBar`, the `i`th coordinate of `∇ f xBar`
in the standard Euclidean basis is the directional derivative of `f` along the `i`th basis
vector. -/
recall gradient_eq_pi_fderiv_stdBasis
    (f : E → ℝ) (xBar : E) (hf : DifferentiableAt ℝ f xBar) :
    ∇ f xBar = fun i ↦ fderiv ℝ f xBar (e i)

/-! ### Definition_1_4_8 (from Chap01) -/
universe u v

/-
Definition 1.4.8 is the source-facing owner file in the order/set-theoretic domain of sublevel
sets.

Relevant owner-style declarations sampled before refinement:
- mathlib `Set.Iic`
- mathlib `Set.preimage`
- mathlib `Set.mem_Iic`
- mathlib `Set.mem_preimage`

Best owner abstraction:
- source-facing: the textbook level-set notation `𝓛[f](a)`
- core/canonical: `(f ⁻¹' Set.Iic a : Set E)`
- bridge/view: the textbook set-builder equality
  `(𝓛[f](a) : Set E) = {x : E | f x ≤ a}`

Primitive data:
- a function `f : E → α`
- a level `a : α`

Derived API:
- pointwise membership via `mem_levelSet_iff`
- the set-builder bridge `levelSet_eq_setOf`

The source notion is exactly the canonical lower-interval preimage `f ⁻¹' Set.Iic a`. This file
therefore places the textbook level-set notation on that owner expression here, together with the
atomic pointwise and set-builder companion lemmas used downstream.
-/

namespace LevelSetNotation

scoped notation:max "𝓛[" f:arg "](" a:arg ")" => f ⁻¹' Set.Iic a

end LevelSetNotation

open scoped LevelSetNotation

section

variable {E : Type u} {α : Type v} [Preorder α]
variable (f : E → α) (a : α)
variable {x : E}

/-
Definition 1.4.8: the level set `𝓛[f](a)` is the canonical lower-interval preimage
`f ⁻¹' Set.Iic a`.
-/
#check (𝓛[f](a) : Set E)

@[simp] theorem mem_levelSet_iff {f : E → α} {a : α} {x : E} :
    x ∈ 𝓛[f](a) ↔ f x ≤ a :=
  Iff.rfl

theorem levelSet_eq_setOf (f : E → α) (a : α) :
    (𝓛[f](a) : Set E) = {x : E | f x ≤ a} :=
  rfl

#check (show x ∈ 𝓛[f](a) ↔ f x ≤ a from mem_levelSet_iff)

#check (show (𝓛[f](a) : Set E) = {x : E | f x ≤ a} from levelSet_eq_setOf f a)

end

/-! ### Definition_1_4_8 (from Items/Chap01) -/
universe u v

/-
Definition 1.4.8 is the source-facing owner file in the order/set-theoretic domain of sublevel
sets.

Relevant owner-style declarations sampled before refinement:
- mathlib `Set.Iic`
- mathlib `Set.preimage`
- mathlib `Set.mem_Iic`
- mathlib `Set.mem_preimage`

Best owner abstraction:
- source-facing: the textbook level-set notation `𝓛[f](a)`
- core/canonical: `(f ⁻¹' Set.Iic a : Set E)`
- bridge/view: the textbook set-builder equality
  `(𝓛[f](a) : Set E) = {x : E | f x ≤ a}`

Primitive data:
- a function `f : E → α`
- a level `a : α`

Derived API:
- pointwise membership via `mem_levelSet_iff`
- the set-builder bridge `levelSet_eq_setOf`

The source notion is exactly the canonical lower-interval preimage `f ⁻¹' Set.Iic a`. This file
therefore places the textbook level-set notation on that owner expression here, together with the
atomic pointwise and set-builder companion lemmas used downstream.
-/

namespace LevelSetNotation

scoped notation:max "𝓛[" f:arg "](" a:arg ")" => f ⁻¹' Set.Iic a

end LevelSetNotation

open scoped LevelSetNotation

section

variable {E : Type u} {α : Type v} [Preorder α]
variable (f : E → α) (a : α)

/-
Definition 1.4.8: the level set `𝓛[f](a)` is the canonical lower-interval preimage
`f ⁻¹' Set.Iic a`.
-/
#check (𝓛[f](a) : Set E)

@[simp] theorem mem_levelSet_iff {f : E → α} {a : α} {x : E} :
    x ∈ 𝓛[f](a) ↔ f x ≤ a :=
  Iff.rfl

theorem levelSet_eq_setOf (f : E → α) (a : α) :
    (𝓛[f](a) : Set E) = {x : E | f x ≤ a} :=
  rfl

#check (f ⁻¹' Set.Iic a : Set E)

#check (show (𝓛[f](a) : Set E) = {x : E | f x ≤ a} from levelSet_eq_setOf f a)

end

/-! ### Definition_1_4_9 (from Chap01) -/
open Filter
open scoped Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- 
Definition 1.4.9 is source-facing: it names the unit tangent directions to a level set.

Primary domain:
- tangent-cone geometry for level sets in real normed spaces.

Relevant owner-style declarations sampled before refinement:
- `posTangentConeAt`
- `mem_tangentConeAt_of_seq`
- `mem_tangentConeAt_iff_exists_seq`
- `mem_sphere_zero_iff_norm`

Owner abstraction:
- `posTangentConeAt`

Primitive data:
- the function `f`
- the base point `xbar`

Derived API:
- the tangent directions as the unit-sphere part of the owner cone to the level set
- the normalized-secant characterization of membership

This file therefore keeps the source-facing name, but expresses it directly through the owner cone
and the canonical unit sphere instead of a bespoke set-builder wrapper.

Source/core/bridge triage:
- source-facing: the unit tangent directions to the level set of `f` through `xbar`
- core/canonical: `posTangentConeAt (f ⁻¹' {f xbar}) xbar`
- bridge/view: the normalized-secant sequence characterization of membership
-/

/-- Definition 1.4.9: the directions tangent to the level set of `f` through `xbar` are the unit
vectors in the positive tangent cone of the level set `f ⁻¹' {f xbar}` at `xbar`. The direct
membership lemma `mem_tangentDirectionsToLevelSet_iff` records this owner-level decomposition, and
the companion theorem `mem_tangentDirectionsToLevelSet_iff_exists_level_set_secant_limit` records
the textbook normalized-secant characterization. -/
def tangentDirectionsToLevelSet (f : E → ℝ) (xbar : E) : Set E :=
  posTangentConeAt (f ⁻¹' {f xbar}) xbar ∩ Metric.sphere (0 : E) 1

/-- Membership in `tangentDirectionsToLevelSet f xbar` means lying in the positive tangent cone to
the level set through `xbar` and having unit norm. -/
@[simp] theorem mem_tangentDirectionsToLevelSet_iff {f : E → ℝ} {xbar s : E} :
    s ∈ tangentDirectionsToLevelSet f xbar ↔
      s ∈ posTangentConeAt (f ⁻¹' {f xbar}) xbar ∧ ‖s‖ = 1 := by
  simp [tangentDirectionsToLevelSet]

/-- Membership in `tangentDirectionsToLevelSet f xbar` is equivalent to admitting a sequence on
the level set through `xbar` whose normalized secants converge to the given direction. -/
-- Proof sketch: a unit vector belongs to the positive tangent cone of the level set iff it is the
-- limit of normalized secants along a sequence in that level set converging to `xbar`.
theorem mem_tangentDirectionsToLevelSet_iff_exists_level_set_secant_limit
    {f : E → ℝ} {xbar s : E} :
    s ∈ tangentDirectionsToLevelSet f xbar ↔
      ∃ y : ℕ → E,
        Tendsto y atTop (𝓝 xbar) ∧
        (∀ k : ℕ, y k ≠ xbar) ∧
        (∀ k : ℕ, y k ∈ f ⁻¹' {f xbar}) ∧
        Tendsto (fun k ↦ ‖y k - xbar‖⁻¹ • (y k - xbar)) atTop (𝓝 s) := by
  rw [mem_tangentDirectionsToLevelSet_iff]
  constructor
  · rintro ⟨hs, hnorm⟩
    have hs_ne : s ≠ 0 := norm_ne_zero_iff.mp (hnorm.symm ▸ one_ne_zero)
    rcases mem_tangentConeAt_iff_exists_seq.mp hs with ⟨c, d, hd₀, hlevel, hcd⟩
    have hcd_ne : ∀ᶠ n in atTop, c n • d n ≠ 0 := hcd.eventually_ne hs_ne
    obtain ⟨N, hN⟩ :
        ∃ N, ∀ n : ℕ,
          xbar + d (n + N) ∈ f ⁻¹' {f xbar} ∧ c (n + N) • d (n + N) ≠ 0 := by
      obtain ⟨N, hN⟩ := (hlevel.and hcd_ne).exists_forall_of_atTop
      exact ⟨N, fun n ↦ hN (n + N) (Nat.le_add_left N n)⟩
    refine ⟨fun n ↦ xbar + d (n + N), ?_, ?_, ?_, ?_⟩
    · have hd₀' : Tendsto (fun n ↦ d (n + N)) atTop (𝓝 (0 : E)) := by
        simpa [Function.comp] using hd₀.comp (tendsto_add_atTop_nat N)
      simpa [Function.comp] using tendsto_const_nhds.add hd₀'
    · intro n hEq
      have hd_ne : d (n + N) ≠ 0 := right_ne_zero_of_smul (hN n).2
      exact hd_ne (by simpa using congrArg (fun z ↦ z - xbar) hEq)
    · intro n
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (hN n).1
    · have hcd' : Tendsto (fun n ↦ c (n + N) • d (n + N)) atTop (𝓝 s) := by
        simpa [Function.comp] using hcd.comp (tendsto_add_atTop_nat N)
      have hnormalize :
          ContinuousAt (fun z : E ↦ ‖z‖⁻¹ • z) s :=
        (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hs_ne)).smul continuousAt_id
      have hnormalized :
          Tendsto (fun n ↦ ‖c (n + N) • d (n + N)‖⁻¹ • (c (n + N) • d (n + N))) atTop (𝓝 s) := by
        simpa [hnorm] using hnormalize.tendsto.comp hcd'
      have hnormalized_eq :
          (fun n ↦ ‖c (n + N) • d (n + N)‖⁻¹ • (c (n + N) • d (n + N))) =ᶠ[atTop]
            fun n ↦ ‖d (n + N)‖⁻¹ • d (n + N) := by
        exact Eventually.of_forall fun n ↦ by
          set cn : NNReal := c (n + N)
          set dn : E := d (n + N)
          have hprod_ne : cn • dn ≠ 0 := by
            simpa [cn, dn] using (hN n).2
          have hc_ne : (cn : ℝ) ≠ 0 := by
            intro hc
            have hc0 : cn = 0 := NNReal.coe_eq_zero.mp hc
            exact hprod_ne (by simp [hc0])
          have hd_ne : dn ≠ 0 := right_ne_zero_of_smul hprod_ne
          have hnorm_d_ne : ‖dn‖ ≠ 0 := norm_ne_zero_iff.mpr hd_ne
          have hnorm_cn : ‖(cn : ℝ)‖ = (cn : ℝ) := by
            rw [Real.norm_eq_abs]
            exact abs_of_nonneg cn.2
          simpa [cn, dn] using
            (show ‖cn • dn‖⁻¹ • (cn • dn) = ‖dn‖⁻¹ • dn from by
              change ‖((cn : ℝ) • dn)‖⁻¹ • (((cn : ℝ) • dn)) = ‖dn‖⁻¹ • dn
              rw [norm_smul, smul_smul, hnorm_cn]
              congr 1
              field_simp [hc_ne, hnorm_d_ne, mul_comm, mul_left_comm, mul_assoc])
      have hsecant :
          Tendsto (fun n ↦ ‖d (n + N)‖⁻¹ • d (n + N)) atTop (𝓝 s) :=
        Tendsto.congr' hnormalized_eq hnormalized
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsecant
  · rintro ⟨y, hy, hy_ne, hy_level, hy_secant⟩
    refine ⟨?_, ?_⟩
    · change s ∈ tangentConeAt NNReal (f ⁻¹' {f xbar}) xbar
      have hy_sub : Tendsto (fun k ↦ y k - xbar) atTop (𝓝 (0 : E)) := by
        have hy_const : Tendsto (fun _ : ℕ ↦ xbar) atTop (𝓝 xbar) := tendsto_const_nhds
        simpa using hy.sub hy_const
      have hy_level' : ∀ᶠ k in atTop, xbar + (y k - xbar) ∈ f ⁻¹' {f xbar} :=
        .of_forall fun k ↦ by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy_level k
      have hy_secant' :
          Tendsto
            (fun k ↦ (Real.toNNReal ‖y k - xbar‖⁻¹ : NNReal) • (y k - xbar))
            atTop (𝓝 s) := by
        refine Tendsto.congr' ?_ hy_secant
        exact .of_forall fun k ↦ by
          change ‖y k - xbar‖⁻¹ • (y k - xbar) =
            ((Real.toNNReal ‖y k - xbar‖⁻¹ : ℝ) • (y k - xbar))
          have hnonneg : 0 ≤ ‖y k - xbar‖⁻¹ := by positivity
          simp [Real.toNNReal_of_nonneg hnonneg]
      exact mem_tangentConeAt_of_seq atTop
        (fun k ↦ (Real.toNNReal ‖y k - xbar‖⁻¹ : NNReal))
        (fun k ↦ y k - xbar) hy_sub hy_level' hy_secant'
    · have hnorm_t :
          Tendsto (fun k ↦ ‖‖y k - xbar‖⁻¹ • (y k - xbar)‖) atTop (𝓝 ‖s‖) :=
        Tendsto.comp continuous_norm.continuousAt hy_secant
      have hnorm_eq :
          (fun k ↦ ‖‖y k - xbar‖⁻¹ • (y k - xbar)‖) =ᶠ[atTop] fun _ : ℕ ↦ (1 : ℝ) :=
        .of_forall fun k ↦ by
          have hnorm_ne : ‖y k - xbar‖ ≠ 0 := by
            exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hy_ne k))
          simp [norm_smul, hnorm_ne]
      exact tendsto_nhds_unique (Tendsto.congr' hnorm_eq hnorm_t) tendsto_const_nhds

/-! ### Definition_1_4_9 (from Items/Chap01) -/
open Filter
open scoped Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- 
Definition 1.4.9 is source-facing: it names the unit tangent directions to a level set.

Primary domain:
- tangent-cone geometry for level sets in real normed spaces.

Relevant owner-style declarations sampled before refinement:
- `posTangentConeAt`
- `mem_tangentConeAt_of_seq`
- `mem_tangentConeAt_iff_exists_seq`
- `mem_sphere_zero_iff_norm`

Owner abstraction:
- `posTangentConeAt`

Primitive data:
- the function `f`
- the base point `xbar`

Derived API:
- the tangent directions as the unit-sphere part of the owner cone to the level set
- the normalized-secant characterization of membership

This file therefore keeps the source-facing name, but expresses it directly through the owner cone
and the canonical unit sphere instead of a bespoke set-builder wrapper.

Source/core/bridge triage:
- source-facing: the unit tangent directions to the level set of `f` through `xbar`
- core/canonical: `posTangentConeAt (f ⁻¹' {f xbar}) xbar`
- bridge/view: the normalized-secant sequence characterization of membership
-/

/-- Definition 1.4.9: the directions tangent to the level set of `f` through `xbar` are the unit
vectors in the positive tangent cone of the level set `f ⁻¹' {f xbar}` at `xbar`. The direct
membership lemma `mem_tangentDirectionsToLevelSet_iff` records this owner-level decomposition, and
the companion theorem `mem_tangentDirectionsToLevelSet_iff_exists_level_set_secant_limit` records
the textbook normalized-secant characterization. -/
def tangentDirectionsToLevelSet (f : E → ℝ) (xbar : E) : Set E :=
  posTangentConeAt (f ⁻¹' {f xbar}) xbar ∩ Metric.sphere (0 : E) 1

/-- Membership in `tangentDirectionsToLevelSet f xbar` means lying in the positive tangent cone to
the level set through `xbar` and having unit norm. -/
theorem mem_tangentDirectionsToLevelSet_iff {f : E → ℝ} {xbar s : E} :
    s ∈ tangentDirectionsToLevelSet f xbar ↔
      s ∈ posTangentConeAt (f ⁻¹' {f xbar}) xbar ∧ ‖s‖ = 1 := by
  simp [tangentDirectionsToLevelSet]

/-- Membership in `tangentDirectionsToLevelSet f xbar` is equivalent to admitting a sequence on
the level set through `xbar` whose normalized secants converge to the given direction. -/
-- Proof sketch: a unit vector belongs to the positive tangent cone of the level set iff it is the
-- limit of normalized secants along a sequence in that level set converging to `xbar`.
theorem mem_tangentDirectionsToLevelSet_iff_exists_level_set_secant_limit
    {f : E → ℝ} {xbar s : E} :
    s ∈ tangentDirectionsToLevelSet f xbar ↔
      ∃ y : ℕ → E,
        Tendsto y atTop (𝓝 xbar) ∧
        (∀ k : ℕ, y k ≠ xbar) ∧
        (∀ k : ℕ, f (y k) = f xbar) ∧
        Tendsto (fun k ↦ ‖y k - xbar‖⁻¹ • (y k - xbar)) atTop (𝓝 s) := by
  rw [mem_tangentDirectionsToLevelSet_iff]
  constructor
  · rintro ⟨hs, hnorm⟩
    have hs_ne : s ≠ 0 := norm_ne_zero_iff.mp (hnorm.symm ▸ one_ne_zero)
    rcases mem_tangentConeAt_iff_exists_seq.mp hs with ⟨c, d, hd₀, hlevel, hcd⟩
    have hcd_ne : ∀ᶠ n in atTop, c n • d n ≠ 0 := hcd.eventually_ne hs_ne
    obtain ⟨N, hN⟩ :
        ∃ N, ∀ n : ℕ,
          xbar + d (n + N) ∈ f ⁻¹' {f xbar} ∧ c (n + N) • d (n + N) ≠ 0 := by
      obtain ⟨N, hN⟩ := (hlevel.and hcd_ne).exists_forall_of_atTop
      exact ⟨N, fun n ↦ hN (n + N) (Nat.le_add_left N n)⟩
    refine ⟨fun n ↦ xbar + d (n + N), ?_, ?_, ?_, ?_⟩
    · have hd₀' : Tendsto (fun n ↦ d (n + N)) atTop (𝓝 (0 : E)) := by
        simpa [Function.comp] using hd₀.comp (tendsto_add_atTop_nat N)
      simpa [Function.comp] using tendsto_const_nhds.add hd₀'
    · intro n hEq
      have hd_ne : d (n + N) ≠ 0 := right_ne_zero_of_smul (hN n).2
      exact hd_ne (by simpa using congrArg (fun z ↦ z - xbar) hEq)
    · intro n
      simpa [Set.mem_preimage, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (hN n).1
    · have hcd' : Tendsto (fun n ↦ c (n + N) • d (n + N)) atTop (𝓝 s) := by
        simpa [Function.comp] using hcd.comp (tendsto_add_atTop_nat N)
      have hnormalize :
          ContinuousAt (fun z : E ↦ NormedSpace.normalize z) s := by
        simpa [NormedSpace.normalize] using
          (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hs_ne)).smul continuousAt_id
      have hnormalized :
          Tendsto (fun n ↦ NormedSpace.normalize (c (n + N) • d (n + N))) atTop (𝓝 s) := by
        simpa [NormedSpace.normalize, hnorm] using hnormalize.tendsto.comp hcd'
      have hnormalized_eq :
          (fun n ↦ NormedSpace.normalize (c (n + N) • d (n + N))) =ᶠ[atTop]
            fun n ↦ ‖d (n + N)‖⁻¹ • d (n + N) := by
        exact Eventually.of_forall fun n ↦ by
          set cn : NNReal := c (n + N)
          set dn : E := d (n + N)
          have hprod_ne : cn • dn ≠ 0 := by
            simpa [cn, dn] using (hN n).2
          have hc_ne : (cn : ℝ) ≠ 0 := by
            exact_mod_cast left_ne_zero_of_smul hprod_ne
          have hc_pos : 0 < (cn : ℝ) := by
            exact lt_of_le_of_ne cn.2 (Ne.symm hc_ne)
          simpa [cn, dn, NormedSpace.normalize, NNReal.smul_def] using
            NormedSpace.normalize_smul_of_pos hc_pos dn
      have hsecant :
          Tendsto (fun n ↦ ‖d (n + N)‖⁻¹ • d (n + N)) atTop (𝓝 s) :=
        Tendsto.congr' hnormalized_eq hnormalized
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsecant
  · rintro ⟨y, hy, hy_ne, hy_level, hy_secant⟩
    refine ⟨?_, ?_⟩
    · change s ∈ tangentConeAt NNReal (f ⁻¹' {f xbar}) xbar
      have hy_sub : Tendsto (fun k ↦ y k - xbar) atTop (𝓝 (0 : E)) := by
        have hy_const : Tendsto (fun _ : ℕ ↦ xbar) atTop (𝓝 xbar) := tendsto_const_nhds
        simpa using hy.sub hy_const
      have hy_level' : ∀ᶠ k in atTop, xbar + (y k - xbar) ∈ f ⁻¹' {f xbar} :=
        .of_forall fun k ↦ by
          simpa [Set.mem_preimage, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            hy_level k
      have hy_secant' :
          Tendsto
            (fun k ↦ (Real.toNNReal ‖y k - xbar‖⁻¹ : NNReal) • (y k - xbar))
            atTop (𝓝 s) := by
        refine Tendsto.congr' ?_ hy_secant
        exact .of_forall fun k ↦ by
          change ‖y k - xbar‖⁻¹ • (y k - xbar) =
            ((Real.toNNReal ‖y k - xbar‖⁻¹ : ℝ) • (y k - xbar))
          have hnonneg : 0 ≤ ‖y k - xbar‖⁻¹ := by positivity
          simp [Real.toNNReal_of_nonneg hnonneg]
      exact mem_tangentConeAt_of_seq atTop
        (fun k ↦ (Real.toNNReal ‖y k - xbar‖⁻¹ : NNReal))
        (fun k ↦ y k - xbar) hy_sub hy_level' hy_secant'
    · have hnorm_t :
          Tendsto (fun k ↦ ‖‖y k - xbar‖⁻¹ • (y k - xbar)‖) atTop (𝓝 ‖s‖) :=
        Tendsto.comp continuous_norm.continuousAt hy_secant
      have hnorm_eq :
          (fun k ↦ ‖‖y k - xbar‖⁻¹ • (y k - xbar)‖) =ᶠ[atTop] fun _ : ℕ ↦ (1 : ℝ) :=
        .of_forall fun k ↦ by
          have hnorm_ne : ‖y k - xbar‖ ≠ 0 := by
            exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hy_ne k))
          simp [norm_smul, hnorm_ne]
      exact tendsto_nhds_unique (Tendsto.congr' hnorm_eq hnorm_t) tendsto_const_nhds

/-! ### Lemma_1_4_10 (from Chap01) -/
noncomputable section

open Filter
open scoped Gradient Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 1.4.10 is refined here by the textbook secant-limit proof.

Source/core/bridge triage:
- source-facing: orthogonality of a tangent direction to the level set of a differentiable function
- core/canonical: the affine-approximation little-o remainder at a differentiability point
- bridge/view: the normalized-secant characterization of `tangentDirectionsToLevelSet`

Primary domain:
- first-order orthogonality of level-set tangent directions in a real inner-product space

Relevant owner-style declarations sampled before refinement:
- `hasGradientAt_iff_isLittleO`
- `mem_tangentDirectionsToLevelSet_iff_exists_level_set_secant_limit`
- `IsLittleO.comp_tendsto`
- `IsLittleO.tendsto_div_nhds_zero`
-/

-- Route correction: follow the textbook affine-expansion proof along a level-set secant sequence,
-- rather than the owner-side local-extremum shortcut through the tangent cone.

/-- Helper for Lemma 1.4.10: the affine-approximation remainder becomes negligible after
normalizing by the secant length along a sequence converging to `xbar`. -/
private lemma affine_remainder_ratio_tendsto_zero_along_level_set_sequence
    {f : E → ℝ} {xbar g : E} {y : ℕ → E}
    (hrem : (fun z ↦ f z - (f xbar + inner ℝ g (z - xbar))) =o[𝓝 xbar] fun z ↦ ‖z - xbar‖)
    (hy : Tendsto y atTop (𝓝 xbar)) :
    Tendsto (fun k ↦ (f (y k) - (f xbar + inner ℝ g (y k - xbar))) / ‖y k - xbar‖)
      atTop (𝓝 0) := by
  -- Pull the little-o remainder along the convergent secant sequence and immediately translate it
  -- into convergence of the normalized scalar remainder.
  simpa [Function.comp] using (hrem.comp_tendsto hy).tendsto_div_nhds_zero

/-- Helper for Lemma 1.4.10: on the level set, dividing the first-order expansion by the secant
length yields the normalized inner-product identity from the textbook proof. -/
private lemma level_set_secant_inner_add_remainder_eq_zero
    {f : E → ℝ} {xbar g : E} {y : ℕ → E}
    (hy_ne : ∀ k, y k ≠ xbar)
    (hy_level : ∀ k, f (y k) = f xbar) :
    ∀ k,
      inner ℝ g (‖y k - xbar‖⁻¹ • (y k - xbar)) +
        (f (y k) - (f xbar + inner ℝ g (y k - xbar))) / ‖y k - xbar‖ = 0 := by
  intro k
  have hnorm_ne : ‖y k - xbar‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hy_ne k))
  -- Rewrite the exact level-set equality as the vanishing of the affine term plus remainder.
  have hsum :
      inner ℝ g (y k - xbar) +
          (f (y k) - (f xbar + inner ℝ g (y k - xbar))) = 0 := by
    linarith [hy_level k]
  -- Rewrite the target as the divided form of `hsum`.
  have htarget :
      inner ℝ g (‖y k - xbar‖⁻¹ • (y k - xbar)) +
        (f (y k) - (f xbar + inner ℝ g (y k - xbar))) / ‖y k - xbar‖ =
      (inner ℝ g (y k - xbar) +
          (f (y k) - (f xbar + inner ℝ g (y k - xbar)))) / ‖y k - xbar‖ := by
    calc
      inner ℝ g (‖y k - xbar‖⁻¹ • (y k - xbar)) +
          (f (y k) - (f xbar + inner ℝ g (y k - xbar))) / ‖y k - xbar‖ =
          ‖y k - xbar‖⁻¹ * inner ℝ g (y k - xbar) +
            (f (y k) - (f xbar + inner ℝ g (y k - xbar))) / ‖y k - xbar‖ := by
        rw [inner_smul_right]
      _ = (inner ℝ g (y k - xbar) +
            (f (y k) - (f xbar + inner ℝ g (y k - xbar)))) / ‖y k - xbar‖ := by
        field_simp [hnorm_ne, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [htarget]
  simp [hsum]

/-- Helper for Lemma 1.4.10: a normalized secant limit along the level set forces orthogonality
with the gradient at the base point. -/
private lemma inner_gradient_eq_zero_of_level_set_secant_limit
    {f : E → ℝ} {xbar s : E} (hf : DifferentiableAt ℝ f xbar)
    {y : ℕ → E} (hy : Tendsto y atTop (𝓝 xbar))
    (hy_ne : ∀ k, y k ≠ xbar) (hy_level : ∀ k, f (y k) = f xbar)
    (hy_secant : Tendsto (fun k ↦ ‖y k - xbar‖⁻¹ • (y k - xbar)) atTop (𝓝 s)) :
    inner ℝ (∇ f xbar) s = 0 := by
  -- Translate differentiability into the textbook affine expansion with little-o remainder.
  have hrem :
      (fun z ↦ f z - (f xbar + inner ℝ (∇ f xbar) (z - xbar))) =o[𝓝 xbar]
        fun z ↦ ‖z - xbar‖ := by
    simpa [Asymptotics.isLittleO_norm_right, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using
        (hasGradientAt_iff_isLittleO :
          HasGradientAt f (∇ f xbar) xbar ↔
            (fun z : E ↦ f z - f xbar - inner ℝ (∇ f xbar) (z - xbar)) =o[𝓝 xbar]
              fun z ↦ z - xbar).mp hf.hasGradientAt
  -- The remainder term disappears after normalization along the chosen sequence.
  have hratio :=
    affine_remainder_ratio_tendsto_zero_along_level_set_sequence hrem hy
  -- The normalized inner-product term converges by continuity of the inner product.
  have hinner :
      Tendsto (fun k ↦ inner ℝ (∇ f xbar) (‖y k - xbar‖⁻¹ • (y k - xbar)))
        atTop (𝓝 (inner ℝ (∇ f xbar) s)) := by
    exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp hy_secant
  have hsum :
      Tendsto
        (fun k ↦
          inner ℝ (∇ f xbar) (‖y k - xbar‖⁻¹ • (y k - xbar)) +
            (f (y k) - (f xbar + inner ℝ (∇ f xbar) (y k - xbar))) / ‖y k - xbar‖)
        atTop (𝓝 (inner ℝ (∇ f xbar) s + 0)) :=
    hinner.add hratio
  -- The divided identity holds at every index, so the same sequence also converges to `0`.
  have hsum_zero :
      Tendsto
        (fun k ↦
          inner ℝ (∇ f xbar) (‖y k - xbar‖⁻¹ • (y k - xbar)) +
            (f (y k) - (f xbar + inner ℝ (∇ f xbar) (y k - xbar))) / ‖y k - xbar‖)
        atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    exact Eventually.of_forall fun k ↦
      (level_set_secant_inner_add_remainder_eq_zero hy_ne hy_level k).symm
  have hlimit : inner ℝ (∇ f xbar) s + 0 = 0 :=
    tendsto_nhds_unique hsum hsum_zero
  simpa using hlimit

/-- Lemma 1.4.10: if `f` is differentiable at `xbar`, then every tangent direction to the level
set of `f` at `xbar` is orthogonal to the gradient at `xbar`. -/
theorem inner_gradient_eq_zero_of_mem_tangentDirectionsToLevelSet
    {f : E → ℝ} {xbar s : E} (hf : DifferentiableAt ℝ f xbar)
    (hs : s ∈ tangentDirectionsToLevelSet f xbar) :
    inner ℝ (∇ f xbar) s = 0 := by
  -- Unpack the tangent-direction hypothesis into the normalized-secant sequence from
  -- Definition 1.4.9.
  rcases mem_tangentDirectionsToLevelSet_iff_exists_level_set_secant_limit.mp hs with
    ⟨y, hy, hy_ne, hy_level, hy_secant⟩
  -- The sequence-form source proof is now exactly the structural helper above.
  apply inner_gradient_eq_zero_of_level_set_secant_limit hf hy hy_ne
  · intro k
    simpa using hy_level k
  · exact hy_secant
