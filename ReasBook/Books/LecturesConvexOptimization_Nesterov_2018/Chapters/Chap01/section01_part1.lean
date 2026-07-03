import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_1_1 (from Chap01) -/
universe u

/- The primary domain here is constrained optimization with finitely many scalar constraint
functions on a basic feasible set.

Sampled owner-style declarations in this domain:
* `FunctionalConstraintsMinimizationProblem` and `GeneralMinimizationProblem` in
  `Chap01/Definition_1_1_3`, the project owner and its textbook Euclidean specialization;
* `LagrangianProblem.constraintVector` and `LagrangianProblem.mem_feasibleSet_iff` in
  `Chap01/Definition_1_10_2`, which reuse the same owner-level constraint packaging;
* `PrimalEqualityConstrainedProblem.mem_feasibleSet_iff` in `Chap02/Definition_2_30`, which
  specializes the same feasible-set interface to equality constraints.

Best owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m`

Primitive data:
* `basicFeasibleSet`
* `objective`
* `constraints`
* `senses`

Derived API:
* the objective coercion
* the packaged constraint map `constraintVector`
* the inequality-only predicate `HasLeConstraints`
* the feasible-set rewrite `mem_feasibleSet_iff`

Source/core/bridge triage:
* source-facing: the textbook `GeneralMinimizationProblem n m` specialization
* core/canonical: `FunctionalConstraintsMinimizationProblem X m`
* bridge/view: `GeneralMinimizationProblem n m` as the Euclidean specialization

This file therefore keeps the main labeled entry as a direct recall of the existing textbook
specialization and puts the reusable companion API on the ambient owner. -/

section

variable {n m : ℕ}

/- Definition 1.1.1: the textbook general minimization problem on `ℝⁿ` is represented by
`GeneralMinimizationProblem n m`, the Euclidean specialization of the ambient owner
`FunctionalConstraintsMinimizationProblem`. The companion owner-level declarations below record
the objective-function coercion, the packaged constraint vector, and the inequality-only feasible
set from the textbook terminology. -/
#check (GeneralMinimizationProblem n m)

end

/-- A functional-constraint minimization problem coerces to its objective function on the basic
feasible set. -/
instance {X : Type u} {m : ℕ} :
    CoeFun (FunctionalConstraintsMinimizationProblem X m)
      (fun problem ↦ problem.basicFeasibleSet → ℝ) where
  coe problem := problem.objective

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type u} {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

-- Proof sketch: unfold the `CoeFun` instance for
-- `FunctionalConstraintsMinimizationProblem` and evaluate it at `x`.
/-- Evaluating a functional-constraint minimization problem at a feasible point returns its
objective value. -/
@[simp] theorem coe_apply (problem : FunctionalConstraintsMinimizationProblem X m)
    (x : problem.basicFeasibleSet) : problem x = problem.objective x :=
  rfl

/-- The vector of functional constraints associated to a minimization problem. -/
def constraintVector (problem : FunctionalConstraintsMinimizationProblem X m) :
    problem.basicFeasibleSet → Λ :=
  fun x ↦ WithLp.toLp 2 fun i ↦ problem.constraints i x

-- Proof sketch: unfold `constraintVector` and evaluate the corresponding coordinate.
/-- The coordinates of the functional-constraint vector are the scalar constraint values. -/
@[simp] theorem constraintVector_apply (problem : FunctionalConstraintsMinimizationProblem X m)
    (x : problem.basicFeasibleSet) (i : Fin m) :
    problem.constraintVector x i = problem.constraints i x :=
  rfl

/-- A minimization problem has only inequality constraints when every comparison sign is `≤`. -/
def HasLeConstraints (problem : FunctionalConstraintsMinimizationProblem X m) : Prop :=
  ∀ i, problem.senses i = .le

-- Proof sketch: unfold `feasibleSet` and `IsFeasible`, then rewrite each constraint sense using
-- the hypothesis that every comparison sign is `ConstraintSense.le`.
/-- Under inequality-only constraints, feasibility is equivalent to satisfying `fⱼ(x) ≤ 0` for
each scalar constraint. -/
@[simp] theorem mem_feasibleSet_iff (problem : FunctionalConstraintsMinimizationProblem X m)
    (h : problem.HasLeConstraints) {x : problem.basicFeasibleSet} :
    x ∈ problem.feasibleSet ↔ ∀ i : Fin m, problem.constraints i x ≤ 0 := by
  constructor
  · intro hx i
    simpa [FunctionalConstraintsMinimizationProblem.feasibleSet,
      FunctionalConstraintsMinimizationProblem.IsFeasible, ConstraintSense.Holds, h i] using hx i
  · intro hx i
    simpa [FunctionalConstraintsMinimizationProblem.feasibleSet,
      FunctionalConstraintsMinimizationProblem.IsFeasible, ConstraintSense.Holds, h i] using hx i

end FunctionalConstraintsMinimizationProblem

/-! ### Definition_1_1_1 (from Items/Chap01) -/
universe u

/- Definition 1.1.1 lies in the finite-dimensional constrained-optimization domain.

Relevant owner-style declarations sampled before refining:
* `FunctionalConstraintsMinimizationProblem` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_1_3.lean`, the
  ambient project owner for a basic feasible set, an objective, and finitely many scalar
  constraints with comparison senses;
* `GeneralMinimizationProblem` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_1_3.lean`, the textbook
  `ℝⁿ` specialization of that ambient owner;
* `FunctionalConstraintsMinimizationProblem.constraintVector` in
  `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_1_1.lean`, the canonical packaging of the scalar constraint family
  into a vector-valued map;
* `FunctionalConstraintsMinimizationProblem.mem_feasibleSet_iff` in
  `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_1_1.lean`, the owner-level feasible-set rewrite under
  inequality-only constraints.

Best owner abstraction:
* source-facing: `GeneralMinimizationProblem n m`
* core/canonical: `FunctionalConstraintsMinimizationProblem X m`
* bridge/view: `GeneralMinimizationProblem n m` as the Euclidean specialization of the ambient
  owner

Primitive data:
* `basicFeasibleSet`
* `objective`
* `constraints`
* `senses`

Derived API:
* the objective coercion
* the packaged constraint map `constraintVector`
* the inequality-only predicate `HasLeConstraints`
* the feasible-set rewrite `mem_feasibleSet_iff`

The exact source-facing owner and its supporting ambient-owner API already live in the chapter
file, so this item is refined to direct recall/use instead of introducing any parallel local
definition. -/

section

variable {n m : ℕ}

/- Definition 1.1.1: the textbook general minimization problem on `ℝⁿ` with `m` scalar
constraints is the Chapter 1 owner `GeneralMinimizationProblem n m`. -/
#check (GeneralMinimizationProblem n m)

end

section

variable {X : Type u} {m : ℕ}
variable (problem : FunctionalConstraintsMinimizationProblem X m)

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/- The ambient owner underlying `GeneralMinimizationProblem n m` is
`FunctionalConstraintsMinimizationProblem X m`. -/
#check (FunctionalConstraintsMinimizationProblem X m)

/- The objective is used through the canonical coercion to a function on the basic feasible
set. -/
recall FunctionalConstraintsMinimizationProblem.coe_apply
    (problem : FunctionalConstraintsMinimizationProblem X m)
    (x : problem.basicFeasibleSet) :
    problem x = problem.objective x

/- The scalar constraints package canonically into the vector-valued map
`problem.constraintVector`. -/
recall FunctionalConstraintsMinimizationProblem.constraintVector
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    problem.basicFeasibleSet → Λ

/- The coordinates of the packaged constraint map recover the original scalar constraint
functions. -/
recall FunctionalConstraintsMinimizationProblem.constraintVector_apply
    (problem : FunctionalConstraintsMinimizationProblem X m)
    (x : problem.basicFeasibleSet) (i : Fin m) :
    problem.constraintVector x i = problem.constraints i x

/- The inequality-only textbook case is the owner predicate `problem.HasLeConstraints`. -/
recall FunctionalConstraintsMinimizationProblem.HasLeConstraints
    (problem : FunctionalConstraintsMinimizationProblem X m) : Prop

/- Under inequality-only constraints, membership in the feasible set is exactly the coordinatewise
system `fᵢ(x) ≤ 0`. -/
recall FunctionalConstraintsMinimizationProblem.mem_feasibleSet_iff
    (problem : FunctionalConstraintsMinimizationProblem X m)
    (h : problem.HasLeConstraints) {x : problem.basicFeasibleSet} :
    x ∈ problem.feasibleSet ↔ ∀ i : Fin m, problem.constraints i x ≤ 0

end

/-! ### Definition_1_1_2 (from Chap01) -/
namespace FunctionalConstraintsMinimizationProblem

variable {X : Type*} {m : ℕ} (problem : FunctionalConstraintsMinimizationProblem X m)

/-
Definition 1.1.2 lies in the constrained-optimization feasibility domain.

Sampled owner-style declarations:
* `ConstraintSense.Holds`, `ConstraintSense.StrictHolds`, and the owner feasible predicate
  `problem.IsFeasible` in
  `Chap01/Definition_1_1_3`
* the owner feasible set `problem.feasibleSet` in `Chap01/Definition_1_1_3`
* `LagrangianProblem.SlaterCondition` in `Chap01/Definition_1_10_9`

Best owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m`

Primitive data:
* `basicFeasibleSet`
* `constraints`
* `senses`

Derived API:
* the owner recall `problem.feasibleSet.Nonempty`
* the source-facing point predicate `problem.IsStrictlyFeasible`
* the owner strict feasible set `problem.strictFeasibleSet`
* the problem-level predicate `problem.StrictlyFeasible`
* the implication to ordinary feasibility and the resulting feasible-set nonemptiness theorem

Source/core/bridge triage:
* source-facing: `problem.IsStrictlyFeasible`, `problem.StrictlyFeasible`
* core/canonical: `ConstraintSense.StrictHolds`, `FunctionalConstraintsMinimizationProblem X m`
* bridge/view: `problem.strictFeasibleSet`, the implication from strict feasibility to ordinary
  feasibility, and the Euclidean specialization `GeneralMinimizationProblem n m`

The later `LagrangianProblem.SlaterCondition` should therefore reuse this owner through its
canonical bridge to `FunctionalConstraintsMinimizationProblem`, rather than restating the same
strict-feasibility data.
-/

#check problem.feasibleSet.Nonempty

end FunctionalConstraintsMinimizationProblem

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type*} {m : ℕ} (problem : FunctionalConstraintsMinimizationProblem X m)

/-- A point of the basic feasible set is strictly feasible if every inequality constraint is
satisfied strictly and every equality constraint exactly. -/
def IsStrictlyFeasible (x : problem.basicFeasibleSet) : Prop :=
  ∀ i, (problem.senses i).StrictHolds (problem.constraints i x)

/-- The strict feasible set, viewed inside the basic feasible set. -/
def strictFeasibleSet : Set problem.basicFeasibleSet :=
  {x | problem.IsStrictlyFeasible x}

/-- Membership in `problem.strictFeasibleSet` is exactly strict feasibility of the point. -/
@[simp] theorem mem_strictFeasibleSet {x : problem.basicFeasibleSet} :
    x ∈ problem.strictFeasibleSet ↔ problem.IsStrictlyFeasible x :=
  Iff.rfl

/-- Definition 1.1.2: A minimization problem is strictly feasible when it has a strictly
feasible point. -/
def StrictlyFeasible : Prop :=
  problem.strictFeasibleSet.Nonempty

/-- Every strictly feasible point is feasible, so the strict feasible set lies in the feasible
set. -/
theorem strictFeasibleSet_subset_feasibleSet :
    problem.strictFeasibleSet ⊆ problem.feasibleSet := by
  intro x hx
  exact fun i ↦ (problem.mem_strictFeasibleSet.mp hx i).holds

/-- A strictly feasible point is feasible. -/
theorem IsStrictlyFeasible.isFeasible {x : problem.basicFeasibleSet}
    (hx : problem.IsStrictlyFeasible x) :
    problem.IsFeasible x := by
  exact problem.strictFeasibleSet_subset_feasibleSet hx

namespace StrictlyFeasible

/-- Strict feasibility provides a feasible point. -/
theorem feasibleSet_nonempty (h : problem.StrictlyFeasible) :
    problem.feasibleSet.Nonempty := by
  rcases h with ⟨x, hx⟩
  exact ⟨x, problem.strictFeasibleSet_subset_feasibleSet hx⟩

end StrictlyFeasible

end FunctionalConstraintsMinimizationProblem

/-! ### Definition_1_1_3 (from Chap01) -/
universe u

/-- A comparison sign used in a scalar constraint against `0`. -/
inductive ConstraintSense where
  | le
  | ge
  | eq

/-- Interprets a constraint sign as the corresponding relation with `0`. -/
def ConstraintSense.Holds (sense : ConstraintSense) (value : ℝ) : Prop :=
  match sense with
  | .le => value ≤ 0
  | .ge => value ≥ 0
  | .eq => value = 0

namespace ConstraintSense

/-- Strict satisfaction of a scalar constraint against `0`. -/
def StrictHolds (sense : ConstraintSense) (value : ℝ) : Prop :=
  match sense with
  | .le => value < 0
  | .ge => value > 0
  | .eq => value = 0

/-- Strict satisfaction of a constraint implies ordinary satisfaction. -/
theorem StrictHolds.holds {sense : ConstraintSense} {value : ℝ}
    (h : sense.StrictHolds value) : sense.Holds value := by
  cases sense with
  | le =>
      exact le_of_lt h
  | ge =>
      exact le_of_lt h
  | eq =>
      exact h

end ConstraintSense

/-- A minimization problem on an ambient type `X` with a basic feasible set, a real-valued
objective on that set, and finitely many scalar constraints with comparison senses. -/
structure FunctionalConstraintsMinimizationProblem (X : Type u) (m : ℕ) where
  basicFeasibleSet : Set X
  objective : basicFeasibleSet → ℝ
  constraints : Fin m → basicFeasibleSet → ℝ
  senses : Fin m → ConstraintSense

/-- The textbook `ℝⁿ` specialization of the ambient functional-constraint owner. -/
abbrev GeneralMinimizationProblem (n m : ℕ) :=
  FunctionalConstraintsMinimizationProblem (EuclideanSpace ℝ (Fin n)) m

/-- A point of the basic feasible set is feasible if it satisfies every scalar constraint. -/
def FunctionalConstraintsMinimizationProblem.IsFeasible {X : Type u} {m : ℕ}
    (problem : FunctionalConstraintsMinimizationProblem X m)
    (x : problem.basicFeasibleSet) : Prop :=
  ∀ i, (problem.senses i).Holds (problem.constraints i x)

/-- The feasible set of a minimization problem, viewed as a subset of the basic feasible set. -/
def FunctionalConstraintsMinimizationProblem.feasibleSet {X : Type u} {m : ℕ}
    (problem : FunctionalConstraintsMinimizationProblem X m) : Set problem.basicFeasibleSet :=
  {x | problem.IsFeasible x}

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type u} {m : ℕ} {problem : FunctionalConstraintsMinimizationProblem X m}

/-- Membership in the owner feasible set is exactly the owner feasibility predicate. -/
@[simp] theorem mem_feasibleSet (problem : FunctionalConstraintsMinimizationProblem X m)
    {x : problem.basicFeasibleSet} :
    x ∈ problem.feasibleSet ↔ problem.IsFeasible x :=
  Iff.rfl

section Optimality

variable [TopologicalSpace X]

/-- A local solution is equivalently described by a neighborhood within the feasible set on which
the objective is minimal. -/
theorem isLocalMinOn_iff_exists_set (problem : FunctionalConstraintsMinimizationProblem X m)
    {xStar : problem.feasibleSet} :
    IsLocalMinOn problem.objective problem.feasibleSet xStar ↔
      ∃ N : Set problem.basicFeasibleSet,
        N ∈ nhdsWithin (xStar : problem.basicFeasibleSet) problem.feasibleSet ∧
          IsMinOn problem.objective N xStar := by
  constructor
  · intro hx
    refine ⟨{x | problem.objective xStar ≤ problem.objective x}, ?_, ?_⟩
    · simpa [IsLocalMinOn, IsMinFilter] using hx
    · exact (isMinOn_iff).2 fun _ hx ↦ hx
  · rintro ⟨N, hN, hmin⟩
    rw [IsLocalMinOn, IsMinFilter]
    exact Filter.mem_of_superset hN <| by
      intro x hx
      exact (isMinOn_iff.mp hmin) x hx

/-- Definition 1.1.3: A feasible point is a strict local minimum when it is strictly better
than every distinct feasible point in some neighborhood inside the feasible set. -/
def IsStrictLocalMinimum (problem : FunctionalConstraintsMinimizationProblem X m)
    (xStar : problem.feasibleSet) : Prop :=
  ∃ N : Set problem.basicFeasibleSet,
    N ∈ nhdsWithin (xStar : problem.basicFeasibleSet) problem.feasibleSet ∧
      ∀ x : problem.basicFeasibleSet,
        x ∈ N → x ≠ xStar → problem.objective xStar < problem.objective x

/-- A strict local minimum is, in particular, a local minimum on the feasible set. -/
theorem IsStrictLocalMinimum.isLocalMinOn
    {xStar : problem.feasibleSet} (hx : problem.IsStrictLocalMinimum xStar) :
    IsLocalMinOn problem.objective problem.feasibleSet xStar := by
  rcases hx with ⟨N, hN, hstrict⟩
  rw [IsLocalMinOn, IsMinFilter]
  refine Filter.mem_of_superset hN ?_
  intro x hxN
  by_cases hx : x = xStar
  · simp [hx]
  · exact le_of_lt (hstrict x hxN hx)

end Optimality

end FunctionalConstraintsMinimizationProblem

/- Definition 1.1.3 lies in the order/topology domain of constrained optimization on a feasible
subtype.

Sampled owner-style declarations:
* `IsMinOn`
* `isMinOn_iff`
* `IsLocalMinOn`
* `GeneralMinimizationProblem` in this chapter

Owner abstraction:
* source-facing owner: `GeneralMinimizationProblem n m`
* bridge/generalization: `FunctionalConstraintsMinimizationProblem X m`

Primitive data:
* `basicFeasibleSet`
* `objective`
* `constraints`
* `senses`

Derived API:
* the shared feasibility predicate `problem.IsFeasible`
* the shared feasible set `problem.feasibleSet`
* the owner feasible-set rewrite `problem.mem_feasibleSet`
* global and local optimality as `IsMinOn` and `IsLocalMinOn` on `problem.feasibleSet`
* the local-set reformulation `problem.isLocalMinOn_iff_exists_set`
* the owner strict-local predicate `problem.IsStrictLocalMinimum`

Source/core/bridge triage:
* source-facing: the feasible-point optimality notions on `GeneralMinimizationProblem n m`
* core/canonical: `FunctionalConstraintsMinimizationProblem X m` together with its feasible-set
  and strict-local-minimum API
* bridge/view: `GeneralMinimizationProblem n m` as the textbook `ℝⁿ` specialization
-/

namespace GeneralMinimizationProblem

section Optimality

variable {n m : ℕ} {problem : GeneralMinimizationProblem n m} {xStar : problem.feasibleSet}

/- Definition 1.1.3 (1): a feasible point `xStar` is an optimal global solution exactly when
`IsMinOn problem.objective problem.feasibleSet xStar`. -/
#check IsMinOn problem.objective problem.feasibleSet xStar

/- Definition 1.1.3 (2): a feasible point `xStar` is a local solution exactly when
`IsLocalMinOn problem.objective problem.feasibleSet xStar`. -/
#check IsLocalMinOn problem.objective problem.feasibleSet xStar

/- Definition 1.1.3 (3): the strict local minimum notion is the owner-level predicate
`problem.IsStrictLocalMinimum xStar`. -/
#check problem.IsStrictLocalMinimum xStar

end Optimality

end GeneralMinimizationProblem

/-! ### Definition_1_1_4_1 (from Chap01) -/
namespace FunctionalConstraintsMinimizationProblem

variable {X : Type*} {m : ℕ}

/- Definition 1.1.4.1 lies in the feasible-set domain of constrained optimization.

Sampled owner-style declarations:
* `FunctionalConstraintsMinimizationProblem X m` and `problem.feasibleSet` in
  `Chap01/Definition_1_1_3`
* `FunctionalConstraintsMinimizationProblem.StrictlyFeasible` in `Chap01/Definition_1_1_2`
* `FunctionalConstraintsMinimizationProblem.IsLinearlyConstrained` in
  `Chap01/Definition_1_1_4_5`
* `Set.ssubset_univ_iff` and `Set.ne_univ_iff_exists_notMem`

Best owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m`

Primitive data:
* `problem.basicFeasibleSet`
* `problem.constraints`
* `problem.senses`

Derived API:
* `problem.feasibleSet`
* `problem.IsConstrained`
* the whole-space and nonmembership reformulations below

Source/core/bridge triage:
* source-facing: `problem.IsConstrained`
* core/canonical: `FunctionalConstraintsMinimizationProblem X m`
* bridge/view: `GeneralMinimizationProblem n m` as the textbook Euclidean specialization

Constrainedness depends only on whether the feasible set fills the ambient type, so the owner lives
on `FunctionalConstraintsMinimizationProblem X m`; the `ℝⁿ` formulation is only its specialization.
-/

/-- Definition 1.1.4.1: a minimization problem is constrained when its feasible set is a proper
subset of the ambient space. -/
def IsConstrained (problem : FunctionalConstraintsMinimizationProblem X m) : Prop :=
  (problem.feasibleSet : Set X) ⊂ Set.univ

/-- A minimization problem is constrained exactly when its feasible set does not fill the ambient
space. -/
theorem isConstrained_iff_feasibleSet_ne_univ
    {problem : FunctionalConstraintsMinimizationProblem X m} :
    problem.IsConstrained ↔ (problem.feasibleSet : Set X) ≠ Set.univ := by
  rw [IsConstrained, Set.ssubset_univ_iff]

/-- A minimization problem is unconstrained exactly when its feasible set fills the ambient
space. -/
theorem not_isConstrained_iff_feasibleSet_eq_univ
    {problem : FunctionalConstraintsMinimizationProblem X m} :
    ¬ problem.IsConstrained ↔ (problem.feasibleSet : Set X) = Set.univ := by
  rw [isConstrained_iff_feasibleSet_ne_univ]
  constructor <;> simp

/-- A constrained problem is equivalently one for which some ambient point lies outside the
feasible set. -/
theorem isConstrained_iff_exists_not_mem_feasibleSet
    {problem : FunctionalConstraintsMinimizationProblem X m} :
    problem.IsConstrained ↔ ∃ x : X, x ∉ (problem.feasibleSet : Set X) := by
  rw [isConstrained_iff_feasibleSet_ne_univ]
  simpa using Set.ne_univ_iff_exists_notMem (problem.feasibleSet : Set X)

end FunctionalConstraintsMinimizationProblem

namespace GeneralMinimizationProblem

variable {n m : ℕ}

variable (problem : GeneralMinimizationProblem n m)

/- Definition 1.1.4.1 in the textbook Euclidean ambient space is the specialization of the owner
predicate `FunctionalConstraintsMinimizationProblem.IsConstrained`. -/
#check problem.IsConstrained

end GeneralMinimizationProblem

/-! ### Definition_1_1_4_2 (from Chap01) -/
namespace GeneralMinimizationProblem

variable {n m : ℕ}

/- Definition 1.1.4.2 is a source-facing recall in the Chapter 1 constrained-optimization owner
domain.

Sampled owner-style declarations:
* `GeneralMinimizationProblem.IsConstrained` in `Definition_1_1_4_1`, the earlier Chapter 1 owner
  predicate for constrainedness;
* `GeneralMinimizationProblem.not_isConstrained_iff_feasibleSet_eq_univ` in
  `Definition_1_1_4_1`, the imported companion bridge from that owner to the textbook whole-space
  formulation;
* the owner expression
  `¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
    problem.toGeneralMinimizationProblem.IsSmooth` together with
  `SetConstrainedMinimizationProblem.unconstrainedSmooth_iff` in `Definition_1_4_3`, the direct
  downstream Chapter 1 reuse of this unconstrainedness predicate;
* `Set.ssubset_univ_iff`, the canonical set-theoretic bridge used upstream to establish that
  companion theorem.

Best owner abstraction:
* source-facing/core: `¬ problem.IsConstrained`
* bridge/view: `GeneralMinimizationProblem.not_isConstrained_iff_feasibleSet_eq_univ`

Primitive data:
* `problem.feasibleSet`
* `problem.IsConstrained`

Derived API:
* none in this recall-only file beyond the imported bridge theorem above

Source/core/bridge triage:
* source-facing: the unconstrainedness predicate `¬ problem.IsConstrained`
* core/canonical: the earlier owner predicate `problem.IsConstrained`
* bridge/view: the whole-space reformulation of the feasible set

This file therefore keeps Definition 1.1.4.2 as a direct recall of the earlier owner predicate,
with the feasible-set equality retained only as the imported thin companion theorem from
`Definition_1_1_4_1` for downstream bridge files. -/

variable (problem : GeneralMinimizationProblem n m)

/- Definition 1.1.4.2: a general minimization problem is unconstrained exactly when the owner
predicate `IsConstrained` does not hold. -/
#check (¬ problem.IsConstrained)

end GeneralMinimizationProblem

/-! ### Definition_1_1_4_3 (from Chap01) -/
universe u

/- Definition 1.1.4.3 lies in the differentiability domain of constrained optimization with a
finite family of scalar constraints.

Sampled owner-style declarations:
* `FunctionalConstraintsMinimizationProblem` in `Definition_1_1_3`, the ambient constrained owner
* `FunctionalConstraintsMinimizationProblem.constraintVector` in `Definition_1_1_1`, the packaged
  finite constraint family
* `DifferentiableOn` together with `differentiableOn_piLp`
* mathlib's canonical ambient-extension operator `Function.extend Subtype.val`

Best owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m`

Primitive data:
* `problem.basicFeasibleSet`
* `problem.objective`
* `problem.constraintVector`

Derived API:
* the ambient zero-extensions `problem.objectiveOnAmbient` and
  `problem.constraintVectorOnAmbient`
* the ambient textbook family `problem.componentOnAmbient`
* the owner smoothness predicate `problem.IsSmooth`
* the componentwise bridge `constraintVector_differentiableOn_iff`

Source/core/bridge triage:
* source-facing: the textbook `GeneralMinimizationProblem n m` specialization
* core/canonical: the ambient owner predicate `problem.IsSmooth`
* bridge/view: the ambient extension maps, the `Fin (m + 1)` component family, and the Euclidean
  specialization

Smoothness here depends only on a real normed ambient space, not on the concrete Euclidean model
`EuclideanSpace ℝ (Fin n)`, so the public owner belongs on
`FunctionalConstraintsMinimizationProblem X m` and the textbook `ℝⁿ` case is recovered as a
specialization. -/

namespace FunctionalConstraintsMinimizationProblem

section AmbientExtension

variable {X : Type u} {m : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin m)

/-- The objective function of a minimization problem, viewed on the ambient space by extending the
owner objective by `0` outside the basic feasible set. -/
noncomputable def objectiveOnAmbient (problem : FunctionalConstraintsMinimizationProblem X m) :
    X → ℝ :=
  Function.extend Subtype.val problem.objective 0

/-- The full constraint family of a minimization problem, viewed on the ambient space by extending
the owner constraint vector by `0` outside the basic feasible set. -/
noncomputable def constraintVectorOnAmbient
    (problem : FunctionalConstraintsMinimizationProblem X m) : X → F :=
  Function.extend Subtype.val problem.constraintVector 0

@[simp] theorem objectiveOnAmbient_apply
    (problem : FunctionalConstraintsMinimizationProblem X m) {x : X}
    (hx : x ∈ problem.basicFeasibleSet) :
    problem.objectiveOnAmbient x = problem.objective ⟨x, hx⟩ := by
  simpa [objectiveOnAmbient] using Function.extend_val_apply hx

@[simp] theorem constraintVectorOnAmbient_apply
    (problem : FunctionalConstraintsMinimizationProblem X m) {x : X}
    (hx : x ∈ problem.basicFeasibleSet) :
    problem.constraintVectorOnAmbient x = problem.constraintVector ⟨x, hx⟩ := by
  simpa [constraintVectorOnAmbient] using Function.extend_val_apply hx

/-- The unified ambient family `f₀, f₁, …, f_m`, where index `0` is the objective and successor
indices are the scalar constraints, obtained by extending each owner component by `0` outside the
basic feasible set. -/
noncomputable def componentOnAmbient
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    Fin (m + 1) → X → ℝ :=
  Fin.cases problem.objectiveOnAmbient fun i ↦ fun x ↦ problem.constraintVectorOnAmbient x i

@[simp] theorem componentOnAmbient_zero
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    problem.componentOnAmbient 0 = problem.objectiveOnAmbient :=
  rfl

@[simp] theorem componentOnAmbient_succ
    (problem : FunctionalConstraintsMinimizationProblem X m) (i : Fin m) :
    problem.componentOnAmbient i.succ = fun x ↦ problem.constraintVectorOnAmbient x i :=
  rfl

end AmbientExtension

section Smoothness

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ}

/-- Definition 1.1.4.3: a functional-constraint minimization problem is smooth when the ambient
extensions of the objective and the packaged constraint vector are differentiable on the basic
feasible set. The textbook family `f₀, f₁, …, f_m` is recovered from these owner maps. -/
def IsSmooth (problem : FunctionalConstraintsMinimizationProblem X m) : Prop :=
  DifferentiableOn ℝ problem.objectiveOnAmbient problem.basicFeasibleSet ∧
    DifferentiableOn ℝ problem.constraintVectorOnAmbient problem.basicFeasibleSet

/-- Smoothness implies differentiability of the objective on the basic feasible set. -/
theorem IsSmooth.objective_differentiableOn
    {problem : FunctionalConstraintsMinimizationProblem X m} (h : problem.IsSmooth) :
    DifferentiableOn ℝ problem.objectiveOnAmbient problem.basicFeasibleSet :=
  h.1

/-- Smoothness implies differentiability of the full constraint map on the basic feasible set. -/
theorem IsSmooth.constraintVector_differentiableOn
    {problem : FunctionalConstraintsMinimizationProblem X m} (h : problem.IsSmooth) :
    DifferentiableOn ℝ problem.constraintVectorOnAmbient problem.basicFeasibleSet :=
  h.2

/-- Smoothness implies continuity of the objective on the basic feasible set. -/
theorem IsSmooth.objective_continuous
    {problem : FunctionalConstraintsMinimizationProblem X m} (h : problem.IsSmooth) :
    Continuous problem.objective := by
  have hObjectiveContinuousOn : ContinuousOn problem.objectiveOnAmbient problem.basicFeasibleSet :=
    h.objective_differentiableOn.continuousOn
  convert hObjectiveContinuousOn.restrict using 1
  ext x
  simp

/-- Smoothness implies continuity of the packaged constraint map on the basic feasible set. -/
theorem IsSmooth.constraintVector_continuous
    {problem : FunctionalConstraintsMinimizationProblem X m} (h : problem.IsSmooth) :
    Continuous problem.constraintVector := by
  have hConstraintContinuousOn :
      ContinuousOn problem.constraintVectorOnAmbient problem.basicFeasibleSet :=
    h.constraintVector_differentiableOn.continuousOn
  convert hConstraintContinuousOn.restrict using 1
  ext x
  simp

/-- The full constraint map is differentiable on the basic feasible set exactly when each scalar
constraint component is differentiable there. -/
theorem constraintVector_differentiableOn_iff
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    DifferentiableOn ℝ problem.constraintVectorOnAmbient problem.basicFeasibleSet ↔
      ∀ i : Fin m,
        DifferentiableOn ℝ (fun x ↦ problem.constraintVectorOnAmbient x i)
          problem.basicFeasibleSet := by
  simpa using differentiableOn_piLp (2 : ENNReal)

/-- Smoothness is equivalent to differentiability of every member of the ambient textbook family
`f₀, f₁, …, f_m` on the basic feasible set. -/
theorem isSmooth_iff_forall_component_differentiableOn
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    problem.IsSmooth ↔
      ∀ j : Fin (m + 1),
        DifferentiableOn ℝ (problem.componentOnAmbient j) problem.basicFeasibleSet := by
  rw [IsSmooth, Fin.forall_fin_succ]
  constructor
  · rintro ⟨hObjective, hConstraintVector⟩
    refine ⟨?_, (constraintVector_differentiableOn_iff problem).mp hConstraintVector⟩
    simpa using hObjective
  · rintro ⟨hObjective, hConstraints⟩
    refine ⟨?_, (constraintVector_differentiableOn_iff problem).mpr hConstraints⟩
    simpa using hObjective

/-- Smoothness implies differentiability of each scalar constraint on the basic feasible set. -/
theorem IsSmooth.constraint_differentiableOn
    {problem : FunctionalConstraintsMinimizationProblem X m} (h : problem.IsSmooth)
    (i : Fin m) :
    DifferentiableOn ℝ (fun x ↦ problem.constraintVectorOnAmbient x i)
      problem.basicFeasibleSet := by
  exact (constraintVector_differentiableOn_iff problem).mp h.constraintVector_differentiableOn i

end Smoothness

end FunctionalConstraintsMinimizationProblem

namespace GeneralMinimizationProblem

section

variable {n m : ℕ} (problem : GeneralMinimizationProblem n m)

/- Definition 1.1.4.3 in the textbook Euclidean ambient space is the specialization of the
ambient owner predicate `FunctionalConstraintsMinimizationProblem.IsSmooth`. -/
#check problem.IsSmooth

end

end GeneralMinimizationProblem

/-! ### Definition_1_1_4_4 (from Chap01) -/
namespace GeneralMinimizationProblem

variable {n m : ℕ}

/- Primary domain: differentiability of the objective/constraint family of a general minimization
problem.

Sampled owner-style declarations before refining:
* `FunctionalConstraintsMinimizationProblem.IsSmooth` in `Definition_1_1_4_3`, the ambient owner
  predicate whose Euclidean specialization gives the textbook nonsmoothness notion
* `FunctionalConstraintsMinimizationProblem.constraintVector_differentiableOn_iff` in
  `Definition_1_1_4_3`, the canonical bridge from packaged constraint-map differentiability to
  scalar constraints
* `FunctionalConstraintsMinimizationProblem.constraintVector` in `Definition_1_1_1`, the upstream
  packaged owner for the scalar constraint family
* `¬ problem.IsConstrained` together with `not_isConstrained_iff_feasibleSet_eq_univ` in
  `Definition_1_1_4_1`, the matching earlier chapter pattern for recall-only negated predicates

Layer classification:
* source-facing: the recall-only negated owner expression `¬ problem.IsSmooth`
* core/canonical: `problem.IsSmooth`
* bridge/view: the explicit objective/constraint split and the scalar-constraint reformulation

Primitive data:
* `problem.basicFeasibleSet`
* `problem.objective`
* `problem.constraintVector`

Derived API:
* `problem.IsSmooth`
* `isNonsmooth_iff` -/

variable (problem : GeneralMinimizationProblem n m)

/- Definition 1.1.4.4: a general minimization problem is nonsmooth exactly when the owner
predicate `IsSmooth` from the previous item does not hold. -/
#check ¬ problem.IsSmooth

/-- Negating the canonical smoothness predicate gives the explicit textbook split into either a
nonsmooth objective or at least one nonsmooth constraint. -/
theorem isNonsmooth_iff (problem : GeneralMinimizationProblem n m) :
    ¬ problem.IsSmooth ↔
      ¬ DifferentiableOn ℝ problem.objectiveOnAmbient problem.basicFeasibleSet ∨
        ∃ i : Fin m,
          ¬ DifferentiableOn ℝ (fun x ↦ problem.constraintVectorOnAmbient x i)
            problem.basicFeasibleSet := by
  classical
  rw [FunctionalConstraintsMinimizationProblem.IsSmooth, not_and_or,
    FunctionalConstraintsMinimizationProblem.constraintVector_differentiableOn_iff, not_forall]

end GeneralMinimizationProblem

/-! ### Definition_1_1_4_5 (from Chap01) -/
open AffineMap

namespace Set

/-- A map on a subset is affine when it is the restriction of an ambient affine map. -/
def AffineOn {X Y : Type*} (Q : Set X) (k : Type*) [Ring k] [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] (f : Q → Y) : Prop :=
  ∃ g : X →ᵃ[k] Y, ∀ x (hx : x ∈ Q), f ⟨x, hx⟩ = g x

end Set

/- Definition 1.1.4.5 lies in the affine/polyhedral constrained-optimization domain.

Sampled owner-style declarations:
* `FunctionalConstraintsMinimizationProblem` in `Chap01/Definition_1_1_3`, the project owner for
  finitely many scalar constraints on an ambient type
* `FunctionalConstraintsMinimizationProblem.constraintVector` in `Chap01/Definition_1_1_1`, the
  packaged finite constraint family
* `Set.AffineOn`
* `Set.SatisfiesInteriorBallCondition` in `Chap03/Definition_3_59`, a chapter-level set-owned
  predicate for an elementary property of subsets
* `AffineMap.pi`

Owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m` for the constrained-problem owner
* `problem.constraintVector` for the packaged affine constraint family
* `Set.AffineOn` and `Set.IsPolyhedron` for affine/polyhedral data on the basic feasible set

Source/core/bridge triage:
* `source-facing`: `FunctionalConstraintsMinimizationProblem.IsLinearlyConstrained`
* `core/canonical`: `FunctionalConstraintsMinimizationProblem X m`, `Set.AffineOn`,
  `Set.IsPolyhedron`
* `bridge/view`: the Euclidean inner-product representation theorems in the
  `GeneralMinimizationProblem` specialization

Primitive data:
* `problem.basicFeasibleSet`
* `problem.senses`
* affine data of the packaged owner map `problem.constraintVector`

Derived API:
* coordinatewise affineness of the scalar constraint family
* Euclidean inner-product formulas for affine scalar constraints
-/

namespace Set

/-- Helper for Definition 1.1.4.5: a subset of a real module is polyhedral if it is cut out by
finitely many affine inequalities and equalities. -/
def IsPolyhedron {X : Type*} [AddCommGroup X] [Module ℝ X] (Q : Set X) : Prop :=
  ∃ k : ℕ, ∃ g : Fin k → X →ᵃ[ℝ] ℝ,
    ∃ senses : Fin k → ConstraintSense,
      Q = {x | ∀ i, (senses i).Holds (g i x)}

end Set

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type*} [AddCommGroup X] [Module ℝ X] {m : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin m)

/-- Helper for Definition 1.1.4.5: the owner constraint vector is affine on the basic feasible
set exactly when each scalar constraint is affine there. -/
theorem constraintVector_affineOn_iff_forall_constraint_affineOn
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    Set.AffineOn problem.basicFeasibleSet ℝ problem.constraintVector ↔
      ∀ j : Fin m, Set.AffineOn problem.basicFeasibleSet ℝ (problem.constraints j) := by
  constructor
  · rintro ⟨g, hg⟩ j
    -- Project the ambient affine witness onto the `j`th coordinate.
    refine ⟨(EuclideanSpace.projₗ j).toAffineMap.comp g, ?_⟩
    intro x hx
    change problem.constraintVector ⟨x, hx⟩ j =
      ((EuclideanSpace.projₗ j).toAffineMap.comp g) x
    simpa using congrArg (fun y : F ↦ y j) (hg x hx)
  · intro h
    choose g hg using h
    -- Assemble the coordinatewise affine witnesses into one Euclidean-valued affine map.
    refine ⟨
      ((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap.toAffineMap).comp (pi g),
      ?_⟩
    intro x hx
    ext j
    change problem.constraintVector ⟨x, hx⟩ j = _
    simp [constraintVector, hg j x hx]

/-- Definition 1.1.4.5: A minimization problem is linearly constrained when its packaged owner
constraint family is affine on the basic feasible set and that basic feasible set is polyhedral. -/
def IsLinearlyConstrained (problem : FunctionalConstraintsMinimizationProblem X m) : Prop :=
  Set.AffineOn problem.basicFeasibleSet ℝ problem.constraintVector ∧
    problem.basicFeasibleSet.IsPolyhedron

/-- Helper for Definition 1.1.4.5: expanding the owner formulation recovers the textbook condition
that each scalar constraint is affine on the basic feasible set and that the basic feasible set is
polyhedral. -/
theorem isLinearlyConstrained_iff (problem : FunctionalConstraintsMinimizationProblem X m) :
    problem.IsLinearlyConstrained ↔
      (∀ j : Fin m, Set.AffineOn problem.basicFeasibleSet ℝ (problem.constraints j)) ∧
        problem.basicFeasibleSet.IsPolyhedron := by
  constructor
  · rintro ⟨hconstraint, hpoly⟩
    -- Rewrite the packaged affine condition into the coordinatewise textbook formulation.
    exact ⟨problem.constraintVector_affineOn_iff_forall_constraint_affineOn.mp hconstraint, hpoly⟩
  · rintro ⟨hconstraint, hpoly⟩
    -- Repackage the scalar affine data into the owner-level affine constraint vector.
    exact ⟨problem.constraintVector_affineOn_iff_forall_constraint_affineOn.mpr hconstraint, hpoly⟩

/-- Helper for Definition 1.1.4.5: a linearly constrained problem has affine functional
constraints. -/
theorem IsLinearlyConstrained.constraint_isAffine
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsLinearlyConstrained) (j : Fin m) :
    Set.AffineOn problem.basicFeasibleSet ℝ (problem.constraints j) := by
  -- Read off the `j`th scalar affine constraint from the textbook reformulation.
  exact (problem.isLinearlyConstrained_iff.mp h).1 j

/-- Helper for Definition 1.1.4.5: a linearly constrained problem has an affine packaged owner
constraint vector. -/
theorem IsLinearlyConstrained.constraintVector_isAffine
    {problem : FunctionalConstraintsMinimizationProblem X m} (h : problem.IsLinearlyConstrained) :
    Set.AffineOn problem.basicFeasibleSet ℝ problem.constraintVector := by
  -- The packaged affine condition is the first field of the definition.
  exact h.1

/-- Helper for Definition 1.1.4.5: a linearly constrained problem has a polyhedral basic feasible
set. -/
theorem IsLinearlyConstrained.isPolyhedron {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsLinearlyConstrained) :
    problem.basicFeasibleSet.IsPolyhedron := by
  -- The polyhedrality clause is the second field of the definition.
  exact h.2

end FunctionalConstraintsMinimizationProblem

namespace GeneralMinimizationProblem

variable {n m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- An affine scalar function on `ℝⁿ` can be written as an inner product with a coefficient vector
plus a constant term. -/
-- Proof sketch: identify an affine functional with a linear functional plus a constant, then use
-- the finite-dimensional real Riesz representation theorem to write the linear part as an inner
-- product with a coefficient vector.
theorem functionIsAffine_iff_exists_inner_add (problem : GeneralMinimizationProblem n m)
    (f : problem.basicFeasibleSet → ℝ) :
    Set.AffineOn problem.basicFeasibleSet ℝ f ↔
      ∃ a : E, ∃ b : ℝ,
        ∀ x (hx : x ∈ problem.basicFeasibleSet),
          f ⟨x, hx⟩ = inner ℝ a x + b := by
  constructor
  · rintro ⟨g, hg⟩
    let L : E →L[ℝ] ℝ :=
      { toLinearMap := g.linear
        cont := g.linear.continuous_of_finiteDimensional }
    let a : E := (InnerProductSpace.toDual ℝ E).symm L
    refine ⟨a, g 0, ?_⟩
    intro x hx
    -- Decompose the ambient affine witness into its linear part and constant part.
    calc
      f ⟨x, hx⟩ = g x := hg x hx
      _ = g.linear x + g 0 := by simpa using congrFun g.decomp x
      _ = inner ℝ a x + g 0 := by
        congr 1
        change (L : E → ℝ) x = inner ℝ a x
        rw [InnerProductSpace.toDual_symm_apply (x := x) (y := L)]
  · rintro ⟨a, b, hf⟩
    let g : E →ᵃ[ℝ] ℝ :=
      AffineMap.const ℝ E b + ((innerSL ℝ a).toLinearMap).toAffineMap
    refine ⟨g, ?_⟩
    intro x hx
    -- Repackage the textbook inner-product formula as an ambient affine map.
    exact by
      simp [g, hf x hx, add_comm]

/-- An affine scalar constraint on `ℝⁿ` can be written as an inner product with a coefficient
vector plus a constant term. -/
theorem constraintIsAffine_iff_exists_inner_add (problem : GeneralMinimizationProblem n m)
    (j : Fin m) :
    Set.AffineOn problem.basicFeasibleSet ℝ (problem.constraints j) ↔
      ∃ a : E, ∃ b : ℝ,
        ∀ x (hx : x ∈ problem.basicFeasibleSet),
          problem.constraints j ⟨x, hx⟩ = inner ℝ a x + b := by
  simpa using functionIsAffine_iff_exists_inner_add problem (problem.constraints j)

/-- Every functional constraint of a linearly constrained Euclidean problem is given by an inner
product with a coefficient vector plus a constant term on the basic feasible set. -/
theorem IsLinearlyConstrained.constraint_eq_inner_add {problem : GeneralMinimizationProblem n m}
    (h : problem.IsLinearlyConstrained) (j : Fin m) :
    ∃ a : E, ∃ b : ℝ,
      ∀ x (hx : x ∈ problem.basicFeasibleSet),
        problem.constraints j ⟨x, hx⟩ = inner ℝ a x + b :=
  (constraintIsAffine_iff_exists_inner_add problem j).mp (h.constraint_isAffine j)

end GeneralMinimizationProblem

/-! ### Definition_1_1_4_6 (from Chap01) -/
namespace FunctionalConstraintsMinimizationProblem

variable {X : Type*} [AddCommGroup X] [Module ℝ X] {m : ℕ}

/-
Definition 1.1.4.6 lies in the affine/linearly constrained optimization domain.

Sampled owner-side declarations in this domain:
* `Set.AffineOn`
* `FunctionalConstraintsMinimizationProblem.IsLinearlyConstrained`
* `FunctionalConstraintsMinimizationProblem.IsLinearlyConstrained.constraint_isAffine`
* `FunctionalConstraintsMinimizationProblem.isLinearlyConstrained_iff`

Owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m`
* `Set.AffineOn` for affine objective data on the basic feasible set
* `problem.IsLinearlyConstrained` for the constraint side

Source/core/bridge triage:
* `source-facing`: the textbook `GeneralMinimizationProblem n m` specialization
* `core/canonical`: `FunctionalConstraintsMinimizationProblem.IsLinearOptimizationProblem`
* `bridge/view`: `GeneralMinimizationProblem n m` as the Euclidean specialization

Primitive data for the core owner notion:
* affine objective data on `problem.basicFeasibleSet`
* linearly constrained constraint data

Derived API:
* the textbook expansion through `problem.isLinearOptimizationProblem_iff`
* the owner-side consequences
  `IsLinearOptimizationProblem.objective_isAffine` and
  `IsLinearOptimizationProblem.isLinearlyConstrained`

Nothing in the definition uses coordinates on `ℝⁿ`; the Euclidean ambient space is only the
textbook specialization of this owner-level notion.
-/

/-- Definition 1.1.4.6: a linear optimization problem is a minimization problem whose objective
function is affine and which is linearly constrained in the sense of
Definition 1.1.4.5. -/
def IsLinearOptimizationProblem (problem : FunctionalConstraintsMinimizationProblem X m) : Prop :=
  Set.AffineOn problem.basicFeasibleSet ℝ problem.objective ∧ problem.IsLinearlyConstrained

/-- Expanding the owner formulation gives the textbook condition that the objective and every
functional constraint are affine and the basic feasible set is polyhedral. -/
theorem isLinearOptimizationProblem_iff
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    problem.IsLinearOptimizationProblem ↔
      Set.AffineOn problem.basicFeasibleSet ℝ problem.objective ∧
        (∀ j : Fin m, Set.AffineOn problem.basicFeasibleSet ℝ (problem.constraints j)) ∧
        problem.basicFeasibleSet.IsPolyhedron := by
  rw [IsLinearOptimizationProblem, problem.isLinearlyConstrained_iff]

/-- A linear optimization problem has an affine objective function. -/
theorem IsLinearOptimizationProblem.objective_isAffine
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsLinearOptimizationProblem) :
    Set.AffineOn problem.basicFeasibleSet ℝ problem.objective :=
  h.1

/-- A linear optimization problem is, in particular, linearly constrained. -/
theorem IsLinearOptimizationProblem.isLinearlyConstrained
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsLinearOptimizationProblem) :
    problem.IsLinearlyConstrained :=
  h.2

end FunctionalConstraintsMinimizationProblem

namespace GeneralMinimizationProblem

variable {n m : ℕ} (problem : GeneralMinimizationProblem n m)

/- Definition 1.1.4.6 in the textbook Euclidean ambient space is the specialization of the owner
predicate `FunctionalConstraintsMinimizationProblem.IsLinearOptimizationProblem`. -/
#check problem.IsLinearOptimizationProblem

end GeneralMinimizationProblem

/-! ### Definition_1_1_4_7 (from Chap01) -/
open AffineMap

namespace Set

/-- A map on a subset is quadratic when it differs from the restriction of an ambient quadratic map
by an affine map on that subset. -/
def QuadraticOn {X Y : Type*} (Q : Set X) (k : Type*) [CommRing k] [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] (f : Q → Y) : Prop :=
  ∃ q : QuadraticMap k X Y, Set.AffineOn Q k (fun x ↦ f x - q x.1)

end Set

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type*} [AddCommGroup X] [Module ℝ X] {m : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin m)

/-
Definition 1.1.4.7 lies in the quadratic constrained-optimization domain.

Sampled owner-side declarations in this domain:
* `FunctionalConstraintsMinimizationProblem.constraintVector`
* `FunctionalConstraintsMinimizationProblem.IsLinearlyConstrained`
* `Set.AffineOn`
* `QuadraticMap`

Owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m` for the constrained-problem owner
* `Set.QuadraticOn` for quadratic data on `problem.basicFeasibleSet`

Source/core/bridge triage:
* `source-facing`: the textbook `GeneralMinimizationProblem n m` specialization
* `core/canonical`: `FunctionalConstraintsMinimizationProblem.IsQuadraticOptimizationProblem`
* `bridge/view`: the coordinatewise quadraticity theorem for `problem.constraintVector`

Primitive data:
* quadratic objective data on `problem.basicFeasibleSet`
* linearly constrained constraint data

Derived API:
* coordinatewise quadraticity of the scalar constraints
* owner-side consequences of quadratic optimization

As in Definition 1.1.4.6, nothing in the main notion uses coordinates on `ℝⁿ`; the Euclidean
ambient space is only the textbook specialization of this owner-level predicate.
-/

/-- The packaged owner constraint vector is quadratic exactly when each scalar constraint is
quadratic. -/
theorem constraintVector_quadraticOn_iff_forall_constraint_quadraticOn
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    Set.QuadraticOn problem.basicFeasibleSet ℝ problem.constraintVector ↔
      ∀ j : Fin m, Set.QuadraticOn problem.basicFeasibleSet ℝ (problem.constraints j) := by
  constructor
  · rintro ⟨q, g, hg⟩ j
    refine ⟨(EuclideanSpace.projₗ j).compQuadraticMap q, ?_⟩
    refine ⟨(EuclideanSpace.projₗ j).toAffineMap.comp g, ?_⟩
    intro x hx
    change (problem.constraintVector ⟨x, hx⟩ - q x) j =
      ((EuclideanSpace.projₗ j).toAffineMap.comp g) x
    simpa using congrArg (fun y : F ↦ y j) (hg x hx)
  · intro h
    choose q hq using h
    choose g hg using hq
    refine ⟨
      (EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap.compQuadraticMap
        (∑ j, (LinearMap.single ℝ (fun _ : Fin m ↦ ℝ) j).compQuadraticMap (q j)),
      ?_⟩
    refine ⟨
      ((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap.toAffineMap).comp (pi g),
      ?_⟩
    intro x hx
    ext j
    simp [hg j x hx]

/-- Quadraticity of the packaged owner constraint vector implies quadraticity of each scalar
constraint. -/
theorem constraint_isQuadratic
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : Set.QuadraticOn problem.basicFeasibleSet ℝ problem.constraintVector)
    (j : Fin m) :
    Set.QuadraticOn problem.basicFeasibleSet ℝ (problem.constraints j) :=
  (problem.constraintVector_quadraticOn_iff_forall_constraint_quadraticOn.mp h) j

/-- Definition 1.1.4.7: a quadratic optimization problem is a minimization problem whose objective
function is quadratic and which is linearly constrained in the sense of
Definition 1.1.4.5. -/
def IsQuadraticOptimizationProblem
    (problem : FunctionalConstraintsMinimizationProblem X m) : Prop :=
  Set.QuadraticOn problem.basicFeasibleSet ℝ problem.objective ∧ problem.IsLinearlyConstrained

/-- A quadratic optimization problem has a quadratic objective function. -/
theorem IsQuadraticOptimizationProblem.objective_isQuadratic
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsQuadraticOptimizationProblem) :
    Set.QuadraticOn problem.basicFeasibleSet ℝ problem.objective :=
  h.1

/-- A quadratic optimization problem is, in particular, linearly constrained. -/
theorem IsQuadraticOptimizationProblem.isLinearlyConstrained
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsQuadraticOptimizationProblem) :
    problem.IsLinearlyConstrained :=
  h.2

/-- Every functional constraint of a quadratic optimization problem is affine. -/
theorem IsQuadraticOptimizationProblem.constraint_isAffine
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsQuadraticOptimizationProblem) (j : Fin m) :
    Set.AffineOn problem.basicFeasibleSet ℝ (problem.constraints j) :=
  h.isLinearlyConstrained.constraint_isAffine j

/-- A quadratic optimization problem has a polyhedral basic feasible set. -/
theorem IsQuadraticOptimizationProblem.isPolyhedron
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsQuadraticOptimizationProblem) :
    problem.basicFeasibleSet.IsPolyhedron :=
  h.isLinearlyConstrained.isPolyhedron

end FunctionalConstraintsMinimizationProblem

namespace GeneralMinimizationProblem

variable {n m : ℕ} (problem : GeneralMinimizationProblem n m)

/- Definition 1.1.4.7 in the textbook Euclidean ambient space is the specialization of the owner
predicate `FunctionalConstraintsMinimizationProblem.IsQuadraticOptimizationProblem`. -/
#check problem.IsQuadraticOptimizationProblem

end GeneralMinimizationProblem

/-! ### Definition_1_1_4_8 (from Chap01) -/
namespace FunctionalConstraintsMinimizationProblem

variable {X : Type*} [AddCommGroup X] [Module ℝ X] {m : ℕ}

/-
Definition 1.1.4.8 lies in the quadratic constrained-optimization domain.

Sampled owner-side declarations in this domain:
* `Set.QuadraticOn`
* `FunctionalConstraintsMinimizationProblem
  .constraintVector_quadraticOn_iff_forall_constraint_quadraticOn`
* `FunctionalConstraintsMinimizationProblem.constraint_isQuadratic`
* `FunctionalConstraintsMinimizationProblem.IsQuadraticOptimizationProblem`

Owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m`
* `Set.QuadraticOn` for quadratic data on `problem.basicFeasibleSet`

Source/core/bridge triage:
* `source-facing`:
  `FunctionalConstraintsMinimizationProblem.IsQuadraticallyConstrainedQuadraticProblem`
* `core/canonical`: `Set.QuadraticOn` on the owner objective and packaged constraint vector
* `bridge/view`: the scalar-constraint expansion and the earlier owner
  `FunctionalConstraintsMinimizationProblem.IsQuadraticOptimizationProblem`

Primitive data:
* quadratic objective data
* quadratic packaged constraint-vector data

Derived API:
* scalar quadratic constraints derived from the packaged owner constraint vector
* the bridge from linearly constrained quadratic optimization to the present owner
-/

/-- Definition 1.1.4.8: a quadratically constrained quadratic problem is a minimization problem
whose objective function and packaged constraint vector, equivalently every scalar constraint, are
quadratic on the basic feasible set. -/
def IsQuadraticallyConstrainedQuadraticProblem
    (problem : FunctionalConstraintsMinimizationProblem X m) : Prop :=
  Set.QuadraticOn problem.basicFeasibleSet ℝ problem.objective ∧
    Set.QuadraticOn problem.basicFeasibleSet ℝ problem.constraintVector

/-- A quadratic optimization problem is, in particular, quadratically constrained quadratic. -/
theorem IsQuadraticOptimizationProblem.isQuadraticallyConstrainedQuadraticProblem
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsQuadraticOptimizationProblem) :
    problem.IsQuadraticallyConstrainedQuadraticProblem := by
  refine ⟨h.objective_isQuadratic, ⟨0, ?_⟩⟩
  simpa using h.isLinearlyConstrained.constraintVector_isAffine

variable {problem : FunctionalConstraintsMinimizationProblem X m}

/-- Unfolding the owner-style definition recovers the scalar-constraint formulation. -/
theorem isQuadraticallyConstrainedQuadraticProblem_iff :
    problem.IsQuadraticallyConstrainedQuadraticProblem ↔
      Set.QuadraticOn problem.basicFeasibleSet ℝ problem.objective ∧
        ∀ j : Fin m, Set.QuadraticOn problem.basicFeasibleSet ℝ (problem.constraints j) := by
  rw [IsQuadraticallyConstrainedQuadraticProblem,
    problem.constraintVector_quadraticOn_iff_forall_constraint_quadraticOn]

/-- A quadratically constrained quadratic problem has a quadratic objective function. -/
theorem IsQuadraticallyConstrainedQuadraticProblem.objective_isQuadratic
    (h : problem.IsQuadraticallyConstrainedQuadraticProblem) :
    Set.QuadraticOn problem.basicFeasibleSet ℝ problem.objective :=
  h.1

/-- A quadratically constrained quadratic problem has a quadratic packaged constraint vector. -/
theorem IsQuadraticallyConstrainedQuadraticProblem.constraintVector_isQuadratic
    (h : problem.IsQuadraticallyConstrainedQuadraticProblem) :
    Set.QuadraticOn problem.basicFeasibleSet ℝ problem.constraintVector :=
  h.2

/-- Every scalar constraint of a quadratically constrained quadratic problem is quadratic. -/
theorem IsQuadraticallyConstrainedQuadraticProblem.constraint_isQuadratic
    (h : problem.IsQuadraticallyConstrainedQuadraticProblem) (j : Fin m) :
    Set.QuadraticOn problem.basicFeasibleSet ℝ (problem.constraints j) :=
  problem.constraint_isQuadratic h.2 j

end FunctionalConstraintsMinimizationProblem

namespace GeneralMinimizationProblem

variable {n m : ℕ} (problem : GeneralMinimizationProblem n m)

/- Definition 1.1.4.8 in the textbook Euclidean ambient space is the specialization of the owner
predicate `FunctionalConstraintsMinimizationProblem.IsQuadraticallyConstrainedQuadraticProblem`. -/
#check problem.IsQuadraticallyConstrainedQuadraticProblem

end GeneralMinimizationProblem

/-! ### Example_1_1_5 (from Chap01) -/
universe u

variable {m : ℕ} {X : Type u}

/- Example 1.1.5 lies in the constrained-optimization domain of bounded functional characteristics.

Sampled owner-style declarations:
* `FunctionalConstraintsMinimizationProblem` and `problem.IsFeasible` in
  `Chap01/Definition_1_1_3`
* `FunctionalConstraintsMinimizationProblem.HasLeConstraints` in
  `Chap01/Definition_1_1_1`
* `FunctionalConstraintsMinimizationProblem.mem_feasibleSet_iff` in
  `Chap01/Definition_1_1_1`
* `LagrangianProblem.toFunctionalConstraintsMinimizationProblem` in
  `Chap01/Definition_1_10_2`

Best owner abstraction:
* `FunctionalConstraintsMinimizationProblem X (m + m)`, obtained by adjoining the lower- and
  upper-bound inequalities as one owner constraint family on the structural set `Q`

Primitive data:
* the structural set `Q`
* the distinguished objective `f₀`
* the characteristic family `fⱼ`
* the lower and upper scalar bounds

Derived API:
* the owner object `boundedCharacteristicProblem`
* the fact that all owner constraints are inequalities
* simp lemmas identifying the lower and upper appended constraint coordinates
* the source-facing feasibility characterization in terms of the paired bounds

Source/core/bridge triage:
* source-facing: the bounded-characteristic optimization problem from the textbook
* core/canonical: `FunctionalConstraintsMinimizationProblem X (m + m)`
* bridge/view: the Euclidean specialization `GeneralMinimizationProblem n (m + m)` and the
  feasibility equivalence unpacking the owner inequalities into lower and upper scalar bounds

The source states `Q ⊆ ℝⁿ`, but this construction only uses the structural set `Q` and the scalar
characteristic family on its subtype. The faithful owner is therefore the ambient
`FunctionalConstraintsMinimizationProblem`, with the textbook Euclidean problem recovered as its
specialization. -/

section

variable (Q : Set X) (objective : Q → ℝ)
variable (characteristics : Fin m → Q → ℝ) (lowerBounds upperBounds : Fin m → ℝ)

/-- Example 1.1.5: Functional characteristics with lower and upper bounds define a general
minimization problem on the structural set `Q`: the distinguished characteristic `f₀` is the
objective, and the remaining characteristics appear as paired lower and upper scalar constraints.
The textbook Euclidean formulation is the specialization of this owner to `X = ℝⁿ`. -/
def boundedCharacteristicProblem
    : FunctionalConstraintsMinimizationProblem X (m + m) where
  basicFeasibleSet := Q
  objective := objective
  constraints :=
    Fin.append
      (fun j x ↦ lowerBounds j - characteristics j x)
      (fun j x ↦ characteristics j x - upperBounds j)
  senses := fun _ ↦ .le

@[simp] theorem boundedCharacteristicProblem_hasLeConstraints
    :
    (boundedCharacteristicProblem Q objective characteristics lowerBounds
      upperBounds).HasLeConstraints :=
  fun _ ↦ rfl

end

section

variable {Q : Set X} {objective : Q → ℝ}
variable {characteristics : Fin m → Q → ℝ} {lowerBounds upperBounds : Fin m → ℝ}

@[simp] theorem boundedCharacteristicProblem_constraints_castAdd
    (j : Fin m)
    (x : Q) :
    (boundedCharacteristicProblem Q objective characteristics lowerBounds upperBounds).constraints
        (j.castAdd m) x =
      lowerBounds j - characteristics j x := by
  change
    Fin.append
        (fun k x ↦ lowerBounds k - characteristics k x)
        (fun k x ↦ characteristics k x - upperBounds k)
        (j.castAdd m) x =
      lowerBounds j - characteristics j x
  exact congrFun
    (Fin.append_left
      (fun k x ↦ lowerBounds k - characteristics k x)
      (fun k x ↦ characteristics k x - upperBounds k)
      j) x

@[simp] theorem boundedCharacteristicProblem_constraints_addNat
    (j : Fin m)
    (x : Q) :
    (boundedCharacteristicProblem Q objective characteristics lowerBounds upperBounds).constraints
        (j.addNat m) x =
      characteristics j x - upperBounds j := by
  simpa [boundedCharacteristicProblem] using
    congrFun
      (Fin.append_right
        (fun k x ↦ lowerBounds k - characteristics k x)
        (fun k x ↦ characteristics k x - upperBounds k)
        j) x

/-- Feasibility for the bounded-characteristic problem is exactly satisfaction of each lower and
upper bound constraint. -/
-- Proof sketch: unfold the owner predicate `IsFeasible`, then use the canonical `Fin.append_left`
-- and `Fin.append_right` equations for the paired lower/upper constraint family; each resulting
-- scalar inequality rewrites by `sub_nonpos`.
theorem boundedCharacteristicProblem_isFeasible_iff
    {x : Q} :
    (boundedCharacteristicProblem Q objective characteristics lowerBounds
      upperBounds).IsFeasible x ↔
      ∀ j : Fin m, lowerBounds j ≤ characteristics j x ∧ characteristics j x ≤ upperBounds j := by
  let problem := boundedCharacteristicProblem Q objective characteristics lowerBounds upperBounds
  change x ∈ problem.feasibleSet ↔ _
  have hproblem :
      x ∈ problem.feasibleSet ↔
        ∀ i : Fin (m + m), problem.constraints i x ≤ 0 :=
    problem.mem_feasibleSet_iff
      (boundedCharacteristicProblem_hasLeConstraints Q objective characteristics lowerBounds
        upperBounds)
  refine hproblem.trans ?_
  constructor
  · intro hx j
    exact
      ⟨by simpa [problem, sub_nonpos] using hx (j.castAdd m),
        by simpa [problem, sub_nonpos] using hx (j.addNat m)⟩
  · intro hx i
    cases i using Fin.addCases with
    | left j =>
        simpa [problem, sub_nonpos] using (hx j).1
    | right j =>
        simpa [problem, sub_nonpos] using (hx j).2

end
