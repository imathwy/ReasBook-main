import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Recall
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_3_1 (from Chap01) -/
/- Definition 1.3.1 lies in the finite-dimensional Euclidean box domain.

Sampled owner-style declarations:
* `Set.Icc` and `Set.mem_Icc` for the scalar closed interval `[0, 1]`
* `EuclideanSpace.equiv (Fin n) ℝ`, the old coordinate-transport bridge being removed here
* the project's coordinatewise Euclidean box owners such as `coordinatewiseUnitBox` and
  `symmetricBox`, whose public surface is intrinsic rather than transported

Source/core/bridge triage:
* source-facing: the textbook box `B_n = [0,1]^n`
* core/canonical in this workspace: the intrinsic coordinatewise scalar interval condition on
  `EuclideanSpace ℝ (Fin n)`
* bridge/view: the coordinatewise membership theorem `mem_zeroOneBox_iff`

Primitive data:
* only the dimension `n`

Derived API:
* the coordinatewise membership criterion
* the origin-feasibility lemma

This removes the redundant `EuclideanSpace.equiv` transport wrapper from the owner itself while
keeping the source semantics unchanged. -/

/-- Definition 1.3.1: the textbook box `B_n = [0,1]^n` in `ℝⁿ`. -/
abbrev zeroOneBox (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1}

/-- Membership in `zeroOneBox n` is exactly the coordinatewise interval condition. -/
-- Proof sketch: unfold membership in the defining set comprehension for `zeroOneBox`.
@[simp] theorem mem_zeroOneBox_iff {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ zeroOneBox n ↔ ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1 :=
  Iff.rfl

/-- The origin belongs to the textbook box `B_n = [0,1]^n`. -/
-- Proof sketch: evaluate each coordinate of the zero vector and use `Set.mem_Icc`.
theorem zeroOneBox_zero_mem (n : ℕ) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ zeroOneBox n := by
  intro i
  simp [Set.mem_Icc]

/-! ### Definition_1_3_1 (from Items/Chap01) -/
/- Definition 1.3.1 lies in the finite-dimensional Euclidean box domain.

Relevant owner-style declarations sampled before refining:
* `Set.Icc`, the canonical scalar owner for the interval `[0, 1]`;
* `Set.mem_Icc`, the canonical bridge from interval membership to inequalities;
* `zeroOneBox` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_1.lean`, the chapter owner of the textbook box
  `B_n = [0,1]^n`;
* `mem_zeroOneBox_iff` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_1.lean`, the chapter bridge exposing
  the coordinatewise interval condition.

Best owner abstraction:
* the chapter owner `zeroOneBox`

Primitive data:
* the dimension `n`

Derived API:
* the membership bridge `mem_zeroOneBox_iff`
* the origin-feasibility lemma `zeroOneBox_zero_mem`

Source/core/bridge triage:
* source-facing: the textbook box `B_n = [0,1]^n`
* core/canonical: the chapter owner `zeroOneBox n : Set (EuclideanSpace ℝ (Fin n))`
* bridge/view: `mem_zeroOneBox_iff` and the inherited feasibility lemma `zeroOneBox_zero_mem`

This item is therefore refined to reuse the exact chapter owner directly, instead of keeping a
parallel local copy of the same box definition or its already-owned companion lemmas. -/

/- Definition 1.3.1: the textbook box `B_n = [0,1]^n` in `ℝⁿ` is the chapter owner
`zeroOneBox n`. -/
recall zeroOneBox (n : ℕ) : Set (EuclideanSpace ℝ (Fin n))

/- Membership in `zeroOneBox n` is exactly the coordinatewise interval condition. -/
recall mem_zeroOneBox_iff {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ zeroOneBox n ↔ ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1

/- The origin belongs to the textbook box `zeroOneBox n`. -/
recall zeroOneBox_zero_mem (n : ℕ) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ zeroOneBox n

/-! ### Definition_1_3_2 (from Chap01) -/
noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Coord" => Fin n → ℝ
local notation "coordEquiv" => EuclideanSpace.equiv (Fin n) ℝ

/- Definition 1.3.2 is the source-facing owner for the textbook `ℓ∞` geometry on `ℝⁿ`.

Layer targeted by this refinement:
* source-facing owner `EuclideanSpace.linftyNorm n : EuclideanSpace ℝ (Fin n) → ℝ`
* core/canonical owner `EuclideanSpace.linftySeminorm n : Seminorm ℝ E`

Primary domain:
* finite-dimensional normed linear algebra on coordinate spaces

Sampled owner-style declarations:
* `normSeminorm ℝ (Fin n → ℝ)` for the canonical seminorm owner attached to the sup norm on
  coordinates
* `Pi.norm_def` for the canonical sup-norm formula on `Fin n → ℝ`
* `EuclideanSpace.equiv (Fin n) ℝ` for the coordinate view of `EuclideanSpace ℝ (Fin n)`
* `Seminorm.closedBall` together with `Seminorm.mem_closedBall_zero` for the canonical
  origin-centered ball API attached to a seminorm

Owner abstraction:
* source-facing owner: `EuclideanSpace.linftyNorm n : E → ℝ`
* core/canonical owner: `EuclideanSpace.linftySeminorm n : Seminorm ℝ E`
* lower-level canonical pullback: `normSeminorm ℝ Coord`

Source/core/bridge triage:
* source-facing: the textbook `ℓ∞` norm on `ℝⁿ`, exposed as `EuclideanSpace.linftyNorm`
* core/canonical: the seminorm owner `EuclideanSpace.linftySeminorm`
* bridge/view: the coordinate transport `x ↦ coordEquiv x` from `E` to `Coord`, the notation
  `‖x‖∞`, and the source-facing origin-centered ball `EuclideanSpace.linftyClosedBall r`

Primitive data:
* a vector `x : E`

Derived API:
* the evaluation notation `‖x‖∞ = EuclideanSpace.linftyNorm n x`
* the bridge `EuclideanSpace.linftyNorm n x = EuclideanSpace.linftySeminorm n x`
* the coordinate-owner bridge `‖x‖∞ = ‖coordEquiv x‖`
* the source-facing ball bridge
  `EuclideanSpace.linftyClosedBall r = (EuclideanSpace.linftySeminorm n).closedBall 0 r`
* the equivalent `WithLp ⊤` bridge `‖x‖∞ = ‖WithLp.toLp ⊤ (fun i ↦ x i)‖`
* the coordinate sup formula `‖x‖∞ = ↑(Finset.univ.sup fun i ↦ ‖x i‖₊)` from `Pi.norm_def`

This file keeps the source-facing textbook owner `EuclideanSpace.linftyNorm`, realized through the
canonical seminorm owner `EuclideanSpace.linftySeminorm`, so the chapter recall layer can use the
norm surface while downstream ball constructions still reuse `Seminorm.closedBall`. -/

namespace EuclideanSpace

private abbrev coordinateLinftyEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv

/-- Definition 1.3.2: the canonical coordinate `ℓ∞` seminorm on `ℝⁿ`, obtained by pulling back
the ordinary sup norm on `Fin n → ℝ` along the Euclidean coordinate linear equivalence. The
textbook `ℓ∞` norm is the derived source-facing owner `EuclideanSpace.linftyNorm`. -/
abbrev linftySeminorm (n : ℕ) : Seminorm ℝ (EuclideanSpace ℝ (Fin n)) :=
  Seminorm.comp (normSeminorm ℝ (Fin n → ℝ)) (coordinateLinftyEquiv n).toLinearMap

/-- Definition 1.3.2: the textbook `ℓ∞` norm on `ℝⁿ`. Its canonical implementation is the
evaluation of `EuclideanSpace.linftySeminorm`. -/
abbrev linftyNorm (n : ℕ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  linftySeminorm n

/-- The closed `ℓ∞`-ball of radius `r` centered at the origin in `ℝⁿ`. -/
abbrev linftyClosedBall {n : ℕ} (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  (linftySeminorm n).closedBall 0 r

end EuclideanSpace

notation "‖" x "‖∞" => EuclideanSpace.linftyNorm _ x

@[simp] theorem linftyNorm_eq_linftySeminorm (x : E) :
    EuclideanSpace.linftyNorm n x = EuclideanSpace.linftySeminorm n x :=
  rfl

/-- Membership in the source-facing closed `ℓ∞`-ball is exactly the `ℓ∞`-norm bound. -/
@[simp] theorem mem_linftyClosedBall_iff {r : ℝ} {x : E} :
    x ∈ EuclideanSpace.linftyClosedBall r ↔ ‖x‖∞ ≤ r := by
    change x ∈ (EuclideanSpace.linftySeminorm n).closedBall 0 r ↔
      EuclideanSpace.linftyNorm n x ≤ r
    exact (EuclideanSpace.linftySeminorm n).mem_closedBall_zero

/-- The `ℓ∞` norm on `EuclideanSpace ℝ (Fin n)` is the canonical sup norm on the coordinate owner
`Fin n → ℝ`. -/
@[simp] theorem linftyNorm_eq_coordNorm (x : E) :
    ‖x‖∞ = ‖coordEquiv x‖ :=
  by
    change ‖(EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv x‖ = ‖coordEquiv x‖
    rfl

/-- The source-facing `ℓ∞` norm agrees with the equivalent `WithLp ⊤` coordinate presentation. -/
@[simp] theorem linftyNorm_eq_toLp (x : E) :
    ‖x‖∞ = ‖WithLp.toLp ⊤ (fun i ↦ x i)‖ := by
  rw [linftyNorm_eq_coordNorm]
  change ‖coordEquiv x‖ = ‖WithLp.toLp ⊤ (coordEquiv x)‖
  rw [PiLp.norm_toLp]

/-- The source-facing `ℓ∞` norm on `EuclideanSpace ℝ (Fin n)` is the coordinatewise sup norm. -/
theorem linftyNorm_eq_sup (x : E) :
    ‖x‖∞ = ↑(Finset.univ.sup fun i ↦ ‖x i‖₊) := by
  rw [linftyNorm_eq_coordNorm]
  simpa using (Pi.norm_def (coordEquiv x))

/-! ### Definition_1_3_2 (from Items/Chap01) -/
/- Definition 1.3.2 lies in the finite-dimensional `ℓ∞`-geometry domain on `ℝⁿ`.

Relevant owner-style declarations sampled before refining:
* `Pi.norm_def`, the canonical sup-norm formula on `Fin n → ℝ`;
* `EuclideanSpace.equiv (Fin n) ℝ`, the canonical coordinate identification of `ℝⁿ`;
* `EuclideanSpace.linftyNorm` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_2.lean`, the chapter owner for
  the textbook `ℓ∞` norm on `EuclideanSpace ℝ (Fin n)`;
* `linftyNorm_eq_sup` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_2.lean`, the source-facing coordinate
  supremum formula for that owner.

Best owner abstraction:
* the chapter owner `EuclideanSpace.linftyNorm`

Primitive data:
* a vector `x : EuclideanSpace ℝ (Fin n)`

Derived API:
* the textbook notation `‖x‖∞`
* the coordinate bridge `linftyNorm_eq_coordNorm`
* the coordinate supremum formula `linftyNorm_eq_sup`

Source/core/bridge triage:
* source-facing: the textbook `ℓ∞` norm on `ℝⁿ`
* core/canonical: the ordinary norm on `Fin n → ℝ`
* bridge/view: transport along `EuclideanSpace.equiv (Fin n) ℝ`

This item is therefore recall-first: the chapter file already owns the `ℓ∞` norm and its
coordinate formula, so the item file reuses that owner directly instead of keeping a parallel local
copy. -/

/- Definition 1.3.2: the textbook `ℓ∞` norm on `ℝⁿ`. -/
recall EuclideanSpace.linftyNorm

/- The textbook `ℓ∞` norm is the maximum absolute value of the coordinates. -/
recall linftyNorm_eq_sup {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖∞ = ↑(Finset.univ.sup fun i ↦ ‖x i‖₊)

/-! ### Definition_1_3_3 (from Chap01) -/
universe u v

/- Definition 1.3.3 lies in the basic domain of box-constrained minimization problems.

Sampled owner-style declarations in the surrounding project:
* `FunctionalConstraintsMinimizationProblem` and `GeneralMinimizationProblem` in
  `Chap01/Definition_1_1_3`, the earlier Chapter 1 ambient owner and its Euclidean specialization;
* `SetConstrainedMinimizationProblem.unconstrained`, the owner-level bridge that packages an
  unconstrained objective on an ambient type as the same minimization-problem owner;
* `SmoothMinimaxProblem.toSetConstrainedMinimizationProblem` in `Chap02/Definition_2_38`, which
  uses the same owner object as the ambient constrained problem attached to a richer source-facing
  structure;
* `LinearEqualityConstrainedConvexProblem` in `Chap03/Definition_3_27`, which extends the same
  owner object and keeps equality-constraint data as extra source-facing structure rather than
  replacing the owner.

Best owner abstraction:
* `SetConstrainedMinimizationProblem X`, whose primitive data are exactly a feasible set and a
  real-valued objective on the ambient space `X`;
* the primary earlier-project bridge is the generic zero-constraint owner
  `FunctionalConstraintsMinimizationProblem X 0`;
* `GeneralMinimizationProblem n 0` is only the `ℝⁿ` specialization of that generic bridge.

Primitive data:
* `feasibleSet : Set X`
* `objective : X → ℝ`

Derived API:
* the coercion to the objective function;
* the generic constrained argmin set `constrainedArgmin Q f`;
* the source-facing specialization `zeroOneBoxProblem n f` for the textbook box `B_n = [0,1]^n`;
* the generic bridge
  `SetConstrainedMinimizationProblem.toFunctionalConstraintsMinimizationProblem`;
* the Euclidean specialization `SetConstrainedMinimizationProblem.toGeneralMinimizationProblem`.

Source/core/bridge triage:
* source-facing: the textbook box problem `min_{x ∈ B_n} f(x)`;
* core/canonical: `SetConstrainedMinimizationProblem` and `constrainedArgmin`;
* bridge/view:
  `SetConstrainedMinimizationProblem.toFunctionalConstraintsMinimizationProblem`, together with
  its Euclidean specialization `SetConstrainedMinimizationProblem.toGeneralMinimizationProblem`
  and the direct source-facing specialization `zeroOneBoxProblem n f`. -/

/-- A real-valued minimization problem with a specified feasible set in an ambient space `X`. -/
structure SetConstrainedMinimizationProblem (X : Type u) where
  /-- The feasible set on which the minimization problem is posed. -/
  feasibleSet : Set X
  /-- The real-valued objective function to be minimized on the feasible set. -/
  objective : X → ℝ

/-- A set-constrained minimization problem can be used as its objective function. -/
instance : CoeFun (SetConstrainedMinimizationProblem X) (fun _ ↦ X → ℝ) where
  coe problem := problem.objective

/-- The constrained optimal set `argmin_{x ∈ Q} f(x)`. -/
abbrev constrainedArgmin
    {X : Type u} {Y : Type v} [Preorder Y] (Q : Set X) (f : X → Y) : Set X :=
  {x | x ∈ Q ∧ IsMinOn f Q x}

namespace ConstrainedArgmin

scoped notation:max "argmin[" Q "]" => constrainedArgmin Q

end ConstrainedArgmin

open scoped ConstrainedArgmin

/-- Membership in `argmin[Q] f` means belonging to `Q` and minimizing `f` on `Q`. -/
-- Proof sketch: unfold the defining set comprehension for `constrainedArgmin`.
@[simp] theorem mem_constrainedArgmin_iff
    {X : Type u} {Y : Type v} [Preorder Y] {Q : Set X} {f : X → Y} {x : X} :
    x ∈ argmin[Q] f ↔ x ∈ Q ∧ IsMinOn f Q x :=
  Iff.rfl

namespace SetConstrainedMinimizationProblem

variable {X : Type u}
variable {Y : Type v}

/-- Evaluating a set-constrained minimization problem returns its objective value. -/
-- Proof sketch: unfold the `CoeFun` instance for `SetConstrainedMinimizationProblem`.
@[simp] theorem coe_apply (problem : SetConstrainedMinimizationProblem X) (x : X) :
  problem x = problem.objective x :=
  rfl

/-- The unconstrained minimization problem with objective `f` on the whole ambient space. -/
def unconstrained (f : X → ℝ) : SetConstrainedMinimizationProblem X where
  feasibleSet := Set.univ
  objective := f

/-- The feasible set of `unconstrained f` is all of the ambient space. -/
@[simp] theorem unconstrained_feasibleSet (f : X → ℝ) :
    (unconstrained f).feasibleSet = Set.univ :=
  rfl

/-- Evaluating `unconstrained f` recovers the ambient objective `f`. -/
@[simp] theorem unconstrained_apply (f : X → ℝ) (x : X) :
    unconstrained f x = f x :=
  rfl

/-- Pulling back a constrained problem along an equivalence gives the same minimization problem on
the source ambient space. -/
def comap (problem : SetConstrainedMinimizationProblem Y) (e : X ≃ Y) :
    SetConstrainedMinimizationProblem X where
  feasibleSet := e ⁻¹' problem.feasibleSet
  objective := problem ∘ e

/-- The feasible set of `problem.comap e` is the preimage of the original feasible set. -/
-- Proof sketch: unfold `SetConstrainedMinimizationProblem.comap`.
@[simp] theorem comap_feasibleSet
    (problem : SetConstrainedMinimizationProblem Y) (e : X ≃ Y) :
    (problem.comap e).feasibleSet = e ⁻¹' problem.feasibleSet :=
  rfl

/-- Evaluating the pullback problem `problem.comap e` applies `problem` after `e`. -/
-- Proof sketch: unfold `SetConstrainedMinimizationProblem.comap`.
@[simp] theorem comap_apply
    (problem : SetConstrainedMinimizationProblem Y) (e : X ≃ Y) (x : X) :
    problem.comap e x = problem (e x) :=
  rfl

/-- A set-constrained minimization problem canonically yields the earlier ambient owner with zero
scalar constraints by taking its feasible set as the basic feasible set. -/
def toFunctionalConstraintsMinimizationProblem
    (problem : SetConstrainedMinimizationProblem X) :
    FunctionalConstraintsMinimizationProblem X 0 where
  basicFeasibleSet := problem.feasibleSet
  objective := fun x ↦ problem x
  constraints := Fin.elim0
  senses := Fin.elim0

/-- The basic feasible set of the zero-constraint bridge is the original feasible set. -/
-- Proof sketch: unfold `toFunctionalConstraintsMinimizationProblem`.
@[simp] theorem toFunctionalConstraintsMinimizationProblem_basicFeasibleSet
    (problem : SetConstrainedMinimizationProblem X) :
    problem.toFunctionalConstraintsMinimizationProblem.basicFeasibleSet = problem.feasibleSet :=
  rfl

/-- The feasible-set coercion of the zero-constraint bridge recovers the original feasible set. -/
-- Proof sketch: extensionality on ambient points, then unfold the zero-constraint feasibility
-- predicate.
@[simp] theorem toFunctionalConstraintsMinimizationProblem_feasibleSet_coe
    (problem : SetConstrainedMinimizationProblem X) :
    ((problem.toFunctionalConstraintsMinimizationProblem.feasibleSet : Set X) =
      problem.feasibleSet) := by
  -- Expand ambient membership in the subtype feasible set and remove the vacuous constraints.
  ext x
  simp [FunctionalConstraintsMinimizationProblem.feasibleSet,
    FunctionalConstraintsMinimizationProblem.IsFeasible]

/-- The objective of the zero-constraint bridge agrees with the original objective. -/
-- Proof sketch: unfold `toFunctionalConstraintsMinimizationProblem`.
@[simp] theorem toFunctionalConstraintsMinimizationProblem_objective_apply
    (problem : SetConstrainedMinimizationProblem X)
    (x : problem.toFunctionalConstraintsMinimizationProblem.basicFeasibleSet) :
    problem.toFunctionalConstraintsMinimizationProblem.objective x = problem x :=
  rfl

/-- Every point of the basic feasible set is feasible for the zero-constraint bridge. -/
-- Proof sketch: unfold the feasible-set predicate and use `Fin.elim0`.
@[simp] theorem toFunctionalConstraintsMinimizationProblem_feasibleSet
    (problem : SetConstrainedMinimizationProblem X) :
    problem.toFunctionalConstraintsMinimizationProblem.feasibleSet = Set.univ := by
  -- Expand feasibility inside the subtype and use that `Fin 0` has no points.
  ext x
  simp [FunctionalConstraintsMinimizationProblem.feasibleSet,
    FunctionalConstraintsMinimizationProblem.IsFeasible]

end SetConstrainedMinimizationProblem

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Definition 1.3.3: the textbook box problem `min_{x ∈ B_n} f(x)` with `B_n = [0,1]^n`. -/
abbrev zeroOneBoxProblem (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n)) where
  feasibleSet := zeroOneBox n
  objective := f

/-- The feasible set of `zeroOneBoxProblem n f` is the textbook box `B_n = [0,1]^n`. -/
-- Proof sketch: unfold `zeroOneBoxProblem`.
@[simp] theorem zeroOneBoxProblem_feasibleSet (f : E → ℝ) :
    (zeroOneBoxProblem n f).feasibleSet = zeroOneBox n :=
  rfl

/-- A point is feasible for `zeroOneBoxProblem n f` exactly when it belongs to the textbook box
`B_n = [0,1]^n`. -/
-- Proof sketch: rewrite the feasible set of `zeroOneBoxProblem n f` using
-- `zeroOneBoxProblem_feasibleSet`.
@[simp] theorem zeroOneBoxProblem_mem_feasibleSet_iff (f : E → ℝ) {x : E} :
    x ∈ (zeroOneBoxProblem n f).feasibleSet ↔ x ∈ zeroOneBox n :=
  Iff.rfl

/-- The constrained argmin set of `zeroOneBoxProblem n f` is exactly the constrained argmin of
`f` on the textbook box `B_n = [0,1]^n`. -/
-- Proof sketch: extensionality on points, then rewrite membership with
-- `mem_constrainedArgmin_iff`, `zeroOneBoxProblem_feasibleSet`, and
-- `zeroOneBoxProblem_isMinOn_iff`.
@[simp] theorem zeroOneBoxProblem_argmin (f : E → ℝ) :
    argmin[(zeroOneBoxProblem n f).feasibleSet] (zeroOneBoxProblem n f) =
      argmin[zeroOneBox n] f := by
  -- Compare the two argmin sets pointwise and simplify both memberships definitionally.
  ext x
  simp

/-- Minimizing `zeroOneBoxProblem n f` on its feasible set is exactly minimizing `f` on the
textbook box `B_n = [0,1]^n`. -/
-- Proof sketch: unfold the feasible set and the objective of `zeroOneBoxProblem`.
@[simp] theorem zeroOneBoxProblem_isMinOn_iff (f : E → ℝ) {x : E} :
    IsMinOn (zeroOneBoxProblem n f) (zeroOneBoxProblem n f).feasibleSet x ↔
      IsMinOn f (zeroOneBox n) x :=
  Iff.rfl

/-- The constrained argmin set of `zeroOneBoxProblem n f` is exactly the set of minimizers of
`f` on the textbook box `B_n = [0,1]^n`. -/
-- Proof sketch: rewrite membership with `mem_constrainedArgmin_iff`, then use
-- `zeroOneBoxProblem_feasibleSet` and `zeroOneBoxProblem_isMinOn_iff`.
@[simp] theorem zeroOneBoxProblem_spec (f : E → ℝ) {x : E} :
    x ∈ argmin[(zeroOneBoxProblem n f).feasibleSet] (zeroOneBoxProblem n f) ↔
      x ∈ zeroOneBox n ∧ IsMinOn f (zeroOneBox n) x := by
  -- Unfold argmin membership and identify the feasible set and objective definitionally.
  simp

/-- A point is feasible for `zeroOneBoxProblem n f` exactly when each coordinate lies in
`[0,1]`. -/
-- Proof sketch: combine `zeroOneBoxProblem_mem_feasibleSet_iff` with `mem_zeroOneBox_iff`.
@[simp] theorem mem_zeroOneBoxProblem_feasibleSet_iff (f : E → ℝ) {x : E} :
    x ∈ (zeroOneBoxProblem n f).feasibleSet ↔
      ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1 := by
  -- Reduce feasibility to box membership and then to the coordinatewise interval condition.
  simp

namespace SetConstrainedMinimizationProblem

variable {n : ℕ}

/-- The Euclidean specialization of the generic zero-constraint bridge. -/
abbrev toGeneralMinimizationProblem
    (problem : SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n))) :
    GeneralMinimizationProblem n 0 :=
  problem.toFunctionalConstraintsMinimizationProblem

end SetConstrainedMinimizationProblem

/-! ### Definition_1_3_3 (from Items/Chap01) -/
open scoped ConstrainedArgmin

/- Definition 1.3.3 lies in the finite-dimensional box-constrained minimization domain.

Relevant owner-style declarations sampled before refining:
* `SetConstrainedMinimizationProblem` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_3.lean`, the chapter's
  canonical owner of a feasible set together with a real-valued objective;
* `constrainedArgmin` / `argmin[Q]`, the chapter owner of constrained minimizer sets for a fixed
  feasible set `Q`;
* `zeroOneBox` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_1.lean`, the chapter owner of the textbook box
  `B_n = [0,1]^n`;
* `zeroOneBoxProblem` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_3.lean`, the source-facing box-problem
  specialization of the ambient owner `SetConstrainedMinimizationProblem`.

Best owner abstraction:
* source-facing owner: `zeroOneBoxProblem n f`;
* core/canonical owner: `SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n))`.

Primitive data:
* the objective `f : EuclideanSpace ℝ (Fin n) → ℝ`.

Derived API:
* the feasible-set identification `(zeroOneBoxProblem n f).feasibleSet = zeroOneBox n`;
* the constrained argmin rewrite
  `argmin[(zeroOneBoxProblem n f).feasibleSet] (zeroOneBoxProblem n f) = argmin[zeroOneBox n] f`.

Source/core/bridge triage:
* source-facing: the textbook box problem `min_{x ∈ B_n} f(x)`;
* core/canonical: `SetConstrainedMinimizationProblem` and `argmin[Q]`;
* bridge/view: `zeroOneBoxProblem_feasibleSet` and `zeroOneBoxProblem_argmin`.

The exact source-facing owner already exists in the chapter file, so this item is refined to a
recall surface instead of reintroducing a parallel local box-problem definition. -/

/- Definition 1.3.3: the textbook box-constrained problem `min_{x ∈ B_n} f(x)` is the chapter
owner `zeroOneBoxProblem n f`. -/
recall zeroOneBoxProblem (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n))

/- The feasible set of `zeroOneBoxProblem n f` is exactly the textbook box `B_n = [0,1]^n`. -/
recall zeroOneBoxProblem_feasibleSet
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (zeroOneBoxProblem n f).feasibleSet = zeroOneBox n

/- The constrained argmin set of `zeroOneBoxProblem n f` is exactly the argmin set of `f` on the
textbook box `B_n`. -/
recall zeroOneBoxProblem_argmin
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    argmin[(zeroOneBoxProblem n f).feasibleSet] (zeroOneBoxProblem n f) =
      argmin[zeroOneBox n] f

/-! ### Definition_1_3_4 (from Chap01) -/
universe u v

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Coord" => Fin n → ℝ
local notation "coordEquiv" => EuclideanSpace.equiv (Fin n) ℝ
local notation "coordBox" => (Set.Icc (0 : Coord) 1)

/- Definition 1.3.4 is a source-facing recall of the chapter's canonical box-Lipschitz owner API.

Layer targeted by this refinement:
* source-facing owner of the textbook class `𝒫∞[n, L]`
* bridge/view to the core/canonical owner predicate already used downstream in Chapter 1

Primary domain:
* Lipschitz continuity on finite-dimensional coordinate cubes

Sampled owner-style declarations:
* `LipschitzOnWith` in mathlib, the owner predicate for a Lipschitz bound on a set
* `lipschitzOnWith_iff_dist_le_mul` in mathlib, the canonical pointwise inequality view
* `EuclideanSpace.linftyNorm` in `Definition_1_3_2.lean`, the source-facing `ℓ∞` norm on
  `EuclideanSpace ℝ (Fin n)`
* `EuclideanSpace.equiv (Fin n) ℝ`, the coordinate transport from `EuclideanSpace ℝ (Fin n)` to
  `Fin n → ℝ`
* `zeroOneBox` and `mem_zeroOneBox_iff` in `Definition_1_3_1.lean`, the source-facing box and
  its coordinate-membership bridge

Source/core/bridge triage:
* source-facing: the textbook class `𝒫∞[n, L]` of objectives that are `L`-Lipschitz on
  `B_n = [0,1]^n` in the `ℓ∞` geometry
* core/canonical: `LipschitzOnWith L g Q`
* bridge/view: transport of `f` and `B_n` along `coordEquiv`, giving the coordinate owner set
  `coordBox = Set.Icc (0 : Coord) 1`

Owner abstraction:
* `linftyLipschitzClass n L`
* notation surface `𝒫∞[n, L]`
* canonical bridge
  `f ∈ 𝒫∞[n, L] ↔ LipschitzOnWith L (f ∘ coordEquiv.symm) coordBox`

Primitive data:
* a Lipschitz constant `L`
* an objective `f : E → ℝ`

Derived API:
* the definitional textbook `ℓ∞` inequality
  `|f x - f y| ≤ (L : ℝ) * ‖x - y‖∞`
  for `x, y ∈ zeroOneBox n`
* the bridge to the canonical coordinate predicate `LipschitzOnWith`
* the source-facing box membership criterion from `mem_zeroOneBox_iff`

This file keeps `LipschitzOnWith` only as a bridge to the coordinate owner predicate. The public
Chapter 1 surface is the source-facing class `𝒫∞[n, L]` on objectives `E → ℝ`, so downstream
files do not recreate `coordEquiv` and `coordBox` just to state admissibility. -/

/-- Definition 1.3.4: the textbook class `𝒫∞[n, L]` of objectives on `B_n = [0,1]^n` that are
`L`-Lipschitz in the `ℓ∞` geometry. Its primitive owner is the canonical coordinate-cube
predicate `LipschitzOnWith`. -/
def linftyLipschitzClass (n : ℕ) (L : NNReal) :
    Set (EuclideanSpace ℝ (Fin n) → ℝ) :=
  {f | LipschitzOnWith L (f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm)
      (Set.Icc (0 : Fin n → ℝ) 1)}

notation "𝒫∞[" n ", " L "]" => linftyLipschitzClass n L

theorem mem_linftyLipschitzClass_iff_lipschitzOnWith {L : NNReal} {f : E → ℝ} :
    f ∈ 𝒫∞[n, L] ↔ LipschitzOnWith L (f ∘ (coordEquiv).symm) coordBox :=
  by
    change
      LipschitzOnWith L (f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm)
          (Set.Icc (0 : Fin n → ℝ) 1) ↔
        LipschitzOnWith L (f ∘ (coordEquiv).symm) coordBox
    rfl

private theorem coordEquiv_mem_coordBox_iff {x : E} :
    coordEquiv x ∈ coordBox ↔ x ∈ zeroOneBox n := by
  constructor
  · intro hx i
    exact ⟨hx.1 i, hx.2 i⟩
  · intro hx
    exact ⟨fun i ↦ (hx i).1, fun i ↦ (hx i).2⟩

/-- Membership in `𝒫∞[n, L]` is exactly the defining textbook `ℓ∞`-Lipschitz estimate on
`B_n = [0,1]^n`. -/
@[simp] theorem mem_linftyLipschitzClass_iff {L : NNReal} {f : E → ℝ} :
    f ∈ 𝒫∞[n, L] ↔
      ∀ x ∈ zeroOneBox n, ∀ y ∈ zeroOneBox n, |f x - f y| ≤ (L : ℝ) * ‖x - y‖∞ := by
  rw [mem_linftyLipschitzClass_iff_lipschitzOnWith, lipschitzOnWith_iff_dist_le_mul]
  constructor
  · intro hf x hx y hy
    have hx' : coordEquiv x ∈ coordBox := by
      exact coordEquiv_mem_coordBox_iff.mpr hx
    have hy' : coordEquiv y ∈ coordBox := by
      exact coordEquiv_mem_coordBox_iff.mpr hy
    simpa [Function.comp, Real.dist_eq, linftyNorm_eq_coordNorm] using
      hf (coordEquiv x) hx' (coordEquiv y) hy'
  · intro hf x hx y hy
    let x' : E := (coordEquiv).symm x
    let y' : E := (coordEquiv).symm y
    have hx' : x' ∈ zeroOneBox n := by
      exact coordEquiv_mem_coordBox_iff.mp <| by
        simpa [x'] using hx
    have hy' : y' ∈ zeroOneBox n := by
      exact coordEquiv_mem_coordBox_iff.mp <| by
        simpa [y'] using hy
    simpa [Function.comp, Real.dist_eq, x', y', linftyNorm_eq_coordNorm] using hf x' hx' y' hy'

/-- The canonical owner predicate on the coordinate cube gives the textbook `ℓ∞`-Lipschitz
estimate on `B_n = [0,1]^n`. -/
theorem abs_sub_le_mul_linftyNorm
    {L : NNReal} {f : E → ℝ} (hf : f ∈ 𝒫∞[n, L])
    {x y : E} (hx : x ∈ zeroOneBox n) (hy : y ∈ zeroOneBox n) :
    |f x - f y| ≤ (L : ℝ) * ‖x - y‖∞ := by
  exact mem_linftyLipschitzClass_iff.mp hf x hx y hy

/-! ### Definition_1_3_4 (from Items/Chap01) -/
section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Coord" => Fin n → ℝ
local notation "coordEquiv" => EuclideanSpace.equiv (Fin n) ℝ
local notation "coordBox" => Set.Icc (0 : Coord) 1

/- Definition 1.3.4 lies in the finite-dimensional box-Lipschitz domain.

Relevant owner-style declarations sampled before refining:
* `LipschitzOnWith` in mathlib, the canonical owner of set-restricted Lipschitz continuity;
* `linftyLipschitzClass` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_4.lean`, the chapter owner of the
  textbook class `𝒫∞[n, L]`;
* `mem_linftyLipschitzClass_iff_lipschitzOnWith` in the same file, the canonical bridge from the
  source-facing `ℓ∞` statement on `B_n` to `LipschitzOnWith`;
* `zeroOneBox` and `EuclideanSpace.linftyNorm` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_1.lean` and
  `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_2.lean`, the upstream chapter owners for the box and `ℓ∞` norm.

Best owner abstraction:
* source-facing owner: `linftyLipschitzClass n L`, with notation `𝒫∞[n, L]`;
* core/canonical owner: `LipschitzOnWith L (f ∘ coordEquiv.symm) coordBox`.

Primitive data:
* the Lipschitz constant `L`;
* the objective `f : EuclideanSpace ℝ (Fin n) → ℝ`.

Derived API:
* the pointwise textbook estimate on `zeroOneBox n`;
* the canonical bridge to `LipschitzOnWith`;
* the pointwise consequence `abs_sub_le_mul_linftyNorm`.

Source/core/bridge triage:
* source-facing: `𝒫∞[n, L]`;
* core/canonical: `LipschitzOnWith`;
* bridge/view: `mem_linftyLipschitzClass_iff_lipschitzOnWith`.

This item therefore reuses the exact chapter owner directly instead of keeping a parallel local
copy of the same box-Lipschitz definition and its companion API. -/

/- Definition 1.3.4: the textbook class `𝒫∞[n, L]` is the chapter owner
`linftyLipschitzClass n L`. -/
recall linftyLipschitzClass (n : ℕ) (L : NNReal) :
    Set (EuclideanSpace ℝ (Fin n) → ℝ)

/- Membership in `𝒫∞[n, L]` is exactly the textbook `ℓ∞`-Lipschitz estimate on `B_n`. -/
recall mem_linftyLipschitzClass_iff {L : NNReal} {f : E → ℝ} :
    f ∈ 𝒫∞[n, L] ↔
      ∀ x ∈ zeroOneBox n, ∀ y ∈ zeroOneBox n, |f x - f y| ≤ (L : ℝ) * ‖x - y‖∞

/- Membership in `𝒫∞[n, L]` is equivalent to the canonical coordinate-cube owner
`LipschitzOnWith`. -/
recall mem_linftyLipschitzClass_iff_lipschitzOnWith {L : NNReal} {f : E → ℝ} :
    f ∈ 𝒫∞[n, L] ↔ LipschitzOnWith L (f ∘ (coordEquiv).symm) coordBox

/- Any objective in `𝒫∞[n, L]` satisfies the defining oscillation bound at box points. -/
recall abs_sub_le_mul_linftyNorm
    {L : NNReal} {f : E → ℝ} (hf : f ∈ 𝒫∞[n, L])
    {x y : E} (hx : x ∈ zeroOneBox n) (hy : y ∈ zeroOneBox n) :
    |f x - f y| ≤ (L : ℝ) * ‖x - y‖∞

end

/-! ### Theorem_1_3_6 (from Chap01) -/
noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

open SetConstrainedMinimizationProblem

/- The only source-facing primitive data in this item are the midpoint grid points, expressed
pointwise on `EuclideanSpace ℝ (Fin n)`. The midpoint grid itself is the derived range of those
points. The surrounding optimization notions are reused from their chapter owners:
`zeroOneBox`, `𝒫∞[n, L]`, and `SetConstrainedMinimizationProblem.IsApproximateMinimizer`. The
auxiliary theorems below are bridge lemmas from `uniformGridPoint` and `uniformGrid` to those
owner abstractions. -/

/-- The midpoint grid point of mesh `1 / p` indexed by `α ∈ {0, ..., p - 1}^n`. -/
def uniformGridPoint (n : ℕ) (p : ℕ+) (α : Fin n → Fin p) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ (((α i : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ))

/-- The uniform midpoint grid of mesh `1 / p` inside `[0,1]^n`. -/
def uniformGrid (n : ℕ) (p : ℕ+) : Set (EuclideanSpace ℝ (Fin n)) :=
  Set.range (uniformGridPoint n p)

@[simp] theorem uniformGridPoint_apply
    (n : ℕ) (p : ℕ+) (α : Fin n → Fin p) (i : Fin n) :
    uniformGridPoint n p α i = (((α i : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ) :=
  by simp [uniformGridPoint]

/-- Each midpoint grid point lies in the cube `[0,1]^n`. -/
theorem uniformGridPoint_mem_zeroOneBox (p : ℕ+) (α : Fin n → Fin p) :
    uniformGridPoint n p α ∈ zeroOneBox n := by
  rw [mem_zeroOneBox_iff]
  intro i
  refine ⟨by simpa [uniformGridPoint] using
      (show 0 ≤ (((α i : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ) by positivity), ?_⟩
  have hp : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.pos
  have hα : ((α i : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (α i).is_lt
  rw [uniformGridPoint_apply n, div_le_iff₀ hp]
  nlinarith

/-- The midpoint grid is contained in the cube `[0,1]^n`. -/
theorem uniformGrid_subset_zeroOneBox (p : ℕ+) :
    uniformGrid n p ⊆ zeroOneBox n := by
  rintro _ ⟨α, rfl⟩
  exact uniformGridPoint_mem_zeroOneBox p α

/-- Helper for Theorem 1.3.6: every scalar coordinate in `[0,1]` is within `1 / (2p)` of some
midpoint of the uniform partition of `[0,1]` into `p` subintervals. -/
theorem exists_midpoint_coordinate_close (p : ℕ+) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : Fin p, |t - ((((i : Fin p) : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ)| ≤
      1 / (2 * (p : ℝ)) := by
  rcases ht with ⟨ht0, ht1⟩
  have hp : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.pos
  by_cases htop : t = 1
  · -- The endpoint `t = 1` is covered by the last midpoint.
    have hpred_lt : ((p : ℕ) - 1) < p := by
      exact Nat.sub_lt (Nat.succ_le_of_lt p.pos) (by decide)
    refine ⟨⟨((p : ℕ) - 1), hpred_lt⟩, ?_⟩
    have hpred : (((p : ℕ) - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
      norm_num [Nat.succ_pred_eq_of_pos p.pos]
    rw [htop, abs_le]
    constructor
    · field_simp [hp.ne']
      nlinarith [hpred]
    · field_simp [hp.ne']
      nlinarith [hpred]
  · -- Away from the endpoint, the floor of `p * t` selects the containing subinterval.
    let m : ℕ := Nat.floor ((p : ℝ) * t)
    have hscaled_nonneg : 0 ≤ (p : ℝ) * t := by
      positivity
    have hm_lt_p : m < p := by
      have ht_lt_one : t < 1 := lt_of_le_of_ne ht1 htop
      have hscaled_lt : (p : ℝ) * t < p := by
        nlinarith
      exact (Nat.floor_lt hscaled_nonneg).2 hscaled_lt
    refine ⟨⟨m, hm_lt_p⟩, ?_⟩
    have hm_le : (m : ℝ) ≤ (p : ℝ) * t := by
      exact Nat.floor_le hscaled_nonneg
    have hm_succ : (p : ℝ) * t < (m : ℝ) + 1 := by
      simpa [m] using (Nat.lt_floor_add_one ((p : ℝ) * t))
    have hlower :
        ((((m : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ)) - (1 / (2 * (p : ℝ))) ≤ t := by
      field_simp [hp.ne']
      nlinarith
    have hupper :
        t ≤ ((((m : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ)) + (1 / (2 * (p : ℝ))) := by
      field_simp [hp.ne']
      nlinarith [le_of_lt hm_succ]
    rw [abs_le]
    constructor <;> nlinarith

/-- Helper for Theorem 1.3.6: coordinatewise midpoint bounds imply the corresponding `ℓ∞` bound
for the whole grid point. -/
theorem linftyNorm_sub_uniformGridPoint_le_of_forall_coord (p : ℕ+) {x : E}
    {α : Fin n → Fin p} {r : ℝ} (hr : 0 ≤ r)
    (hcoord : ∀ i, |x i - uniformGridPoint n p α i| ≤ r) :
    ‖x - uniformGridPoint n p α‖∞ ≤ r := by
  -- Rewrite the `ℓ∞` norm as the coordinate sup norm and apply the coordinatewise bound directly.
  rw [linftyNorm_eq_coordNorm]
  simpa [Real.norm_eq_abs] using
    (pi_norm_le_iff_of_nonneg hr).2 hcoord

/-- Every point of `[0,1]^n` is within `ℓ∞`-distance `1 / (2p)` of some midpoint grid point. -/
-- Proof sketch: choose in each coordinate the midpoint of the unique subinterval of the uniform
-- partition of `[0,1]` that contains that coordinate. The coordinatewise midpoint error is at
-- most `1 / (2p)`, and the `ℓ∞`-norm is the maximum of those coordinate errors.
theorem exists_uniformGrid_linfty_close (p : ℕ+) {x : E} (hx : x ∈ zeroOneBox n) :
    ∃ y ∈ uniformGrid n p, ‖x - y‖∞ ≤ 1 / (2 * (p : ℝ)) := by
  classical
  rw [mem_zeroOneBox_iff] at hx
  have hmid : ∀ i : Fin n,
      ∃ j : Fin p, |x i - ((((j : Fin p) : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ)| ≤
        1 / (2 * (p : ℝ)) :=
    fun i ↦ exists_midpoint_coordinate_close p (hx i)
  let α : Fin n → Fin p := fun i ↦ Classical.choose (hmid i)
  have hα : ∀ i : Fin n, |x i - uniformGridPoint n p α i| ≤ 1 / (2 * (p : ℝ)) := by
    -- The chosen midpoint in each coordinate defines the global grid index `α`.
    intro i
    simpa [α, uniformGridPoint_apply] using Classical.choose_spec (hmid i)
  refine ⟨uniformGridPoint n p α, ⟨α, rfl⟩, ?_⟩
  -- Aggregate the coordinatewise midpoint errors into the global `ℓ∞` bound.
  exact linftyNorm_sub_uniformGridPoint_le_of_forall_coord p (by positivity) hα

/- The theorem layer for item 1.3.6 has two surfaces:
the source-facing value-gap statement against `(zeroOneBoxProblem n f).optimalValue`, and the
derived bridge into the canonical owner predicate
`(zeroOneBoxProblem n f).IsApproximateMinimizer`. -/
-- Proof sketch: let `x ∈ B_n`. Choose a nearby midpoint grid point `y ∈ uniformGrid n p` using
-- `exists_uniformGrid_linfty_close`. Since `xBar` minimizes `f` on the grid and
-- `xBar ∈ uniformGrid n p`,
-- we have `f xBar ≤ f y`. Apply the Lipschitz estimate between `y` and `x`, using
-- `uniformGrid_subset_zeroOneBox` to see that `y ∈ [0,1]^n`, and conclude
-- `f xBar ≤ f x + L / (2p)` for every `x ∈ B_n`. This yields the claimed bound against
-- `(zeroOneBoxProblem n f).optimalValue`.
/-- Theorem 1.3.6: if `f ∈ 𝒫∞[n, L]` and the value `f xBar` is minimal on the midpoint grid of
mesh `1 / p`, then `f xBar` is at most `L / (2p)` above the canonical optimal value of the box
problem `min_{x ∈ B_n} f(x)`. -/
theorem uniformGrid_value_le_optimalValue_add_of_isMinOn
    (f : E → ℝ) (L : NNReal) (p : ℕ+) (xBar : E)
    (hf_lipschitz : f ∈ 𝒫∞[n, L])
    (hxBar_min : IsMinOn f (uniformGrid n p) xBar) :
    (f xBar : EReal) ≤ (zeroOneBoxProblem n f).optimalValue + (L : ℝ) / (2 * (p : ℝ)) := by
  let ε : ℝ := (L : ℝ) / (2 * (p : ℝ))
  have hxBar_le_add {x : E} (hx : x ∈ zeroOneBox n) :
      (f xBar : EReal) ≤ (f x : EReal) + ε := by
    rcases exists_uniformGrid_linfty_close p hx with ⟨y, hy_grid, hxy⟩
    have hxBar_le_y : f xBar ≤ f y := by
      rw [isMinOn_iff] at hxBar_min
      exact hxBar_min y hy_grid
    have hy_box : y ∈ zeroOneBox n :=
      uniformGrid_subset_zeroOneBox p hy_grid
    have hyx_dist :
        (L : ℝ) * ‖y - x‖∞ ≤ ε := by
      have hxy' : ‖y - x‖∞ ≤ 1 / (2 * (p : ℝ)) := by
        simpa [norm_sub_rev] using hxy
      have hL_nonneg : 0 ≤ (L : ℝ) := by
        exact_mod_cast L.2
      calc
        (L : ℝ) * ‖y - x‖∞ ≤ (L : ℝ) * (1 / (2 * (p : ℝ))) := by
          gcongr
        _ = ε := by
          simp [ε, div_eq_mul_inv]
    have hy_dist :
        |f y - f x| ≤ ε := by
      exact (abs_sub_le_mul_linftyNorm hf_lipschitz hy_box hx).trans hyx_dist
    have hy_le_x : f y ≤ f x + ε := by
      have hy_sub_x : f y - f x ≤ ε := (abs_sub_le_iff.mp hy_dist).1
      linarith
    have hxBar_le_x : f xBar ≤ f x + ε :=
      le_trans hxBar_le_y hy_le_x
    exact_mod_cast hxBar_le_x
  by_contra h
  have hgap : (zeroOneBoxProblem n f).optimalValue + ε < (f xBar : EReal) := by
    simpa [ε] using h
  have hopt_lt : (zeroOneBoxProblem n f).optimalValue < (f xBar : EReal) - ε := by
    exact (EReal.lt_sub_iff_add_lt (.inl (EReal.coe_ne_bot ε)) (.inl (EReal.coe_ne_top ε))).2 hgap
  rw [optimalValue_eq_sInf_image] at hopt_lt
  have himage_nonempty :
      ((fun x ↦ (zeroOneBoxProblem n f x : EReal)) ''
        (zeroOneBoxProblem n f).feasibleSet).Nonempty := by
    refine ⟨(f 0 : EReal), ?_⟩
    refine ⟨0, ?_, by simp⟩
    change (0 : E) ∈ zeroOneBox n
    exact zeroOneBox_zero_mem n
  rcases exists_lt_of_csInf_lt himage_nonempty hopt_lt with ⟨v, hv, hvlt⟩
  rcases hv with ⟨x, hx, rfl⟩
  have hxBar_le : (f xBar : EReal) ≤ (f x : EReal) + ε := by
    simpa [ε] using hxBar_le_add (by simpa using hx)
  have hlt : (f x : EReal) + ε < (f xBar : EReal) := by
    exact EReal.add_lt_of_lt_sub (by simpa [ε] using hvlt)
  exact (not_lt_of_ge hxBar_le hlt)

/-- Theorem 1.3.6 in the canonical approximate-minimizer owner language. -/
theorem uniformGrid_isApproximateMinimizer_of_isMinOn
    (f : E → ℝ) (L : NNReal) (p : ℕ+) (xBar : E)
    (hxBar : xBar ∈ uniformGrid n p)
    (hf_lipschitz : f ∈ 𝒫∞[n, L])
    (hxBar_min : IsMinOn f (uniformGrid n p) xBar) :
    (zeroOneBoxProblem n f).IsApproximateMinimizer ((L : ℝ) / (2 * (p : ℝ))) xBar := by
  rw [isApproximateMinimizer_iff]
  refine ⟨?_, uniformGrid_value_le_optimalValue_add_of_isMinOn f L p xBar hf_lipschitz hxBar_min⟩
  simpa using uniformGrid_subset_zeroOneBox p hxBar

/-! ### Theorem_1_3_6 (from Items/Chap01) -/
noncomputable section

open SetConstrainedMinimizationProblem

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 1.3.6 lies in the finite-dimensional box-constrained midpoint-grid optimization
domain.

Relevant owner-style declarations sampled before refining:
* `uniformGridPoint` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Theorem_1_3_6.lean`, the chapter owner of the midpoint
  grid points;
* `uniformGrid` in the same file, the chapter owner of the midpoint grid itself;
* `isMinOn_iff` in mathlib, the canonical owner-style elimination rule for the minimizer
  hypothesis `IsMinOn f (uniformGrid n p) xBar`;
* `SetConstrainedMinimizationProblem.optimalValue` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_7.lean`,
  the canonical owner of the constrained optimal value.

Best owner abstraction:
* source-facing: the midpoint grid `uniformGrid n p` and the textbook value-gap conclusion;
* core/canonical: `IsMinOn f (uniformGrid n p) xBar` together with
  `(zeroOneBoxProblem n f).optimalValue`;
* bridge/view: the explicit value inequality derived directly from the grid minimizer hypothesis
  and the canonical optimal-value owner.

Primitive data:
* the dimension `n`;
* the mesh parameter `p : ℕ+`;
* the midpoint-grid minimizer hypothesis `IsMinOn f (uniformGrid n p) xBar`.

Derived API:
* the coordinate formula for midpoint-grid points;
* feasibility of midpoint-grid points and grid approximation inside `zeroOneBox n`;
* the explicit objective-value inequality against the canonical constrained optimal value.

This item therefore reuses the exact chapter owners directly and keeps only the source-facing
value-gap theorem as a thin bridge from the canonical optimal-value owner, rather than
redefining the box, `ℓ∞` norm, Lipschitz class, grid, or optimal-value API locally. -/

/- The midpoint grid point of mesh `1 / p` is the chapter owner `uniformGridPoint n p α`. -/
recall uniformGridPoint (n : ℕ) (p : ℕ+) (α : Fin n → Fin p) :
    EuclideanSpace ℝ (Fin n)

/- The midpoint grid of mesh `1 / p` is the chapter owner `uniformGrid n p`. -/
recall uniformGrid (n : ℕ) (p : ℕ+) : Set (EuclideanSpace ℝ (Fin n))

/- The coordinates of a midpoint grid point are given by the midpoint formula. -/
recall uniformGridPoint_apply
    (n : ℕ) (p : ℕ+) (α : Fin n → Fin p) (i : Fin n) :
    uniformGridPoint n p α i = (((α i : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ)

/- Each midpoint grid point lies in the textbook box `B_n = [0,1]^n`. -/
recall uniformGridPoint_mem_zeroOneBox
    (p : ℕ+) (α : Fin n → Fin p) :
    uniformGridPoint n p α ∈ zeroOneBox n

/- The midpoint grid is contained in the textbook box `B_n = [0,1]^n`. -/
recall uniformGrid_subset_zeroOneBox (p : ℕ+) :
    uniformGrid n p ⊆ zeroOneBox n

/- Every point of `B_n = [0,1]^n` is within `ℓ∞`-distance `1 / (2p)` of some midpoint grid
point. -/
recall exists_uniformGrid_linfty_close
    (p : ℕ+) {x : E} (hx : x ∈ zeroOneBox n) :
    ∃ y ∈ uniformGrid n p, ‖x - y‖∞ ≤ 1 / (2 * (p : ℝ))

/- The canonical chapter theorem expresses Theorem 1.3.6 as approximate optimality for the box
problem owner `zeroOneBoxProblem n f`. -/
recall uniformGrid_isApproximateMinimizer_of_isMinOn
    (f : E → ℝ) (L : NNReal) (p : ℕ+) (xBar : E)
    (hxBar : xBar ∈ uniformGrid n p)
    (hf_lipschitz : f ∈ 𝒫∞[n, L])
    (hxBar_min : IsMinOn f (uniformGrid n p) xBar) :
    (zeroOneBoxProblem n f).IsApproximateMinimizer ((L : ℝ) / (2 * (p : ℝ))) xBar

/-- Theorem 1.3.6: if `f ∈ 𝒫∞[n, L]` and the value `f xBar` is minimal on the midpoint grid of
mesh `1 / p`, then `f xBar` is at most `L / (2p)` above the canonical optimal value of the box
problem `min_{x ∈ B_n} f(x)`. -/
theorem uniformGrid_value_le_optimalValue_add_of_isMinOn
    (f : E → ℝ) (L : NNReal) (p : ℕ+) (xBar : E)
    (hf_lipschitz : f ∈ 𝒫∞[n, L])
    (hxBar_min : IsMinOn f (uniformGrid n p) xBar) :
    (f xBar : EReal) ≤ (zeroOneBoxProblem n f).optimalValue + (L : ℝ) / (2 * (p : ℝ)) := by
  let ε : ℝ := (L : ℝ) / (2 * (p : ℝ))
  have hxBar_le_add {x : E} (hx : x ∈ zeroOneBox n) :
      (f xBar : EReal) ≤ (f x : EReal) + ε := by
    rcases exists_uniformGrid_linfty_close p hx with ⟨y, hy_grid, hxy⟩
    have hxBar_le_y : f xBar ≤ f y := by
      rw [isMinOn_iff] at hxBar_min
      exact hxBar_min y hy_grid
    have hy_box : y ∈ zeroOneBox n :=
      uniformGrid_subset_zeroOneBox p hy_grid
    have hyx_dist :
        (L : ℝ) * ‖y - x‖∞ ≤ ε := by
      have hxy' : ‖y - x‖∞ ≤ 1 / (2 * (p : ℝ)) := by
        simpa [norm_sub_rev] using hxy
      have hL_nonneg : 0 ≤ (L : ℝ) := by
        exact_mod_cast L.2
      calc
        (L : ℝ) * ‖y - x‖∞ ≤ (L : ℝ) * (1 / (2 * (p : ℝ))) := by
          gcongr
        _ = ε := by
          simp [ε, div_eq_mul_inv]
    have hy_dist :
        |f y - f x| ≤ ε := by
      exact (abs_sub_le_mul_linftyNorm hf_lipschitz hy_box hx).trans hyx_dist
    have hy_le_x : f y ≤ f x + ε := by
      have hy_sub_x : f y - f x ≤ ε := (abs_sub_le_iff.mp hy_dist).1
      linarith
    have hxBar_le_x : f xBar ≤ f x + ε :=
      le_trans hxBar_le_y hy_le_x
    exact_mod_cast hxBar_le_x
  by_contra h
  have hgap : (zeroOneBoxProblem n f).optimalValue + ε < (f xBar : EReal) := by
    simpa [ε] using h
  have hopt_lt : (zeroOneBoxProblem n f).optimalValue < (f xBar : EReal) - ε := by
    exact (EReal.lt_sub_iff_add_lt (.inl (EReal.coe_ne_bot ε)) (.inl (EReal.coe_ne_top ε))).2 hgap
  rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image] at hopt_lt
  have himage_nonempty :
      ((fun x ↦ (zeroOneBoxProblem n f x : EReal)) '' (zeroOneBoxProblem n f).feasibleSet).Nonempty := by
    refine ⟨(f 0 : EReal), ?_⟩
    refine ⟨0, ?_, by simp⟩
    change (0 : E) ∈ zeroOneBox n
    exact zeroOneBox_zero_mem n
  rcases exists_lt_of_csInf_lt himage_nonempty hopt_lt with ⟨v, hv, hvlt⟩
  rcases hv with ⟨x, hx, rfl⟩
  have hxBar_le : (f xBar : EReal) ≤ (f x : EReal) + ε := by
    simpa [ε] using hxBar_le_add (by simpa using hx)
  have hlt : (f x : EReal) + ε < (f xBar : EReal) := by
    exact EReal.add_lt_of_lt_sub (by simpa [ε] using hvlt)
  exact (not_lt_of_ge hxBar_le hlt)

/-! ### Definition_1_3_7 (from Chap01) -/
universe u

noncomputable section

namespace SetConstrainedMinimizationProblem

open scoped ConstrainedArgmin

variable {X : Type u}

/- Definition 1.3.7 is expressed through the Chapter 1 owner abstraction
`SetConstrainedMinimizationProblem`. The primitive data remain only the feasible set and
objective; the optimal value and approximate-minimizer predicate are derived notions. -/

/-- The optimal value `f* = inf_{x ∈ Q} f(x)` of a set-constrained minimization problem, viewed
in `EReal` so that unbounded-below feasible objectives are represented faithfully. -/
def optimalValue (problem : SetConstrainedMinimizationProblem X) : EReal :=
  sInf ((fun x ↦ (problem x : EReal)) '' problem.feasibleSet)

/-- Expanding `problem.optimalValue` gives the infimum of the feasible objective values, taken
over the owner feasible set. -/
theorem optimalValue_eq_sInf_image (problem : SetConstrainedMinimizationProblem X) :
    problem.optimalValue =
      sInf ((fun x ↦ (problem x : EReal)) '' problem.feasibleSet) :=
  rfl

/-- The optimal value is bounded above by the objective value at every feasible point. -/
theorem optimalValue_le_of_mem_feasibleSet
    (problem : SetConstrainedMinimizationProblem X) {x : X} (hx : x ∈ problem.feasibleSet) :
    problem.optimalValue ≤ (problem x : EReal) := by
  rw [optimalValue_eq_sInf_image]
  refine csInf_le ?_ ?_
  · exact ⟨⊥, fun _ _ ↦ bot_le⟩
  · exact ⟨x, hx, rfl⟩

/-- If two constrained minimization problems have the same feasible set and the first objective is
pointwise bounded above by the second on that feasible set, then the first owner optimal value is
bounded above by the second. -/
theorem optimalValue_le_optimalValue_of_forall_le
    (problem₁ problem₂ : SetConstrainedMinimizationProblem X)
    (hfeasible : problem₁.feasibleSet = problem₂.feasibleSet)
    (hpointwise : ∀ x ∈ problem₁.feasibleSet, problem₁ x ≤ problem₂ x) :
    problem₁.optimalValue ≤ problem₂.optimalValue := by
  rw [problem₂.optimalValue_eq_sInf_image]
  refine le_sInf ?_
  rintro _ ⟨x, hx₂, rfl⟩
  have hx₁ : x ∈ problem₁.feasibleSet := by
    simpa [hfeasible] using hx₂
  refine (problem₁.optimalValue_le_of_mem_feasibleSet hx₁).trans ?_
  change ((problem₁ x : ℝ) : EReal) ≤ ((problem₂ x : ℝ) : EReal)
  exact_mod_cast hpointwise x hx₁

/-- If two constrained minimization problems have the same feasible set and the first objective is
pointwise at most `Δ` above the second on that feasible set, then the first owner optimal value is
at most `Δ` above the second. -/
theorem optimalValue_sub_le_optimalValue_of_forall_sub_le
    (problem₁ problem₂ : SetConstrainedMinimizationProblem X) {Δ : ℝ}
    (hfeasible : problem₁.feasibleSet = problem₂.feasibleSet)
    (hpointwise : ∀ x ∈ problem₁.feasibleSet, problem₁ x - Δ ≤ problem₂ x) :
    problem₁.optimalValue - Δ ≤ problem₂.optimalValue := by
  rw [problem₂.optimalValue_eq_sInf_image]
  refine le_sInf ?_
  rintro _ ⟨x, hx₂, rfl⟩
  apply EReal.sub_le_of_le_add
  have hx₁ : x ∈ problem₁.feasibleSet := by
    simpa [hfeasible] using hx₂
  refine (problem₁.optimalValue_le_of_mem_feasibleSet hx₁).trans ?_
  have hpointwise' : problem₁ x ≤ problem₂ x + Δ := by
    exact sub_le_iff_le_add.mp (hpointwise x hx₁)
  change ((problem₁ x : ℝ) : EReal) ≤ ((problem₂ x : ℝ) : EReal) + (Δ : EReal)
  exact_mod_cast hpointwise'

/-- If the constrained minimum is attained at a feasible point, then the owner optimal value is
that attained objective value. -/
theorem optimalValue_eq_of_isMinOn
    (problem : SetConstrainedMinimizationProblem X) {x : X} (hx : x ∈ problem.feasibleSet)
    (hmin : IsMinOn problem problem.feasibleSet x) :
    problem.optimalValue = (problem x : EReal) := by
  rw [optimalValue_eq_sInf_image]
  have hminEReal : IsMinOn (fun y ↦ (problem y : EReal)) problem.feasibleSet x := by
    rw [isMinOn_iff] at hmin ⊢
    intro y hy
    exact_mod_cast hmin y hy
  exact (hminEReal.isGLB hx).csInf_eq ⟨_, ⟨x, hx, rfl⟩⟩

/-- Any point in the canonical constrained argmin set realizes the owner optimal value. -/
theorem optimalValue_eq_of_mem_argmin
    (problem : SetConstrainedMinimizationProblem X) {x : X}
    (hx : x ∈ argmin[problem.feasibleSet] problem) :
    problem.optimalValue = (problem x : EReal) := by
  rw [mem_constrainedArgmin_iff] at hx
  exact problem.optimalValue_eq_of_isMinOn hx.1 hx.2

/-- Definition 1.3.7: `xBar` is an `ε`-approximate minimizer in function value for a
set-constrained minimization problem when it is feasible and its objective value is at most `ε`
above the optimal value. -/
def IsApproximateMinimizer (problem : SetConstrainedMinimizationProblem X)
    (ε : ℝ) (xBar : X) : Prop :=
  xBar ∈ problem.feasibleSet ∧ (problem xBar : EReal) ≤ problem.optimalValue + ε

/-- Unfolding `problem.IsApproximateMinimizer ε xBar` gives feasibility together with the
canonical additive bound on the objective value. -/
@[simp] theorem isApproximateMinimizer_iff (problem : SetConstrainedMinimizationProblem X)
    (ε : ℝ) (xBar : X) :
    problem.IsApproximateMinimizer ε xBar ↔
      xBar ∈ problem.feasibleSet ∧ (problem xBar : EReal) ≤ problem.optimalValue + ε :=
  Iff.rfl

end SetConstrainedMinimizationProblem

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type u} {m : ℕ}

/-- A functional-constraint minimization problem canonically yields a set-constrained
minimization problem on its basic feasible set, with feasible points cut out by the owner
constraint family and objective inherited from the owner objective. -/
def toSetConstrainedMinimizationProblem
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    SetConstrainedMinimizationProblem problem.basicFeasibleSet where
  feasibleSet := problem.feasibleSet
  objective := problem

/-- The canonical bridge preserves the owner feasible set. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- The canonical bridge evaluates to the owner objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : FunctionalConstraintsMinimizationProblem X m)
    (x : problem.basicFeasibleSet) :
    problem.toSetConstrainedMinimizationProblem x = problem x :=
  rfl

end FunctionalConstraintsMinimizationProblem

/-! ### Corollary_1_3_8 (from Chap01) -/
noncomputable section

variable (n : ℕ)

open DeterministicValueOracleMethod

/- Corollary 1.3.8 stays in the Chapter 1 value-oracle complexity domain.

Relevant owner-style declarations sampled before refining:
* `uniformGrid_isApproximateMinimizer_of_isMinOn` in `Theorem_1_3_6.lean`, the canonical bridge
  from a midpoint-grid minimizer to approximate optimality on the box problem;
* `uniformGridMethod_output_isMinOn` in `Algorithm_1_3_5.lean`, which supplies the required
  midpoint-grid minimizer after exactly `p^n` oracle calls;
* `solvesLinftyLipschitzProblemClassWithin_of_isApproximateMinimizer_outputAfter` in
  `Theorem_1_3_9.lean`, the owner bridge from a uniform approximate-minimizer guarantee to the
  chapter solve predicate;
* `DeterministicValueOracleMethod.SolvesLinftyLipschitzProblemClassWithin` in
  `Theorem_1_3_9.lean`, the owner oracle-complexity predicate for this chapter.

Source/core/bridge triage:
* source-facing: the textbook uniform-grid method and the bound `(\lfloor L / (2 ε) \rfloor + 1)^n`;
* core/canonical: `DeterministicValueOracleMethod (zeroOneBox n)` and its solve predicate;
* bridge/view: deriving the owner solve predicate for `uniformGridMethod n p` from Theorem 1.3.6
  and Algorithm 1.3.5.

Primitive data:
* the dimension `n` and mesh parameter `p : ℕ+` for `uniformGridMethod n p`.

Derived API:
* the solve guarantee within `p^n` value-oracle calls;
* the corollary obtained by the canonical choice `p = ⌊L / (2 ε)⌋ + 1`. -/

/-- Bridge theorem from Theorem 1.3.6 and Algorithm 1.3.5 to the owner oracle-complexity
predicate. If the midpoint mesh `p` satisfies `L / (2p) < ε`, then the canonical uniform grid
method solves the `L`-Lipschitz box problem class within `p^n` value-oracle calls. -/
theorem uniformGridMethod_solvesLinftyLipschitzProblemClassWithin
    (p : ℕ+) (L : NNReal) {ε : ℝ}
    (hp : (L : ℝ) / (2 * (p : ℝ)) < ε) :
    (uniformGridMethod n p).SolvesLinftyLipschitzProblemClassWithin L ε ((p : ℕ) ^ n) := by
  -- Route the grid-minimizer guarantee through the chapter's owner solve predicate.
  refine
    solvesLinftyLipschitzProblemClassWithin_of_isApproximateMinimizer_outputAfter
      (uniformGridMethod n p) hp ?_
  intro f hf
  -- Theorem 1.3.6 turns the grid minimizer produced by Algorithm 1.3.5 into the required
  -- approximate minimizer on the box problem.
  exact
    uniformGrid_isApproximateMinimizer_of_isMinOn
      f L p
      ((uniformGridMethod n p).outputAfter (f ∘ (↑)) ((p : ℕ) ^ n))
      (uniformGridMethod_output_mem_uniformGrid n p f)
      hf
      (uniformGridMethod_output_isMinOn n p f)

/-- Helper for Corollary 1.3.8: the floor-based mesh choice makes the midpoint discretization
error strictly smaller than `ε`. -/
lemma uniform_grid_floor_mesh_lt_eps
    (L : NNReal) {ε : ℝ} (hε : 0 < ε) :
    let m := Nat.floor ((L : ℝ) / (2 * ε))
    (L : ℝ) / (2 * (((Nat.succPNat m : ℕ) : ℝ))) < ε := by
  -- Write the chosen mesh parameter as `m + 1`, where `m = ⌊L / (2 ε)⌋`.
  dsimp
  set m : ℕ := Nat.floor ((L : ℝ) / (2 * ε))
  have hfloor : (L : ℝ) / (2 * ε) < (m : ℝ) + 1 := by
    simpa [m] using Nat.lt_floor_add_one ((L : ℝ) / (2 * ε))
  have hε2 : 0 < 2 * ε := by
    positivity
  -- Clear the denominator in the floor inequality to obtain the numerator bound needed later.
  have hscaled : (L : ℝ) < ((m : ℝ) + 1) * (2 * ε) := by
    exact (div_lt_iff₀ hε2).1 hfloor
  have hdenom : 0 < (2 : ℝ) * (((m + 1 : ℕ) : ℝ)) := by
    positivity
  have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by
    norm_num [Nat.cast_add]
  -- Re-express the chosen mesh size as a positive denominator and finish by linear arithmetic.
  apply (div_lt_iff₀ hdenom).2
  rw [hcast]
  nlinarith [hscaled]

/-- Corollary 1.3.8: for the uniform grid method on the `L`-Lipschitz box problem class, the
analytical complexity is at most `(\lfloor L / (2 ε) \rfloor + 1)^n`. -/
-- Proof sketch: choose the mesh parameter `p = (⌊L / (2 ε)⌋).succPNat`, so that
-- `(p : ℕ) = ⌊L / (2 ε)⌋ + 1` and `L / (2 p) < ε`, then apply
-- `uniformGridMethod_solvesLinftyLipschitzProblemClassWithin`.
theorem uniformGridMethod_analyticalComplexity_bound
    (L : NNReal) {ε : ℝ} (hε : 0 < ε) :
    (uniformGridMethod n
      (Nat.floor ((L : ℝ) / (2 * ε))).succPNat).SolvesLinftyLipschitzProblemClassWithin
      L ε ((Nat.floor ((L : ℝ) / (2 * ε)) + 1) ^ n) := by
  -- Choose the textbook mesh parameter `p = ⌊L / (2 ε)⌋ + 1` and invoke the owner bridge theorem.
  simpa [Nat.succPNat_coe] using
    uniformGridMethod_solvesLinftyLipschitzProblemClassWithin
      (n := n)
      (p := (Nat.floor ((L : ℝ) / (2 * ε))).succPNat)
      L
      (uniform_grid_floor_mesh_lt_eps L hε)
