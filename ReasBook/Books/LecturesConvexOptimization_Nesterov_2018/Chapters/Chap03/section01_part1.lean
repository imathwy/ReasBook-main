import Mathlib
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_3_1_1 (from Chap03) -/
/- Corollary 3.1.1 is a source-facing recall in the convex-analysis maximum-principle domain.

Primary domain:
- convex functions and the finite convex-hull maximum principle

Sampled owner-style declarations:
- `ConvexOn.map_sum_le`
- `ConvexOn.le_sup_of_mem_convexHull`
- `ConvexOn.inf_le_of_mem_convexHull`
- `convexOn_value_le_max_of_convex_combination`

Best owner abstraction:
- `ConvexOn.le_sup_of_mem_convexHull`

Primitive data:
- a finite vertex set `t : Finset E`
- a convex function `hf : ConvexOn ℝ s f`
- the inclusion `(t : Set E) ⊆ s`
- a point `x` with `x ∈ convexHull ℝ (t : Set E)`

Derived API:
- the canonical bound `f x ≤ t.sup' ... f`

Source/core/bridge triage:
- source-facing: the textbook corollary for finitely many points `x₁, …, xₘ`
- core/canonical: `ConvexOn.le_sup_of_mem_convexHull`
- bridge/view: the earlier chapter theorem
  `convexOn_value_le_max_of_convex_combination`, which packages the convex-combination input in the
  chapter owner `is_convex_combination_of`; the textbook coefficient display is kept only in the
  companion theorem `convexOn_value_le_max_of_convex_combination_of_coefficients`

The coefficient-based chapter statement is bridge API, while this corollary is governed directly by
the convex-hull owner theorem. This file therefore recalls the canonical owner declaration instead
of keeping a specialized local shell. -/

recall ConvexOn.le_sup_of_mem_convexHull

/-! ### Corollary_3_1_1_1 (from Chap03) -/
/-
Corollary 3.1.1.1 lies in the convex-analysis domain of the finite convex-hull maximum principle.

Sampled owner-style declarations:
- `ConvexOn.map_sum_le`
- `ConvexOn.le_sup_of_mem_convexHull`
- `ConvexOn.inf_le_of_mem_convexHull`
- `convexOn_value_le_max_of_convex_combination`

Best owner abstraction:
- `ConvexOn.le_sup_of_mem_convexHull`

Primitive data:
- a finite set `t : Finset E`
- a convex function `hf : ConvexOn ℝ s f`
- the inclusion `(t : Set E) ⊆ s`
- a point `x` with `x ∈ convexHull ℝ (t : Set E)`

Derived API:
- the canonical bound `f x ≤ t.sup' ... f`

Source/core/bridge triage:
- source-facing: the corollary that the value at a convex combination is bounded by the maximum of
  the endpoint values
- core/canonical: `ConvexOn.le_sup_of_mem_convexHull`
- bridge/view: the chapter theorem
  `convexOn_value_le_max_of_convex_combination`, which uses the chapter owner
  `is_convex_combination_of`; the displayed equality `x = ∑ i, α i • points i` is kept only in the
  companion theorem `convexOn_value_le_max_of_convex_combination_of_coefficients`

The coefficient-level theorem is bridge API, not the owner of this item. This file therefore
recalls the canonical convex-hull maximum principle directly; when the source presentation names a
point by an equality `x = ∑ i, α i • points i`, that equality should be used only as a bridge to
`x ∈ convexHull ℝ (Set.range points)` at the call site or in a companion theorem.
-/

recall ConvexOn.le_sup_of_mem_convexHull

/-! ### Corollary_3_1_1_2 (from Chap03) -/
/-
Corollary 3.1.1.2 lies in the convex-analysis domain of the finite convex-hull maximum principle.

Sampled owner-style declarations:
- `ConvexOn.exists_ge_of_mem_convexHull`
- `ConvexOn.le_sup_of_mem_convexHull`
- `ConvexOn.inf_le_of_mem_convexHull`

Best owner abstraction:
- `ConvexOn.exists_ge_of_mem_convexHull`

Primitive data:
- a vertex set `t : Set E`, or equivalently a finite vertex family viewed through `Set.range`
- a set `s` and a convex function `hf : ConvexOn ℝ s f`
- the inclusion `t ⊆ s`
- a point `x ∈ convexHull ℝ t`

Derived API:
- a vertex `y ∈ t` with `f x ≤ f y`

Source/core/bridge triage:
- source-facing: the corollary that the maximum of a convex function on a finite convex hull is
  attained at a vertex
- core/canonical: `ConvexOn.exists_ge_of_mem_convexHull`
- bridge/view: the finite-sup theorem `ConvexOn.le_sup_of_mem_convexHull` and coefficient or
  index-level attainment formulations derived from the owner theorem

The chapter theorem `convexOn_value_le_max_of_convex_combination` is a bridge/view reformulation;
this file keeps only the canonical witness-level convex-hull maximum-principle recall.
-/

recall ConvexOn.exists_ge_of_mem_convexHull

/-! ### Definition_3_1 (from Chap03) -/
universe u

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/-
Definition 3.1 is a source-facing recall in the convex constrained minimization domain.

Primary domain:
- finite-dimensional convex minimization with an extended-real-valued objective and finitely many
  extended-real-valued inequality constraints.

Sampled owner-style declarations:
- `GeneralMinimizationProblem` in `Chap01/Definition_1_1_3`, the earlier project owner for a
  basic feasible set together with finitely many scalar constraints and comparison senses.
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the zero-constraint owner for
  an ambient feasible set and a real-valued objective.
- `GeneralConvexMinimizationProblem` in `Definition_3_1_1_1`, the chapter owner matching the
  exact extended-valued convex data of Definition 3.1.
- `GeneralConvexMinimizationProblem.IsFeasible`, the derived feasibility predicate attached to
  that owner.

Best owner abstraction:
- `GeneralConvexMinimizationProblem X m`, with textbook specialization
  `X = EuclideanSpace ℝ (Fin n)`

Primitive data:
- `feasibleSet : Set X`
- `objective : X → WithTop ℝ`
- `constraints : Fin m → X → WithTop ℝ`
- `feasibleSet_closed`
- `feasibleSet_convex`
- `objective_convex`
- `constraints_convex`

Derived API:
- the coercion to the ambient objective function
- `GeneralConvexMinimizationProblem.IsFeasible`

Source/core/bridge triage:
- source-facing: the textbook general convex minimization problem with convex inequality
  constraints `fᵢ(x) ≤ 0`.
- core/canonical: `GeneralConvexMinimizationProblem X m`.
- bridge/view: the textbook Euclidean specialization
  `X = EuclideanSpace ℝ (Fin n)`, together with the coercion to the ambient objective and the
  feasibility predicate `GeneralConvexMinimizationProblem.IsFeasible`.

This file therefore recalls the canonical owner abstraction directly and keeps no parallel public
wrapper such as `ConvexOptimizationProblem` or a separate feasibility package.
-/

recall GeneralConvexMinimizationProblem
    {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] (m : ℕ) :
    Type u

recall GeneralConvexMinimizationProblem.IsFeasible
    {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] {m : ℕ}
    (problem : GeneralConvexMinimizationProblem X m) (x : X) :
    Prop

/-! ### Definition_3_1_1_1 (from Chap03) -/
universe u

open scoped WithTopConvexAnalysis

/-
Definition 3.1.1.1 lies in the convex constrained minimization domain.

Sampled owner-style declarations:
- `withTopEffectiveDomain`, `withTopRealPart`, and `constrainedEpigraph` in `Definition_3_3`, the
  earlier chapter owner layer for `WithTop`-valued convex-analysis data and its canonical
  epigraph bridge;
- `GeneralMinimizationProblem` in `Chap01/Definition_1_1_3`, the earlier project owner for a
  feasible set together with finitely many scalar constraints on a subtype;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the earlier project owner for
  the ambient feasible set and real-valued objective layer of a constrained problem;
- `ConvexInequalityConstrainedMinimizationProblem` in `Chap05/Definition_5_0_1`, the later
  whole-space real-valued convex inequality owner.

Best owner abstraction:
- `GeneralConvexMinimizationProblem X m` for the source-facing constrained minimization problem on
  a real ambient space `X`;
- `Definition_3_3` remains the owner for the ambient `WithTop` epigraph bridge;
- the textbook `ℝⁿ` formulation is a specialization of this owner, not its primitive core.

Primitive data:
- `feasibleSet`
- `objective`
- `constraints`
- the closedness and convexity witnesses.

Derived API:
- the coercion to the ambient objective function;
- the real-valued bridge `ofReal`, which reuses the Chapter 1 owner
  `SetConstrainedMinimizationProblem` for the feasible-set / objective layer;
- `GeneralConvexMinimizationProblem.IsFeasible` and its atomic consequence lemmas.

Source/core/bridge triage:
- source-facing: the textbook general convex minimization problem with convex inequality
  constraints;
- core/canonical: `GeneralConvexMinimizationProblem X m`;
- bridge/view: the textbook Euclidean specialization `X = EuclideanSpace ℝ (Fin n)`, together
  with the coercion to the ambient objective function and the feasibility lemmas; the ambient
  epigraph bridge is reused from `Definition_3_3`.

This file therefore keeps the chapter owner abstraction and does not collapse it to the earlier
Chapter 1 owners, whose objective and constraint data live on a subtype and in `ℝ` rather than as
ambient `WithTop ℝ` convex functions.
-/

/-- Definition 3.1.1.1, generalized from the textbook `ℝⁿ` setting: a general convex
minimization problem consists of minimizing an ambient extended-real-valued convex objective
function over a closed convex set `Q ⊆ X`, subject to finitely many ambient extended-real-valued
convex inequality constraints `fᵢ(x) ≤ 0`; no differentiability is assumed for the objective or
constraint functions. -/
structure GeneralConvexMinimizationProblem
    (X : Type u) [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] (m : ℕ) where
  /-- The ambient feasible set `Q ⊆ X`. -/
  feasibleSet : Set X
  /-- The ambient extended-real-valued objective function. -/
  objective : X → WithTop ℝ
  /-- The finitely many ambient extended-real-valued inequality constraints. -/
  constraints : Fin m → X → WithTop ℝ
  /-- The ambient feasible set `Q` is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The ambient feasible set `Q` is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The objective is convex in the Chapter 3 `WithTop` sense. -/
  objective_convex : ConvexOn ℝ (dom objective) (withTopRealPart objective)
  /-- Each inequality constraint is convex in the Chapter 3 `WithTop` sense. -/
  constraints_convex (i : Fin m) :
      ConvexOn ℝ (dom (constraints i)) (withTopRealPart (constraints i))

namespace GeneralConvexMinimizationProblem

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] {m : ℕ}

/-- A general convex minimization problem can be used as its ambient objective function. -/
instance : CoeFun (GeneralConvexMinimizationProblem X m) (fun _ ↦ X → WithTop ℝ) where
  coe := objective

/-- A real-valued constrained convex minimization problem with whole-space convex objective and
constraint functions canonically yields the Chapter 3 extended-valued owner by reusing the
Chapter 1 owner for the feasible-set / objective layer and coercing the functions to `WithTop ℝ`.
-/
def ofReal
    (problem : SetConstrainedMinimizationProblem X) (constraints : Fin m → X → ℝ)
    (feasibleSet_closed : IsClosed problem.feasibleSet)
    (feasibleSet_convex : Convex ℝ problem.feasibleSet)
    (objective_convex : ConvexOn ℝ Set.univ problem.objective)
    (constraints_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (constraints i)) :
    GeneralConvexMinimizationProblem X m where
  feasibleSet := problem.feasibleSet
  objective := fun x ↦ (problem x : WithTop ℝ)
  constraints := fun i x ↦ (constraints i x : WithTop ℝ)
  feasibleSet_closed := feasibleSet_closed
  feasibleSet_convex := feasibleSet_convex
  objective_convex := by
    simpa [withTopEffectiveDomain, withTopRealPart] using
      objective_convex
  constraints_convex i := by
    simpa [withTopEffectiveDomain, withTopRealPart] using
      constraints_convex i

/-- Evaluating a convex minimization problem as a function means evaluating its objective. -/
@[simp] theorem coe_apply (problem : GeneralConvexMinimizationProblem X m) (x : X) :
    problem x = problem.objective x :=
  rfl

/-- A point is feasible for a general convex minimization problem when it belongs to `Q` and
satisfies every inequality constraint `fᵢ(x) ≤ 0`. -/
def IsFeasible (problem : GeneralConvexMinimizationProblem X m) (x : X) : Prop :=
  x ∈ problem.feasibleSet ∧ ∀ i : Fin m, problem.constraints i x ≤ 0

/-- A point is feasible exactly when it lies in `Q` and satisfies every inequality constraint. -/
@[simp] theorem isFeasible_iff {problem : GeneralConvexMinimizationProblem X m} {x : X} :
    problem.IsFeasible x ↔ x ∈ problem.feasibleSet ∧ ∀ i : Fin m, problem.constraints i x ≤ 0 :=
  Iff.rfl

/-- A feasible point lies in the ambient feasible set `Q`. -/
theorem IsFeasible.mem_feasibleSet {problem : GeneralConvexMinimizationProblem X m} {x : X}
    (hx : problem.IsFeasible x) :
    x ∈ problem.feasibleSet :=
  hx.1

/-- A feasible point satisfies each inequality constraint `fᵢ(x) ≤ 0`. -/
theorem IsFeasible.constraint_nonpos {problem : GeneralConvexMinimizationProblem X m} {x : X}
    (hx : problem.IsFeasible x) (i : Fin m) :
    problem.constraints i x ≤ 0 :=
  hx.2 i

end GeneralConvexMinimizationProblem

/-! ### Definition_3_1_1_2 (from Chap03) -/
universe u

/- Definition 3.1.1.2 is the source-facing owner of the finite-value domain of an
extended-real-valued function.

Primary domain:
- finite-value domains of `EReal`-valued functions.

Relevant owner-style declarations sampled before refinement:
- chapter `withTopEffectiveDomain` in `Definition_3_3`, the analogous owner for `WithTop ℝ`
- chapter `mem_withTopEffectiveDomain_iff` in `Definition_3_3`, the atomic membership bridge for
  that owner
- mathlib `EReal.canLift`, whose predicate is exactly "neither `⊤` nor `⊥`"
- mathlib `EReal.range_coe_eq_Ioo`, the canonical order-theoretic description of finite `EReal`
  values

Best owner abstraction:
- `extendedRealEffectiveDomain`

Primitive data:
- the pointwise finiteness predicate `f x ≠ ⊤ ∧ f x ≠ ⊥`

Derived API:
- `mem_extendedRealEffectiveDomain_iff`
- `extendedRealEffectiveDomain_nonempty_iff`

Source/core/bridge triage:
- source-facing: the effective domain of an extended-real-valued function
- core/canonical: `extendedRealEffectiveDomain`
- bridge/view: `mem_extendedRealEffectiveDomain_iff`

The textbook states this notion for functions on `ℝⁿ`, but the domain construction itself uses no
Euclidean structure. Following the chapter owner style from `Definition_3_3`, this file exposes
the canonical owner on an arbitrary domain type; later items simply specialize it. -/

/-- Definition 3.1.1.2: the chapter's effective-domain owner for an extended-real-valued
function, namely the set of points where the value is a finite real. The textbook then treats the
nonemptiness condition on this domain as a standing assumption. -/
abbrev extendedRealEffectiveDomain {X : Type u} (f : X → EReal) : Set X :=
  {x | f x ≠ ⊤ ∧ f x ≠ ⊥}

/-- Textbook notation for the effective domain of an extended-real-valued function. -/
scoped[ConvexAnalysis] notation "dom " f:arg => extendedRealEffectiveDomain f

open scoped ConvexAnalysis

/-- Membership in the effective domain means that the function value is neither `⊤` nor `⊥`. -/
@[simp] theorem mem_extendedRealEffectiveDomain_iff {X : Type u} {f : X → EReal} {x : X} :
    x ∈ dom f ↔ f x ≠ ⊤ ∧ f x ≠ ⊥ :=
  Iff.rfl

/-- The effective domain is nonempty exactly when the function takes a finite value somewhere. -/
-- Proof sketch: unpack `Set.Nonempty` for `extendedRealEffectiveDomain f` and translate pointwise
-- membership through `mem_extendedRealEffectiveDomain_iff`.
theorem extendedRealEffectiveDomain_nonempty_iff {X : Type u} {f : X → EReal} :
    (dom f).Nonempty ↔ ∃ x, f x ≠ ⊤ ∧ f x ≠ ⊥ := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩

section

variable {X : Type u} (f : X → EReal)

/- The textbook immediately adds the standing assumption that the effective domain is nonempty.
The canonical Lean surface for that assumption is simply `(dom f).Nonempty`. -/
#check (dom f).Nonempty

end

/-! ### Definition_3_1_1_3 (from Chap03) -/
universe u

noncomputable section

open scoped ConvexAnalysis

/-
Definition 3.1.1.3 is the chapter's `EReal`-valued convex-analysis bridge.

Primary domain:
- finite-value domains and finite real parts of `EReal`-valued functions, together with their
  canonical convexity owners.

Relevant owner-style declarations sampled before refinement:
- mathlib `ConvexOn` in `Mathlib/Analysis/Convex/Function`
- mathlib `StrictConvexOn` in `Mathlib/Analysis/Convex/Function`
- mathlib `ConcaveOn` in `Mathlib/Analysis/Convex/Function`
- chapter `extendedRealEffectiveDomain` in `Definition_3_1_1_2`, exposed on the theorem surface
  by the textbook notation `dom f`
- mathlib `EReal.coe_toReal` in `Mathlib/Data/EReal/Basic`, the finite-value identification used
  in the bridge comparison lemmas

Best owner abstraction:
- the imported owner `extendedRealEffectiveDomain` together with the derived bridge
  `extendedRealRealPart` and the source-facing epigraph owner `effectiveEpigraph`
- core/canonical convexity owners:
  `ConvexOn ℝ (dom f) (extendedRealRealPart f)`,
  `StrictConvexOn ℝ (dom f) (extendedRealRealPart f)`, and
  `ConcaveOn ℝ (dom f) (extendedRealRealPart f)`.

Primitive data:
- the imported effective domain `dom f`
- the finite real part `extendedRealRealPart f`
- the effective epigraph `effectiveEpigraph f`, defined directly as the real epigraph owner over
  `dom f`

Derived API:
- `extendedRealRealPart_eq_toReal`
- `coe_extendedRealRealPart`
- the order-translation lemmas for `extendedRealRealPart` on `dom f`
- `mem_effectiveEpigraph_iff`, which restores the textbook `f x ≤ t` membership reading
- `effectiveEpigraph_eq_epigraph_extendedRealRealPart`

Source/core/bridge triage:
- source-facing: the three specialized convexity predicates recalled below
- core/canonical: mathlib `ConvexOn`, `StrictConvexOn`, and `ConcaveOn`
- bridge/view: `extendedRealRealPart`, `effectiveEpigraph`, and their comparison lemmas

The textbook states these notions on `ℝⁿ`, but this derived bridge still uses no Euclidean
structure beyond the imported domain owner. This file therefore keeps the arbitrary-domain owner
style and records only the finite-real-part bridge plus the three canonical convexity recalls.
-/

/-- The finite real part of an extended-real-valued function, extended by `0` at `±∞`. -/
abbrev extendedRealRealPart {X : Type u} (f : X → EReal) : X → ℝ :=
  EReal.toReal ∘ f

/-- The effective epigraph of an extended-real-valued function, realized canonically as the real
epigraph of its finite real part over `dom f`. -/
abbrev effectiveEpigraph {X : Type u} (f : X → EReal) : Set (X × ℝ) :=
  {p | p.1 ∈ dom f ∧ extendedRealRealPart f p.1 ≤ p.2}

/-- Evaluating `extendedRealRealPart` simply applies `EReal.toReal` to `f x`. -/
@[simp] theorem extendedRealRealPart_eq_toReal {X : Type u} {f : X → EReal} {x : X} :
    extendedRealRealPart f x = (f x).toReal :=
  rfl

/-- On the finite-value domain, coercing the finite real part back to `EReal` recovers the
original extended-real value. -/
@[simp] theorem coe_extendedRealRealPart {X : Type u} {f : X → EReal} {x : X}
    (hx : x ∈ dom f) :
    ((extendedRealRealPart f x : ℝ) : EReal) = f x := by
  rcases mem_extendedRealEffectiveDomain_iff.mp hx with ⟨hx_top, hx_bot⟩
  simpa [extendedRealRealPart] using (EReal.coe_toReal hx_top hx_bot)

/-- On the finite-value domain, a real upper bound on `extendedRealRealPart f x` is exactly an
upper bound on `f x` by the corresponding real point of `EReal`. -/
theorem extendedRealRealPart_le_iff {X : Type u} {f : X → EReal} {x : X}
    (hx : x ∈ dom f) {r : ℝ} :
    extendedRealRealPart f x ≤ r ↔ f x ≤ (r : EReal) := by
  rw [← coe_extendedRealRealPart hx]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- On the finite-value domain, a real lower bound by `extendedRealRealPart f x` is exactly a
lower bound by the corresponding real point of `EReal`. -/
theorem le_extendedRealRealPart_iff {X : Type u} {f : X → EReal} {x : X}
    (hx : x ∈ dom f) {r : ℝ} :
    r ≤ extendedRealRealPart f x ↔ (r : EReal) ≤ f x := by
  rw [← coe_extendedRealRealPart hx]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- Membership in `effectiveEpigraph f` means belonging to the finite-value domain and lying
above the original extended-real value. -/
@[simp] theorem mem_effectiveEpigraph_iff {X : Type u} {f : X → EReal} {p : X × ℝ} :
    p ∈ effectiveEpigraph f ↔ p.1 ∈ dom f ∧ f p.1 ≤ p.2 :=
by
  constructor
  · rintro ⟨hp, hp₂⟩
    exact ⟨hp, (extendedRealRealPart_le_iff hp).1 hp₂⟩
  · rintro ⟨hp, hp₂⟩
    exact ⟨hp, (extendedRealRealPart_le_iff hp).2 hp₂⟩

/-- The effective epigraph of `f` is exactly the real epigraph of its finite real part over
`dom f`. -/
theorem effectiveEpigraph_eq_epigraph_extendedRealRealPart {X : Type u} (f : X → EReal) :
    effectiveEpigraph f = {p : X × ℝ | p.1 ∈ dom f ∧ extendedRealRealPart f p.1 ≤ p.2} := by
  rfl

section Convexity

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]

/-
Definition 3.1.1.3 (1): an `EReal`-valued function is convex when its finite real part is convex
on its effective domain. The chapter owner surface is the specialized mathlib predicate below.
-/
variable (f : X → EReal)

#check ConvexOn ℝ (dom f) (extendedRealRealPart f)

/- Definition 3.1.1.3 (2): an `EReal`-valued function is strictly convex when its finite real part
is strictly convex on the same effective domain. -/
#check StrictConvexOn ℝ (dom f) (extendedRealRealPart f)

/- Definition 3.1.1.3 (3): an `EReal`-valued function is concave when its finite real part is
concave on the same effective domain. -/
#check ConcaveOn ℝ (dom f) (extendedRealRealPart f)

end Convexity

end

/-! ### Definition_3_1_1_4 (from Chap03) -/
/- Definition 3.1.1.4 lives in the finite convex-combination domain.

Sampled owner-style declarations:
- `StdSimplex`
- `StdSimplex.map`
- `ConvexSpace.convexCombination`
- `convexCombination_eq_sum`

Best owner abstraction:
- `convexCombination (w.map points)` for `w : StdSimplex R ι`

Primitive data:
- a simplex weight vector `w : StdSimplex R ι`
- a family `points : ι → E`, with finiteness carried intrinsically by the simplex witness

Derived API:
- `is_convex_combination_of R`, the source-facing owner-shaped predicate
- `StdSimplex.map`, transporting coefficient data to a simplex of points
- `StdSimplex.convexCombination_map_eq_sum`, rewriting the owner-shaped convex combination on a
  family indexed by a finite type into the textbook weighted-sum formula
- `convexCombination_eq_sum`, identifying the canonical convex combination with the textbook
  weighted sum
- `is_convex_combination_of_iff_exists_coefficients`, the coefficient bridge

Source/core/bridge triage:
- source-facing: `is_convex_combination_of R points x`, centered on the owner-shaped simplex
  presentation
- core/canonical: `convexCombination (w.map points)`
- bridge/view: `is_convex_combination_of_iff_exists_coefficients`

There is no earlier chapter declaration with this exact source-facing interface, so this file
introduces the source-facing predicate directly in terms of the mathlib owner abstraction over an
arbitrary scalar `R`, index type `ι`, and convex space. The finiteness of the combination is
encoded intrinsically by the simplex witness rather than by a separate public `Fintype`
assumption. The textbook real / `Fin m` coefficient formula is kept only as a companion bridge in
the module layer. -/

section Owner

variable (R : Type u) [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
variable {ι : Type v}
variable {E : Type w} [ConvexSpace R E]

/-- Definition 3.1.1.4: a point is a convex combination of a finite family of points when it is
the canonical convex combination associated to some simplex weight vector on that family. -/
def is_convex_combination_of (points : ι → E) (x : E) : Prop :=
  ∃ w : StdSimplex R ι, x = convexCombination (w.map points)

end Owner

section Module

variable (R : Type u) [PartialOrder R] [Ring R] [IsStrictOrderedRing R]
variable {ι : Type v} [Fintype ι]
variable {E : Type w} [AddCommGroup E] [Module R E]

local notation "convexCombination" =>
  @ConvexSpace.convexCombination R E inferInstance inferInstance inferInstance inferInstance

namespace StdSimplex

/-- Rewriting the canonical convex combination of a finite family gives the usual weighted-sum
formula with the simplex coefficients. -/
theorem convexCombination_map_eq_sum (w : StdSimplex R ι) (points : ι → E) :
    convexCombination (w.map points) = ∑ i, w.weights i • points i := by
  rw [convexCombination_eq_sum, StdSimplex.map]
  rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ add_smul _ _ _)]
  simpa using
    (Finsupp.sum_fintype w.weights (fun i r ↦ r • points i) (fun _ ↦ by simp))

end StdSimplex

/-- Unpacking the canonical simplex-based convex combination into coefficient data gives exactly
the textbook finite convex-combination formula, and conversely. -/
-- Proof sketch: read the coefficients directly from the simplex weights, using the `StdSimplex`
-- axioms for nonnegativity and normalization; conversely, package a coefficient family on the
-- finite index type `ι` into a finitely supported weight vector via
-- `Finsupp.equivFunOnFinite.symm`, then rewrite the owner-shaped convex combination by
-- `StdSimplex.convexCombination_map_eq_sum`.
theorem is_convex_combination_of_iff_exists_coefficients
    (points : ι → E) (x : E) :
    is_convex_combination_of R points x ↔
      ∃ α : ι → R, (∀ i, 0 ≤ α i) ∧ (∑ i, α i) = 1 ∧ x = ∑ i, α i • points i := by
  unfold is_convex_combination_of
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.weights, fun i ↦ w.nonneg i, ?_, ?_⟩
    · simpa [Finsupp.sum_fintype] using w.total
    · simpa [StdSimplex.convexCombination_map_eq_sum R w points] using hw
  · rintro ⟨α, hαnonneg, hαsum, rfl⟩
    let w : StdSimplex R ι :=
      ⟨Finsupp.equivFunOnFinite.symm α,
        by simpa using hαnonneg,
        by simpa using (Finsupp.equivFunOnFinite_symm_sum α).trans hαsum⟩
    refine ⟨w, ?_⟩
    simpa [w] using (StdSimplex.convexCombination_map_eq_sum R w points).symm

end Module

/-! ### Definition_3_1_1_5 (from Chap03) -/
universe u

open scoped WithTopConvexAnalysis

/-- On a set where `f` is finite, the constrained epigraph of `f` is exactly the ordinary
epigraph of the finite real part `withTopRealPart f`. -/
theorem constrainedEpigraph_eq_epigraph_withTopRealPart
    {X : Type u} {Q : Set X} {f : X → WithTop ℝ}
    (hQ_dom : Q ⊆ dom f) :
    constrainedEpigraph Q f = {p : X × ℝ | p.1 ∈ Q ∧ withTopRealPart f p.1 ≤ p.2} := by
  ext p
  constructor
  · rintro ⟨hpQ, hp⟩
    exact ⟨hpQ, (withTopRealPart_le_iff (hQ_dom hpQ)).2 hp⟩
  · rintro ⟨hpQ, hp⟩
    exact ⟨hpQ, (withTopRealPart_le_iff (hQ_dom hpQ)).1 hp⟩

/- Definition 3.1.1.5 lives in the chapter's `WithTop`-valued convex-analysis API.

Primary domain:
- closed convex extended-real-valued functions on real topological modules, specializing to the
  textbook `ℝⁿ` setting.

Sampled owner-style declarations in this domain:
- `withTopEffectiveDomain`, `withTopRealPart`, `constrainedEpigraph` from `Definition_3_3`
- mathlib `ConvexOn`
- mathlib `convexOn_iff_convex_epigraph`

Owner abstraction:
- source-facing owner: `ClosedConvexOn Q f`
- core/canonical convexity view: `ConvexOn ℝ Q (withTopRealPart f)`
- primitive bridge data: `dom f` and `constrainedEpigraph Q f`

Primitive data:
- the domain inclusion `Q ⊆ dom f`
- the closedness of `constrainedEpigraph Q f`
- the convexity of `constrainedEpigraph Q f`

Derived API:
- `constrainedEpigraph_eq_epigraph_withTopRealPart`
- the projection lemmas out of `ClosedConvexOn`
- `ClosedConvexOn.convexOn_withTopRealPart`
- `ClosedConvexOn.convex`
- `ClosedConvexFunction f` as the special case `Q = dom f`

Source/core/bridge triage:
- source-facing: `ClosedConvexOn`, `ClosedConvexFunction`
- core/canonical: `withTopEffectiveDomain`, `constrainedEpigraph`, `ConvexOn`
- bridge/view: `constrainedEpigraph_eq_epigraph_withTopRealPart`, the projection lemmas, and the
  `ConvexOn` consequences on `dom f`

This file therefore reuses the owner effective-domain abstraction directly instead of keeping a
parallel set-level presentation, while exposing the canonical `ConvexOn` owner view as derived
API rather than storing it as parallel primitive data. -/

section

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/-- Definition 3.1.1.5, generalized from the textbook `ℝⁿ` setting: an `ℝ ∪ {+∞}`-valued
function is closed and convex on `Q` when `Q ⊆ dom f` and its constrained epigraph is a closed
convex subset of `X × ℝ`. -/
def ClosedConvexOn (Q : Set X) (f : X → WithTop ℝ) : Prop :=
  Q ⊆ dom f ∧
    IsClosed (constrainedEpigraph Q f) ∧
    Convex ℝ (constrainedEpigraph Q f)

namespace ClosedConvexOn

variable {Q : Set X} {f : X → WithTop ℝ}

/-- A function that is closed and convex on `Q` is finite on every point of `Q`. -/
-- Proof sketch: unfold `ClosedConvexOn` and read off the first conjunct recording
-- `Q ⊆ dom f`.
theorem subset_withTopEffectiveDomain (hf : ClosedConvexOn Q f) :
    Q ⊆ dom f :=
  hf.1

/-- A function that is closed and convex on `Q` has a closed constrained epigraph over `Q`. -/
-- Proof sketch: unfold `ClosedConvexOn` and project to the second conjunct.
theorem isClosed_constrainedEpigraph (hf : ClosedConvexOn Q f) :
    IsClosed (constrainedEpigraph Q f) :=
  hf.2.1

/-- A function that is closed and convex on `Q` has a convex constrained epigraph over `Q`. -/
-- Proof sketch: unfold `ClosedConvexOn` and project to the final conjunct.
theorem convex_constrainedEpigraph (hf : ClosedConvexOn Q f) :
    Convex ℝ (constrainedEpigraph Q f) :=
  hf.2.2

/-- A closed convex function on `Q` induces the canonical `ConvexOn` structure on its finite
real part over `Q`. -/
theorem convexOn_withTopRealPart (hf : ClosedConvexOn Q f) :
    ConvexOn ℝ Q (withTopRealPart f) := by
  refine (convexOn_iff_convex_epigraph).2 ?_
  simpa [constrainedEpigraph_eq_epigraph_withTopRealPart hf.subset_withTopEffectiveDomain] using
    hf.convex_constrainedEpigraph

/-- A function that is closed and convex on `Q` has a convex feasible set `Q`. -/
theorem convex (hf : ClosedConvexOn Q f) :
    Convex ℝ Q :=
  hf.convexOn_withTopRealPart.1

/-- Restricting a closed convex function to a closed convex subset preserves closed convexity. -/
theorem restrict
    {Q Q₁ : Set X} (hf : ClosedConvexOn Q f) (hQ₁_closed : IsClosed Q₁)
    (hQ₁_convex : Convex ℝ Q₁) (hQ₁Q : Q₁ ⊆ Q) :
    ClosedConvexOn Q₁ f := by
  have hQ₁_domain : Q₁ ⊆ dom f := fun x hx ↦
    hf.subset_withTopEffectiveDomain (hQ₁Q hx)
  have hEpigraph :
      constrainedEpigraph Q₁ f = (Q₁ ×ˢ (Set.univ : Set ℝ)) ∩ constrainedEpigraph Q f :=
    constrainedEpigraph_eq_prod_univ_inter_of_subset hQ₁Q
  refine ⟨hQ₁_domain, ?_, ?_⟩
  · rw [hEpigraph]
    exact (hQ₁_closed.prod isClosed_univ).inter hf.isClosed_constrainedEpigraph
  · rw [hEpigraph]
    exact (hQ₁_convex.prod convex_univ).inter hf.convex_constrainedEpigraph

end ClosedConvexOn

/-- A function is a closed convex function when it is closed and convex on its effective domain. -/
abbrev ClosedConvexFunction (f : X → WithTop ℝ) : Prop :=
  ClosedConvexOn (dom f) f

end

/-! ### Definition_3_1_1_6 (from Chap03) -/
/- Definition 3.1.1.6 is a recall-only item in the seminorm-geometry domain.

Layer targeted by this refinement:
- source-facing recall of the core/canonical owner closed-ball API for seminorms

Primary domain:
- closed balls attached to seminorms.

Sampled owner-style declarations:
- `Seminorm.closedBall`
- `Seminorm.mem_closedBall`
- `Seminorm.mem_closedBall_zero`
- `Seminorm.closedBall_zero_eq`

Primitive data:
- a seminorm `p : Seminorm ℝ E`
- a center `x₀ : E`
- a radius `r : ℝ`

Derived API:
- `Seminorm.mem_closedBall` gives the set-builder characterization
  `x ∈ p.closedBall x₀ r ↔ p (x - x₀) ≤ r`.

Source/core/bridge triage:
- source-facing: the textbook closed ball attached to a seminorm
- core/canonical: `Seminorm.closedBall`
- bridge/view: the defining membership lemma `Seminorm.mem_closedBall`

This file therefore keeps only the general owner declaration and its defining bridge view.
Downstream unit-ball files should use the same owner declaration directly and recall the zero-center
specializations there.
-/

recall Seminorm.closedBall
recall Seminorm.mem_closedBall

/-! ### Definition_3_1_1_7 (from Chap03) -/
open scoped BigOperators
open scoped EuclideanSpaceLp

/- Definition 3.1.1.7 lies in the finite-dimensional `ℓ_p`-geometry domain.

Sampled owner-style declarations:
- `Seminorm.closedBall`
- `Seminorm.mem_closedBall`
- `EuclideanSpace.lpSeminorm`
- `EuclideanSpace.lpNorm_eq_sum`

Best owner abstraction:
- `(EuclideanSpace.lpSeminorm n p).closedBall x₀ r`

Primitive data:
- the ambient dimension `n : ℕ`
- the exponent `p : EuclideanSpace.LpExponent`
- the center `x₀ : EuclideanSpace ℝ (Fin n)`
- the radius `r : ℝ`

Derived API:
- the coordinate membership criterion below, obtained from the canonical owner membership lemma
  `Seminorm.mem_closedBall` and the coordinate formula `EuclideanSpace.lpNorm_eq_sum`

Source/core/bridge triage:
- source-facing: the coordinate description of the textbook `ℓ_p` closed ball
- core/canonical: `(EuclideanSpace.lpSeminorm n p).closedBall x₀ r`
- bridge/view: `mem_lp_closedBall_coord_iff`

The previous file duplicated `Seminorm.mem_closedBall` under the local name
`mem_lp_closedBall_iff`. Since the owner declaration is already recalled in
`Definition_3_1_1_6`, this file keeps only the genuine coordinate bridge. -/

/-- Definition 3.1.1.7: membership in the textbook `ℓ_p` closed ball centered at `x₀` and of
radius `r` is equivalent to the usual coordinate `ℓ_p` inequality. -/
theorem mem_lp_closedBall_coord_iff (n : ℕ) (p : EuclideanSpace.LpExponent)
    (x₀ x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    x ∈ (EuclideanSpace.lpSeminorm n p).closedBall x₀ r ↔
      (∑ i, |(x - x₀) i| ^ p.toReal) ^ (1 / p.toReal : ℝ) ≤ r := by
  rw [(EuclideanSpace.lpSeminorm n p).mem_closedBall, EuclideanSpace.lpNorm_eq_sum (x - x₀) p]

/-! ### Lemma_3_1 (from Chap03) -/
/- Lemma 3.1 lies in the finite Jensen / convex-combination domain.

Primary mathematical domain:
- Jensen's inequality for convex functions on finite weighted sums

Relevant owner-style declarations sampled before refinement:
- `ConvexOn.map_centerMass_le`
- `ConvexOn.map_sum_le`
- `Convex.sum_mem`
- `ConvexOn.map_add_sum_le`

Best owner abstraction:
- `ConvexOn.map_sum_le`

Primitive data:
- a convex-on-set witness `hf : ConvexOn ℝ s f`
- a finite family `x : Fin m → E` with `x i ∈ s`
- a coefficient family `α : Fin m → ℝ` with `0 ≤ α i` and `∑ i, α i = 1`

Derived API:
- Jensen's inequality at the weighted sum `∑ i, α i • x i`
- the separate domain-membership consequence from `Convex.sum_mem`
- any simplex-packaged or convex-combination-packaged presentation as downstream bridge API, not as
  the owner theorem itself

Source/core/bridge triage:
- source-facing: the explicit finite Jensen inequality from the text
- core/canonical: `ConvexOn.map_sum_le`
- bridge/view: `Convex.sum_mem` for domain membership, and later chapter simplex packaging only as a
  presentation layer for the same finite weighted-sum data

The textbook item is Jensen's inequality itself. Since mathlib already owns that statement in the
correct nonnegative-weight form, this file centers the canonical owner declaration directly. The
domain-membership consequence belongs to `Convex.sum_mem` and is not bundled into the main item.
-/

recall ConvexOn.map_sum_le

/-! ### Lemma_3_1_1 (from Chap03) -/
/- Lemma 3.1.1 is a recall-only item in the finite Jensen / convex-combination domain.

Primary mathematical domain:
- Jensen's inequality for convex functions on finite weighted sums

Relevant owner-style declarations sampled before refinement:
- `ConvexOn.map_centerMass_le`
- `ConvexOn.map_sum_le`
- `ConvexOn.map_add_sum_le`
- `Convex.sum_mem`

Best owner abstraction:
- `ConvexOn.map_sum_le`

Primitive data:
- a convex-on-set witness `hf : ConvexOn ℝ s f`
- a finite family `x : Fin m → E` with `x i ∈ s`
- a coefficient family `α : Fin m → ℝ`

Derived API:
- Jensen's inequality at the weighted sum `∑ i, α i • x i`
- the positivity-to-nonnegativity specialization `0 < α i → 0 ≤ α i`, used only at call sites
- the separate domain-membership consequence from `Convex.sum_mem`

Source/core/bridge triage:
- source-facing: the textbook finite Jensen inequality with positive coefficients
- core/canonical: `ConvexOn.map_sum_le`
- bridge/view: the redundant positivity specialization from the source wording to the owner
  theorem's nonnegative-weight interface

The exact mathematical content here is already owned canonically by `ConvexOn.map_sum_le`, and the
earlier chapter file `Lemma_3_1.lean` already centers that owner theorem. This file therefore does
not keep a second local `example` proof with the stronger positivity hypotheses; those hypotheses
are bridge-only and should be discharged at the use site by passing `fun i ↦ (hαpos i).le` into
the owner theorem.
-/

recall ConvexOn.map_sum_le

/-! ### Lemma_3_1_1_1 (from Chap03) -/
/- Lemma 3.1.1.1 is a recall-only Euclidean specialization in the finite Jensen domain.

Primary mathematical domain:
- Jensen's inequality for convex functions on finite weighted sums

Relevant owner-style declarations sampled before refinement:
- `Lemma_3_1_1`, the earlier chapter recall of `ConvexOn.map_sum_le`
- `ConvexOn.map_centerMass_le`
- `ConvexOn.map_sum_le`
- `Convex.sum_mem`

Best owner abstraction:
- `ConvexOn.map_sum_le`

Primitive data:
- a convex-on-set witness `hf : ConvexOn ℝ s f`
- a finite family `x : Fin m → EuclideanSpace ℝ (Fin n)` with `x i ∈ s`
- a coefficient family `α : Fin m → ℝ` summing to `1`

Derived API:
- the Euclidean specialization of Jensen's inequality
- the positivity-to-nonnegativity bridge `0 < α i → 0 ≤ α i`, which belongs only at use sites

Source/core/bridge triage:
- source-facing: the textbook Euclidean specialization
- core/canonical: `ConvexOn.map_sum_le`
- bridge/view: specializing the ambient module to `EuclideanSpace ℝ (Fin n)`

This item adds no new mathematics beyond the owner theorem. The source's positivity wording is a
use-site bridge to the owner's nonnegativity hypothesis, so the file keeps the owner declaration as
the main public entry and lets the Euclidean specialization elaborate directly at call sites. -/

recall ConvexOn.map_sum_le

/-! ### Lemma_3_1_1_2 (from Chap03) -/
universe u

section

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/- Lemma 3.1.1.2 is a source-facing recall in the chapter's closed-convex `WithTop`-valued
convex-analysis domain.

Primary domain:
- restriction of a closed convex extended-real-valued function to a closed convex subset.

Sampled owner-style declarations:
- `ClosedConvexOn`
- `ClosedConvexOn.restrict`
- `ClosedConvexOn.isClosed_constrainedEpigraph`
- mathlib `ConvexOn.subset`

Best owner abstraction:
- `ClosedConvexOn`

Primitive data:
- a witness `hf : ClosedConvexOn Q f`
- the subset, closedness, and convexity data for `Q₁ ⊆ Q`

Derived API:
- the canonical owner theorem `ClosedConvexOn.restrict`

Source/core/bridge triage:
- source-facing: the restriction lemma for closed convex functions on a closed convex subset
- core/canonical: `ClosedConvexOn`
- bridge/view: `constrainedEpigraph` together with mathlib `ConvexOn.subset`

The main entry now reuses the owner theorem at the same ambient abstraction level as
`ClosedConvexOn` itself, instead of recalling a later `ℝⁿ`-specialized duplicate. -/

recall ClosedConvexOn.restrict
    {f : X → WithTop ℝ} {Q Q₁ : Set X}
    (hf : ClosedConvexOn Q f)
    (hQ₁_closed : IsClosed Q₁)
    (hQ₁_convex : Convex ℝ Q₁)
    (hQ₁Q : Q₁ ⊆ Q) :
    ClosedConvexOn Q₁ f

end

/-! ### Proposition_3_1 (from Chap03) -/
universe u v w

section

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type v} [AddCommGroup E] [Module 𝕜 E]
variable {β : Type w} [ConditionallyCompleteLinearOrder β] [AddCommGroup β]
  [IsOrderedAddMonoid β] [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β]

/- Proposition 3.1 lies in the convex-analysis domain of finite convex-hull maximum principles on
ordered scalar modules.

Sampled owner-style declarations:
- `ConvexOn.le_sup_of_mem_convexHull`
- `ConvexOn.exists_ge_of_mem_convexHull`
- `Finset.sup'_eq_csSup_image`

Best owner abstraction:
- `ConvexOn.le_sup_of_mem_convexHull`

Primitive data:
- a finite nonempty vertex set `t : Finset E`
- an ordered scalar `𝕜` and ordered codomain `β`
- a convex function `hf : ConvexOn 𝕜 C f`
- the source-faithful inclusion `(t : Set E) ⊆ C`

Derived API:
- the equality between the supremum of `f` on `convexHull 𝕜 (t : Set E)` and the supremum of `f`
  on the vertex set `(t : Set E)`
- the finite-maximum reformulation through `t.sup' ht f`

Source/core/bridge triage:
- source-facing: the simplex maximum principle from the textbook proposition
- core/canonical: `ConvexOn.le_sup_of_mem_convexHull`
- bridge/view: `Finset.sup'_eq_csSup_image`, which identifies the supremum on the finite vertex set
  with the finite maximum

The owner theorem is already organized around a finite vertex set, so this file uses the same
primitive data instead of introducing a parallel family-index API. The source-facing content is the
equality of the convex-hull supremum with the vertex supremum, while the ambient scalar and codomain
now remain at the canonical generality already supported by the owner theorem. -/

/-- Proposition 3.1: if a `β`-valued convex function is defined on a set containing a finite
nonempty vertex set `t`, then its supremum on `convexHull 𝕜 (t : Set E)` equals its supremum on
the vertex set itself. Since `t` is finite and nonempty, this is exactly the finite-maximum
statement behind the textbook real-valued simplex maximum principle; specializing `𝕜 = β = ℝ`
recovers the usual formulation. -/
theorem convexOn_sSup_image_convexHull_eq_sSup_image_vertices
    (t : Finset E) (ht : t.Nonempty) {C : Set E} {f : E → β} (hf : ConvexOn 𝕜 C f)
    (htC : (t : Set E) ⊆ C) :
    sSup (f '' convexHull 𝕜 (t : Set E)) = sSup (f '' (t : Set E)) := by
  have hpointwise_upper :
      ∀ y ∈ f '' convexHull 𝕜 (t : Set E), y ≤ t.sup' ht f := by
    rintro _ ⟨x, hx, rfl⟩
    exact hf.le_sup_of_mem_convexHull htC hx
  have hconv_nonempty : (f '' convexHull 𝕜 (t : Set E)).Nonempty :=
    ((Finset.Nonempty.to_set ht).mono (subset_convexHull 𝕜 (t : Set E))).image f
  have hbounded : BddAbove (f '' convexHull 𝕜 (t : Set E)) := ⟨_, hpointwise_upper⟩
  have hvertex_nonempty : (f '' (t : Set E)).Nonempty := (Finset.Nonempty.to_set ht).image f
  have himage_mono : f '' (t : Set E) ⊆ f '' convexHull 𝕜 (t : Set E) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, subset_convexHull 𝕜 (t : Set E) hx, rfl⟩
  have hupper : sSup (f '' convexHull 𝕜 (t : Set E)) ≤ t.sup' ht f :=
    csSup_le hconv_nonempty hpointwise_upper
  have hlower : t.sup' ht f ≤ sSup (f '' convexHull 𝕜 (t : Set E)) := by
    rw [Finset.sup'_eq_csSup_image t ht f]
    exact csSup_le_csSup hbounded hvertex_nonempty himage_mono
  rw [Finset.sup'_eq_csSup_image t ht f] at hupper hlower
  exact le_antisymm hupper hlower

end

/-! ### Proposition_3_1_1_1 (from Chap03) -/
/- Proposition 3.1.1.1 lies in the chapter's extended-real effective-epigraph closedness domain.

Primary domain:
- closedness of effective epigraphs of `EReal`-valued functions on topological spaces, expressed
  through continuity of the finite real part on the effective domain.

Sampled owner-style declarations:
- chapter `dom f` and `extendedRealRealPart f` from `Definition_3_1_1_3`, the canonical
  finite-value owner/bridge vocabulary in this domain;
- `isClosed_effectiveEpigraph_of_continuousOn_of_isClosed_dom` in `Proposition_3_2`, the
  source-facing chapter theorem on `effectiveEpigraph f`;
- `isClosed_effectiveEpigraph_of_lowerSemicontinuousOn_of_isClosed_dom` in `Proposition_3_2`,
  the stronger companion obtained by weakening continuity to lower semicontinuity;
- mathlib `ContinuousOn.lowerSemicontinuousOn`, the canonical bridge from the source-facing
  continuity statement to the companion strengthening;
- mathlib `LowerSemicontinuousOn.isClosed_re_epigraph`, the canonical real-epigraph closedness
  owner used by the chapter theorem.

Best owner abstraction:
- the existing chapter theorem
  `isClosed_effectiveEpigraph_of_continuousOn_of_isClosed_dom`.

Primitive data:
- the `EReal`-valued function `f`;
- continuity of `extendedRealRealPart f` on `dom f`;
- closedness of `dom f`.

Derived API:
- closedness of the effective epigraph `{p : X × ℝ | p.1 ∈ dom f ∧ f p.1 ≤ p.2}`.
- companion strengthening under lower semicontinuity on `dom f`.

Source/core/bridge triage:
- source-facing: this effective-epigraph closedness proposition;
- core/canonical: mathlib lower-semicontinuity / `isClosed_re_epigraph`;
- bridge/view: the chapter theorem
  `isClosed_effectiveEpigraph_of_continuousOn_of_isClosed_dom`.

This file therefore remains recall-only: the proposition-level statement already exists upstream in
the minimal chapter closure with the correct canonical `dom f` owner surface, so introducing a
second local theorem here would only recreate the duplicate-wheel problem. -/

recall isClosed_effectiveEpigraph_of_continuousOn_of_isClosed_dom

/-! ### Proposition_3_1_1_2 (from Chap03) -/
/- Proposition 3.1.1.2 lies in the chapter's real convex-analysis / epigraph domain.

Primary domain:
- the epigraph of the absolute value function on `ℝ` and its half-space description in `ℝ × ℝ`.

Sampled owner-style declarations:
- project `abs_convexOn_univ` in `Proposition_3_3`, which owns the convexity of `x ↦ |x|`;
- project `abs_epigraph_isClosed` in `Proposition_3_3`, which owns the closedness of the same
  epigraph;
- project `abs_epigraph_eq_inter_halfspaces` in `Proposition_3_3`, which already has the exact
  textbook set-theoretic statement for this item;
- mathlib `ConvexOn.convex_epigraph`, the canonical ambient epigraph-convexity owner in this
  domain.

Best owner abstraction:
- the existing chapter theorem `abs_epigraph_eq_inter_halfspaces`.

Primitive data:
- none locally; the full mathematical statement already exists upstream in the minimal chapter
  closure.

Derived API:
- the supporting convexity and closedness facts in `Proposition_3_3`.

Source/core/bridge triage:
- source-facing: the half-space description of the epigraph of `|x|`;
- core/canonical: the existing chapter theorem `abs_epigraph_eq_inter_halfspaces`;
- bridge/view: the supporting owner facts `abs_convexOn_univ` and `abs_epigraph_isClosed`.

This file is therefore recall-only. Keeping local definitions such as `absEpigraph`,
`upperDiagonalHalfspace`, or renamed theorem shells would be a forbidden duplicate wrapper around
the existing chapter owner.
-/

/- Proposition 3.1.1.2 is the direct recall of the chapter's half-space description of the
epigraph of the absolute value function. -/
recall abs_epigraph_eq_inter_halfspaces

/-! ### Proposition_3_1_1_3 (from Chap03) -/
universe u

open scoped WithTopConvexAnalysis

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/-- Proposition 3.1.1.3, generalized from the textbook `ℝⁿ` setting: a continuous convex
real-valued function on a real topological module is a closed convex function; equivalently, after
coercing `f` to `WithTop ℝ`, its epigraph is a closed convex subset of `X × ℝ`. -/
-- Proof sketch: for the `WithTop ℝ`-valued coercion of `f`, the effective domain is all of `X`,
-- so `ClosedConvexFunction` reduces to closedness and convexity of the usual epigraph.
-- Convexity is exactly `hf_convex.convex_epigraph`, and closedness follows from
-- `IsClosed.epigraph isClosed_univ hf_cont.continuousOn`.
theorem closedConvexFunction_coe_of_convexOn_continuous
    {f : X → ℝ}
    (hf_convex : ConvexOn ℝ Set.univ f) (hf_cont : Continuous f) :
    ClosedConvexFunction (fun x ↦ (f x : WithTop ℝ)) := by
  let g : X → WithTop ℝ := fun x ↦ (f x : WithTop ℝ)
  have hconstrained :
      constrainedEpigraph (dom g) g =
        {p : X × ℝ | p.1 ∈ dom g ∧ withTopRealPart g p.1 ≤ p.2} :=
    constrainedEpigraph_eq_epigraph_withTopRealPart (subset_rfl : dom g ⊆ dom g)
  refine ⟨subset_rfl, ?_, ?_⟩
  · rw [hconstrained]
    simpa [withTopEffectiveDomain, withTopRealPart, g] using
      IsClosed.epigraph isClosed_univ hf_cont.continuousOn
  · rw [hconstrained]
    simpa [withTopEffectiveDomain, withTopRealPart, g] using hf_convex.convex_epigraph

/-! ### Proposition_3_1_1_4 (from Chap03) -/
/- Proposition 3.1.1.4 lies in the chapter's one-dimensional extended-real convex-analysis domain.

Primary domain:
- the reciprocal function on `(0, ∞)` and its `WithTop ℝ` epigraph/lower-semicontinuity package.

Sampled owner-style declarations:
- chapter `positiveReciprocalExtension`
- chapter `reciprocalEpigraphOnPositiveRay`
- chapter `dom f` and `constrainedEpigraph Q f` from `Definition_3_3`
- mathlib `strictConvexOn_zpow`
- mathlib `lowerSemicontinuous_iff_isClosed_epigraph`

Best owner abstraction:
- the existing chapter owner declaration `positiveReciprocalExtension` from `Proposition_3_5`,
  together with the Chapter 2 owner set `reciprocalEpigraphOnPositiveRay` and the chapter
  canonical epigraph/domain owners `constrainedEpigraph` and `dom` from `Definition_3_3`.

Primitive data:
- the extended reciprocal function on `ℝ`

Derived API:
- the epigraph identification bridge to `reciprocalEpigraphOnPositiveRay`
- convexity on `Set.Ioi 0`
- lower semicontinuity
- closedness of the epigraph
- identification and openness of the effective domain

Source/core/bridge triage:
- source-facing: the reciprocal-extension proposition package already owned by `Proposition_3_5`
- core/canonical: `reciprocalEpigraphOnPositiveRay`, `dom`, `constrainedEpigraph`, and the
  mathlib convexity/lower-semicontinuity owners
- bridge/view: this numbering-local file, which should only recall the upstream chapter owner
  declarations and canonical expressions instead of reintroducing a parallel duplicate API

This file is therefore recall-only. Keeping local names such as `reciprocalWithTop` would create a
second public owner for the same mathematics with the same interface, which is exactly the
duplicate-wheel pattern the chapter policy forbids. -/

recall positiveReciprocalExtension

recall reciprocalEpigraphOnPositiveRay

recall positiveReciprocalExtensionEpigraph_eq_reciprocalEpigraphOnPositiveRay

recall mem_reciprocalEpigraphOnPositiveRay_iff

recall convexOn_one_div_Ioi_zero

recall lowerSemicontinuous_positiveReciprocalExtension

recall reciprocalEpigraphOnPositiveRay_isClosed

recall positiveReciprocalExtension_effectiveDomain_eq_Ioi

recall isOpen_positiveReciprocalExtension_effectiveDomain

/-! ### Proposition_3_1_1_5 (from Chap03) -/
universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 3.1.1.5 lies in the chapter's closed-convex `WithTop`-valued convex-analysis
domain.

Primary domain:
- closed convexity of seminorm functions on finite-dimensional real normed spaces, with the
  textbook `ℝⁿ` case as a specialization.

Sampled owner-style declarations:
- `ClosedConvexOn` and `ClosedConvexFunction` in `Definition_3_1_1_5`, the chapter owners for
  closed convex extended-real-valued functions;
- `Seminorm.closedConvexFunction` in `Proposition_3_6`, the existing chapter theorem giving the
  canonical owner statement for `x ↦ p x`;
- mathlib `Seminorm.convexOn`, the canonical convexity owner behind the theorem;
- mathlib `ConvexOn.continuousOn`, the canonical continuity bridge on the open owner domain
  `Set.univ`.

Best owner abstraction:
- `ClosedConvexFunction (fun x : E ↦ (p x : WithTop ℝ))`.

Primitive data:
- a seminorm `p : Seminorm ℝ E`.

Derived API:
- the owner theorem `Seminorm.closedConvexFunction`;
- the `ClosedConvexOn Set.univ` specialization obtained from the owner abbreviation because norm
  functions are finite everywhere.

Source/core/bridge triage:
- source-facing: the proposition that a norm function is closed and convex on all of `ℝⁿ`;
- core/canonical: `ClosedConvexFunction` / `ClosedConvexOn`;
- bridge/view: the identification of the norm function's effective domain with `Set.univ`.

This file is therefore recall-only. `Proposition_3_6` already introduced the correct owner-level
theorem in the minimal chapter closure, so keeping another named theorem here would only duplicate
that API under a second shell. -/

recall Seminorm.closedConvexFunction
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) :
    ClosedConvexFunction (fun x : E ↦ (p x : WithTop ℝ))

/-! ### Proposition_3_1_1_6 (from Chap03) -/
variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e[" i "]" => EuclideanSpace.single i (1 : ℝ)

/- Proposition 3.1.1.6 lies in the chapter's finite-dimensional `ℓ₁`-geometry / convex-hull
domain.

Layer targeted by this refinement:
- source-facing proposition stated at the canonical `ℓ₁`-closed-ball owner layer

Sampled owner-style declarations:
- `EuclideanSpace.l1Seminorm`
- `Seminorm.closedBall`
- `l1_ball_eq_convexHull_signed_standard_basis_prop`

Best owner abstraction:
- `(EuclideanSpace.l1Seminorm n).closedBall x₀ r`

Primitive data:
- the ambient dimension `n : ℕ`
- the center `x₀ : E`
- the radius `r : ℝ`

Derived API:
- the convex-hull description of that closed ball by the signed standard-basis vertices, already
  established in `Proposition_3_7`

Dimension side condition:
- `0 < n`, excluding the degenerate `n = 0` case where the signed-vertex set is empty while the
  closed ball is nonempty for `r ≥ 0`

Source/core/bridge triage:
- source-facing: the `ℓ₁` closed ball / signed-vertex convex-hull equality
- core/canonical: `Seminorm.closedBall` for `EuclideanSpace.l1Seminorm n`
- bridge/view: this recall-only file

`Proposition_3_7` now already states the proposition on the canonical closed-ball owner surface.
Keeping a second theorem here with the same interface would only duplicate that owner-level API
under a different name, so this file is recall-only.
-/

recall l1_ball_eq_convexHull_signed_standard_basis_prop
    (hn : 0 < n) (x₀ : E) (r : ℝ) (hr : 0 ≤ r) :
    (EuclideanSpace.l1Seminorm n).closedBall x₀ r =
      convexHull ℝ
        (Set.range (fun i : Fin n ↦ x₀ + r • e[i]) ∪
          Set.range (fun i : Fin n ↦ x₀ - r • e[i]))

/-! ### Proposition_3_1_1_7 (from Chap03) -/
/- Proposition 3.1.1.7 lies in the chapter's source-facing unit-disk boundary-extension domain.

Primary domain:
- lower-semicontinuity of a `WithTop ℝ`-valued boundary extension on the Euclidean unit disk.

Sampled owner-style declarations:
- `unitDiskBoundaryExtension` in `Proposition_3_8`, the existing source-facing owner for the
  textbook construction;
- `unitDiskBoundaryExtension_convex_and_effectiveDomain` in `Proposition_3_8`, the companion
  theorem supplying the owner-level convexity and effective-domain data of the same owner;
- `unitDiskBoundaryExtension_lowerSemicontinuous_iff_eq_zero` in `Proposition_3_8`, which already
  has the exact textbook interface of this item;
- mathlib `LowerSemicontinuous` together with the chapter's closed-convex recall surface in
  `Theorem_3_1_4`.

Best owner abstraction:
- the imported source-facing owner `unitDiskBoundaryExtension`.

Primitive data:
- the boundary datum `φ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℝ`;
- the owner construction `unitDiskBoundaryExtension φ`.

Derived API:
- the open-disk value theorem already proved in `Proposition_3_8`;
- the convexity/effective-domain companion theorem
  `unitDiskBoundaryExtension_convex_and_effectiveDomain`;
- the lower-semicontinuity criterion
  `unitDiskBoundaryExtension_lowerSemicontinuous_iff_eq_zero`.

Source/core/bridge triage:
- source-facing: the unit-disk boundary extension and its vanishing criterion on the unit circle;
- core/canonical: `LowerSemicontinuous` for `WithTop ℝ`-valued functions;
- bridge/view: the owner-level convexity and effective-domain companion theorem from
  `Proposition_3_8`.

This file previously rebuilt the same owner and theorem family under duplicate local declarations.
Since `Proposition_3_8` already provides the correct source-facing owner in the minimal chapter
closure, this item is recall-only and reuses that canonical chapter declaration directly. -/

recall unitDiskBoundaryExtension_lowerSemicontinuous_iff_eq_zero
