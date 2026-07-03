import Mathlib
import Mathlib.Order.Filter.Extr
import Mathlib.Order.SaddlePoint
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_6_28_1 (from Chap06) -/
noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace OrdinaryConvexProgram

-- Proof sketch: closedness of the objective and constraint data on the closed constraint set makes
-- the indicator-extended weighted objective attached to `(lam, μ)` a closed proper convex
-- function. The singleton hypothesis says that this weighted objective has a unique minimizer
-- `xBar`. Section 27 then gives existence of an optimal solution of `P`, while
-- `weightedObjectiveComplementaryMinimizerSet_eq_optimalSolutionSet` identifies every optimal
-- solution with a weighted-objective minimizer, forcing every optimal solution to equal `xBar`.
/-- Corollary 6.28.1: if `(lam, μ)` is a Kuhn--Tucker vector for an ordinary convex program `P`,
the objective and all constraint functions are closed on the closed constraint set, and the
weighted objective attached to `(lam, μ)` has canonical minimum set `{xBar}`, then `xBar` is the
unique optimal solution of `P`, expressed as equality between the canonical
`optimalSolutionSet` and the singleton `{xBar}`. -/
theorem optimalSolutionSet_eq_singleton_of_minimumSet_weightedObjective_eq_singleton
    {r s : ℕ} (P : OrdinaryConvexProgram ℝ E EReal r s)
    (lam : Fin r → ℝ) (μ : Fin s → ℝ) (hKT : P.IsKuhnTuckerVector lam μ)
    (hC_closed : IsClosed P.constraintSet)
    (hobjective_closed : LowerSemicontinuous P.objective)
    (hinequality_closed : ∀ i, LowerSemicontinuous (P.inequality i))
    (hequality_closed : ∀ j, LowerSemicontinuous (P.equality j))
    (xBar : E)
    (hminimum : minimumSet (P.weightedObjective lam μ) = {xBar}) :
    P.optimalSolutionSet = {xBar} := sorry

end OrdinaryConvexProgram

end

/-! ### Definition_6_28_1 (from Chap06) -/
universe u v w

noncomputable section

section

open scoped Rockafellar

variable {𝕜 : Type v} {E : Type u} {β : Type w}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.1 introduces an ordinary convex program: a constraint set `C`
  together with a convex objective on `C`, convex inequality functions on `C`, and affine
  equality functions on `C`. The source data is only the tuple of values on `C`.
- `core/canonical`: the owner predicates are `ConvexOn 𝕜 C F` and `affOn[𝕜](F, C)` on ambient
  functions. Their canonical ambient layer needs only the scalar/order data required by those
  owners (`Semiring 𝕜`, `PartialOrder 𝕜`, additive ambient spaces with scalar action). Chapter 1
  already fixes `affOn[𝕜](·, ·)` as the project's canonical affine-on-a-set owner.
- `bridge/view`: the source indexing `i = 1, …, r` and `i = r + 1, …, m` is represented by two
  index owners (inequality/equality blocks), with defaults `Fin r` and `Fin s` for textbook
  numbering. Restricted data on `C` is compared to the ambient owners through the canonical
  extension bridge `Function.extendByZero`, exactly as other restricted-data files in the project
  use namespaced subtype-extension owners (`Function.extendByTop`, `Function.toWithTopBotOn`).

Domain-style sampling used here:
- `ConvexOn` and `ConcaveOn` from mathlib's convex-function API;
- the conjunction projections from the project affine-on-set owner notation `affOn[𝕜](·, ·)` in
  `ConvexAnalysis_Rockafellar_1970/Chap01/Definition_4_3.lean`;
- `Function.extend_val_apply` / `Function.extend_val_apply'` from mathlib's subtype-extension API;
- the restricted-data owner bridge `Function.extendByTop` in
  `ConvexAnalysis_Rockafellar_1970/Chap04/Definition_17_2_2.lean`;
- the set-affine bridge pattern in
  `ConvexAnalysis_Rockafellar_1970/Chap01/Definition_4_3.lean` and
  `ConvexAnalysis_Rockafellar_1970/Chap01/Remark_4_5_0.lean`.

Primitive data vs derived API:
- primitive data: the constraint set together with the objective, inequality family, and equality
  family as functions on the subtype `C`;
- primitive owner properties: convexity of the objective and inequalities, and affinity of the
  equalities, recorded through `ConvexOn`/`affOn[𝕜](·, ·)` on the canonical ambient extension of the
  restricted data;
- derived API: the fact that the constraint set is convex, recovered from the owner's
  `ConvexOn` fields instead of stored primitively as duplicate data.

Layer target: `source-facing`. This item defines a genuine program object, so it stays a
structure; the later feasible set, perturbation function, and Kuhn-Tucker data should be derived
from this owner rather than stored primitively.
-/

/-- Extend a function on a subtype domain to the ambient type by `0` off the subtype. -/
def Function.extendByZero {C : Set E} [Zero β] (f : C → β) : E → β :=
  Function.extend Subtype.val f (fun _ ↦ 0)

/-- On the defining constraint set, `extendZero f` agrees with `f`. -/
@[simp] theorem Function.extendByZero_apply_of_mem
    {C : Set E} [Zero β] (f : C → β) {x : E} (hx : x ∈ C) :
    Function.extendByZero f x = f ⟨x, hx⟩ := by
  simpa [Function.extendByZero] using
    (Function.extend_val_apply (g := f) (j := fun _ : E ↦ (0 : β)) hx)

/-- Off the defining constraint set, `extendZero f` takes the value `0`. -/
@[simp] theorem Function.extendByZero_apply_of_notMem
    {C : Set E} [Zero β] (f : C → β) {x : E}
    (hx : x ∉ C) :
    Function.extendByZero f x = 0 := by
  simpa [Function.extendByZero] using
    (Function.extend_val_apply' (g := f) (j := fun _ : E ↦ (0 : β)) hx)

/-- On the subtype domain, `Function.extendByZero` agrees with the original function. -/
@[simp] theorem Function.extendByZero_apply
    {C : Set E} [Zero β] (f : C → β) (x : C) :
    Function.extendByZero f x = f x := by
  simp [Function.extendByZero]

/-- Restricting `Function.extendByZero` back to the subtype recovers the original function. -/
@[simp] theorem Function.extendByZero_comp_subtype_val
    {C : Set E} [Zero β] (f : C → β) :
    Function.extendByZero f ∘ (Subtype.val : C → E) = f := by
  funext x
  simp [Function.extendByZero]

/-- Backward-compatible short name for `Function.extendByZero`. -/
abbrev extendZero {C : Set E} [Zero β] (f : C → β) : E → β :=
  Function.extendByZero f

/-- On the defining constraint set, `extendZero f` agrees with `f`. -/
@[simp] theorem extendZero_apply {C : Set E} [Zero β] (f : C → β) (x : C) :
    extendZero f x = f x := by
  simp [extendZero]

/-- Off the defining constraint set, `extendZero f` takes the value `0`. -/
@[simp] theorem extendZero_apply_of_notMem {C : Set E} [Zero β] (f : C → β) {x : E}
    (hx : x ∉ C) :
    extendZero f x = 0 := by
  simpa [extendZero] using (Function.extendByZero_apply_of_notMem (f := f) hx)

variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]

/-- Definition 6.28.1: an ordinary convex program consists of a constraint set together with a
`β`-valued objective, finitely many convex inequalities, and finitely many affine equalities, all
given only on that constraint set. The indexing owners are explicit type parameters
`inequalityIndex` and `equalityIndex`, required to be finite and cardinality-matched to `r` and
`s`. Defaults `Fin r` and `Fin s` retain the textbook block numbering surface when ordered
positions are desired. -/
structure OrdinaryConvexProgram (𝕜 : Type v) (E : Type u) (β : Type w)
    [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]
    [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]
    (r s : ℕ)
    (inequalityIndex : Type := Fin r)
    (equalityIndex : Type := Fin s)
    [Fintype inequalityIndex] [Fintype equalityIndex]
    [Fact (Fintype.card inequalityIndex = r)]
    [Fact (Fintype.card equalityIndex = s)] where
  constraintSet : Set E
  objective : constraintSet → β
  objective_convexOn : ConvexOn 𝕜 constraintSet (Function.extendByZero objective)
  inequality : inequalityIndex → constraintSet → β
  inequality_convexOn (i : inequalityIndex) :
    ConvexOn 𝕜 constraintSet (Function.extendByZero (inequality i))
  equality : equalityIndex → constraintSet → β
  equality_affOn (i : equalityIndex) :
    affOn[𝕜](Function.extendByZero (equality i), constraintSet)

namespace OrdinaryConvexProgram

instance (n : ℕ) : Fact (Fintype.card (Fin n) = n) := ⟨Fintype.card_fin n⟩

variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

abbrev objectiveAmbient : E → β :=
  Function.extendByZero P.objective

abbrev inequalityAmbient (i : ι) : E → β :=
  Function.extendByZero (P.inequality i)

abbrev equalityAmbient (i : κ) : E → β :=
  Function.extendByZero (P.equality i)

/-- On the constraint set, `P.objectiveAmbient` agrees with `P.objective`. -/
@[simp] theorem objectiveAmbient_apply (x : P.constraintSet) :
    P.objectiveAmbient x = P.objective x := by
  simp [OrdinaryConvexProgram.objectiveAmbient]

/-- On the constraint set, `P.inequalityAmbient i` agrees with `P.inequality i`. -/
@[simp] theorem inequalityAmbient_apply (i : ι) (x : P.constraintSet) :
    P.inequalityAmbient i x = P.inequality i x := by
  simp [OrdinaryConvexProgram.inequalityAmbient]

/-- On the constraint set, `P.equalityAmbient i` agrees with `P.equality i`. -/
@[simp] theorem equalityAmbient_apply (i : κ) (x : P.constraintSet) :
    P.equalityAmbient i x = P.equality i x := by
  simp [OrdinaryConvexProgram.equalityAmbient]

/-- Each equality constraint in an ordinary convex program is convex on the constraint set. -/
theorem equality_convexOn (i : κ) :
    ConvexOn 𝕜 P.constraintSet (P.equalityAmbient i) :=
  (P.equality_affOn i).1

/-- Each equality constraint in an ordinary convex program is concave on the constraint set. -/
theorem equality_concaveOn (i : κ) :
    ConcaveOn 𝕜 P.constraintSet (P.equalityAmbient i) :=
  (P.equality_affOn i).2

/-- Bridge view: each equality constraint is convex on `P.constraintSet` as an ambient map. -/
theorem equality_convexOn_ambient (i : κ) :
    ConvexOn 𝕜 P.constraintSet (P.equalityAmbient i) :=
  P.equality_convexOn i

/-- Bridge view: each equality constraint is concave on `P.constraintSet` as an ambient map. -/
theorem equality_concaveOn_ambient (i : κ) :
    ConcaveOn 𝕜 P.constraintSet (P.equalityAmbient i) :=
  P.equality_concaveOn i

/-- The constraint set of an ordinary convex program is convex. -/
theorem constraintSet_convex :
    Convex 𝕜 P.constraintSet :=
  P.objective_convexOn.1

end OrdinaryConvexProgram

end

/-! ### Proposition_6_28_1 (from Chap06) -/
noncomputable section

open scoped Pointwise Rockafellar

universe u v

namespace Function

section

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {ι : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 6.28.1 is the Slater-qualified subdifferential formula for the
  constrained objective from Definition 6.28.8.
- `core/canonical`: the owner abstractions already upstream are
  `Function.toWithTopBotOn` on the finite feasible-set owner for the constrained objective,
  `strictConvexInequalitySolutionSetOn` for the strict feasible region on the same finite
  subsystem, and
  `_root_.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom` for the
  intrinsic finite-sum subdifferential equality on the dual owner.
- `bridge/view`: the proposition rewrites the single constrained-objective owner into the sum of
  the lifted objective subdifferential and the individual indicator-sublevel subdifferentials, all
  on the intrinsic dual owner.

Domain-style sampling used here:
- the Definition 6.28.8 owner surface
  `Function.toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f)`;
- `strictConvexInequalitySolutionSetOn` from `Chap04.Text_21_0_1`;
- `weakConvexInequalitySolutionSetOn` from `Chap04.Text_21_0_1`, the canonical Chapter 21 owner
  reused by Definition 6.28.8;
- `_root_.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom` from
  `Chap05.Theorem_23_8`.

Primitive data vs derived API:
- primitive source data: a `𝕜`-valued objective `f₀`, a finite subsystem `s`, a family of
  `𝕜`-valued constraints `f i`, their convexity on `s`, and the Chapter 21 strict feasible region
  for those inequalities;
- derived API: the intrinsic dual-owner subdifferential decomposition of the constrained
  objective.

Abstraction audit:
- codomain/scalar layer: this proposition lives on the ordered-field scalar layer `𝕜` and
  `WithTopBot 𝕜`, not on a concrete `ℝ` specialization.

Layer target: `source-facing`, but on the intrinsic dual-owner subdifferential layer and with the
feasible-set surface routed through the existing Chapter 21 weak/strict finite-subsystem owners
instead of the fully expanded mixed-relation feasible-set expression.
-/

-- Proof sketch: rewrite the constrained objective from Definition 6.28.8 as the finite sum of
-- `f₀.toWithTopBot` and the indicator functions of the individual sublevel sets
-- `{y | f i y ≤ 0}`. Use the finite-sum formula
-- `_root_.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom` from
-- Theorem 23.8.
-- A point of the Chapter 21 strict feasible set lies in the relative interior of every sublevel
-- set because each `f i` is finite and convex on `Set.univ`, hence continuous, so the common
-- relative-interior qualification holds.
/-- Proposition 6.28.1: if the finite-valued objective `f₀` and the constraint functions `f i`
indexed by the finite subsystem `s` are convex on all of `E`, and the Chapter 21 strict feasible
set of those inequalities is nonempty, then the subdifferential of the Definition 6.28.8
`toWithTopBotOn` owner on `weakConvexInequalitySolutionSetOn s f` equals the Minkowski sum of the
intrinsic dual-owner subdifferential of the objective lift and the intrinsic dual-owner
subdifferentials of the individual constraint indicators. -/
theorem
    subdifferentialAt_toWithTopBotOn_weakConvexInequalitySolutionSetOn_eq
    (f₀ : E → 𝕜) (s : Finset ι) (f : ι → E → 𝕜)
    (hf₀_convex : ConvexOn 𝕜 Set.univ f₀)
    (hf_convex : ∀ i ∈ s, ConvexOn 𝕜 Set.univ (f i))
    (hstrict : (strictConvexInequalitySolutionSetOn s f).Nonempty)
    (x : E) :
    (∂ (toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f)) at x) =
      (∂ f₀.toWithTopBot at x) +
        s.sum (fun i ↦ (∂ (δ[𝕜](· | {y : E | f i y ≤ 0})) at x)) := sorry

end

end Function

/-! ### Theorem_6_28_1 (from Chap06) -/
noncomputable section

universe u v

open scoped BigOperators

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type*} [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β] [Top β]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.28.1 fixes a Kuhn--Tucker multiplier pair `(lam, μ)` for an ordinary
  convex program `P`, forms the weighted objective
  `f₀ + Σ λᵢ fᵢ + Σ μⱼ hⱼ`, and characterizes the optimal solutions of `P`.
- `core/canonical`: the Chapter 6 owners already present are `P.feasibleSet`,
  `P.feasibleObjective`, `P.optimalValue`, `P.weightedObjective`, the Kuhn--Tucker owner
  `P.IsKuhnTuckerVector`, and `Function.IsProper` together with the effective-domain notation
  `dom(·)`.
- `bridge/view`: the theorem is kept source-facing as a set equality between the ambient points
  satisfying the weighted-objective minimizer and complementary-slackness conditions and the
  ambient optimal-solution set.

Domain-style sampling used here:

- `IsMinOn` from mathlib's order-extrema API as the canonical attained-minimum owner;
- `Function.IsProper` and `dom(·)` from Chapter 1;
- `OrdinaryConvexProgram`, `extendZero`, `P.feasibleSet`, `P.feasibleObjective`,
  `P.optimalValue`, `P.weightedObjective`, and `P.IsKuhnTuckerVector` from
  Definitions 6.28.1--6.28.3.

Primitive data vs derived API:

- primitive data: the program `P` and the multiplier blocks `(lam, μ)`;
- primitive owner-side objects: the feasible region, the feasible objective, and the ambient
  extension of the weighted objective;
- derived source-facing sets: the canonical minimum set
  `minimumSet (P.weightedObjective lam μ)`, the complementary minimizer subset, and the
  ambient optimal-solution set.

Layer target: `source-facing`. The numbered item is a direct optimal-solution characterization, so
the theorem is stated directly about sets of points in `E` rather than through a surrogate data
package.
-/

variable {r s : ℕ} {ι : Type} {κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-- The subset `D₀` from Theorem 6.28.1: weighted-objective minimizers whose inequality
constraints satisfy the zero-multiplier weak inequalities, whose nonzero-multiplier inequality
constraints are active, and whose equality constraints vanish. -/
def weightedObjectiveComplementaryMinimizerSet
    (lam : ι → 𝕜) (μ : κ → 𝕜) : Set E :=
  {x | x ∈ minimumSet (P.weightedObjective lam μ) ∧
      (∀ i, lam i = 0 → extendZero (P.inequality i) x ≤ 0) ∧
      (∀ i, lam i ≠ 0 → extendZero (P.inequality i) x = 0) ∧
      (∀ j, extendZero (P.equality j) x = 0)}

-- Proof sketch: unfold `weightedObjectiveComplementaryMinimizerSet`; the four conjuncts record
-- exactly the ambient minimizer condition, the weak inequalities attached to zero multipliers, the
-- active-constraint equalities attached to nonzero multipliers, and the equality constraints.
/-- Membership in `weightedObjectiveComplementaryMinimizerSet` is the conjunction of the
weighted-objective minimizer condition with the side conditions defining `D₀` in Theorem 6.28.1.
-/
@[simp] theorem mem_weightedObjectiveComplementaryMinimizerSet
    (lam : ι → 𝕜) (μ : κ → 𝕜) (x : E) :
    x ∈ P.weightedObjectiveComplementaryMinimizerSet lam μ ↔
      x ∈ minimumSet (P.weightedObjective lam μ) ∧
        (∀ i, lam i = 0 → extendZero (P.inequality i) x ≤ 0) ∧
        (∀ i, lam i ≠ 0 → extendZero (P.inequality i) x = 0) ∧
        (∀ j, extendZero (P.equality j) x = 0) := sorry

end OrdinaryConvexProgram

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace OrdinaryConvexProgram

variable {r s : ℕ} {ι : Type} {κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

-- Proof sketch: use the Kuhn--Tucker owner fields for `(lam, μ)` to obtain properness of the
-- weighted objective, effective-domain identification with `P.constraintSet`, strict lower
-- boundedness of the weighted-objective infimum, and equality of that infimum with the feasible
-- optimal value. Compare weighted and feasible objectives on feasible points, and characterize the
-- equality case by the zero/nonzero multiplier side conditions together with the equality
-- constraints. This identifies `D₀` with the ambient image of the minimizer set of
-- `P.feasibleObjective`.
/-- Theorem 6.28.1: if `(lam, μ)` satisfies the Kuhn--Tucker conditions for an ordinary convex
program `P`, then the points where the weighted objective attains its ambient infimum and the
zero/nonzero multiplier side conditions hold are exactly the optimal solutions of `P`. -/
theorem weightedObjectiveComplementaryMinimizerSet_eq_optimalSolutionSet
    (lam : ι → 𝕜) (μ : κ → 𝕜)
    (hKT : P.IsKuhnTuckerVector lam μ) :
    P.weightedObjectiveComplementaryMinimizerSet lam μ = P.optimalSolutionSet := sorry

end OrdinaryConvexProgram

end

/-! ### Corollary_6_28_2 (from Chap06) -/
noncomputable section

open scoped BigOperators

universe u v w

namespace Function

section

variable {𝕜 : Type v} {E : Type u} {β : Type w} {ι : Type*}
variable [AddCommMonoid β]

/-- Textbook notation for the finite Lagrange combination
`f₀ + ∑ i ∈ s, λ i • f i`. -/
scoped notation "L[" s "](" f₀ ", " f ", " lam ")" =>
  (fun x ↦ f₀ x + ∑ i ∈ s, lam i • f i x)

section Minimizer

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [PartialOrder β] [IsOrderedAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]

-- Proof sketch: this is exactly `StrictConvexOn.eq_of_isMinOn` specialized to
-- `fun x ↦ f₀ x + ∑ i ∈ s, lam i • f i x`.
/-- If a Lagrange combination is strictly convex on `C`, then any two minimizers on `C` coincide. -/
theorem eq_of_isMinOn_lagrangeCombination
    {C : Set E} {s : Finset ι} {f₀ : E → β} {f : ι → E → β} {lam : ι → 𝕜}
    (hstrict : StrictConvexOn 𝕜 C (L[s](f₀, f, lam)))
    {x y : E}
    (hx : x ∈ C) (hy : y ∈ C)
    (hminx : IsMinOn (L[s](f₀, f, lam)) C x)
    (hminy : IsMinOn (L[s](f₀, f, lam)) C y) :
    x = y :=
  hstrict.eq_of_isMinOn hminx hminy hx hy

end Minimizer

section Strict

variable [CommSemiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [PartialOrder β] [IsOrderedCancelAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]

-- Proof sketch: each summand `fun x ↦ λ i • f i x` is convex on `C` by `ConvexOn.smul` because
-- `λ i ≥ 0`. Finite sums of convex functions are convex on `C`, and adding that convex sum to the
-- strictly convex objective `f₀` yields a strictly convex function via
-- `StrictConvexOn.add_convexOn`.
/-- A Lagrange combination is strictly convex on `C` when its objective term is strictly convex on
`C` and every weighted constraint term has a nonnegative coefficient and a convex underlying
function. -/
theorem strictConvexOn_lagrangeCombination_of_nonneg
    {C : Set E} {s : Finset ι} {f₀ : E → β} {f : ι → E → β} {lam : ι → 𝕜}
    (hf₀ : StrictConvexOn 𝕜 C f₀)
    (hf : ∀ i ∈ s, ConvexOn 𝕜 C (f i))
    (hLam : ∀ i ∈ s, 0 ≤ lam i) :
    StrictConvexOn 𝕜 C (L[s](f₀, f, lam)) := sorry

end Strict

section StrictMinimizer

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [PartialOrder β] [IsOrderedCancelAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]

-- Proof sketch: first apply `strictConvexOn_lagrangeCombination_of_nonneg` to obtain strict
-- convexity of `fun x ↦ f₀ x + ∑ i ∈ s, lam i • f i x` on `C`. Then apply
-- `eq_of_isMinOn_lagrangeCombination`.
/-- Corollary 6.28.2: if `f₀` is strictly convex on `C`, then the Lagrange combination
`h = f₀ + ∑ i ∈ s, λ i • f i` with nonnegative coefficients and convex summands is strictly convex
on `C`; consequently, if the infimum of `h` on `C` is attained, the minimizing point is unique. -/
theorem eq_of_isMinOn_lagrangeCombination_of_nonneg
    {C : Set E} {s : Finset ι} {f₀ : E → β} {f : ι → E → β} {lam : ι → 𝕜}
    (hf₀ : StrictConvexOn 𝕜 C f₀)
    (hf : ∀ i ∈ s, ConvexOn 𝕜 C (f i))
    (hLam : ∀ i ∈ s, 0 ≤ lam i)
    {x y : E}
    (hx : x ∈ C) (hy : y ∈ C)
    (hminx : IsMinOn (L[s](f₀, f, lam)) C x)
    (hminy : IsMinOn (L[s](f₀, f, lam)) C y) :
    x = y :=
  let hstrict : StrictConvexOn 𝕜 C (L[s](f₀, f, lam)) :=
    strictConvexOn_lagrangeCombination_of_nonneg
      (C := C) (s := s) (f₀ := f₀) (f := f) (lam := lam) hf₀ hf hLam
  eq_of_isMinOn_lagrangeCombination
    (hstrict := hstrict)
    hx hy hminx hminy

end StrictMinimizer

end

end Function

/-! ### Definition_6_28_2 (from Chap06) -/
universe u v w

noncomputable section

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

/-- Canonical split index type for the inequality and equality blocks of `P`. -/
abbrev ConstraintIndex (_ : OrdinaryConvexProgram 𝕜 E β r s ι κ) : Type := ι ⊕ κ

/-- Ambient constraint family attached to `P`, built from the canonical zero-extension of each
source inequality/equality branch. -/
def constraint (P : OrdinaryConvexProgram 𝕜 E β r s ι κ) : P.ConstraintIndex → E → β :=
  Sum.elim P.inequalityAmbient P.equalityAmbient

@[simp] theorem constraint_inl (i : ι) :
    P.constraint (Sum.inl i) = P.inequalityAmbient i := by
  rfl

@[simp] theorem constraint_inr (j : κ) :
    P.constraint (Sum.inr j) = P.equalityAmbient j := by
  rfl

/-- The canonical equality-index subset inside `P.ConstraintIndex`: exactly the right branch of
the split index type. -/
abbrev equalityIndices (P : OrdinaryConvexProgram 𝕜 E β r s ι κ) : Set P.ConstraintIndex :=
  Set.range Sum.inr

@[simp] theorem inl_not_mem_equalityIndices (i : ι) :
    Sum.inl i ∉ P.equalityIndices := by
  simp [OrdinaryConvexProgram.equalityIndices]

@[simp] theorem inr_mem_equalityIndices (j : κ) :
    Sum.inr j ∈ P.equalityIndices := by
  simp [OrdinaryConvexProgram.equalityIndices]

/-- Mixed relation map attached to `P`: equality on the right block and weak inequality on the
left block, expressed through the Chapter 1 canonical owner `LinearConstraintRelation.eqOn`. -/
abbrev relation
    (P : OrdinaryConvexProgram 𝕜 E β r s ι κ) : P.ConstraintIndex → LinearConstraintRelation :=
  LinearConstraintRelation.eqOn P.equalityIndices

@[simp] theorem relation_inl (i : ι) :
    P.relation (Sum.inl i) = .le := by
  simp [OrdinaryConvexProgram.relation, LinearConstraintRelation.eqOn]

@[simp] theorem relation_inr (j : κ) :
    P.relation (Sum.inr j) = .eq := by
  simp [OrdinaryConvexProgram.relation, LinearConstraintRelation.eqOn]

/-- Definition 6.28.2: the feasible solution set of an ordinary convex program is the ambient
constraint set together with the nonpositive inequality constraints and zero equality constraints.
The source index owners are `ι` and `κ` (defaulting to textbook `Fin r` and `Fin s`), and the
constraint family is routed through the Chapter 1 homogeneous mixed-feasible-set owner via the
canonical evaluation pairing on ambient functions. -/
def feasibleSet : Set E :=
  P.constraintSet ∩
    LinearConstraintRelation.homogeneousFeasibleSet β
      P.relation
      P.constraint

-- Proof sketch: unfold `feasibleSet`; membership in the intersection gives the ambient
-- constraint witness `hxC : x ∈ P.constraintSet` plus the mixed homogeneous relation family.
-- Then rewrite each ambient value through the constrained representative `⟨x, hxC⟩`.
/-- Intrinsic owner-level view of feasibility: a point is feasible iff it has a witness
`hxC : x ∈ P.constraintSet` such that every inequality value at `⟨x, hxC⟩` is nonpositive and
every equality value at `⟨x, hxC⟩` is zero. -/
theorem mem_feasibleSet (x : E) :
    x ∈ P.feasibleSet ↔
      ∃ hxC : x ∈ P.constraintSet,
        (∀ i, P.inequality i ⟨x, hxC⟩ ≤ 0) ∧
        (∀ j, P.equality j ⟨x, hxC⟩ = 0) := by
  constructor
  · intro hx
    have hxAmbient :
        x ∈ P.constraintSet ∧
          (∀ i, P.inequalityAmbient i x ≤ 0) ∧
          (∀ j, P.equalityAmbient j x = 0) := by
      simpa [OrdinaryConvexProgram.feasibleSet, OrdinaryConvexProgram.constraint] using hx
    refine ⟨hxAmbient.1, ?_, ?_⟩
    · intro i
      have hix : P.inequalityAmbient i x ≤ 0 := hxAmbient.2.1 i
      have hix_eq : P.inequalityAmbient i x = P.inequality i ⟨x, hxAmbient.1⟩ := by
        simpa using (P.inequalityAmbient_apply i ⟨x, hxAmbient.1⟩)
      exact hix_eq ▸ hix
    · intro j
      have hjx : P.equalityAmbient j x = 0 := hxAmbient.2.2 j
      have hjx_eq : P.equalityAmbient j x = P.equality j ⟨x, hxAmbient.1⟩ := by
        simpa using (P.equalityAmbient_apply j ⟨x, hxAmbient.1⟩)
      exact hjx_eq ▸ hjx
  · rintro ⟨hxC, hxI, hxE⟩
    have hxAmbient :
        x ∈ P.constraintSet ∧
          (∀ i, P.inequalityAmbient i x ≤ 0) ∧
          (∀ j, P.equalityAmbient j x = 0) := by
      refine ⟨hxC, ?_, ?_⟩
      · intro i
        have hix : P.inequalityAmbient i x = P.inequality i ⟨x, hxC⟩ := by
          simpa using (P.inequalityAmbient_apply i ⟨x, hxC⟩)
        exact hix ▸ hxI i
      · intro j
        have hjx : P.equalityAmbient j x = P.equality j ⟨x, hxC⟩ := by
          simpa using (P.equalityAmbient_apply j ⟨x, hxC⟩)
        exact hjx ▸ hxE j
    simpa [OrdinaryConvexProgram.feasibleSet, OrdinaryConvexProgram.constraint] using hxAmbient

-- Proof sketch: this is the ambient bridge form obtained by unfolding `feasibleSet`.
/-- Ambient bridge view of feasibility through the canonical ambient owners
`P.inequalityAmbient` and `P.equalityAmbient`. -/
@[simp] theorem mem_feasibleSet_ambient (x : E) :
    x ∈ P.feasibleSet ↔
      x ∈ P.constraintSet ∧
        (∀ i, P.inequalityAmbient i x ≤ 0) ∧
        (∀ j, P.equalityAmbient j x = 0) := by
  simp [OrdinaryConvexProgram.feasibleSet, OrdinaryConvexProgram.constraint]

/-- Every feasible point of an ordinary convex program belongs to its ambient constraint set. -/
theorem feasible_mem_constraintSet (x : P.feasibleSet) :
    x.1 ∈ P.constraintSet :=
  by
    rcases (P.mem_feasibleSet x.1).1 x.2 with ⟨hxC, -, -⟩
    exact hxC

section Convexity

variable [Module 𝕜 β] [IsOrderedAddMonoid β] [PosSMulMono 𝕜 β]

-- Proof sketch: `P.constraintSet` is convex by `P.constraintSet_convex`. For each inequality
-- index `i`, the sublevel set `{x ∈ P.constraintSet | P.inequalityAmbient i x ≤ 0}` is
-- convex by `ConvexOn.convex_le` applied to `P.inequality_convexOn i`. For each equality index
-- `j`, the zero set is the intersection of a convex sublevel set and a convex superlevel set,
-- using the convex and concave consequences of `P.equality_affOn j`. Intersecting these convex
-- sets yields `P.feasibleSet`.
/-- The feasible solution set of an ordinary convex program is convex. -/
theorem feasibleSet_convex :
    Convex 𝕜 P.feasibleSet := sorry

end Convexity

end OrdinaryConvexProgram

end

/-! ### Proposition_6_28_2 (from Chap06) -/
noncomputable section

open scoped Pointwise Rockafellar

universe u v

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 6.28.2 identifies the subdifferential of the indicator of the
  inequality set `C = {y | f y ≤ 0}` with the normal cone to `C`, and then gives the standard
  three-case formula at boundary, interior, and exterior points of that sublevel set. The
  boundary clause is source-faithful only with a strict-feasibility witness `∃ y, f y < 0`,
  since without such a point the positive-hull formula fails at minimizers.
- `core/canonical`: the owner abstractions already present in the project are
  `_root_.subdifferentialAt`, indicator notation `δ[𝕜](· | C)`, and the normal-cone owner
  `N[𝕜, N](x | C)`.
- `bridge/view`: the first clause is exactly the generic indicator-function/normal-cone theorem
  from Example 23.0.7, and the boundary clause is the zero-level specialization of the Chapter 23
  owner `normalCone_sublevel_eq_closure_cone_subdifferentialAt`.

Domain-style sampling used here:
- `_root_.subdifferentialAt_indicatorFunction_eq_normalCone` from
  `Chap05.Example_23_0_7`;
- `_root_.normalCone_sublevel_eq_closure_cone_subdifferentialAt` from
  `Chap05.Theorem_23_7`;
- `_root_.subdifferentialAt` from `Chap05.Definition_23_0_6`;
- `normalCone` from `Chap01.Definition_2_7_10`.

Primitive data vs derived API:
- primitive source data: a finite-valued constraint function `f : E → 𝕜` and the associated
  sublevel set `{y | f y ≤ 0}`;
- main owner statement already upstream: the subdifferential of the indicator of a set is its
  normal cone;
- derived companion API: the boundary formula at `f x = 0`, plus the interior/exterior indicator
  clauses with source-facing strict/interior and strict/exterior corollaries.

Topology language note:
- the interior clause below stays in ambient `interior`, not `intrinsicInterior`, because it is a
  pure local-openness statement that does not require convexity of the sublevel set. Promoting it
  to relative/intrinsic interior would force extra convexity data not needed by the proposition.

Layer target: `source-facing`, stated directly on the chapter's canonical pairing/dual owners.
-/

section IndicatorSublevelNormalCone

variable {𝕜 : Type v} [CommRing 𝕜] [TopologicalSpace 𝕜] [Preorder 𝕜] [AddLeftMono 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {N : Type (max u v)} [AddCommMonoid N] [Module 𝕜 N] [HasLinearPairing E N 𝕜]

-- Proof sketch: this is the `C = {y | f y ≤ 0}` specialization of the canonical indicator/normal
-- cone theorem from Example 23.0.7.
/-- Proposition 6.28.2, indicator/normal-cone clause at the canonical pairing-owner layer: for the
zero-sublevel set `C = {y | f y ≤ 0}`, the subdifferential of the indicator is the normal cone. -/
theorem subdifferentialAt_indicator_sublevel_eq_normalCone
    (f : E → 𝕜) (x : E) :
    ∂[N] (δ[𝕜](· | {y : E | f y ≤ 0}))(x) =
      N[𝕜, N](x | {y : E | f y ≤ 0}) := by
  simpa using (_root_.subdifferentialAt_indicatorFunction_eq_normalCone
    (N := N) (C := {y : E | f y ≤ 0}) (x := x))

end IndicatorSublevelNormalCone

section IndicatorSublevelBoundary

variable {𝕜 : Type v} [NormedField 𝕜] [LinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [AddLeftMono 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {N : Type (max u v)} [AddCommMonoid N] [Module 𝕜 N] [TopologicalSpace N]
variable [HasLinearPairing E N 𝕜]

-- Proof sketch: this is the canonical boundary formula from Theorem 23.7, specialized to the
-- zero sublevel set `{y | f y ≤ 0}` and rewritten using `f x = 0`.
/-- Pairing-owner boundary clause for Proposition 6.28.2: at a boundary point `x` with `f x = 0`,
the indicator subdifferential equals the closure of the cone generated by the intrinsic
subdifferential of `f.toWithBotTop` at `x`, provided convexity, subdifferentiability at `x`, and
nonminimality at `x` for `f.toWithBotTop`. -/
theorem subdifferentialAt_indicator_sublevel_eq_closure_cone_of_eq_zero_of_notMin
    (f : E → 𝕜) (hf_convex : f.toWithBotTop.IsConvex 𝕜) {x : E} (hx : f x = 0)
    (hsub : (∂[N]f.toWithBotTop(x)).Nonempty)
    (hnotmin : ¬ IsMinOn f.toWithBotTop Set.univ x) :
    ∂[N] (δ[𝕜](· | {y : E | f y ≤ 0}))(x) =
      closure (cone[𝕜] (∂[N]f.toWithBotTop(x)) : Set N) := by
  sorry

-- Proof sketch: if there is a strict feasible point `y` with `f y < 0`, then a boundary point
-- `x` with `f x = 0` is not a minimizer of `f.toWithBotTop`; then apply the previous theorem.
/-- At a boundary point `x` of the zero sublevel set of a finite-valued convex function, provided
there exists a strict feasible point `y` with `f y < 0` and `f` is subdifferentiable at `x`, the
indicator subdifferential is the closure of the cone generated by the intrinsic subdifferential of
`f.toWithBotTop` at `x`. -/
theorem subdifferentialAt_indicator_sublevel_eq_closure_cone_subdifferentialAt_of_eq_zero
    (f : E → 𝕜) (hf_convex : ConvexOn 𝕜 Set.univ f) {x : E} (hx : f x = 0)
    (hsub : (∂[N]f.toWithBotTop(x)).Nonempty)
    (hstrict : ∃ y : E, f y < 0) :
    ∂[N] (δ[𝕜](· | {y : E | f y ≤ 0}))(x) =
      closure (cone[𝕜] (∂[N]f.toWithBotTop(x)) : Set N) := by
  have hf_convex' : f.toWithBotTop.IsConvex 𝕜 := by
    simpa using Function.isConvex_coe_of_convexOn_univ hf_convex
  have hnotmin : ¬ IsMinOn f.toWithBotTop Set.univ x := by
    intro hmin
    rcases hstrict with ⟨y, hy⟩
    have hxy : f.toWithBotTop x ≤ f.toWithBotTop y := hmin (by simp : y ∈ Set.univ)
    have hxy_bot : ((0 : 𝕜) : WithBotTop 𝕜) ≤ (f y : WithBotTop 𝕜) := by
      simpa [Function.toWithBotTop, hx] using hxy
    have hxy_scalar : (0 : 𝕜) ≤ f y := WithBotTop.coe_le_coe.mp hxy_bot
    exact (not_le_of_gt hy) hxy_scalar
  have hboundary :=
    subdifferentialAt_indicator_sublevel_eq_closure_cone_of_eq_zero_of_notMin
      (N := N) (f := f) hf_convex' (x := x) hx hsub hnotmin
  exact hboundary

end IndicatorSublevelBoundary

section IndicatorSublevelInterior

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [AddLeftMono 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- Proof sketch: at an interior point of the sublevel set, indicator subgradients satisfy opposite
-- inequalities in every direction; testing at `x + ε • u` and `x + ε • (-u)` forces each dual
-- evaluation to vanish, so the subdifferential is exactly `{0}`.
/-- Interior clause for Proposition 6.28.2: at interior points of the zero sublevel set, the
indicator subdifferential is the singleton `{0}` in the canonical dual owner. -/
theorem subdifferentialAt_indicator_sublevel_eq_singleton_zero_of_mem_interior
    (f : E → 𝕜) {x : E} (hx_int : x ∈ interior {y : E | f y ≤ 0}) :
    ∂[StrongDual 𝕜 E] (δ[𝕜](· | {y : E | f y ≤ 0}))(x) =
      ({0} : Set (StrongDual 𝕜 E)) := by
  let C : Set E := {y : E | f y ≤ 0}
  have hxC : x ∈ C := interior_subset hx_int
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨?_, ?_⟩
  · refine (_root_.mem_subdifferentialAt_indicatorFunction_iff
      (C := C) (x := x) (xStar := (0 : StrongDual 𝕜 E))).2 ?_
    refine ⟨hxC, ?_⟩
    intro z hz
    change (0 : 𝕜) ≤ 0
    exact le_rfl
  · intro xStar hxStar
    rcases (_root_.mem_subdifferentialAt_indicatorFunction_iff
        (C := C) (x := x) (xStar := xStar)).1 hxStar with ⟨_, hineq⟩
    ext u
    rcases (Set.forall_exists_pos_add_smul_mem_of_mem_interior (𝕜 := 𝕜)
      (C := C) (z := x) hx_int u) with ⟨ε₁, hε₁, hε₁mem⟩
    rcases (Set.forall_exists_pos_add_smul_mem_of_mem_interior (𝕜 := 𝕜)
      (C := C) (z := x) hx_int (-u)) with ⟨ε₂, hε₂, hε₂mem⟩
    have hle₁ : ε₁ * xStar u ≤ 0 := by
      have h := hineq (x + ε₁ • u) hε₁mem
      have hpair : (⟪(x + ε₁ • u) - x, xStar⟫ₚ : 𝕜) = ε₁ * xStar u := by
        calc
          (⟪(x + ε₁ • u) - x, xStar⟫ₚ : 𝕜) = xStar ((x + ε₁ • u) - x) := by
            rfl
          _ = xStar (ε₁ • u) := by abel_nf
          _ = ε₁ * xStar u := by simp
      exact hpair ▸ h
    have hle₂ : (-ε₂) * xStar u ≤ 0 := by
      have h := hineq (x + ε₂ • (-u)) hε₂mem
      have hpair : (⟪(x + ε₂ • (-u)) - x, xStar⟫ₚ : 𝕜) = (-ε₂) * xStar u := by
        calc
          (⟪(x + ε₂ • (-u)) - x, xStar⟫ₚ : 𝕜) = xStar ((x + ε₂ • (-u)) - x) := by
            rfl
          _ = xStar (ε₂ • (-u)) := by abel_nf
          _ = ε₂ * xStar (-u) := by simp
          _ = ε₂ * (-xStar u) := by simp
          _ = (-ε₂) * xStar u := by ring
      exact hpair ▸ h
    have hnonpos : xStar u ≤ 0 := by
      nlinarith [hε₁, hle₁]
    have hnonneg : 0 ≤ xStar u := by
      nlinarith [hε₂, hle₂]
    exact le_antisymm hnonpos hnonneg

-- Proof sketch: `f x < 0` and continuity imply `x ∈ interior {y | f y ≤ 0}`. Apply the interior
-- theorem above.
/-- Source-facing strict-interior corollary for Proposition 6.28.2: if `f` is continuous and
`f x < 0`, then the indicator subdifferential at `x` is `{0}`. -/
theorem subdifferentialAt_indicator_sublevel_eq_singleton_zero_of_lt_zero
    [OrderTopology 𝕜] (f : E → 𝕜) (hcont : Continuous f) {x : E} (hx : f x < 0) :
    ∂[StrongDual 𝕜 E] (δ[𝕜](· | {y : E | f y ≤ 0}))(x) =
      ({0} : Set (StrongDual 𝕜 E)) := by
  have hx_int : x ∈ interior {y : E | f y ≤ 0} := by
    have hOpenLt : IsOpen {y : E | f y < 0} := by
      simpa using hcont.isOpen_preimage (Set.Iio (0 : 𝕜)) isOpen_Iio
    have hxInteriorLt : x ∈ interior {y : E | f y < 0} := by
      exact mem_interior_iff_mem_nhds.mpr (IsOpen.mem_nhds hOpenLt hx)
    refine interior_mono ?_ hxInteriorLt
    intro y hy
    exact le_of_lt hy
  exact subdifferentialAt_indicator_sublevel_eq_singleton_zero_of_mem_interior
    (f := f) (x := x) hx_int

end IndicatorSublevelInterior

section IndicatorSublevelExterior

variable {𝕜 : Type v} [CommRing 𝕜] [TopologicalSpace 𝕜] [Preorder 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {N : Type (max u v)} [HasPairing E N 𝕜]

-- Proof sketch: when `x ∉ {y | f y ≤ 0}`, the indicator membership criterion forces a
-- contradiction for any purported subgradient.
/-- Exterior clause for Proposition 6.28.2: if `x` is outside the zero sublevel set, the indicator
subdifferential is empty. -/
theorem subdifferentialAt_indicator_sublevel_eq_empty_of_notMem
    (f : E → 𝕜) {x : E} (hx : x ∉ {y : E | f y ≤ 0}) :
    ∂[N] (δ[𝕜](· | {y : E | f y ≤ 0}))(x) = (∅ : Set N) := by
  ext xStar
  constructor
  · intro hxsub
    rcases (_root_.mem_subdifferentialAt_indicatorFunction_iff
        (C := {y : E | f y ≤ 0}) (x := x) (xStar := xStar)).1 hxsub with ⟨hxC, _⟩
    exact False.elim <| hx hxC
  · intro hxempty
    exact False.elim hxempty

-- Proof sketch: `0 < f x` implies `x ∉ {y | f y ≤ 0}`; apply the previous theorem.
/-- Source-facing exterior corollary for Proposition 6.28.2: if `0 < f x`, then the indicator
subdifferential is empty. -/
theorem subdifferentialAt_indicator_sublevel_eq_empty_of_pos
    (f : E → 𝕜) {x : E} (hx : 0 < f x) :
    ∂[N] (δ[𝕜](· | {y : E | f y ≤ 0}))(x) = (∅ : Set N) := by
  have hx_not_mem : x ∉ {y : E | f y ≤ 0} := by
    intro hxC
    exact (not_le_of_gt hx) hxC
  exact subdifferentialAt_indicator_sublevel_eq_empty_of_notMem
    (f := f) (x := x) hx_not_mem

end IndicatorSublevelExterior

end Function

/-! ### Theorem_6_28_2 (from Chap06) -/
noncomputable section

open scoped BigOperators

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type*} [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]

namespace OrdinaryConvexProgram

variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-- The canonical finite pairing on the intrinsic perturbation index owner
`P.ConstraintIndex = ι ⊕ κ`. -/
def perturbationPairing
    (uStar u : P.ConstraintIndex → 𝕜) : WithBotTop 𝕜 :=
  ((∑ i : P.ConstraintIndex, uStar i * u i : 𝕜) : WithBotTop 𝕜)

-- Proof sketch: unfold `perturbationPairing`; the finite sum vanishes at the zero perturbation
-- vector.
/-- The intrinsic multiplier-perturbation pairing vanishes at the zero perturbation vector. -/
@[simp] theorem perturbationPairing_zero
    (uStar : P.ConstraintIndex → 𝕜) :
    P.perturbationPairing uStar 0 = 0 := sorry

end OrdinaryConvexProgram

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.28.2 characterizes Kuhn--Tucker multipliers by a global inequality
  for the perturbation value function `p(u)`.
- `core/canonical`: the Chapter 6 owner already present for the multiplier condition is
  `P.IsKuhnTuckerVector`, together with the existing optimal-value owner `P.optimalValue`.
- `bridge/view`: the source writes vectors in one perturbation space. The project's intrinsic
  owner for that space is `P.ConstraintIndex → 𝕜`, with split multipliers `(lam, μ)` mapped into
  it by the canonical bridge `P.splitMultiplier lam μ`.

Domain-style sampling used here:

- `P.optimalValue` and `P.IsKuhnTuckerVector` from `Definition_6_28_3`;
- finite sums over `P.ConstraintIndex` from mathlib's `BigOperators` API;
- indexed infima over subtype-defined feasible sets, as in the Chapter 6 optimal-value owner.

Primitive data vs derived API:

- primitive data: the program `P`, the split multiplier pair `(lam, μ)`, and one intrinsic
  perturbation vector `u : P.ConstraintIndex → 𝕜`;
- source-facing bridge objects: the scalar-threshold perturbation value
  `P.perturbationValue u`, the intrinsic pairing `P.perturbationPairing`, and the split-to-
  intrinsic bridge `P.splitMultiplier`;
- main owner statement: the equivalence between `P.IsKuhnTuckerVector lam μ` and the global lower
  support inequality for `P.perturbationValue`.

Layer target: `source-facing`, stated directly on the existing Kuhn--Tucker owner with only the
minimal bridge data needed to express the perturbation inequality in the book's terms.
-/

variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]

variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

/-- Bridge owner: the split multiplier blocks `(lam, μ)` viewed as one intrinsic multiplier map on
`P.ConstraintIndex`. -/
abbrev splitMultiplier (lam : ι → 𝕜) (μ : κ → 𝕜) :
    P.ConstraintIndex → 𝕜 :=
  Sum.elim lam μ

/-- The scalar-threshold perturbation value `p(u)` of `P`, obtained by taking the infimum of the
objective over points of the constraint set satisfying the perturbed inequality and equality
levels encoded by `u`. -/
def perturbationValue (u : P.ConstraintIndex → 𝕜) : WithBotTop 𝕜 :=
  ⨅ x : {x : P.constraintSet //
      (∀ i : ι, P.inequality i x ≤ u (Sum.inl i)) ∧
      (∀ j : κ, P.equality j x = u (Sum.inr j))},
    P.objective x.1

-- Proof sketch: compare the subtype indexing `P.perturbationValue 0` with the feasible-point
-- subtype defining `P.optimalValue`; both describe exactly the points of `P.constraintSet`
-- satisfying the zero right-hand-side inequality and equality constraints.
/-- At the zero perturbation vector, the perturbation value is the unperturbed optimal value. -/
theorem perturbationValue_zero_eq_optimalValue :
    P.perturbationValue 0 = P.optimalValue := sorry

-- Proof sketch: use `P.perturbationValue_zero_eq_optimalValue` to rewrite the source term `p(0)`
-- as the optimal value in the defining Kuhn--Tucker owner. Then compare the infimum of the
-- weighted objective in `P.IsKuhnTuckerVector lam μ` with the family of perturbed infima
-- `P.perturbationValue u`, so that the Kuhn--Tucker condition becomes exactly the global
-- support inequality `p(u) + ⟨(lam, μ), u⟩ ≥ p(0)` for every perturbation `u`.
/-- Theorem 6.28.2: if the unperturbed perturbation value `p(0)` is finite, then a split
multiplier pair `(lam, μ)` is a Kuhn--Tucker vector for `P` if and only if every intrinsic
perturbation vector `u : P.ConstraintIndex → 𝕜` satisfies
`p(u) + ⟨splitMultiplier(lam, μ), u⟩ ≥ p(0)`. -/
theorem isKuhnTuckerVector_iff_forall_perturbationValue_add_perturbationPairing_ge_at_zero
    (lam : ι → 𝕜) (μ : κ → 𝕜)
    (hfinite : ⊥ < P.perturbationValue 0 ∧ P.perturbationValue 0 < ⊤) :
    P.IsKuhnTuckerVector lam μ ↔
      ∀ u : P.ConstraintIndex → 𝕜,
        P.perturbationValue u + P.perturbationPairing (P.splitMultiplier lam μ) u ≥
          P.perturbationValue 0 := sorry

end OrdinaryConvexProgram

end

/-! ### Corollary_6_28_3 (from Chap06) -/
noncomputable section

universe u v

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.28.3 is the pure-inequality specialization of the Kuhn--Tucker
  existence theorem: there are no equality constraints, and the Slater-type hypothesis is a point
  of the constraint set where every inequality is strict.
- `core/canonical`: the existing Chapter 6 owners are `P.optimalValue` and
  `P.IsKuhnTuckerVector`.
- `bridge/view`: in the case `s = 0`, the textbook Kuhn--Tucker vector is expressed by the
  existing split owner with the unique empty equality block `Fin.elim0`.

Domain-style sampling used here:
- `OrdinaryConvexProgram.IsKuhnTuckerVector` from `Definition_6_28_3`;
- `OrdinaryConvexProgram.optimalValue` from `Definition_6_28_3`;
- `OrdinaryConvexProgram` from `Definition_6_28_1`, via `Definition_6_28_3`;
- `OrdinaryConvexProgram.exists_kuhnTuckerVector_of_nonaffine_strict_feasibility`
  from `Theorem_6_28_3`;
- the canonical empty-index function `Fin.elim0` from mathlib's `Fin` API.

Primitive data vs derived API:
- primitive source data: a program `P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) m 0`, a feasible
  optimal value, and a point of `P.constraintSet` where every inequality is strict;
- derived API: existence of a Kuhn--Tucker vector with no equality multiplier block.

Layer target: `source-facing`, stated directly on the existing ordinary-convex-program owners.
-/

section StrictFeasibility

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {m : ℕ} (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) m 0 (Fin m) (Fin 0))

-- Proof sketch: in the pure-inequality case `s = 0`, weak feasibility is immediate from strict
-- inequalities, the equality block is vacuous, and strictness on all inequalities implies
-- strictness on the nonaffine subfamily.
/-- A point of `P.constraintSet` satisfying all inequalities strictly yields the nonaffine
strict-feasibility qualification used in Theorem 6.28.3. -/
theorem hasStrictlyFeasiblePointOnNonaffineInequalities_of_exists_strict_inequality_point
    (hstrict : ∃ x : P.constraintSet, ∀ i, P.inequality i x < 0) :
    P.HasStrictlyFeasiblePointOnNonaffineInequalities := by
  rcases hstrict with ⟨x, hxstrict⟩
  have hxFeasible : x.1 ∈ P.feasibleSet := by
    refine (P.mem_feasibleSet x.1).2 ⟨x.2, ?_, ?_⟩
    · intro i
      exact (hxstrict i).le
    · intro j
      exact Fin.elim0 j
  refine ⟨⟨x.1, hxFeasible⟩, ?_⟩
  intro i _
  simpa [extendZero_apply] using hxstrict i

end StrictFeasibility

section Existence

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {m : ℕ} (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) m 0 (Fin m) (Fin 0))

-- Proof sketch: first convert the source hypothesis to
-- the corresponding strict-feasibility hypothesis in the pure-inequality case of
-- Theorem 6.28.3. Then specialize the resulting Kuhn--Tucker vector to the unique empty equality
-- multiplier block (written as `0` at the theorem surface).
/-- Corollary 6.28.3: if an ordinary convex program has only inequality constraints, its optimal
value is not `-∞`, and some point of the constraint set satisfies every inequality strictly, then
the program admits a Kuhn--Tucker vector. -/
theorem exists_kuhnTuckerVector_of_strict_inequality_point
    (hopt : P.optimalValue ≠ ⊥)
    (hstrict : ∃ x : P.constraintSet, ∀ i, P.inequality i x < 0) :
    ∃ lam : Fin m → 𝕜, P.IsKuhnTuckerVector lam 0 := by
  have hstrict_nonaffine : P.HasStrictlyFeasiblePointOnNonaffineInequalities :=
    P.hasStrictlyFeasiblePointOnNonaffineInequalities_of_exists_strict_inequality_point hstrict
  rcases exists_kuhnTuckerVector_of_nonaffine_strict_feasibility
      (P := P) hopt hstrict_nonaffine with ⟨lam, μ, hKT⟩
  have hμ : μ = 0 := Subsingleton.elim _ _
  refine ⟨lam, ?_⟩
  cases hμ
  exact hKT

end Existence

end OrdinaryConvexProgram

end

/-! ### Definition_6_28_3 (from Chap06) -/
noncomputable section

universe u v w

open scoped BigOperators

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type w} [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.3 introduces the notion of a Kuhn--Tucker coefficient vector
  for an ordinary convex program `(P)`.
- `core/canonical`: the helper owners live on the ambient program owner
  `OrdinaryConvexProgram 𝕜 E β r s` (for feasible/optimal-solution and weighted-objective
  interfaces), and the Kuhn--Tucker owner layer is stated on the same owner with the extra
  codomain structure it actually uses (`Top`/`Bot` + complete-lattice infimum). This reuses the
  Chapter 6 minimizer owner `minimumSet`, the effective-domain owner `dom(·)`, and the properness
  owner `Function.IsProper`.
- `bridge/view`: the textbook coefficient vector `(λ₁, …, λ_m)` is represented canonically by two
  blocks of scalar coefficients indexed by the intrinsic finite owners of `P`: `λ : ι → 𝕜` for
  inequality constraints and `μ : κ → 𝕜` for equality constraints.

Domain-style sampling used here:
- `minimumSet` from Definition 6.27.3 as the canonical owner for minimizers;
- `Function.IsProper` and `dom(·)` from Chapter 1;
- `Function.extend` for extending subtype-defined functions to the ambient space by `⊤`;
- the finite-sum owner surface from mathlib's `BigOperators` notation, used for the weighted
  objective branch;
- `OrdinaryConvexProgram` and `extendZero` from Definition 6.28.1.

Primitive data vs derived API:
- primitive source-facing data: the multiplier blocks `(λ, μ)`;
- primitive owner-side objects: the optimal value of `P` and the ambient `⊤`-extension of the
  weighted objective `f₀ + ∑ λᵢ fᵢ + ∑ μⱼ hⱼ`;
- derived API: the chapter owner `minimumSet` applied to the feasible objective, the ambient
  optimal-solution set obtained from that minimum set and its pointwise membership predicate, the
  codomain-valued saddle Lagrangian
  built from the weighted-objective extension, and the Kuhn--Tucker property itself, recorded as
  a `Prop`-valued structure whose fields express nonnegativity of the inequality multipliers,
  properness of the weighted objective, identification of its effective domain with the
  constraint set, strict lower boundedness of its infimum, and equality of that infimum with the
  optimal value of `(P)`.

Layer target: `source-facing`. This item defines a genuine new property of multiplier data for an
ordinary convex program, so it is exposed directly on the existing owner
`OrdinaryConvexProgram` rather than through a surrogate package.
-/

variable {r s : ℕ} {ι : Type} {κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-- The objective of `P`, restricted to its feasible-set subtype. -/
def feasibleObjective (x : P.feasibleSet) : β :=
  P.objective ⟨x.1, P.feasible_mem_constraintSet x⟩

section CompleteLatticeCodomain

variable [CompleteLattice β]

/-- The optimal value of `P`, defined as the infimum of the objective over feasible points. -/
def optimalValue : β :=
  ⨅ x : P.feasibleSet, P.feasibleObjective x

/-- The optimal value of `P` is the infimum of its feasible objective. -/
theorem optimalValue_eq_iInf :
    P.optimalValue = ⨅ x : P.feasibleSet, P.feasibleObjective x :=
  rfl

end CompleteLatticeCodomain

section TopCodomain

variable [Top β]

/-- The ambient `⊤`-extension of the weighted objective attached to the multiplier blocks
`(λ, μ)`. -/
def weightedObjective (lam : ι → 𝕜) (μ : κ → 𝕜) : E → β :=
  Function.extend Subtype.val
    (fun x : P.constraintSet ↦
      P.objective x +
        (∑ i, lam i • P.inequality i x) +
          ∑ j, μ j • P.equality j x)
    ⊤

/-- On the constraint set, the ambient weighted objective agrees with the source formula
`f₀ + ∑ λᵢ fᵢ + ∑ μⱼ hⱼ`. -/
@[simp] theorem weightedObjective_of_mem_constraintSet
    (lam : ι → 𝕜) (μ : κ → 𝕜) {x : E} (hx : x ∈ P.constraintSet) :
    P.weightedObjective lam μ x =
      P.objective ⟨x, hx⟩ +
        (∑ i, lam i • P.inequality i ⟨x, hx⟩) +
          ∑ j, μ j • P.equality j ⟨x, hx⟩ := by
  change
    Function.extend Subtype.val
      (fun y : P.constraintSet ↦
        P.objective y +
          (∑ i, lam i • P.inequality i y) +
            ∑ j, μ j • P.equality j y)
      (fun _ : E ↦ (⊤ : β))
      x =
      P.objective ⟨x, hx⟩ +
        (∑ i, lam i • P.inequality i ⟨x, hx⟩) +
          ∑ j, μ j • P.equality j ⟨x, hx⟩
  simpa using Function.extend_val_apply hx

/-- Off the constraint set, the ambient weighted objective takes the value `⊤`. -/
@[simp] theorem weightedObjective_of_notMem_constraintSet
    (lam : ι → 𝕜) (μ : κ → 𝕜) {x : E} (hx : x ∉ P.constraintSet) :
    P.weightedObjective lam μ x = ⊤ := by
  simp [weightedObjective, Function.extend, hx]

end TopCodomain

end OrdinaryConvexProgram

namespace OrdinaryConvexProgram

section OptimalSolution

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type w} [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]
variable {r s : ℕ} {ι : Type} {κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-- The ambient set of optimal solutions of `P`, obtained by viewing the canonical minimum set of
the feasible objective in the ambient space. -/
def optimalSolutionSet : Set E :=
  Subtype.val '' minimumSet P.feasibleObjective

/-- An ambient point is an optimal solution of `P` exactly when it belongs to the ambient image of
the canonical minimum set of the feasible objective. -/
def IsOptimalSolution (x : E) : Prop :=
  x ∈ P.optimalSolutionSet

/-- Membership in `optimalSolutionSet` is the ambient optimal-solution predicate. -/
@[simp] theorem mem_optimalSolutionSet (x : E) :
    x ∈ P.optimalSolutionSet ↔ P.IsOptimalSolution x :=
  Iff.rfl

/-- An ambient point is optimal exactly when its feasible representative belongs to the canonical
minimum set of the feasible objective. -/
@[simp] theorem isOptimalSolution_iff (x : E) :
    P.IsOptimalSolution x ↔
      ∃ hx : x ∈ P.feasibleSet, ⟨x, hx⟩ ∈ minimumSet P.feasibleObjective := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using hy⟩
  · rintro ⟨hx, hmin⟩
    exact ⟨⟨x, hx⟩, hmin, rfl⟩

/-- An optimal solution is feasible. -/
theorem IsOptimalSolution.feasible {x : E} (hx : P.IsOptimalSolution x) :
    x ∈ P.feasibleSet := by
  rcases (P.isOptimalSolution_iff x).1 hx with ⟨hx, -⟩
  exact hx

/-- An optimal solution, viewed on the feasible-set subtype, belongs to the canonical minimum set
of the feasible objective. -/
theorem IsOptimalSolution.mem_minimumSet {x : E} (hx : P.IsOptimalSolution x) :
    ⟨x, hx.feasible⟩ ∈ minimumSet P.feasibleObjective := by
  rcases (P.isOptimalSolution_iff x).1 hx with ⟨_, hmin⟩
  simpa using hmin

/-- An optimal solution minimizes the feasible objective on the feasible-set subtype. -/
theorem IsOptimalSolution.isMin {x : E} (hx : P.IsOptimalSolution x) :
    IsMinOn P.feasibleObjective Set.univ ⟨x, hx.feasible⟩ :=
  hx.mem_minimumSet

end OptimalSolution

section SaddleLagrangian

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type w} [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β] [Top β] [Bot β]
variable {r s : ℕ} {ι : Type} {κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-- The codomain-valued Lagrangian used in the Kuhn--Tucker saddle-point formulation: on the
constraint set it is the weighted objective for nonnegative inequality multipliers and `⊥` for
inadmissible multipliers, while off the constraint set it is `⊤`. -/
def saddleLagrangian : ((ι → 𝕜) × (κ → 𝕜)) → E → β :=
  let _ : DecidablePred (fun x : E ↦ x ∈ P.constraintSet) := Classical.decPred _
  let _ : DecidablePred (fun u : (ι → 𝕜) × (κ → 𝕜) ↦ ∀ i, 0 ≤ u.1 i) :=
    Classical.decPred _
  fun u x ↦
    if _hnonneg : ∀ i, 0 ≤ u.1 i then
      P.weightedObjective u.1 u.2 x
    else if x ∈ P.constraintSet then
      ⊥
    else
      ⊤

end SaddleLagrangian

section KuhnTucker

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type w} [AddCommMonoid β] [CompleteLattice β] [SMul 𝕜 β]
variable {r s : ℕ} {ι : Type} {κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-- Definition 6.28.3: a split multiplier pair `(λ, μ)` is a vector of Kuhn--Tucker
coefficients for an ordinary convex program `P` when the inequality multipliers `λ` are
nonnegative, the ambient `⊤`-extension of the weighted objective
`f₀ + ∑ λᵢ fᵢ + ∑ μⱼ hⱼ` is proper with effective domain exactly `P.constraintSet`, its infimum
is strictly above `⊥`, and that infimum is the optimal value of `P`. Properness already supplies
the finite-point upper bound `inf < ⊤`. This is the source's coefficient vector
`(λ₁, …, λ_m)` split into the `r` inequality block and the `s` equality block from Definition
6.28.1. -/
class IsKuhnTuckerVector (lam : ι → 𝕜) (μ : κ → 𝕜) : Prop where
  nonneg : ∀ i, 0 ≤ lam i
  proper_weightedObjective : (P.weightedObjective lam μ).IsProper
  effectiveDomain_eq :
    dom(P.weightedObjective lam μ) = P.constraintSet
  infimum_bot_lt :
    ⊥ < (⨅ x : E, P.weightedObjective lam μ x)
  infimum_eq_optimalValue :
    (⨅ x : E, P.weightedObjective lam μ x) = P.optimalValue

/-- Bundled multiplier owner for Definition 6.28.3: the source multiplier vector is represented by
`u = (lam, μ)` and satisfies the Kuhn--Tucker conditions as one intrinsic object. -/
abbrev IsKuhnTuckerMultiplier (u : (ι → 𝕜) × (κ → 𝕜)) : Prop :=
  P.IsKuhnTuckerVector u.1 u.2

/-- Fieldwise constructor for the bundled Kuhn--Tucker multiplier owner. -/
theorem isKuhnTuckerMultiplier_of_fields
    (u : (ι → 𝕜) × (κ → 𝕜))
    (h_nonneg : ∀ i, 0 ≤ u.1 i)
    (h_proper_weightedObjective : (P.weightedObjective u.1 u.2).IsProper)
    (h_effectiveDomain_eq :
      dom(P.weightedObjective u.1 u.2) = P.constraintSet)
    (h_infimum_bot_lt :
      ⊥ < (⨅ x : E, P.weightedObjective u.1 u.2 x))
    (h_infimum_eq_optimalValue :
      (⨅ x : E, P.weightedObjective u.1 u.2 x) = P.optimalValue) :
    P.IsKuhnTuckerMultiplier u := by
  exact
    ⟨h_nonneg, h_proper_weightedObjective, h_effectiveDomain_eq, h_infimum_bot_lt,
      h_infimum_eq_optimalValue⟩

/-- Bridge between the bundled and split Kuhn--Tucker owners. -/
@[simp] theorem isKuhnTuckerMultiplier_iff_isKuhnTuckerVector
    (u : (ι → 𝕜) × (κ → 𝕜)) :
    P.IsKuhnTuckerMultiplier u ↔ P.IsKuhnTuckerVector u.1 u.2 :=
  Iff.rfl

/-- Bridge reindexed by split multipliers. -/
@[simp] theorem isKuhnTuckerVector_iff_isKuhnTuckerMultiplier
    (lam : ι → 𝕜) (μ : κ → 𝕜) :
    P.IsKuhnTuckerVector lam μ ↔ P.IsKuhnTuckerMultiplier (lam, μ) :=
  Iff.rfl

/-- The five defining source conditions assemble into the canonical owner
`P.IsKuhnTuckerVector lam μ`. This is the owner-level bridge for downstream statements that are
still phrased field-by-field. -/
theorem isKuhnTuckerVector_of_fields
    (lam : ι → 𝕜) (μ : κ → 𝕜)
    (h_nonneg : ∀ i, 0 ≤ lam i)
    (h_proper_weightedObjective : (P.weightedObjective lam μ).IsProper)
    (h_effectiveDomain_eq :
      dom(P.weightedObjective lam μ) = P.constraintSet)
    (h_infimum_bot_lt :
      ⊥ < (⨅ x : E, P.weightedObjective lam μ x))
    (h_infimum_eq_optimalValue :
      (⨅ x : E, P.weightedObjective lam μ x) = P.optimalValue) :
    P.IsKuhnTuckerVector lam μ := sorry

namespace IsKuhnTuckerVector

variable {P} {lam : ι → 𝕜} {μ : κ → 𝕜}

/-- A Kuhn--Tucker vector canonically supplies properness of its weighted objective. -/
instance instIsProperWeightedObjective [h : P.IsKuhnTuckerVector lam μ] :
    (P.weightedObjective lam μ).IsProper :=
  h.proper_weightedObjective

/-- Properness of the weighted objective forces the Kuhn--Tucker infimum to lie strictly below
`⊤`. -/
theorem infimum_lt_top (h : P.IsKuhnTuckerVector lam μ) :
    (⨅ x : E, P.weightedObjective lam μ x) < ⊤ := by
  rcases h.proper_weightedObjective.nonempty_dom with ⟨x, hx⟩
  exact lt_of_le_of_lt (iInf_le _ x) (mem_effectiveDomain.mp hx)

/-- A Kuhn--Tucker vector forces the weighted-objective infimum to be finite. -/
theorem infimum_finite (h : P.IsKuhnTuckerVector lam μ) :
    ⊥ < (⨅ x : E, P.weightedObjective lam μ x) ∧
      (⨅ x : E, P.weightedObjective lam μ x) < ⊤ :=
  ⟨h.infimum_bot_lt, h.infimum_lt_top⟩

/-- A Kuhn--Tucker vector rewrites the primal optimal value as the weighted-objective infimum. -/
theorem optimalValue_eq_infimum (h : P.IsKuhnTuckerVector lam μ) :
    P.optimalValue = ⨅ x : E, P.weightedObjective lam μ x := sorry

/-- A Kuhn--Tucker vector forces the primal optimal value of the ordinary convex program to be
finite. -/
theorem optimalValue_finite (h : P.IsKuhnTuckerVector lam μ) :
    ⊥ < P.optimalValue ∧ P.optimalValue < ⊤ := by
  rw [← h.infimum_eq_optimalValue]
  exact h.infimum_finite

end IsKuhnTuckerVector

end KuhnTucker

end OrdinaryConvexProgram

end
