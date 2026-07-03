import Mathlib
import Mathlib.Order.WithBotTop
import Mathlib.Tactic.Recall
import Mathlib.Topology.Semicontinuity.Defs

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_29_15 (from Chap06) -/
noncomputable section

universe u v w

namespace Bifunction

open scoped Rockafellar

section

variable {U : Type u} {X : Type v} {α : Type w}
variable [InfSet α] [Zero U]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.15 names the optimal value of the generalized convex program
  attached to a bifunction `F` as the infimum of the objective `F₀`.
- `core/canonical`: the existing owner abstractions are the zero-slice objective `objective F`
  from Definition 6.29.12 and the perturbation-value function `perturbationFunction F` from
  Definition 6.29.1.
- `bridge/view`: the source infimum of `F₀` over the primal variable is exactly both
  `perturbationFunction F 0` and `⨅ x, (F)₀ x`.

Domain-style sampling used here:
- `Bifunction.objective`;
- `Bifunction.objective_apply`;
- `Bifunction.perturbationFunction`;
- `Bifunction.perturbationFunction_apply`.

Primitive data vs derived API:
- primitive source data: the bifunction `F : U → X → α` at the codomain layer where infima are
  available (specialized in Chapter 6 to `WithBotTop` codomains);
- primitive source-facing owner in this file: `optimalValue F`;
- primitive defining formula: `optimalValue F = ⨅ x, (F)₀ x`;
- derived API: the bridge identification `optimalValue F = perturbationFunction F 0`.

Layer target: `source-facing`. This item introduces a genuine piece of chapter vocabulary, so it
gets a direct owner on the existing bifunction data rather than a wrapper package.
-/

/-- Definition 6.29.15: the optimal value of the generalized convex program attached to `F` is
the infimum of the zero-slice objective `F₀`. -/
def optimalValue (F : U → X → α) : α :=
  ⨅ x : X, (F)₀ x

/-- The optimal value is the perturbation value at the zero perturbation. -/
@[simp]
theorem optimalValue_eq_perturbationFunction_zero
    (F : U → X → α) :
    optimalValue F = perturbationFunction F 0 :=
  by
    simpa [optimalValue] using (perturbationFunction_zero_eq_iInf (F := F)).symm

/-- The optimal value is the infimum of the objective `F₀` over the primal variable. -/
@[simp]
theorem optimalValue_eq_iInf
    (F : U → X → α) :
    optimalValue F = ⨅ x : X, (F)₀ x :=
  rfl

end

end Bifunction

/-! ### Definition_6_29_16 (from Chap06) -/
noncomputable section

universe u v w

namespace Bifunction

open scoped Rockafellar

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [Zero U] [Top β] [LT β]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.16 introduces the feasible solutions of the generalized convex
  program `(P)` as the points of the effective domain of the zero-slice objective `F₀`.
- `core/canonical`: the existing owners are the Chapter 6 zero-slice objective
  `Bifunction.objective` from Definition 6.29.12 and the Chapter 1 effective-domain owner
  `dom(·)` from Definition 4.4.
- `bridge/view`: the textbook inequality `F₀(x) < +∞` is exactly membership in
  `dom((F)₀)`.

Domain-style sampling used here:
- `Bifunction.objective`;
- `Bifunction.objective_apply`;
- `effectiveDomain`, notation `dom(·)`, and `mem_effectiveDomain`.

Primitive data vs derived API:
- primitive source-facing owner: `feasibleSet F`;
- canonical defining owner expression: `dom((F)₀)`;
- downstream membership/value API should reuse the canonical Chapter 1 bridge
  `mem_effectiveDomain` on `dom((F)₀)` rather than a parallel local theorem.

Layer target: `source-facing`. This item introduces genuine chapter vocabulary for the primal
feasible set, but it should be defined directly from the existing owners rather than through a new
program wrapper.
-/

/-- Definition 6.29.16: the feasible solutions of the generalized convex program attached to a
bifunction `F` are the points of the effective domain of its objective function `F₀`. -/
def feasibleSet (F : U → X → β) : Set X :=
  dom((F)₀)

/-- A point is feasible exactly when its objective value is strictly below `⊤`. -/
@[simp] theorem mem_feasibleSet {F : U → X → β} {x : X} :
    x ∈ feasibleSet F ↔ (F)₀ x < ⊤ := by
  simp [feasibleSet]

end

end Bifunction

/-! ### Definition_6_29_17 (from Chap06) -/
noncomputable section

universe u v w

namespace Bifunction

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.17 says that the generalized convex program `(P)` is
  consistent exactly when it has at least one feasible solution, equivalently when the feasible-set
  owner `feasibleSet F = dom((F)₀)` is nonempty.
- `core/canonical`: the Chapter 6 consistency owner already exists as `Bifunction.IsConsistent`
  from Definition 6.29.1, and Definition 6.29.8 provides the source-facing bifunction-domain
  owner `dom F`.
- `bridge/view`: Definition 6.29.16 introduced the feasible-set owner `Bifunction.feasibleSet`;
  this file bridges it first to `(0 : U) ∈ dom F`, then exposes the thin
  `dom((F)₀)` companion theorem via definitional unfolding.

Domain-style sampling used here:
- `Bifunction.IsConsistent`;
- `Bifunction.dom`;
- `Bifunction.feasibleSet`;
- `Bifunction.objective`;
- `Bifunction.isConsistent_iff_zero_mem_dom`.

Primitive data vs derived API:
- primitive owner: `IsConsistent F`;
- source-facing domain bridge: `(0 : U) ∈ dom F`;
- derived feasible-set bridge: nonemptiness of `feasibleSet F`;
- derived companion view: nonemptiness of `dom((F)₀)`.

Layer target: `core/canonical recall/use`, with one source-facing bridge theorem and one thin
bridge/view companion.
-/

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [Zero U] [Top β] [LT β]

/- Definition 6.29.17: the generalized convex program `(P)` is consistent exactly when the
already existing Chapter 6 owner `Bifunction.IsConsistent F` holds; the present item re-expresses
that owner through the feasible-set language, with `feasibleSet F = dom((F)₀)` available
as the defining expansion. -/
recall IsConsistent

/-- The source-facing bifunction-domain condition at zero is exactly nonemptiness of the feasible
set. -/
@[simp] theorem zero_mem_dom_iff_feasibleSet_nonempty (F : U → X → β) :
    (0 : U) ∈ dom F ↔ (feasibleSet F).Nonempty := by
  simp [mem_dom, feasibleSet, objective]

/-- Definition 6.29.17 (1): ordinary consistency is exactly nonemptiness of the feasible set. -/
theorem isConsistent_iff_feasibleSet_nonempty (F : U → X → β) :
    IsConsistent F ↔ (feasibleSet F).Nonempty := by
  rw [isConsistent_iff_zero_mem_dom, zero_mem_dom_iff_feasibleSet_nonempty]

/-- Definition 6.29.17 (2): ordinary consistency is exactly nonemptiness of the zero-slice domain
`dom((F)₀)`. -/
theorem isConsistent_iff_dom_objective_nonempty (F : U → X → β) :
    IsConsistent F ↔ (dom((F)₀)).Nonempty := by
  rw [isConsistent_iff_feasibleSet_nonempty, feasibleSet]

-- Proof sketch: this is the objective-notation restatement of the primitive consistency bridge
-- `isConsistent_iff_exists_lt_top` from Definition 6.29.1.
/-- Ordinary consistency is exactly existence of a point where the objective `F₀` is finite. -/
theorem isConsistent_iff_exists_objective_lt_top (F : U → X → β) :
    IsConsistent F ↔ ∃ x : X, (F)₀ x < ⊤ := by
  rw [isConsistent_iff_exists_lt_top]
  simp [objective]

end

end Bifunction

/-! ### Definition_6_29_18 (from Chap06) -/
namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.18 gives the perturbation function of the generalized convex
  program `(P)` the source notation `inf F`, surfaced canonically in Lean as `infᵇ(F)`, with
  value at `u` equal to the infimum of the slice `F u`.
- `core/canonical`: the owner abstraction is already the Chapter 6 definition
  `Bifunction.perturbationFunction` from Definition 6.29.1.
- `bridge/view`: the displayed source equation `((inf F)(u) = inf_x F u x)` is already the
  companion owner theorem `Bifunction.perturbationFunction_apply`; the owner-literal
  `sInf (Set.range (F u))` form is `Bifunction.perturbationFunction_apply_eq_sInf_range`.

Domain-style sampling used here:
- `Bifunction.perturbationFunction`;
- `Bifunction.perturbationFunction_apply_eq_sInf_range`;
- `Bifunction.perturbationFunction_apply`.

Primitive data vs derived API:
- primitive data: the bifunction `F`;
- primitive owner: `Bifunction.perturbationFunction F`;
- derived API: the value formula at `u`.

Layer target: `core/canonical`, recall-shaped. This item adds no new mathematical owner beyond the
existing Chapter 6 perturbation-function construction.

Notation decision: the stable source-facing Lean notation is the scoped form `infᵇ(F)` from
Definition 6.29.1, which avoids conflict with Lean's global `inf` identifier while tracking the
textbook `inf F` surface.
-/

/- Definition 6.29.18: Rockafellar's perturbation function `inf F`, surfaced as `infᵇ(F)`, is the
existing Chapter 6 owner `Bifunction.perturbationFunction`. The source's concrete
parameter-space and extended-codomain presentation is a specialization of this codomain-general
owner layer. -/
recall perturbationFunction

/- The owner-literal value formula for `infᵇ(F)` at `u` is the infimum of the corresponding slice
range. -/
recall perturbationFunction_apply_eq_sInf_range

/- The displayed source formula `((inf F)(u) = inf_x F u x)` (Lean: `infᵇ(F) u = inf_x F u x`) is
the existing owner-side
evaluation theorem `Bifunction.perturbationFunction_apply`. -/
recall perturbationFunction_apply

end Bifunction

/-! ### Definition_6_29_19 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v w z

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type z} {α : Type w}
variable [ConditionallyCompleteLattice α] [Add α] [Zero U]
variable [HasPairing U UStar α]

local notation "shiftedInf(" F ", " uStar ")" =>
  (⨅ u : U, perturbationFunction F u + ⟪u, uStar⟫ₚ)

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.19 introduces the notion of a Kuhn--Tucker vector `u⋆` for the
  generalized convex program attached to a bifunction `F`.
- `core/canonical`: the existing Chapter 6 owners are `Bifunction.perturbationFunction` from
  Definition 6.29.1 and `Bifunction.optimalValue` from Definition 6.29.15; under the stronger
  additive hypotheses needed for conjugation, the shifted infimum is the canonical concave
  conjugate owner `concaveConjugate (- perturbationFunction F)`.
- `bridge/view`: at the present weak codomain generality the source displayed infimum identity is
  kept as the primitive owner-side formulation, while the pointwise inequality
  `optimalValue F ≤ perturbationFunction F u + ⟪u, u⋆⟫ₚ` is the equivalent
  supporting-hyperplane reformulation and a later companion theorem bridges the infimum to the
  concave-conjugate owner once negation/subtraction are available.

Domain-style sampling used here:
- `Bifunction.perturbationFunction`;
- `Bifunction.perturbationFunction_apply`;
- `Bifunction.optimalValue`;
- `Bifunction.isConsistent_iff_optimalValue_lt_top`;
- `concaveConjugate` and `concaveConjugate_eq_iInf_pairing_sub`.

Primitive data vs derived API:
- primitive source data: the bifunction `F` and the dual vector `u⋆`;
- primitive owner in this file: `Bifunction.IsKuhnTuckerVector F uStar`, defined by the finiteness
  and equality statement for the infimum over perturbations;
- derived API: the pointwise lower-bound condition and consistency of the generalized convex
  program.

Layer target: `source-facing`. This item introduces a genuine new property of dual vectors for a
generalized convex program, so it is exposed directly on the existing bifunction owner rather than
through a witness package or a restated infimum wrapper.
-/

/-- Definition 6.29.19: a dual vector `u⋆` is a Kuhn--Tucker vector for the generalized convex
program attached to `F` when the infimum of the shifted perturbation values
`perturbationFunction F u + ⟪u, u⋆⟫ₚ` is finite and equals the unperturbed optimal value
`optimalValue F`. The source-facing primitive data are the two-sided finiteness of this shifted
infimum together with the equality, while primal consistency is derived API through
`optimalValue F < ⊤`. -/
class IsKuhnTuckerVector (F : U → X → WithBotTop α) (uStar : UStar) : Prop where
  infimum_mem_Ioo : shiftedInf(F, uStar) ∈ Set.Ioo (⊥ : WithBotTop α) ⊤
  infimum_eq_optimalValue : shiftedInf(F, uStar) = optimalValue F

/-- The Kuhn--Tucker vector set of the generalized convex program attached to `F`. -/
def kuhnTuckerVectorSet (F : U → X → WithBotTop α) : Set UStar :=
  {uStar | IsKuhnTuckerVector F uStar}

scoped[Rockafellar] notation "KT(" F ")" => (Bifunction.kuhnTuckerVectorSet F)

/-- Membership in `KT(F)` is exactly the Kuhn--Tucker-vector predicate. -/
@[simp] theorem mem_kuhnTuckerVectorSet
    {F : U → X → WithBotTop α} {uStar : UStar} :
    uStar ∈ KT(F) ↔ IsKuhnTuckerVector F uStar :=
  Iff.rfl

namespace IsKuhnTuckerVector

variable {F : U → X → WithBotTop α} {uStar : UStar}

/-- Lower finiteness bound from the defining interval-membership field. -/
theorem infimum_bot_lt (h : IsKuhnTuckerVector F uStar) :
    ⊥ < shiftedInf(F, uStar) :=
  h.infimum_mem_Ioo.1

/-- Upper finiteness bound from the defining interval-membership field. -/
theorem infimum_lt_top (h : IsKuhnTuckerVector F uStar) :
    shiftedInf(F, uStar) < ⊤ :=
  h.infimum_mem_Ioo.2

-- Proof sketch: unpack the defining interval-membership field `infimum_mem_Ioo`.
/-- A Kuhn--Tucker vector makes the defining shifted perturbation infimum finite. -/
theorem infimum_finite (h : IsKuhnTuckerVector F uStar) :
    ⊥ < shiftedInf(F, uStar) ∧ shiftedInf(F, uStar) < ⊤ :=
    ⟨h.infimum_bot_lt, h.infimum_lt_top⟩

-- Proof sketch: take the symmetric form of the defining equality
-- `h.infimum_eq_optimalValue`.
/-- A Kuhn--Tucker vector rewrites the optimal value as the defining shifted perturbation
infimum. -/
theorem optimalValue_eq_infimum (h : IsKuhnTuckerVector F uStar) :
    optimalValue F = shiftedInf(F, uStar) :=
    h.infimum_eq_optimalValue.symm

-- Proof sketch: rewrite `optimalValue F` using `h.optimalValue_eq_infimum`, then apply the upper
-- finiteness part of the defining data.
/-- A Kuhn--Tucker vector forces the primal optimal value to lie strictly below `⊤`. -/
theorem optimalValue_lt_top (h : IsKuhnTuckerVector F uStar) :
    optimalValue F < ⊤ :=
    by
      rw [← h.infimum_eq_optimalValue]
      exact h.infimum_lt_top

-- Proof sketch: combine `isConsistent_iff_optimalValue_lt_top` with
-- `IsKuhnTuckerVector.optimalValue_lt_top`.
/-- A Kuhn--Tucker vector forces consistency of the generalized convex program. -/
theorem consistent (h : IsKuhnTuckerVector F uStar) :
    IsConsistent F :=
    (isConsistent_iff_optimalValue_lt_top F).2 h.optimalValue_lt_top

-- Proof sketch: rewrite the defining infimum as `optimalValue F` using
-- `infimum_eq_optimalValue`; then transfer the lower bound from `infimum_bot_lt` and the upper
-- bound from `optimalValue_lt_top`.
/-- A Kuhn--Tucker vector forces the primal optimal value to be finite. -/
theorem optimalValue_finite (h : IsKuhnTuckerVector F uStar) :
    ⊥ < optimalValue F ∧ optimalValue F < ⊤ :=
    by
      refine ⟨?_, h.optimalValue_lt_top⟩
      rw [← h.infimum_eq_optimalValue]
      exact h.infimum_bot_lt

-- Proof sketch: rewrite `optimalValue F` using `h.infimum_eq_optimalValue`. The indexed infimum
-- is below each perturbed value `perturbationFunction F u + ⟪u, uStar⟫ₚ`, yielding the source's
-- equivalent lower-bound inequality.
/-- A Kuhn--Tucker vector satisfies the supporting-hyperplane inequality
`optimalValue F ≤ perturbationFunction F u + ⟪u, u⋆⟫ₚ` for every perturbation `u`. -/
theorem optimalValue_le_perturbationFunction_add_pairing
    (h : IsKuhnTuckerVector F uStar) (u : U) :
    optimalValue F ≤ perturbationFunction F u + ⟪u, uStar⟫ₚ :=
    by
      rw [h.optimalValue_eq_infimum]
      exact iInf_le _ u

end IsKuhnTuckerVector

end

section

variable {U : Type u} {X : Type v} {UStar : Type z} {α : Type w}
variable [ConditionallyCompleteLattice α] [AddCommSemigroup α] [InvolutiveNeg α]
variable [HasPairing U UStar α]

local notation "shiftedInf(" F ", " uStar ")" =>
  (⨅ u : U, perturbationFunction F u + ⟪u, uStar⟫ₚ)

/-- Under commutative addition and involutive negation on `α`, the shifted perturbation infimum
from Definition 6.29.19 is exactly the Chapter 6 concave-conjugate owner
`(- perturbationFunction F)∗`. -/
theorem shiftedInf_eq_concaveConjugate_neg_perturbationFunction
    (F : U → X → WithBotTop α) (uStar : UStar) :
    shiftedInf(F, uStar) = (- perturbationFunction F)∗ uStar := by
  rw [concaveConjugate_eq_iInf_pairing_sub]
  congr with u
  rw [WithBotTop.sub_eq_add_neg]
  calc
    perturbationFunction F u + ⟪u, uStar⟫ₚ
      = -(- perturbationFunction F u) + ⟪u, uStar⟫ₚ := by simp
    _ = ⟪u, uStar⟫ₚ + -(- perturbationFunction F u) := by rw [add_comm]

namespace IsKuhnTuckerVector

variable [Zero U]
variable {F : U → X → WithBotTop α} {uStar : UStar}

/-- Under commutative addition and involutive negation on `α`, a Kuhn--Tucker vector identifies
the canonical concave-conjugate owner `(- perturbationFunction F)∗` at `u⋆` with the primal
optimal value. -/
theorem concaveConjugate_neg_perturbationFunction_eq_optimalValue
    (h : IsKuhnTuckerVector F uStar) :
    (- perturbationFunction F)∗ uStar = optimalValue F := by
  rw [← shiftedInf_eq_concaveConjugate_neg_perturbationFunction, h.infimum_eq_optimalValue]

end IsKuhnTuckerVector

end

end Bifunction

/-! ### Definition_6_29_20 (from Chap06) -/
universe u v w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [Zero U] [Top β] [LT β]

/-- Definition 6.29.20, canonical source-facing statement: the generalized convex program
associated with a bifunction `F` is consistent exactly when the base perturbation belongs to the
bifunction domain. -/
@[simp] theorem isConsistent_iff (F : U → X → β) :
    IsConsistent F ↔ (0 : U) ∈ dom F :=
  isConsistent_iff_zero_mem_dom (F := F)

/-- Bridge to the zero-slice effective-domain wording: the source-facing condition `0 ∈ dom F`
is exactly nonemptiness of `dom (F 0)`. -/
@[simp] theorem isConsistent_iff_dom_zero_nonempty (F : U → X → β) :
    IsConsistent F ↔ (effectiveDomain (F 0)).Nonempty := by
  simp [IsConsistent]

end

end Bifunction

/-! ### Definition_6_29_21 (from Chap06) -/
namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.21 says that the convex program `(P)` attached to a bifunction
  `F` is strongly consistent when the origin belongs to the relative interior of the bifunction
  domain, written in the source as `0 ∈ ri (dom F)`.
- `core/canonical`: the chapter already owns this notion as `Bifunction.IsStronglyConsistent 𝕜 F`
  from Definition 6.29.10.
- `bridge/view`: the source wording is already the canonical specification theorem
  `Bifunction.isStronglyConsistent_iff`, with `ri[𝕜](·)` just the chapter notation for
  `intrinsicInterior`.

Domain-style sampling used here:
- `Bifunction.IsStronglyConsistent` from `Definition_6_29_10`;
- `Bifunction.isStronglyConsistent_iff` from `Definition_6_29_10`;
- `intrinsicInterior` as the mathlib owner for relative interior.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β` with ordered-top codomain data;
- primitive owner: `IsStronglyConsistent 𝕜 F`;
- derived API: the source-facing spelling `(0 : U) ∈ ri[𝕜](dom F)` of the owner theorem.

Layer target: `core/canonical` recall of the owner and its existing specification theorem, with no
parallel local wrapper.
-/

/- Definition 6.29.21: the strong-consistency notion for the convex program associated with a
bifunction `F` is the already existing owner `Bifunction.IsStronglyConsistent 𝕜 F`; the source
condition `0 ∈ ri (dom F)` is rendered here as `(0 : U) ∈ ri[𝕜](dom F)`. -/
recall IsStronglyConsistent

/- Definition 6.29.21, source-facing specification: the canonical owner theorem is already
`Bifunction.isStronglyConsistent_iff`. -/
recall isStronglyConsistent_iff

end Bifunction

/-! ### Definition_6_29_22 (from Chap06) -/
namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.22 says that the convex program `(P)` attached to a bifunction
  `F` is strictly consistent when the origin belongs to the interior of the bifunction domain,
  written in the source as `{0} ∈ int (dom F)`.
- `core/canonical`: the chapter already owns this notion as `Bifunction.IsStrictlyConsistent F`
  from Definition 6.29.10.
- `bridge/view`: the source wording is already the canonical specification theorem
  `Bifunction.isStrictlyConsistent_iff`.

Domain-style sampling used here:
- `Bifunction.IsStrictlyConsistent` from `Definition_6_29_10`;
- `Bifunction.isStrictlyConsistent_iff` from `Definition_6_29_10`;
- `TopologicalSpace.interior` as the canonical owner for ordinary interior.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β` on the codomain layer `[Top β] [LT β]`;
- primitive owner: `IsStrictlyConsistent F`;
- derived API: the source-facing spelling `0 ∈ interior (dom F)` of the owner theorem.

Abstraction checks:
- codomain/ambient layer: already at the codomain-generic owner layer used by `dom F`;
- scalar structure: none is required for strict consistency itself;
- model owner: the owner is intrinsic (`Bifunction.IsStrictlyConsistent`), not a local wrapper;
- topology phrasing: ambient `interior` is primary for strict consistency, while relative
  interior is the separate strong-consistency owner from Definition 6.29.10.

Layer target: `core/canonical` recall of the owner and its existing specification theorem, with no
parallel local wrapper.
-/

/- Definition 6.29.22: the strict-consistency notion for the convex program associated with a
bifunction `F` is the already existing owner `Bifunction.IsStrictlyConsistent F`; the source
condition `{0} ∈ int (dom F)` is rendered here as `0 ∈ interior (dom F)`. -/
recall IsStrictlyConsistent

/- Definition 6.29.22, source-facing specification: the canonical owner theorem is already
`Bifunction.isStrictlyConsistent_iff`. -/
recall isStrictlyConsistent_iff

end Bifunction

/-! ### Definition_6_29_23 (from Chap06) -/
universe u v w

namespace Rockafellar

/-- Source-facing notation for Definition 6.29.23: a bifunction is polyhedral exactly when its
graph function has polyhedral epigraph in the Chapter 19 owner sense. -/
scoped notation:70 "polyᵇ " F =>
  Function.HasPolyhedralEpigraph (Function.uncurry F)

end Rockafellar

namespace Bifunction

open scoped Rockafellar

section

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Semiring 𝕜] [Preorder 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.23 says that a bifunction is polyhedral exactly when its graph
  function is polyhedral.
- `core/canonical`: Definition 6.29.2 already fixes the graph function as `Function.uncurry F`,
  and Chapter 19 already fixes function-side polyhedrality by `Function.HasPolyhedralEpigraph`.
- `bridge/view`: the textbook bifunction wording is just the canonical owner expression
  `((Function.uncurry F).HasPolyhedralEpigraph)`; no separate `Bifunction.IsPolyhedral` owner is
  needed.

Domain-style sampling used here:
- `Function.uncurry` from `Definition_6_29_2`;
- `Function.HasPolyhedralEpigraph` from `Chap04.Text_19_0_8`;
- `Function.HasPolyhedralEpigraph.isPolyhedral` from `Chap04.Text_19_0_8`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive ambient structure: additive/module structures on the bifunction variables `U` and `X`
  (with the product ambient inferred canonically);
- canonical owner surface: `(Function.uncurry F).HasPolyhedralEpigraph`;
- derived API: convexity and other epigraph-side consequences should continue to come from the
  Chapter 19 owner namespace, not from a parallel bifunction wrapper.

Layer target: `core/canonical` source-facing theorem surface.
-/

variable (F : U → X → WithBotTop 𝕜)

/-- Definition 6.29.23, source-facing specification:
a bifunction is polyhedral exactly when its graph function has a polyhedral epigraph in the
canonical Chapter 19 owner `Function.HasPolyhedralEpigraph`. -/
@[simp] theorem poly_iff_uncurry_hasPolyhedralEpigraph :
    (polyᵇ F) ↔ (Function.uncurry F).HasPolyhedralEpigraph :=
  Iff.rfl

end

end Bifunction

/-! ### Definition_6_29_24 (from Chap06) -/
noncomputable section

open scoped Rockafellar
open Function

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.24 uses the textbook closure surface `cl F` for a bifunction.
- `core/canonical`: Definition 6.29.2 already fixes the graph function as `Function.uncurry F`,
  and Chapter 2 already fixes Rockafellar's closure owner as `cl(·)`.
- `bridge/view`: no additional bifunction closure owner is needed; `cl F` is a thin notation
  bridge built directly from the canonical graph closure `cl(Function.uncurry F)`.

Primary mathematical domain:
- closure of extended-valued bifunctions via their graph functions on `U × X`.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` from `Definition_6_29_1`, showing the chapter pattern of
  source-facing owners implemented as thin specializations of earlier function-level owners;
- `Function.uncurry` from `Definition_6_29_2`;
- `Function.curry`;
- `lowerSemicontinuousHull`, written `cl(·)`, from `Chap02.Text_7_0_4`;
- `Function.uncurry_curry`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → WithBotTop α`;
- source-facing notation introduced here: `cl F`;
- canonical defining expression: `curry (cl(uncurry F))`;
- derived API retained here: the pointwise evaluation formula and the graph-function identity
  obtained by uncurrying `cl F`.

Ambient-structure check:
- the closure owner acts on the graph function `Function.uncurry F : U × X → WithBotTop α`;
- accordingly the minimal ambient structure is exactly a
  `ConditionallyCompleteLinearOrder α`, a `TopologicalSpace α`, and a `TopologicalSpace` on
  `U × X`.

Layer target: `source-facing`, with a thin bridge to the canonical Chapter 2 closure owner on the
graph function.
-/

/-- Definition 6.29.24: the closure `cl F` of a bifunction `F` is the bifunction whose graph
function is the Chapter 2 closure of the graph function `Function.uncurry F`.

This is intentionally a thin notation bridge to the canonical graph-level owner
`cl (Function.uncurry F)`. -/
scoped[Rockafellar] prefix:max "cl " =>
  (Function.curry ∘ _root_.lowerSemicontinuousHull ∘ Function.uncurry)

section

variable {U : Type u} {X : Type v} {α : Type w}
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
variable [TopologicalSpace (U × X)]

-- Proof sketch: unfold the notation `cl F`; evaluation of `Function.curry` at `(u, x)` is
-- definitionally evaluation of `cl (Function.uncurry F)` at `(u, x)`.
/-- Evaluating the bifunction closure is the same as evaluating the closed graph function at the
corresponding pair. -/
@[simp] theorem closure_apply (F : U → X → WithBotTop α) (u : U) (x : X) :
    cl F u x = cl(uncurry F) (u, x) :=
  rfl

-- Proof sketch: this is exactly the defining graph-function specification of
-- the notation `cl F`.
/-- Uncurrying the source-facing bifunction closure recovers the canonical graph closure. -/
@[simp] theorem uncurry_closure (F : U → X → WithBotTop α) :
    uncurry (cl F) = cl(uncurry F) :=
  rfl

end

end Bifunction
