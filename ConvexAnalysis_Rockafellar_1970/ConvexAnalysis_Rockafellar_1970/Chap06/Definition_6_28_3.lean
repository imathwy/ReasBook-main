import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_2

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
