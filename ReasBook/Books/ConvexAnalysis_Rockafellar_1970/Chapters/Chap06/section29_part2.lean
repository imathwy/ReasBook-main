import Mathlib
import Mathlib.Order.WithBotTop
import Mathlib.Tactic.Recall
import Mathlib.Topology.Semicontinuity.Defs

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_6_29_3 (from Chap06) -/
set_option linter.style.longLine false

/-!
Source/core/bridge triage for this item.

- `source-facing`: despite the legacy file name, the Chapter 6 content here is the textbook
  differentiability/uniqueness criterion for Kuhn--Tucker objects of a convex bifunction, with
  the Euclidean coordinate formula treated as a downstream bridge.
- `core/canonical`: the owner abstractions already live in the chapter as
  `Bifunction.perturbationFunction` and `Bifunction.IsKuhnTuckerVector`, with the intrinsic
  dual-owner uniqueness theorem and the inner-product gradient bridge supplied upstream in
  `Corollary_6_29_3`, and the interior-domain owner `Bifunction.IsStrictlyConsistent` from
  Definition 6.29.10.
- `bridge/view`: this file adds no new mathematics beyond the canonical source-facing theorem
  family already present in `Items/Chap06/Corollary_6_29_3.lean`, so the correct refinement is
  direct recall of those owner theorems rather than a parallel duplicate.

Primary mathematical domain:
- perturbation functions of convex bifunctions, Kuhn--Tucker vectors/functionals, and the
  differentiability/subgradient bridge.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `Bifunction.IsKuhnTuckerVector` from `Definition_6_29_19`;
- `Function.differentiableAt_iff_existsUnique_mem_subdifferentialAt` from `Theorem_25_2`;
- the intrinsic uniqueness theorem, gradient bridge, and coordinate bridge from
  `Corollary_6_29_3`.

Primitive data vs derived API:
- primitive source data: a convex bifunction `F` and its Chapter 6 owners
  `perturbationFunction F`, `IsStrictlyConsistent F`, and `IsKuhnTuckerVector F`;
- derived API: the uniqueness criterion via strict consistency together with differentiability at
  `0`, the intrinsic gradient formula, and the Euclidean coordinate formula as a bridge.

Layer target: `bridge/view`. The public surface should reuse the canonical Chapter 6 theorem family
already owned upstream, with no second wrapper theorem layer in this file.
-/

/- The strict-consistency plus differentiability uniqueness criterion is already the intrinsic
dual-owner source-facing theorem from `Corollary_6_29_3`. -/
recall Bifunction.existsUnique_kuhnTuckerFunctional_iff_differentiableAt_perturbationFunction_zero_of_optimalValue_finite

/- The inner-product bridge identifying a Kuhn--Tucker vector with the negative gradient is
already canonical in `Corollary_6_29_3`. -/
recall Bifunction.kuhnTuckerVector_eq_neg_gradient_perturbationFunction_zero

/- The strict-consistency plus differentiability uniqueness criterion is already the canonical
inner-product vector form from `Corollary_6_29_3`. -/
recall Bifunction.existsUnique_kuhnTuckerVector_iff_differentiableAt_perturbationFunction_zero_of_optimalValue_finite

/- The coordinate formula for a Kuhn--Tucker vector is the Euclidean bridge form and is recalled
as such from `Corollary_6_29_3`. -/
recall Bifunction.kuhnTuckerVector_apply_eq_neg_partialDeriv_perturbationFunction_zero

/-! ### Corollary_6_29_4 (from Chap06) -/
noncomputable section

open Function
open scoped Rockafellar

universe u v w z

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.29.4 concludes, under finite optimal value and strong or strict
  consistency, that the Kuhn--Tucker vector set is nonempty and that the directional derivative of
  the perturbation function at `0` is the negative infimum of the pairing over all Kuhn--Tucker
  vectors. Since strict consistency already implies strong consistency in the chapter owner API,
  the main declarations below are refined to the canonical hypothesis `IsStronglyConsistent 𝕜 F`.
- `core/canonical`: the ambient owner declarations are already present as
  `Bifunction.perturbationFunction`, `Bifunction.kuhnTuckerVectorSet`,
  `Function.directionalDerivativeAt`, and the support function `δᵛ(· | ·)` over `WithBotTop 𝕜`.
- `bridge/view`: the displayed `-sInf` image formula is the pointwise spelling of the support
  function of
  the reflected Kuhn--Tucker set `Neg.neg '' kuhnTuckerVectorSet F`; this reflected support owner
  is the canonical abstraction, while the explicit infimum is derived API via
  `HasPairingNegRight.pairing_neg_right`.

Domain-style sampling used here:
- `Bifunction.isStronglyConsistent_iff_mem_riDom_perturbationFunction` from
  `Definition_6_29_10`;
- `Bifunction.isKuhnTuckerVector_iff_neg_mem_subdifferentialAt_zero_of_optimalValue_finite` from
  `Theorem_6_29_1`;
- `directionalDerivativeAt_eq_supportFunction_subdifferentialAt_of_mem_riDom` from
  `Chap05.Theorem_23_4`;
- `neg_supportFunction_neg_eq_sInf_image_pairing` from `Chap03.Text_13_0_2`.

Primitive data vs derived API:
- primitive source data: the perturbation function `perturbationFunction F` and the canonical set
  `kuhnTuckerVectorSet F`;
- derived API: the reflected support-function identity and the explicit negative-infimum pairing
  formula.

Layer target:
- the nonemptiness statement remains `source-facing`;
- the directional-derivative identity is refined first to the canonical reflected-support owner,
  with the displayed `-sInf` formula retained as a thin `bridge/view` companion.
-/

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type z}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Neg UStar]
variable [HasPairing U UStar 𝕜]
variable [HasPairingNegRight U UStar 𝕜]

variable {F : U → X → WithBotTop 𝕜}

local notation "p" => perturbationFunction F

-- Proof sketch: let `p := perturbationFunction F`. Theorem 6.29.1 makes `p` convex and identifies
-- Kuhn--Tucker vectors with negatives of subgradients at `0`. Strong consistency gives
-- `0 ∈ riDom[𝕜](p)` directly; strict consistency is already absorbed by the upstream implication
-- `IsStrictlyConsistent.isStronglyConsistent`. Since `p 0 = optimalValue F` is finite, Theorem
-- 7.2 forces `p` to be proper; then Theorem 23.4 gives a nonempty subdifferential at `0`, and
-- Theorem 6.29.1 transports that witness back to a Kuhn--Tucker vector.
/-- The Kuhn--Tucker set is nonempty when the optimal value is finite and the program is strongly
consistent. Strict consistency is a sufficient special case via
`IsStrictlyConsistent.isStronglyConsistent`. -/
theorem kuhnTuckerVectorSet_nonempty_of_optimalValue_finite_of_stronglyConsistent
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤)
    (hstrong : IsStronglyConsistent 𝕜 F) :
    (kuhnTuckerVectorSet F : Set UStar).Nonempty := sorry

-- Proof sketch: first obtain the nonempty subdifferential of `p` at `0` from Theorem 23.4 and
-- rewrite the owner equality `directionalDerivativeAt p 0 = δᵛ(· | ∂[UStar]p(0))`. Then use
-- Theorem 6.29.1 to identify `∂[UStar]p(0)` with the reflected Kuhn--Tucker set
-- `Neg.neg '' kuhnTuckerVectorSet F`.
/-- Corollary 6.29.4, owner form: if the optimal value of the convex program attached to `F` is
finite and the program is strongly consistent, then the directional derivative of the perturbation
function `inf F` at `0` is the support function of the reflected Kuhn--Tucker vector set. Strict
consistency is a sufficient special case via `IsStrictlyConsistent.isStronglyConsistent`. -/
theorem
    directionalDerivativeAt_perturbationFunction_zero_eq_supportFunction_reflected_kuhnTucker
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤)
    (hstrong : IsStronglyConsistent 𝕜 F) :
    directionalDerivativeAt p (0 : U) =
      (fun u : U ↦
        δᵛ[WithBotTop 𝕜](u | Neg.neg '' (kuhnTuckerVectorSet F : Set UStar))) := sorry

-- Proof sketch: apply the owner theorem above and expand the support function of the reflected set
-- `Neg.neg '' kuhnTuckerVectorSet F`. Reindex that supremum by
-- `u⋆ ∈ kuhnTuckerVectorSet F` and use
-- `⟪u, -uStar⟫ₚ = -⟪u, uStar⟫ₚ` to rewrite the resulting supremum as the displayed negative
-- infimum.
/-- Corollary 6.29.4: if the optimal value of the convex program attached to `F` is finite and
the program is strongly consistent, then the directional derivative of the perturbation function
`inf F` at `0` is the negative infimum of the pairing over all Kuhn--Tucker vectors. Strict
consistency is a sufficient special case via `IsStrictlyConsistent.isStronglyConsistent`. -/
theorem
    directionalDerivativeAt_perturbationFunction_zero_eq_neg_sInf_image_pairing_kuhnTuckerVectorSet
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤)
    (hstrong : IsStronglyConsistent 𝕜 F)
    (u : U) :
    directionalDerivativeAt p (0 : U) u =
      -sInf ((fun uStar : UStar ↦ (⟪u, uStar⟫ₚ : WithBotTop 𝕜)) ''
        (kuhnTuckerVectorSet F : Set UStar)) := sorry

end

end Bifunction

/-! ### Definition_6_29_4 (from Chap06) -/
universe u v w z

namespace Rockafellar

/-- Source-facing notation for Definition 6.29.4: a bifunction is convex exactly when its graph
function is convex. -/
scoped[Rockafellar] notation:70 "convᵇ[" 𝕜 "](" F ")" =>
  Function.IsConvex 𝕜 (Function.uncurry F)

end Rockafellar

section

open scoped Rockafellar

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid α] [SMul 𝕜 α] [PartialOrder α]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.4 introduces the phrase “convex bifunction” by requiring the
  graph function from Definition 6.29.2 to be convex on the product space.
- `core/canonical`: the project's convexity owner is already `Function.IsConvex 𝕜`, and
  Definition 6.29.2 already identifies the graph function of `F` with the canonical uncurried map
  `Function.uncurry F`, whose canonical owner surface is `(Function.uncurry F).IsConvex 𝕜`.
- `bridge/view`: no separate `Bifunction.IsConvex` owner should be introduced here; the textbook
  notion is exactly the canonical owner applied to `Function.uncurry F`, and the source-facing
  shorthand is the scoped notation `convᵇ[𝕜](F)`.

Domain-style sampling used here:
- `Function.IsConvexOn` and `Function.IsConvex` from `Chap01.Theorem_4_2`;
- `Function.isConvex_iff_convex_epigraph` from `Chap01.Theorem_4_2`;
- `Function.uncurry` recalled in `Definition_6_29_2`;
- scoped notation `convᵇ[𝕜](F)`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → WithTopBot α`;
- primitive ambient structure: additive/scalar structures on `U` and `X`, inducing the canonical
  product structure on `U × X`;
- canonical owner surface: `(Function.uncurry F).IsConvex 𝕜`;
- source-facing notation surface: `convᵇ[𝕜](F)`;
- no extra owner wrapper is needed, because the source definition is only this direct owner usage.

Layer target: `core/canonical recall/use`.
-/

variable (F : U → X → WithTopBot α)

recall Function.IsConvex
recall Function.isConvex_iff_convex_epigraph

/- Definition 6.29.4: a bifunction is convex exactly when its graph function from
Definition 6.29.2, namely `Function.uncurry F`, is convex on the product space. The canonical owner
expression for this notion is `(Function.uncurry F).IsConvex 𝕜`, with source-facing notation
`convᵇ[𝕜](F)`. -/
#check (convᵇ[𝕜](F) : Prop)

end

/-! ### Lemma_6_29_4 (from Chap06) -/
noncomputable section

universe u v w x

namespace OrdinaryConvexProgram

section

open scoped Rockafellar

variable {𝕜 : Type x} {E : Type u} {β : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.4 says that the bifunction associated with an ordinary convex
  program is proper.
- `core/canonical`: Chapter 1 already owns properness of an extended-value function as
  `Function.IsProper`, and the Chapter 6 bifunction attached to `P` is already `P.perturbedProblem`.
- `bridge/view`: the graph-function surface is therefore directly
  `(Function.uncurry P.perturbedProblem).IsProper`.

Domain-style sampling used here:
- `Function.IsProper` from `Chap01.Definition_4_6`;
- `OrdinaryConvexProgram.perturbedProblem` from `Definition_6_28_4`;
- `OrdinaryConvexProgram.dom_perturbedProblem_nonempty` from `Lemma_6_29_3`;
- `Bifunction.mem_dom_iff_exists_mem_dom_uncurry` from `Proposition_6_29_2`.

Primitive data vs derived API:
- primitive source data: the program `P`;
- primitive owner-side hypothesis: nonemptiness of the bifunction domain
  `dom P.perturbedProblem`, i.e. existence of one finite graph point;
- source-facing hypothesis: nonemptiness of `P.constraintSet`, used only to build that primitive
  domain witness via Lemma 6.29.3;
- derived conclusion: properness of the graph function `(Function.uncurry P.perturbedProblem)`.

Layer target: `source-facing`, on the existing owner `P.perturbedProblem`.
-/

-- Proof sketch: from a domain witness `u ∈ dom P.perturbedProblem`, the canonical bridge
-- `Bifunction.mem_dom_iff_exists_mem_dom_uncurry` gives a finite graph point of
-- `Function.uncurry P.perturbedProblem`. Since `P.perturbedProblem` is built using
-- `Function.toWithBotTopOn`, graph values are never `⊥`.
/-- Core owner form: if the bifunction domain of the perturbed problem is nonempty, then its graph
function is proper in the Chapter 1 sense. -/
theorem uncurry_perturbedProblem_isProper_of_dom_nonempty
    (hdom : (dom P.perturbedProblem).Nonempty) :
    (Function.uncurry P.perturbedProblem).IsProper := by
  rw [Function.isProper_iff]
  refine ⟨?_, ?_⟩
  · rcases hdom with ⟨u, hu⟩
    rcases (Bifunction.mem_dom_iff_exists_mem_dom_uncurry).1 hu with ⟨x, hx⟩
    exact ⟨(u, x), hx⟩
  · rintro ⟨u, x⟩
    rw [Function.uncurry, P.perturbedProblem_apply]
    split_ifs <;> simp

/-- Lemma 6.29.4 (source-facing form): if the constraint set of an ordinary convex program is
nonempty, then the graph function of its perturbed problem is proper. -/
theorem uncurry_perturbedProblem_isProper (hC : P.constraintSet.Nonempty) :
    (Function.uncurry P.perturbedProblem).IsProper :=
  P.uncurry_perturbedProblem_isProper_of_dom_nonempty (P.dom_perturbedProblem_nonempty hC)

end

end OrdinaryConvexProgram

/-! ### Proposition_6_29_4 (from Chap06) -/
noncomputable section

open scoped Rockafellar
open Function

universe u v

namespace Bifunction

section Convexity

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [IsTopologicalAddGroup 𝕜] [ContinuousConstSMul 𝕜 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace (U × X)]
variable [AddCommGroup (U × X)] [Module 𝕜 (U × X)]
variable [IsTopologicalAddGroup (U × X)] [ContinuousConstSMul 𝕜 (U × X)]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.29.4 says that for a convex bifunction `F`, the bifunction
  closure `cl F` is closed and convex, and is proper exactly when `F` is proper.
- `core/canonical`: the existing owner for bifunction closure is `Bifunction.closure`, while the
  mathematical properties are already organized on the graph-function side through
  `Function.uncurry`, `Function.IsConvex`, `LowerSemicontinuous`, and `Function.IsProper`.
- `bridge/view`: the item is therefore best stated as the direct bifunction specialization of the
  Chapter 2 function-side closure theorems for `cl(·)`, using `uncurry_closure` from
  Definition 6.29.24 to identify the graph function of `cl F`.

Primary mathematical domain:
- convex extended-codomain bifunctions and the lower-semicontinuous hull of their graph
  functions.

Domain-style sampling used here:
- source-facing bifunction owner notation `convᵇ[𝕜](·)`, `closedᵇ(·)`, and `properᵇ(·)`;
- `Bifunction.closure` and `Bifunction.uncurry_closure` from `Definition_6_29_24`;
- `Function.IsConvex.lowerSemicontinuousHull_isConvex` from `Chap02.Corollary_7_2_2`;
- `lowerSemicontinuous_lowerSemicontinuousHull` from `Chap02.Text_7_0_4` through
  `Chap02.Corollary_7_2_2`;
- `Function.IsConvex.lowerSemicontinuousHull_isClosedProperConvex_of_isProper` from
  `Chap02.Theorem_7_4`;
- `Function.lowerSemicontinuousHull_not_isProper_of_not_isProper` from
  `Chap02.Corollary_7_2_2`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive source-facing owners: `convᵇ[𝕜](F)`, `closedᵇ(F)`, and `properᵇ(F)`;
- primitive source-facing closure owner: `cl F`;
- derived bridge API: uncurried graph-function forms used only as proof bridges.

Layer target: `source-facing` owner surfaces, with uncurried graph-function expressions retained
only as bridge statements when needed.
-/

-- Proof sketch: rewrite `Function.uncurry (cl F)` using `uncurry_closure`, then specialize
-- the Chapter 2 theorem `Function.IsConvex.lowerSemicontinuousHull_isConvex` to the graph
-- function `Function.uncurry F`.
/-- Proposition 6.29.4 (1): if a bifunction `F` is convex, then its closure `cl F` is convex. -/
theorem closure_isConvex
    {F : U → X → WithBotTop 𝕜} (hF_convex : convᵇ[𝕜](F)) :
    convᵇ[𝕜](cl F) := by
  simpa [uncurry_closure] using hF_convex.lowerSemicontinuousHull_isConvex

end Convexity

section LowerSemicontinuity

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜] [NoMinOrder 𝕜]
variable [AddCommGroup 𝕜] [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜]
variable [Nonempty 𝕜]
variable [TopologicalSpace (U × X)]

-- Proof sketch: rewrite `Function.uncurry (cl F)` as `cl(Function.uncurry F)` by
-- `uncurry_closure`, then apply the Chapter 2 owner theorem
-- `lowerSemicontinuous_lowerSemicontinuousHull`.
/-- Proposition 6.29.4 (2), source owner notation form: the closure bifunction `cl F` is
graph-closed. -/
theorem closure_isGraphClosed
    {F : U → X → WithBotTop 𝕜} :
    closedᵇ(cl F) := by
  simpa [uncurry_closure] using
    (lowerSemicontinuous_lowerSemicontinuousHull (uncurry F))

/-- Bridge form of Proposition 6.29.4 (2): the graph function of `cl F` is lower
semicontinuous. -/
theorem lowerSemicontinuous_uncurry_closure
    {F : U → X → WithBotTop 𝕜} :
    LowerSemicontinuous (uncurry (cl F)) := by
  simpa using (closure_isGraphClosed (F := F))

end LowerSemicontinuity

section PropernessCore

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [NoBotOrder 𝕜]
variable [TopologicalSpace (U × X)]

-- Proof sketch: this is the contrapositive of the Chapter 2 persistence theorem
-- `Function.lowerSemicontinuousHull_not_isProper_of_not_isProper` after rewriting
-- `uncurry (cl F)` as `cl(uncurry F)`.
/-- Primitive properness direction: if the closure of a bifunction is proper, then the
bifunction is proper. -/
theorem proper_of_closure_proper
    {F : U → X → WithBotTop 𝕜}
    (hcl_proper : properᵇ(cl F)) :
    properᵇ(F) := by
  by_contra hF_not_proper
  exact
    (Function.lowerSemicontinuousHull_not_isProper_of_not_isProper hF_not_proper) <|
      by simpa [uncurry_closure] using hcl_proper

end PropernessCore

section Properness

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [NormedAddCommGroup (U × X)] [NormedSpace 𝕜 (U × X)]
variable [FiniteDimensional 𝕜 (U × X)]

-- Proof sketch: rewrite `uncurry (cl F)` as `cl(uncurry F)` and apply
-- `Function.IsConvex.lowerSemicontinuousHull_isClosedProperConvex_of_isProper`,
-- extracting the properness field.
/-- Primitive properness direction under the finite-dimensional convex hypotheses used in
Theorem 7.4: properness of `F` implies properness of `cl F`. -/
theorem closure_proper_of_proper
    {F : U → X → WithBotTop 𝕜} (hF_convex : convᵇ[𝕜](F))
    (hF_proper : properᵇ(F)) :
    properᵇ(cl F) := by
  simpa [uncurry_closure] using
    (hF_convex.lowerSemicontinuousHull_isClosedProperConvex_of_isProper hF_proper).proper

-- Proof sketch: combine the generic primitive direction
-- `proper_of_closure_proper` with the finite-dimensional convex direction
-- `closure_proper_of_proper`.
/-- Proposition 6.29.4 (3): for a convex bifunction `F`, `cl F` is proper
if and only if `F` is proper. -/
theorem closure_proper_iff
    {F : U → X → WithBotTop 𝕜} (hF_convex : convᵇ[𝕜](F)) :
    properᵇ(cl F) ↔ properᵇ(F) := by
  constructor
  · exact proper_of_closure_proper
  · exact closure_proper_of_proper hF_convex

end Properness

end Bifunction

/-! ### Theorem_6_29_4 (from Chap06) -/
noncomputable section

open scoped Rockafellar
open Function

universe u v

namespace Bifunction

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [FiniteDimensional 𝕜 (U × X)]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.29.4 compares the closure of a convex bifunction with the closures of
  its slices on `ri[𝕜](dom F)`, and compares the parameter domains of `F` and `cl F`.
- `core/canonical`: the Chapter 6 owners already present are `Bifunction.closure`,
  `Bifunction.perturbationFunction`, and `Bifunction.dom`; for the domain clauses, the raw owner
  abstraction is the graph function `uncurry F`, together with the Chapter 2 closure-domain owner
  theorems for `cl(uncurry F)` and the Chapter 6 projection bridge
  `dom_eq_image_fst_dom_uncurry`.
- `bridge/view`: the slice infimum identity is expressed on the canonical row-infimum owner
  `perturbationFunction`, while the slice-closure identity keeps the source-facing equality
  `cl F u = cl(F u)` and the domain clauses project graph-domain statements
  back to parameter
  domains.

Primary mathematical domain:
- convex extended-scalar-valued bifunctions, with finite-dimensionality imposed at the graph-owner
  layer `U × X`.

Domain-style sampling used here:
- `Bifunction.closure` and `Bifunction.closure_apply` from `Definition_6_29_24`;
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `Bifunction.dom` and `Bifunction.dom_eq_image_fst_dom_uncurry` from
  `Definition_6_29_8`/`Proposition_6_29_2`;
- `(uncurry F).IsConvex 𝕜` from `Definition_6_29_4`;
- `(uncurry F).IsProper` from `Definition_6_29_6`;
- `Function.subset_dom_lowerSemicontinuousHull` and
  `Function.IsConvex.closure_dom_lowerSemicontinuousHull_eq_closure_dom_of_isProper` from
  `Chap02.Corollary_7_4_1`;
- `image_closure_subset_closure_image` for projecting graph-domain closure to parameter-domain
  closure;
- the Chapter 2 owners `cl(·)` and `ri[𝕜](·)`.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owner hypotheses: convexity of the graph function, and for the domain-closure clause
  properness of the graph function;
- derived API: slice-wise closure equality, slice-infimum equality, and the two parameter-domain
  inclusions.

Layer target: `source-facing`, split into atomic owner-level clauses rather than a conjunction.
-/

-- Proof sketch: pass from the convex graph function `uncurry F` on `U × X` to its
-- closure on the product, then specialize the Chapter 2 segment-limit/relative-interior closure
-- theorem to the vertical slice over `u ∈ ri[𝕜](dom F)`.
/-- Theorem 6.29.4 (1): for a convex bifunction `F`, the `u`-slice of the bifunction closure
`cl F` agrees with the Chapter 2 closure `cl(F u)` of the slice whenever
`u ∈ ri[𝕜](dom F)`. -/
theorem closure_slice_eq_lowerSemicontinuousHull_of_mem_ri_dom
    {F : U → X → WithBotTop 𝕜} (hF : convᵇ[𝕜](F))
    {u : U} (hu : u ∈ ri[𝕜](dom F)) :
    cl F u = cl(F u) := sorry

-- Proof sketch: apply clause `(1)` to identify the slice `(cl F) u` with
-- `cl(F u)`, then use the one-variable fact that taking the Chapter 2
-- closure does not change the infimum of a convex slice on the relative interior of its effective
-- domain.
/-- Theorem 6.29.4 (2): for a convex bifunction `F`, the infimum of the slice of `cl F` at `u`
equals the infimum of the original slice at every `u ∈ ri[𝕜](dom F)`, written on the canonical
row-infimum owner as `perturbationFunction (cl F) u = perturbationFunction F u`. -/
theorem perturbationFunction_closure_eq_perturbationFunction_of_mem_ri_dom
    {F : U → X → WithBotTop 𝕜} (hF : convᵇ[𝕜](F))
    {u : U} (hu : u ∈ ri[𝕜](dom F)) :
    perturbationFunction (cl F) u = perturbationFunction F u := sorry

end

section

variable {U : Type u} {X : Type v}
variable {α : Type*}
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [Nonempty α]
variable [TopologicalSpace (U × X)]

-- Proof sketch: the graph-function closure `cl(uncurry F)` can only enlarge the
-- effective domain of the graph function. Projecting that inclusion onto the parameter space gives
-- `dom F ⊆ dom(cl F)`. The textbook's extra properness hypothesis is redundant here.
/-- Theorem 6.29.4 (3): passing from a bifunction to its closure can only enlarge the parameter
domain. This is the source inclusion `dom F ⊆ dom(cl F)`. -/
theorem subset_dom_closure (F : U → X → WithBotTop α) :
    dom F ⊆ dom (cl F) := by
  intro u hu
  rw [mem_dom_iff_exists_mem_dom_uncurry] at hu ⊢
  rcases hu with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simpa [uncurry_closure] using
    (Function.subset_dom_lowerSemicontinuousHull (uncurry F) hx)

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [FiniteDimensional 𝕜 (U × X)]

-- Proof sketch: apply the Chapter 2 domain-closure theorem to the convex proper graph function
-- `uncurry F`, obtaining `dom(cl(uncurry F)) ⊆ closure(dom(uncurry F))`, and then
-- project this inclusion onto the parameter factor to identify the source parameter domains.
/-- Theorem 6.29.4 (4): if the graph function of a convex bifunction `F` is proper, then the
parameter domain of `cl F` is contained in the closure of the parameter domain of `F`. -/
theorem dom_closure_subset_closure_dom_of_isProper
    {F : U → X → WithBotTop 𝕜} (hF_convex : convᵇ[𝕜](F))
    (hF_proper : properᵇ(F)) :
    dom (cl F) ⊆ _root_.closure (dom F) := by
  intro u hu
  rw [dom_eq_image_fst_dom_uncurry] at hu
  rcases hu with ⟨⟨u, x⟩, hx, rfl⟩
  have hx' : (u, x) ∈ _root_.effectiveDomain (cl(uncurry F)) := by
    simpa [uncurry_closure] using hx
  have hgraph :
      _root_.closure (_root_.effectiveDomain (cl(uncurry F))) =
        _root_.closure (_root_.effectiveDomain (uncurry F)) :=
    hF_convex.closure_dom_lowerSemicontinuousHull_eq_closure_dom_of_isProper hF_proper
  have hx_closure : (u, x) ∈ _root_.closure (_root_.effectiveDomain (uncurry F)) := by
    rw [← hgraph]
    exact subset_closure hx'
  have hu_closure :
      u ∈ _root_.closure (Prod.fst '' _root_.effectiveDomain (uncurry F)) :=
    image_closure_subset_closure_image continuous_fst ⟨(u, x), hx_closure, rfl⟩
  simpa [dom_eq_image_fst_dom_uncurry] using hu_closure

end

end Bifunction

/-! ### Corollary_6_29_5 (from Chap06) -/
noncomputable section

open Function
open scoped Rockafellar

universe u v

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.29.5 states two consequences for a convex bifunction `F` whose
  associated generalized convex program has finite optimal value and is strictly consistent:
  `(inf F)` is finite and continuous on some open convex neighborhood of `0`, and the
  Kuhn--Tucker vectors form a nonempty closed bounded convex set.
- `core/canonical`: the relevant owner layer is already present as
  `Bifunction.perturbationFunction`, `Bifunction.optimalValue`, `Bifunction.IsStrictlyConsistent`,
  and `Bifunction.kuhnTuckerVectorSet`, with the Kuhn--Tucker geometry owned intrinsically on
  `StrongDual ℝ U`.
- `bridge/view`: clause `(1)` routes continuity of `inf F` through the canonical convex-function
  continuity theorem on subsets of the effective domain, while the Euclidean self-dual reading of
  the Kuhn--Tucker geometry is kept only as an inner-product-space bridge specialization.

Domain-style sampling used here:
- `Bifunction.perturbationFunction_isConvex` and
  `Bifunction.isKuhnTuckerVector_iff_neg_mem_subdifferentialAt_zero_of_optimalValue_finite`
  from `Chap06.Theorem_6_29_1`;
- `Bifunction.IsStrictlyConsistent` and
  `Bifunction.isStrictlyConsistent_iff_mem_interior_dom_perturbationFunction` from
  `Chap06.Definition_6_29_10`;
- `Bifunction.kuhnTuckerVectorSet_nonempty_of_optimalValue_finite_of_stronglyConsistent` from
  `Chap06.Corollary_6_29_4`, together with
  `Bifunction.isClosed_kuhnTuckerVectorSet_of_optimalValue_finite` and
  `Bifunction.convex_kuhnTuckerVectorSet_of_optimalValue_finite` from
  `Chap06.Corollary_6_29_1`;
- `Function.IsConvex.continuousOn` from
  `Chap02.Theorem_10_1`;
- `_root_.subdifferentialAt_nonempty_and_bounded_iff_mem_interior_dom` from
  `Chap05.Theorem_23_4`.

Primitive data vs derived API:
- primitive source data: a convex bifunction `F : U → X → WithBotTop ℝ`;
- primitive owner hypotheses: finiteness of `optimalValue F` and strict consistency of `F`;
- derived API: an open convex neighborhood of `0` on which `perturbationFunction F = inf F` is
  finite and continuous, and the nonempty/closed/bounded/convex geometry of the Kuhn--Tucker set
  in the canonical dual, with Euclidean vector-space restatements only as bridge views.

Layer target:
- clause `(1)` remains `source-facing`, written directly with `IsOpen`, `Convex`, `dom(·)`,
  `≠ ⊥`, and `ContinuousOn` rather than through a parallel neighborhood wrapper;
- clauses `(2)` and `(3)` are refined first to the `core/canonical` dual owner
  `StrongDual ℝ U`;
- Euclidean inner-product-space formulations are kept only as `bridge/view` companions.
-/

section Neighborhood

variable {U : Type u} {X : Type v}
variable [AddCommGroup U] [TopologicalSpace U] [IsTopologicalAddGroup U]
variable [Module ℝ U] [ContinuousConstSMul ℝ U] [FiniteDimensional ℝ U]
variable [AddCommMonoid X] [Module ℝ X]
variable {F : U → X → WithBotTop ℝ}

local notation "p" => perturbationFunction F

-- Proof sketch: `perturbationFunction F` is convex by Theorem 6.29.1. Strict consistency gives
-- `0 ∈ interior (dom (perturbationFunction F))`, and finiteness of `optimalValue F = p 0`
-- rules out the improper case by Theorem 7.2, so `p` is finite on that interior neighborhood.
-- Then Theorem 10.1 yields continuity on the chosen open convex neighborhood, and the
-- conclusion is recorded directly by the canonical owners `IsOpen`, `Convex`, `dom(·)`,
-- `ContinuousOn`, together with the lower-side finiteness clause `p u ≠ ⊥`.
omit [AddCommMonoid X] [Module ℝ X] in
/-- Corollary 6.29.5 (1), owner form: assuming convexity of the perturbation-function owner
`perturbationFunction F`, finite optimal value, and strict consistency, there is an open convex
neighborhood `C` of `0` on which `perturbationFunction F` is finite and continuous. -/
theorem
    exists_open_convex_neighborhood_zero_finite_continuous_of_perturbationFunction_isConvex
    (hp_convex : (perturbationFunction F).IsConvex ℝ)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hstrict : IsStrictlyConsistent F) :
    ∃ C : Set U,
      IsOpen C ∧ Convex ℝ C ∧ (0 : U) ∈ C ∧ C ⊆ dom(perturbationFunction F) ∧
        (∀ u : U, u ∈ C → perturbationFunction F u ≠ ⊥) ∧
        ContinuousOn (perturbationFunction F) C := sorry

/-- Corollary 6.29.5 (1), source-facing form: if a convex bifunction `F` has finite optimal value
and is strictly consistent, then there exists an open convex neighborhood `C` of `0` on which the
perturbation function `perturbationFunction F`, i.e. `inf F`, is finite and continuous. Here
“finite” is recorded canonically as `u ∈ dom(p)` together with `p u ≠ ⊥`. -/
theorem exists_open_convex_neighborhood_zero_on_which_perturbationFunction_is_finite_and_continuous
    (hF : (uncurry F).IsConvex ℝ)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hstrict : IsStrictlyConsistent F) :
    ∃ C : Set U,
      IsOpen C ∧ Convex ℝ C ∧ (0 : U) ∈ C ∧ C ⊆ dom(p) ∧
        (∀ u : U, u ∈ C → p u ≠ ⊥) ∧ ContinuousOn p C := by
  exact
    exists_open_convex_neighborhood_zero_finite_continuous_of_perturbationFunction_isConvex
      (F := F) (hp_convex := perturbationFunction_isConvex hF) hoptimal hstrict

end Neighborhood

section KuhnTuckerDual

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [AddCommMonoid X] [Module ℝ X]
variable {F : U → X → WithBotTop ℝ}

local notation "p" => perturbationFunction F

-- Proof sketch: Theorem 6.29.1 identifies Kuhn--Tucker vectors with negatives of the
-- subdifferential of `perturbationFunction F` at `0`. Strict consistency puts `0` in the
-- interior of the perturbation-function domain, and Theorem 23.4 then makes that
-- subdifferential nonempty and bounded; reflection by negation preserves both properties.
omit [AddCommMonoid X] [Module ℝ X] in
/-- Corollary 6.29.5 (2), owner boundedness form: if `perturbationFunction F` is convex, the
optimal value is finite, and `F` is strictly consistent, then the Kuhn--Tucker vector set is
bounded in the canonical dual perturbation space. -/
theorem
    isBounded_kuhnTuckerVectorSet_of_optimalValue_finite_of_strictConsistency_of_pConvex
    (hp_convex : (perturbationFunction F).IsConvex ℝ)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hstrict : IsStrictlyConsistent F) :
    Bornology.IsBounded (kuhnTuckerVectorSet F : Set (StrongDual ℝ U)) := sorry

/-- Corollary 6.29.5 (2): under finite optimal value and strict consistency, the Kuhn--Tucker
vectors of `F` form a nonempty bounded subset of the canonical dual perturbation space. -/
theorem kuhnTuckerVectorSet_nonempty_and_bounded_of_optimalValue_finite_of_isStrictlyConsistent
    (hF : (uncurry F).IsConvex ℝ)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hstrict : IsStrictlyConsistent F) :
    (kuhnTuckerVectorSet F : Set (StrongDual ℝ U)).Nonempty ∧
      Bornology.IsBounded (kuhnTuckerVectorSet F : Set (StrongDual ℝ U)) := by
  refine ⟨?_, ?_⟩
  · exact kuhnTuckerVectorSet_nonempty_of_optimalValue_finite_of_stronglyConsistent
      hF hoptimal hstrict.isStronglyConsistent
  · exact
      isBounded_kuhnTuckerVectorSet_of_optimalValue_finite_of_strictConsistency_of_pConvex
        (F := F) (hp_convex := perturbationFunction_isConvex hF) hoptimal hstrict

-- Proof sketch: Corollary 6.29.1 already gives closedness and convexity of the Kuhn--Tucker
-- vector set from finiteness of the optimal value, via the subdifferential characterization at
-- `0` and invariance of these properties under negation.
omit [FiniteDimensional ℝ U] [AddCommMonoid X] [Module ℝ X] in
/-- Corollary 6.29.5 (3): if the optimal value of the generalized convex program associated with
`F` is finite, then the Kuhn--Tucker vectors form a closed convex subset of the perturbation
dual space. -/
theorem isClosed_and_convex_kuhnTuckerVectorSet_of_optimalValue_finite
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤) :
    IsClosed (kuhnTuckerVectorSet F : Set (StrongDual ℝ U)) ∧
      Convex ℝ (kuhnTuckerVectorSet F : Set (StrongDual ℝ U)) := by
  exact ⟨isClosed_kuhnTuckerVectorSet_of_optimalValue_finite hoptimal,
    convex_kuhnTuckerVectorSet_of_optimalValue_finite hoptimal⟩

end KuhnTuckerDual

section KuhnTuckerEuclideanBridge

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
variable [AddCommMonoid X] [Module ℝ X]
variable {F : U → X → WithBotTop ℝ}

local notation "KTᵥ(" F ")" => (kuhnTuckerVectorSet F : Set U)

-- Proof sketch: transport the intrinsic dual-owner theorem through the Fréchet-Riesz
-- identification `InnerProductSpace.toDualMap ℝ U`.
/-- Corollary 6.29.5 (2), Euclidean bridge form: under finite optimal value and strict
consistency, the Kuhn--Tucker vectors form a nonempty bounded subset of the self-dual
inner-product perturbation space. -/
theorem kuhnTuckerVectorSet_nonempty_and_bounded_euclidean
    (hF : (uncurry F).IsConvex ℝ)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hstrict : IsStrictlyConsistent F) :
    (KTᵥ(F)).Nonempty ∧ Bornology.IsBounded (KTᵥ(F)) := sorry

-- Proof sketch: transport the intrinsic dual-owner closed/convex theorem through the same
-- Fréchet-Riesz identification.
omit [FiniteDimensional ℝ U] [AddCommMonoid X] [Module ℝ X] in
/-- Corollary 6.29.5 (3), Euclidean bridge form: if the optimal value is finite, then the
Kuhn--Tucker vectors form a closed convex subset of the self-dual inner-product perturbation
space. -/
theorem isClosed_and_convex_kuhnTuckerVectorSet_euclidean
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤) :
    IsClosed (KTᵥ(F)) ∧ Convex ℝ (KTᵥ(F)) := sorry

end KuhnTuckerEuclideanBridge

end Bifunction

/-! ### Definition_6_29_5 (from Chap06) -/
universe u v w

open Function

namespace Rockafellar

/-- Source-facing notation for Definition 6.29.5: a bifunction is graph-closed exactly when its
graph function is lower semicontinuous. -/
scoped[Rockafellar] notation:70 "closedᵇ(" F ")" =>
  LowerSemicontinuous (Function.uncurry F)

end Rockafellar

namespace Bifunction

section

open scoped Rockafellar

variable {U : Type u} {X : Type v} {α : Type w}
variable [TopologicalSpace (U × X)]
variable [Preorder α]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.5 calls a bifunction closed when its graph function is closed.
- `core/canonical`: the graph function is already the canonical uncurried map
  `uncurry F`, and the project's closedness owner for ordered-valued functions is
  `LowerSemicontinuous`; the primitive ambient structure is only a topology on the graph space
  `U × X`.
- `bridge/view`: later slice-wise closedness notions are downstream bridges from this global
  graph-function closedness and should not replace it here.

Domain-style sampling used here:
- `uncurry` (from `Function.uncurry`) as the graph-function owner from Definition 6.29.2;
- `LowerSemicontinuous` as the canonical closedness predicate for ordered-valued functions;
- `Bifunction.lowerSemicontinuous_slice_of_closedb` and
  `Bifunction.IsConvexClosed` in Chapter 7 as later bridges from the uncurried owner to slice-wise
  closedness.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → WithBotTop α`;
- primitive ambient structure: a topology on `U × X` (not separately on each factor);
- canonical owner surface: `LowerSemicontinuous (uncurry F)`;
- source-facing notation surface: `closedᵇ(F)`;
- derived bridge API: any slice-wise closedness consequences belong in later companion results,
  not in the owner for this definition.

Layer target: `core/canonical recall/use`.
-/

variable (F : U → X → WithBotTop α)

/- Definition 6.29.5: a bifunction is graph-closed exactly when its graph function from
Definition 6.29.2, namely `uncurry F`, is lower semicontinuous on `U × X`. The canonical owner
expression for this notion is `LowerSemicontinuous (uncurry F)`, with source-facing notation
`closedᵇ(F)`. -/
#check (closedᵇ(F) : Prop)

end

end Bifunction

/-! ### Lemma_6_29_5 (from Chap06) -/
noncomputable section

universe u v w x

namespace OrdinaryConvexProgram

section

variable {𝕜 : Type x} {E : Type u} {β : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E] [TopologicalSpace E]
variable [AddCommMonoid β] [LinearOrder β] [SMul 𝕜 β] [TopologicalSpace β]
variable {r s : ℕ}

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.5 says that the bifunction associated with an ordinary convex
  program is closed once the constraint set is closed, the objective and inequality branches are
  closed on that set, and the equality branches satisfy a closedness bridge for equality slices.
- `core/canonical`: Definition 6.29.5 already identifies bifunction closedness with lower
  semicontinuity of the graph function `Function.uncurry F`, and the Chapter 6 owner is
  `P.perturbedProblem`.
- `bridge/view`: `P.perturbedProblem` is the canonical `+∞`-extension of the source objective to
  the perturbed feasible slices. The source data of `OrdinaryConvexProgram` already lives on the
  closed constraint set, so the closedness assumptions stay on the primitive branch data; equality
  slices are handled by a two-sided semicontinuity bridge (`LowerSemicontinuous` and
  `UpperSemicontinuous`) rather than being left implicit in affine data.

Domain-style sampling used here:
- `OrdinaryConvexProgram.perturbedProblem` from `Definition_6_28_4`;
- `LowerSemicontinuous (Function.uncurry F)` from `Definition_6_29_5`;
- `Function.toWithBotTopOn` from `Chap01.Remark_4_4_5`;
- `LowerSemicontinuous` / `UpperSemicontinuous` as the canonical closedness owners for
  inequality/equality branches.

Primitive data vs derived API:
- primitive source-facing data: the program `P`;
- primitive source-facing closedness assumptions: closedness of `P.constraintSet`, lower
  semicontinuity of `P.objective`, lower semicontinuity of each `P.inequality i`, and two-sided
  semicontinuity for each equality branch `P.equality j`;
- derived conclusion: lower semicontinuity of the graph function of `P.perturbedProblem`.

Layer target: `source-facing`, on the existing owner `P.perturbedProblem`.
-/

variable (P : OrdinaryConvexProgram 𝕜 E β r s)

-- Proof sketch: the perturbed feasible set is cut out inside the closed set `P.constraintSet` by
-- lower-semicontinuous inequality branches and equality slices controlled by both lower and upper
-- semicontinuity, hence it is closed. The perturbed problem is then the canonical `+∞`-extension
-- of the lower-semicontinuous objective branch to that closed feasible slice, so its graph
-- function is lower semicontinuous.
/-- Lemma 6.29.5: if the constraint set of an ordinary convex program is closed, the objective
and inequality branches are lower semicontinuous on that set, and each equality branch has both
lower and upper semicontinuity (so equality slices have an explicit closedness bridge), then the
graph function of the perturbed problem is lower semicontinuous. -/
theorem uncurry_perturbedProblem_lowerSemicontinuous
    (hconstraintSet : IsClosed P.constraintSet)
    (hobjective : LowerSemicontinuous P.objective)
    (hineq : ∀ i, LowerSemicontinuous (P.inequality i))
    (heq_lower : ∀ j, LowerSemicontinuous (P.equality j))
    (heq_upper : ∀ j, UpperSemicontinuous (P.equality j)) :
    LowerSemicontinuous (Function.uncurry P.perturbedProblem) := sorry

end

end OrdinaryConvexProgram

/-! ### Corollary_6_29_6 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.29.6 says that if one slice of a convex bifunction has infimum
  `-∞`, then every parameter in `ri (dom F)` has slice infimum `-∞`; outside `dom F`, the slice
  infimum is `+∞`.
- `core/canonical`: the Chapter 6 owners already present are `perturbationFunction`, `dom F`, and
  the convexity theorem `perturbationFunction_isConvex` from Theorem 6.29.1. The Chapter 2 owner
  theorem `Function.IsConvex.eq_bot_of_mem_riDom` is the canonical `-∞` propagation statement for
  convex extended-valued functions.
- `bridge/view`: Rockafellar's `inf F_u` is the owner value `perturbationFunction F u`, while
  `ri (dom F)` is the chapter surface `ri[𝕜](dom F)`, bridged to
  `riDom[𝕜](perturbationFunction F)` by Definition 6.29.8.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `Bifunction.perturbationFunction_isConvex` from `Theorem_6_29_1`;
- `Bifunction.dom` and `Bifunction.mem_ri_dom_iff_mem_riDom_perturbationFunction`
  from `Definition_6_29_8`;
- `Function.IsConvex.eq_bot_of_mem_riDom` from `Chap02.Theorem_7_2`.

Primitive data vs derived API:
- primitive input for clause `(1)`: owner convexity of `perturbationFunction F`, together with the
  source hypothesis that some slice infimum is `⊥`;
- source-facing bridge for clause `(1)`: convexity of `Function.uncurry F`, converted to owner
  convexity by `perturbationFunction_isConvex`;
- primitive input for clause `(2)`: a parameter outside `dom(perturbationFunction F)`;
- source-facing bridge for clause `(2)`: outside-domain membership for `dom F`, converted by
  `mem_dom_perturbationFunction_iff_mem_dom`.

Layer target: each clause is first exposed at the primitive owner layer for
`perturbationFunction`, with source-facing `dom F` / `ri[𝕜](dom F)` forms kept as thin wrappers.
-/

section RelativeInteriorOwner

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]

-- Proof sketch: an equality `perturbationFunction F u₀ = ⊥` shows this owner function is
-- improper. Then apply the Chapter 2 owner theorem `Function.IsConvex.eq_bot_of_mem_riDom`
-- directly on `perturbationFunction F`.
/-- Owner form of Corollary 6.29.6 (1): if `perturbationFunction F` is convex and equals `⊥` at
some parameter, then it equals `⊥` at every point of `riDom[𝕜](perturbationFunction F)`. -/
theorem perturbationFunction_eq_bot_of_exists_eq_bot_of_mem_riDom_of_isConvex
    {F : U → X → WithBotTop 𝕜}
    (hp_convex : (perturbationFunction F).IsConvex 𝕜)
    (hbot : ∃ u0 : U, perturbationFunction F u0 = ⊥)
    {u : U} (hu : u ∈ riDom[𝕜](perturbationFunction F)) :
    perturbationFunction F u = ⊥ := by
  have hp_not_proper : ¬ (perturbationFunction F).IsProper := by
    intro hp
    rcases hbot with ⟨u0, hu0⟩
    exact (hp.ne_bot u0) hu0
  exact hp_convex.eq_bot_of_mem_riDom hp_not_proper hu

end RelativeInteriorOwner

section RelativeInterior

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

-- Proof sketch: Theorem 6.29.1 makes `perturbationFunction F` convex. Transport
-- `u ∈ ri[𝕜](dom F)` to `u ∈ riDom[𝕜](perturbationFunction F)` via Definition 6.29.8, then apply
-- the owner theorem
-- `perturbationFunction_eq_bot_of_exists_eq_bot_of_mem_riDom_of_isConvex`.
/-- Corollary 6.29.6 (1): if some slice of a convex bifunction `F` has infimum `⊥`, then every
parameter in `ri[𝕜](dom F)` has slice infimum `⊥`. -/
theorem perturbationFunction_eq_bot_of_exists_eq_bot_of_mem_ri_dom
    {F : U → X → WithBotTop 𝕜}
    (hF : (Function.uncurry F).IsConvex 𝕜)
    (hbot : ∃ u0 : U, perturbationFunction F u0 = ⊥)
    {u : U} (hu : u ∈ ri[𝕜](dom F)) :
    perturbationFunction F u = ⊥ := by
  have hu' : u ∈ riDom[𝕜](perturbationFunction F) := by
    simpa using (mem_ri_dom_iff_mem_riDom_perturbationFunction).1 hu
  exact perturbationFunction_eq_bot_of_exists_eq_bot_of_mem_riDom_of_isConvex
    (F := F) (hp_convex := perturbationFunction_isConvex hF) hbot hu'

end RelativeInterior

section OutsidePerturbationDomain

variable {U : Type u} {X : Type v} {β : Type w}
variable [InfSet β] [PartialOrder β] [OrderTop β]

-- Proof sketch: `u ∉ dom(perturbationFunction F)` is exactly
-- `¬ perturbationFunction F u < ⊤`; rewrite with `not_lt_top_iff`.
/-- Owner form of Corollary 6.29.6 (2): if `u` lies outside
`dom(perturbationFunction F)`, then `perturbationFunction F u = ⊤`. -/
theorem perturbationFunction_eq_top_of_not_mem_dom_perturbationFunction
    {F : U → X → β} {u : U}
    (hu : u ∉ dom(perturbationFunction F)) :
    perturbationFunction F u = ⊤ := by
  have hpu_not : ¬ perturbationFunction F u < ⊤ := by
    intro hpu
    exact hu ((_root_.mem_effectiveDomain (f := perturbationFunction F) (x := u)).2 hpu)
  exact (not_lt_top_iff).1 hpu_not

end OutsidePerturbationDomain

section OutsideDomain

variable {U : Type u} {X : Type v} {β : Type w}
variable [CompleteLattice β]

-- Proof sketch: by definition, `u ∉ dom F` means that every slice value `F u x` is `⊤`. The
-- perturbation function is the infimum of that slice, so its value at `u` is also `⊤`.
/-- Corollary 6.29.6 (2): if a parameter `u` lies outside the bifunction domain `dom F`, then the
slice infimum at `u` is `⊤`. -/
theorem perturbationFunction_eq_top_of_not_mem_dom
    {F : U → X → β} {u : U} (hu : u ∉ dom F) :
    perturbationFunction F u = ⊤ := by
  have hu' : u ∉ dom(perturbationFunction F) := by
    intro hpu
    exact hu ((mem_dom_perturbationFunction_iff_mem_dom).1 hpu)
  exact perturbationFunction_eq_top_of_not_mem_dom_perturbationFunction
    (F := F) hu'

end OutsideDomain

end Bifunction

/-! ### Definition_6_29_6 (from Chap06) -/
universe u v w

namespace Rockafellar

/-- Source-facing notation for Definition 6.29.6: a bifunction is proper exactly when its graph
function is proper. -/
scoped[Rockafellar] notation:70 "properᵇ(" F ")" =>
  Function.IsProper (Function.uncurry F)

end Rockafellar

section

open Function
open scoped Rockafellar

variable {U : Type u} {X : Type v} {β : Type w}
variable [Top β] [Bot β] [LT β]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.6 calls a bifunction proper when its graph function is proper.
- `core/canonical`: Definition 6.29.2 already identifies the graph function of `F` with the
  canonical uncurried map `uncurry F`, and Chapter 1 already owns properness for codomain values
  with `⊤`, `⊥`, and `<` through `Function.IsProper`, whose short owner surface is `f.IsProper`.
- `bridge/view`: later source-facing bifunction properness notions built from slice domains are
  different chapter-level owners and should not replace this graph-function properness definition.

Domain-style sampling used here:
- `Function.IsProper` from `Chap01.Definition_4_6`;
- `uncurry` as the graph-function owner from `Definition_6_29_2`;
- scoped notation `properᵇ(F)`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → β`;
- canonical owner surface: `(uncurry F).IsProper`;
- source-facing notation surface: `properᵇ(F)`;
- no extra wrapper declaration is needed, because the source definition is exactly this canonical
  owner usage.

Layer target: `core/canonical recall/use`.
-/

variable (F : U → X → β)

/- Definition 6.29.6: a bifunction is proper exactly when its graph function from
Definition 6.29.2, namely `uncurry F`, is proper. The canonical owner expression for this notion
is `(uncurry F).IsProper`, with source-facing notation `properᵇ(F)`. -/
#check (properᵇ(F) : Prop)

end

/-! ### Lemma_6_29_6 (from Chap06) -/
noncomputable section

universe u v w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [CompleteLattice β] [Zero U]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.6 states that the generalized convex program `(P)` is consistent if
  and only if its optimal value is strictly below `⊤` (specializing to `+∞` on `WithBotTop`).
- `core/canonical`: the existing Chapter 6 owners are `Bifunction.IsConsistent` from
  Definition 6.29.1 and `Bifunction.optimalValue` from Definition 6.29.15.
- `bridge/view`: the source wording is exactly the comparison between those two owners, since
  `optimalValue F = perturbationFunction F 0`.

Domain-style sampling used here:
- `Bifunction.IsConsistent`;
- `Bifunction.IsConsistent.optimalValue_lt_top`;
- `Bifunction.isConsistent_of_optimalValue_lt_top`;
- `Bifunction.isConsistent_iff_lt_top`;
- `Bifunction.optimalValue`;
- `Bifunction.optimalValue_eq_perturbationFunction_zero`.

Primitive data vs derived API:
- primitive source data: the bifunction `F : U → X → β`;
- primitive owners: `IsConsistent F` and `optimalValue F`;
- derived API: their equivalence via the zero-perturbation value `perturbationFunction F 0`.

Layer target: `bridge/view`, stated directly on the existing canonical owners with no new wrapper.
-/

-- Proof sketch: unfold `IsConsistent` through `isConsistent_iff_lt_top`, then rewrite the
-- zero-perturbation value `perturbationFunction F 0` as `optimalValue F` using
-- `optimalValue_eq_perturbationFunction_zero`.
/-- Lemma 6.29.6: the generalized convex program attached to `F` is consistent if and only if its
optimal value is strictly below `⊤` (equivalently below `+∞` in the `WithBotTop` codomain
specialization). -/
@[simp]
theorem isConsistent_iff_optimalValue_lt_top
    (F : U → X → β) :
    IsConsistent F ↔ optimalValue F < ⊤ := by
  simpa [optimalValue_eq_perturbationFunction_zero] using isConsistent_iff_lt_top F

/-- Owner-form elimination: consistency forces the optimal value to lie strictly below `⊤`. -/
theorem IsConsistent.optimalValue_lt_top
    {F : U → X → β}
    (h : IsConsistent F) :
    optimalValue F < ⊤ :=
  (isConsistent_iff_optimalValue_lt_top F).1 h

/-- Owner-form introduction: an optimal value strictly below `⊤` forces consistency. -/
theorem isConsistent_of_optimalValue_lt_top
    {F : U → X → β}
    (h : optimalValue F < ⊤) :
    IsConsistent F :=
  (isConsistent_iff_optimalValue_lt_top F).2 h

end

end Bifunction

/-! ### Corollary_6_29_7 (from Chap06) -/
noncomputable section

universe u v w w'

open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type w'}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [HasPairing U UStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "L" => lagrangian (toOrderDual F)

-- Proof sketch: apply the Chapter 7 optimality criterion
-- `isMinOn_objective_iff_exists_zero_mem_subdifferentialAt_lagrangian`, which under the same
-- qualification identifies primal optimal points with existence of a dual vector whose
-- Lagrangian saddle subdifferential contains `0`. Then rewrite that vanishing-subdifferential
-- condition as the saddle-point predicate via Proposition 36.5.2. The source's strict
-- consistency branch is absorbed by the canonical implication
-- `IsStrictlyConsistent.isStronglyConsistent`.
/-- Corollary 6.29.7: under either the closed-convex strong-consistency hypothesis (hence also
under strict consistency) or the polyhedral-consistent hypothesis, a point `x` is an optimal
solution of the convex program associated with `F` if and only if there exists a dual vector
`u⋆` such that `(u⋆, x)` is a saddle-point of the Lagrangian `lagrangian (toOrderDual F)`. -/
theorem isMinOn_objective_iff_exists_isSaddlePoint_lagrangian
    (hqual : (IsClosedConvex F ∧ IsStronglyConsistent 𝕜 F) ∨
      (Function.HasPolyhedralEpigraph (Function.uncurry F) ∧ IsConsistent F)) (x : X) :
    IsMinOn (F)₀ Set.univ x ↔
      ∃ uStar : UStar, IsSaddlePoint L uStar x := sorry

end

end Bifunction

/-! ### Definition_6_29_7 (from Chap06) -/
universe u v w

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 6.29.7 names the graph domain of a bifunction `F`.
- `core/canonical`: Definition 6.29.2 already fixes the graph function as `uncurry F`,
  and Definition 4.4 already fixes effective domains through the owner `effectiveDomain`, written
  `dom(·)`.
- `bridge/view`: the source pointwise reading "the pairs `(u, x)` where `F u x < ⊤`" is not a
  second owner; it is exactly `mem_effectiveDomain` specialized to `uncurry F`.

Domain-style sampling used here:
- `Function.uncurry` (used as `uncurry`) from `Definition_6_29_2`;
- `effectiveDomain` and the notation `dom(·)` from `Definition_4_4`;
- `mem_effectiveDomain` from `Definition_4_4`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β` into a codomain with `⊤` and `<`;
- canonical owner surface: `dom(uncurry F)`;
- derived API: downstream files should use `mem_effectiveDomain` directly on
  `uncurry F`, rather than a parallel local wrapper theorem.

Layer target: `core/canonical recall/use`.
-/

section

open Function

variable {U : Type u} {X : Type v} {β : Type w}
variable [Top β] [LT β]
variable (F : U → X → β)

/- Definition 6.29.7: the graph domain of a bifunction `F` is the effective domain of its graph
function from Definition 6.29.2, namely the canonical owner set `dom(uncurry F)`. -/
#check (dom(uncurry F) : Set (U × X))

/- Pointwise bridge (without introducing a duplicate owner): membership in the graph domain is
exactly the strict-top test for the uncurried graph function. -/
#check (show ∀ p : U × X, p ∈ dom(uncurry F) ↔ F p.1 p.2 < ⊤ from
  fun p => by
    calc
      p ∈ dom(uncurry F) ↔ uncurry F p < ⊤ :=
        (_root_.mem_effectiveDomain (f := uncurry F) (x := p))
      _ ↔ F p.1 p.2 < ⊤ := by
        simp [uncurry])

end

/-! ### Lemma_6_29_7 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {α : Type w}
variable [ConditionallyCompleteLattice α] [Zero U]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.7 says that a generalized convex program cannot have a finite
  optimal value unless its objective `F₀` is proper.
- `core/canonical`: the owner theorem should live on chapter owners
  `Bifunction.IsConsistent`/`Bifunction.optimalValue` together with the Chapter 1 properness owner
  `Function.IsProper`.
- `bridge/view`: finite-optimal-value hypotheses are a derived route to consistency via
  `isConsistent_of_optimalValue_lt_top`.

Domain-style sampling used here:
- `Bifunction.IsConsistent`;
- `Bifunction.isConsistent_iff_dom_objective_nonempty`;
- `Bifunction.isConsistent_of_optimalValue_lt_top`;
- `Bifunction.optimalValue` and `optimalValue_eq_iInf`;
- `iInf_le`;
- `Function.IsProper` and `Function.isProper_iff_nonempty_dom_and_bot_lt`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → WithBotTop α`;
- primitive owner hypotheses: program consistency `IsConsistent F` and the lower bound
  `⊥ < optimalValue F`;
- derived bridge hypothesis: the upper bound `optimalValue F < ⊤`, converted to consistency using
  `isConsistent_of_optimalValue_lt_top`;
- derived conclusion: properness of `(F)₀`.

Layer target:
- a primitive `core/canonical` theorem stated on `IsConsistent F` and `optimalValue F`;
- the source-facing finite-optimal-value statement as a thin bridge corollary.
-/

-- Proof sketch (core): consistency provides nonempty `dom((F)₀)` via
-- `isConsistent_iff_dom_objective_nonempty`; then the pointwise lower bound follows from
-- `optimalValue F = ⨅ y, (F)₀ y` and `optimalValue F ≤ (F)₀ y`.
/-- Core owner form: if the generalized convex program attached to `F` is consistent and the
optimal value is strictly above `⊥`, then the objective `F₀` is proper. -/
theorem objective_isProper_of_isConsistent_and_optimalValue_bot_lt
    {F : U → X → WithBotTop α}
    (hcons : IsConsistent F)
    (hbot : ⊥ < optimalValue F) :
    ((F)₀).IsProper := by
  rw [Function.isProper_iff_nonempty_dom_and_bot_lt]
  refine ⟨(isConsistent_iff_dom_objective_nonempty F).1 hcons, ?_⟩
  intro y
  exact lt_of_lt_of_le hbot <| by
    rw [optimalValue_eq_iInf]
    exact iInf_le (F)₀ y

-- Proof sketch (bridge): convert `optimalValue F < ⊤` to consistency using
-- `isConsistent_of_optimalValue_lt_top`, then apply the core theorem above.
/-- Lemma 6.29.7, canonical owner form: if the optimal value of the generalized convex program
attached to `F` is finite, then its objective function `F₀` is proper. -/
theorem objective_isProper_of_optimalValue_bounds
    {F : U → X → WithBotTop α}
    (hbot : ⊥ < optimalValue F)
    (htop : optimalValue F < ⊤) :
    ((F)₀).IsProper := by
  exact objective_isProper_of_isConsistent_and_optimalValue_bot_lt
    (isConsistent_of_optimalValue_lt_top htop) hbot

/-- Lemma 6.29.7, source-facing finite-optimal-value form. -/
theorem objective_isProper_of_optimalValue_finite
    {F : U → X → WithBotTop α}
    (hopt : ⊥ < optimalValue F ∧ optimalValue F < ⊤) :
    ((F)₀).IsProper := by
  exact objective_isProper_of_optimalValue_bounds hopt.1 hopt.2

end

end Bifunction
