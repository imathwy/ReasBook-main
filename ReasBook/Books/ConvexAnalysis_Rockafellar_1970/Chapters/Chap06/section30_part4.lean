import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_30_18 (from Chap06) -/
noncomputable section

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 6.30.18 introduces the perturbation bifunction attached to linear
  program data `(c, a, A)`.
- `core/canonical`: the orthant constraint is the canonical cone owner `ConvexCone.positive`, and
  the perturbation term is encoded by the indicator owner `δ[𝕜](· | C)`.
- `bridge/view`: coordinate/matrix spellings are downstream bridges; this owner file keeps the
  intrinsic ordered-module statement surface.

Domain-style sampling used here:
- `orthant[𝕜](X)` and `ConvexCone.mem_positive`;
- `indicator` / `δ[𝕜](· | C)` from `Chap01.Defintion_4_8_1`;
- `Bifunction.objective` / `(·)₀` from `Chap06.Definition_6_29_12`.

Primitive data vs derived API:
- primitive source data: the objective pairing-side element `c : XStar`, the right-hand side `a`,
  and the linear map `A : X →ₗ[𝕜] U`;
- primitive source-facing owner: `linearProgramFeasibleSet a A u` and
  `linearProgram c a A`;
- derived API: pointwise unfolding, branch lemmas on/off feasibility, and the zero-slice objective
  formula.

Layer target: `source-facing` at the intrinsic ordered-module + linear-map layer.
-/

section

variable {𝕜 : Type*} {U X XStar : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid X] [PartialOrder X] [IsOrderedAddMonoid X] [Module 𝕜 X]
variable [PosSMulMono 𝕜 X]
variable [AddCommMonoid U] [Preorder U] [Module 𝕜 U]
variable [HasPairing XStar X 𝕜]

/-- Definition 6.30.18: the feasible set in the perturbation parameter `u` for the linear-program
constraints attached to `(a, A)`. -/
def linearProgramFeasibleSet
    (a : U) (A : X →ₗ[𝕜] U) (u : U) : Set X :=
  {x | x ∈ orthant[𝕜](X) ∧ a ≤ A x + u}

@[simp] theorem mem_linearProgramFeasibleSet_iff
    {a : U} {A : X →ₗ[𝕜] U} {u : U} {x : X} :
    x ∈ linearProgramFeasibleSet a A u ↔
      0 ≤ x ∧ a ≤ A x + u := by
  simp [linearProgramFeasibleSet]

/-- Definition 6.30.18: the bifunction associated with the linear program data `(c, a, A)`. -/
def linearProgram
    (c : XStar) (a : U) (A : X →ₗ[𝕜] U) :
    U → X → WithTopBot 𝕜 :=
  fun u x ↦ ((⟪c, x⟫ₚ : 𝕜) : WithTopBot 𝕜) + δ[𝕜](x | linearProgramFeasibleSet a A u)

@[simp] theorem linearProgram_apply
    (c : XStar) (a : U) (A : X →ₗ[𝕜] U) (u : U) (x : X) :
    linearProgram c a A u x =
      ((⟪c, x⟫ₚ : 𝕜) : WithTopBot 𝕜) + δ[𝕜](x | linearProgramFeasibleSet a A u) :=
  rfl

/-- On the perturbed feasible set, the LP bifunction is just the linear objective branch. -/
@[simp] theorem linearProgram_apply_of_mem
    {c : XStar} {a : U} {A : X →ₗ[𝕜] U} {u : U} {x : X}
    (hx : x ∈ linearProgramFeasibleSet a A u) :
    linearProgram c a A u x = ((⟪c, x⟫ₚ : 𝕜) : WithTopBot 𝕜) := by
  simp [linearProgram, hx]

/-- Off the perturbed feasible set, the LP bifunction takes the value `+∞`. -/
@[simp] theorem linearProgram_apply_of_notMem
    {c : XStar} {a : U} {A : X →ₗ[𝕜] U} {u : U} {x : X}
    (hx : x ∉ linearProgramFeasibleSet a A u) :
    linearProgram c a A u x = ⊤ := by
  change ((⟪c, x⟫ₚ : 𝕜) : WithTopBot 𝕜) + δ[𝕜](x | linearProgramFeasibleSet a A u) =
      (⊤ : WithTopBot 𝕜)
  simp [hx]

/-- The unperturbed objective `(linearProgram c a A)₀` of the LP bifunction is
`x ↦ ⟪c, x⟫ₚ + δ[𝕜](x | x ∈ orthant[𝕜](X), a ≤ A x + 0)`. -/
@[simp] theorem objective_linearProgram_apply
    (c : XStar) (a : U) (A : X →ₗ[𝕜] U) (x : X) :
    (linearProgram c a A)₀ x =
      ((⟪c, x⟫ₚ : 𝕜) : WithTopBot 𝕜) + δ[𝕜](x | linearProgramFeasibleSet a A 0) := by
  rfl

end

end Bifunction

/-! ### Theorem_6_30_18 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.18 states strong duality for the polyhedral primal-dual pair:
  the primal optimal value and the dual optimal value coincide unless both programs are
  inconsistent.
- `core/canonical`: the Chapter 6 owners already present are `optimalValue`,
  `upperPerturbationFunction`, `adjoint`, and `IsConsistent`.
- `bridge/view`: the source dual value `v(P*)` is rendered canonically by the dual perturbation
  value `upperPerturbationFunction (adjoint F) 0`, which Corollary 6.30.2 also identifies
  with the supremum of the dual zero-slice objective.

Primary mathematical domain:
- convex duality for polyhedral proper convex bifunctions on finite-dimensional paired
  spaces with the Chapter 6 extended-value codomain `WithBotTop 𝕜`.

Domain-style sampling used here:
- `Function.HasPolyhedralEpigraph` and its convexity/closedness API from Chapter 19;
- `optimalValue` from Definition 6.29.15;
- `upperPerturbationFunction` from Definition 6.30.11;
- `adjoint` from Definition 6.30.14;
- the primal-dual value identities at `0` from Corollary 6.30.2.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜`;
- source hypotheses: polyhedrality of the graph epigraph, properness of the graph function, and
  consistency of at least one side of the primal-dual pair;
- primitive owners already upstream: `optimalValue F`, `upperPerturbationFunction F⋆ 0`, and the
  consistency predicates for `F` and `F⋆`;
- derived API added here: the strong-duality equality of the primal and dual optimal values.

Layer target: `bridge/view`, stated directly on the canonical Chapter 6 value owners rather than
through a new wrapper for the primal-dual program pair.
-/

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type*} {XStar : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [T2Space U] [FiniteDimensional 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X] [FiniteDimensional 𝕜 X]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => ((adjoint XStar UStar F) : XStar → UStar → WithBotTop 𝕜)
local notation "q" => supᵇ(F⋆)

-- Proof sketch: use polyhedrality plus properness to upgrade `Function.uncurry F` to the closed
-- proper convex owner, and use polyhedrality again on the primal or dual perturbation function
-- that corresponds to the consistent side. Corollary 6.30.2 identifies the dual value with
-- `cl(perturbationFunction F) 0`; consistency of either the primal or the dual side forces the
-- relevant polyhedral perturbation function to be closed at `0`, so the closure value equals the
-- actual value and yields `optimalValue F = upperPerturbationFunction F⋆ 0`.
/-- Theorem 6.30.18: if `F` has polyhedral epigraph, its graph function is proper, and at least
one of the primal program `(P)` or the adjoint dual program `(P*)` is consistent, then the
optimal values of `(P)` and `(P*)` are equal. Canonically, this is the equality between the
primal optimal value `optimalValue F` and the dual perturbation value
`upperPerturbationFunction F⋆ 0`. The polyhedral-epigraph owner already includes the convexity
part of the source phrase “polyhedral proper convex.” -/
theorem optimalValue_eq_dualValue_of_polyhedral_of_primal_or_dual_consistent
    (hF_poly : (Function.uncurry F).HasPolyhedralEpigraph)
    (hF_proper : (Function.uncurry F).IsProper)
    (hconsistent : IsConsistent F ∨ IsConsistent F⋆) :
    optimalValue F = q 0 := sorry

end

end Bifunction

/-! ### Theorem_6_30_19 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.19 identifies Kuhn--Tucker vectors of the primal program `(P)`
  with optimal solutions of the dual program `(P*)`, and dually identifies Kuhn--Tucker vectors
  of `(P*)` with optimal solutions of `(P)`.
- `core/canonical`: the chapter owners already present are
  `IsKuhnTuckerVector`, `IsDualKuhnTuckerVector`, `perturbationFunction`, `objective`,
  `adjoint`, `upperPerturbationFunction`, and the convex closure `cl(·)`.
- `bridge/view`: the source phrase “optimal solution” is rendered directly by the ambient
  optimizer owners `IsMinOn` and `IsMaxOn`, rather than by a new local optimal-solution wrapper
  for generalized primal/dual bifunction programs.

Domain-style sampling used here:
- `IsKuhnTuckerVector` from Definition 6.29.19;
- `objective`, `perturbationFunction`, and `upperPerturbationFunction`;
- `adjoint` from Definition 6.30.14;
- the conjugacy identities of Theorem 6.30.15.

Primitive data vs derived API:
- primitive input: a closed convex bifunction `F : U → X → WithBotTop 𝕜`;
- normality assumptions: the primal perturbation function and the dual upper perturbation function
  agree with their closures at `0`;
- derived API: the two source iff-statements, split atomically.

Layer target: `source-facing`, stated directly on the existing Chapter 6 owners without
introducing a parallel “dual optimal solution” or “dual Kuhn--Tucker package”.
-/

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type*} {XStar : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [Neg UStar]
variable [Zero XStar] [TopologicalSpace XStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "p" => perturbationFunction F
local notation "F⋆" => ((adjoint XStar UStar F) : XStar → UStar → WithBotTop 𝕜)
local notation "q" => upperPerturbationFunction F⋆
local notation "f₀" => ((F)₀ : X → WithBotTop 𝕜)
local notation "d₀" => ((F⋆)₀ : UStar → WithBotTop 𝕜)

/- Theorem 6.30.19 is split into two atomic declarations, one for each direction stated
independently in the source. -/

-- Proof sketch: use primal normality to replace `p` by `cl p` at `0`, then apply the conjugacy
-- identity from Theorem 6.30.15 identifying `(adjoint F)₀` with the concave conjugate of
-- `-p`. The Kuhn--Tucker owner `IsKuhnTuckerVector F uStar` is the supporting-hyperplane
-- condition at `0` for `p`, while attainment of the supremum of `(adjoint F)₀` at
-- `uStar` is the equivalent
-- concave-subgradient optimality condition under that conjugacy.
/-- Theorem 6.30.19 (1): if the primal perturbation function and the dual upper perturbation
function are normal at `0`, then a vector `u⋆` is a Kuhn--Tucker vector for the convex program
associated with `F` if and only if it is an optimal solution of the dual concave program,
rendered canonically as a maximizer of the dual zero-slice objective `(F⋆)₀`. -/
theorem isKuhnTuckerVector_iff_isMaxOn_dualObjective_of_normality
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F))
    (hp_normal : p 0 = cl(p) 0)
    (hq_normal : q 0 = (-cl(-q)) 0)
    (uStar : UStar) :
    IsKuhnTuckerVector F uStar ↔
      IsMaxOn d₀ Set.univ uStar := sorry

-- Proof sketch: apply the previous primal-dual clause to the adjoint bifunction `F⋆`.
-- The dual normality hypothesis is exactly the primal normality condition for `F⋆`, while the
-- primal normality hypothesis converts the double-adjoint closure back to the original primal
-- objective. This identifies Kuhn--Tucker vectors for `(P*)` with minimizers of `(F)₀`.
/-- Theorem 6.30.19 (2): under the same two normality assumptions, a vector `x` is a Kuhn--Tucker
vector for the dual program `(P*)`, rendered canonically by the Chapter 6 source-facing owner
`IsDualKuhnTuckerVector`, if and only if it is an optimal solution of the primal program,
rendered canonically as a minimizer of the primal zero-slice objective `(F)₀`. -/
theorem isDualKuhnTuckerVector_iff_isMinOn_objective_of_normality
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F))
    (hp_normal : p 0 = cl(p) 0)
    (hq_normal : q 0 = (-cl(-q)) 0)
    (x : X) :
    IsDualKuhnTuckerVector UStar XStar F x ↔
      IsMinOn f₀ Set.univ x := sorry

end

end Bifunction

/-! ### Theorem_6_30_20 (from Chap06) -/
noncomputable section

open scoped BigOperators Pointwise Rockafellar

universe u v w

namespace OrdinaryConvexProgram

attribute [local instance] Classical.propDecidable

section

variable {m : ℕ}
variable {𝕜 : Type w}
variable {X : Type u} {XStar : Type v}
variable {ι : Type}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [HasPairing X XStar 𝕜]
variable [Fintype ι] [Fact (Fintype.card ι = m)]

variable (P : OrdinaryConvexProgram 𝕜 X (WithBotTop 𝕜) m 0 ι)

local notation "F" => (P.pureInequalityPerturbedProblem : (ι → 𝕜) → X → WithBotTop 𝕜)
local notation "weighted" => (fun u : ι → 𝕜 ↦ P.weightedObjective u 0)

/-- The source multiplier space `𝕜^m`, represented intrinsically as `ι → 𝕜`, carries the canonical
pairing used by the Chapter 6 adjoint owner and by the pure-inequality specialization of
`P.perturbedProblem`. -/
local instance : HasPairing (ι → 𝕜) (ι → 𝕜) 𝕜 :=
  instHasPairingOfHasLinearPairing

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.20 computes the adjoint of the bifunction attached to a
  pure-inequality ordinary convex program.
- `core/canonical`: Chapter 6 already owns the perturbed-problem bifunction as
  `P.perturbedProblem`, its pure-inequality bridge owner `P.pureInequalityPerturbedProblem`, and
  the multiplier-weighted primal objective `P.weightedObjective`.
- `bridge/view`: in the case `s = 0`, the source bifunction is exactly the canonical chapter
  bridge owner `P.pureInequalityPerturbedProblem`.

Domain-style sampling used here:
- `OrdinaryConvexProgram.perturbedProblem` from `Definition_6_28_4`;
- `OrdinaryConvexProgram.pureInequalityPerturbedProblem` from `Definition_6_28_4`;
- `OrdinaryConvexProgram.weightedObjective` from `Definition_6_28_3`, specialized to the
  pure-inequality case by setting the equality block to `0`;
- `Bifunction.adjoint` and the scoped adjoint notation `(·)⋆` from
  `Definition_6_30_14`;
- the canonical function-space pairing supplied by `instHasPairingOfHasLinearPairing`.

Primitive data vs derived API:
- primitive source data: the ordinary convex program `P` and the multiplier vector
  `uStar : ι → 𝕜`;
- primitive owner objects: `P.pureInequalityPerturbedProblem` and
  `P.weightedObjective uStar 0`;
- main derived API: the explicit adjoint-value formula for that pure-inequality bridge, with the
  admissible-multiplier condition expressed through the canonical order owner `0 ≤ uStar`.

Layer target: `bridge/view`, with the theorem centered on the existing ordinary-program owners and
only the canonical `s = 0` bridge owner `P.pureInequalityPerturbedProblem` exposed on the
bifunction side.
-/

-- Proof sketch: start from the owner identity
-- `(P.pureInequalityPerturbedProblem)⋆ xStar uStar =
--  -((Function.uncurry P.pureInequalityPerturbedProblem)⋆ (-uStar, xStar))`.
-- A non-admissible multiplier vector forces the value `⊥`, while for an admissible multiplier
-- `uStar` satisfying `0 ≤ uStar` the perturbation infimum occurs at the boundary values of the
-- inequality block, leaving the negative Fenchel conjugate of
-- `P.weightedObjective uStar 0`.
/-- Theorem 6.30.20: the adjoint of the perturbed-problem bifunction of a pure-inequality
ordinary convex program is the negative Fenchel conjugate of the weighted primal objective when
the multiplier vector is admissible in the canonical order interval `Set.Ici (0 : ι → 𝕜)`,
equivalently when `0 ≤ uStar`, and it is `-∞` otherwise. -/
theorem adjointFunction_pureInequalityPerturbedProblem_apply
    (xStar : XStar) (uStar : ι → 𝕜) :
    F⋆ xStar uStar =
      if 0 ≤ uStar then
        -((weighted uStar)⋆ xStar)
      else
        (⊥ : WithBotTop 𝕜) := sorry

end

end OrdinaryConvexProgram

/-! ### Theorem_6_30_21 (from Chap06) -/
noncomputable section

open scoped BigOperators Pointwise Rockafellar Function

universe u v w

attribute [local instance] Classical.propDecidable

section

variable {m : ℕ}
variable {𝕜 : Type w}
variable {X : Type u} {XStar : Type v}
variable {ι : Type}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [HasPairing X XStar 𝕜] [Zero XStar]
variable [Fintype ι] [Fact (Fintype.card ι = m)]

variable (P : OrdinaryConvexProgram 𝕜 X (WithBotTop 𝕜) m 0 ι)

local notation "F" => (P.pureInequalityPerturbedProblem : (ι → 𝕜) → X → WithBotTop 𝕜)
local notation "F⋆₀" =>
  (((F⋆ : XStar → (ι → 𝕜) → WithBotTop 𝕜)₀) : (ι → 𝕜) → WithBotTop 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.21 identifies the dual zero-slice objective of the pure-inequality
  ordinary convex program `P`, then characterizes its feasible multiplier vectors.
- `core/canonical`: the relevant Chapter 6 owners already exist upstream as
  the adjoint and zero-slice owners `(·)⋆`, `(·)₀`, the pure-inequality bridge owner `F`, and
  `P.weightedObjective`.
- `bridge/view`: in the case `s = 0`, the source bifunction is exactly the canonical chapter
  bridge owner `F = P.pureInequalityPerturbedProblem`.

Domain-style sampling used here:
- `OrdinaryConvexProgram.adjointFunction_pureInequalityPerturbedProblem_apply` from
  `Theorem_6_30_20`;
- `Bifunction.objective` / `(·)₀` from `Definition_6_30_16`;
- `OrdinaryConvexProgram.pureInequalityPerturbedProblem` from `Definition_6_28_4`;
- `OrdinaryConvexProgram.weightedObjective` from `Definition_6_28_3`, specialized to the
  pure-inequality case by setting the equality block to `0`;
- `effectiveDomain` / `dom(·)` from `Chap01.Definition_4_4`.

Primitive data vs derived API:
- primitive source data: the program `P` and the multiplier vector `uStar : ι → 𝕜`;
- primitive owner-side objects: `F` and `P.weightedObjective uStar 0`;
- derived API: the explicit dual-objective formula and the dual-feasibility criterion, both using
  the canonical admissibility condition `0 ≤ uStar`.

Layer target: `bridge/view`, with the theorem centered on the existing ordinary-program owners and
only the canonical `s = 0` bridge owner `F` exposed on the bifunction side.
-/

-- Proof sketch: specialize Theorem 6.30.20 at `xStar = 0`, then rewrite the zero slice through
-- the zero slice of the canonical pure-inequality bridge owner `F`.
-- For any function `g`, `-(g⋆ 0)` is the indexed infimum of `g`, so the surviving
-- admissible-multiplier branch becomes the infimum of the canonical weighted
-- objective `P.weightedObjective uStar 0`.
/-- Theorem 6.30.21: the zero-slice objective of the dual concave program attached to the
perturbed problem of a pure-inequality ordinary convex program equals the infimum of the weighted
primal objective when the multiplier vector satisfies the canonical admissibility condition
`0 ≤ uStar`, and it is `-∞`
otherwise. -/
theorem OrdinaryConvexProgram.dualObjective_pureInequalityPerturbedProblem_apply
    (uStar : ι → 𝕜) :
    F⋆₀ uStar =
      if 0 ≤ uStar then
        ⨅ x : X, P.weightedObjective uStar 0 x
      else
        (⊥ : WithBotTop 𝕜) := sorry

-- Proof sketch: rewrite feasibility of the dual objective as membership in
-- `dom (-((F⋆)₀))`, then
-- substitute the owner formula
-- above. The admissible branch is exactly the source condition that the weighted-objective
-- infimum be strictly above `-∞`.
/-- A multiplier vector is dual feasible for the pure-inequality ordinary convex program exactly
when it satisfies the canonical admissibility condition `0 ≤ uStar` and the infimum of the
weighted primal objective is strictly above `-∞`. -/
theorem OrdinaryConvexProgram.dualFeasible_iff_nonnegative_and_weightedObjective_boundedBelow
    (uStar : ι → 𝕜) :
    uStar ∈ dom(-F⋆₀) ↔
      0 ≤ uStar ∧
        (⊥ : WithBotTop 𝕜) < ⨅ x : X, P.weightedObjective uStar 0 x := sorry

end

namespace Function

section ConjugateDomain

variable {m : ℕ}
variable {𝕜 : Type w} {X : Type u} {XStar : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommMonoid XStar] [Module 𝕜 XStar] [HasPairing X XStar 𝕜]

local notation "U" => Fin m → 𝕜

-- Proof sketch: apply the bounded-below criterion at the origin to
-- `g := L[Finset.univ](f₀, f, uStar)`, which rewrites the source
-- condition `⊥ < ⨅ x, g x` as `0 ∈ dom(g⋆)`. Then use the hypothesis `hdom` identifying `dom(g⋆)`
-- with the Minkowski sum of the conjugate domains of `f₀` and the weighted constraint functions.
/-- Under the source conjugate-domain formula for the weighted objective, the condition that
`f₀ + v₁* f₁ + ⋯ + v_m* f_m` be bounded below is equivalent to the origin lying in the Minkowski
sum `dom(f₀⋆) + v₁* dom(f₁⋆) + ⋯ + v_m* dom(f_m⋆)`. -/
theorem lagrangeCombination_boundedBelow_iff_zero_mem_sum_conjugateDomains_of_conjugateDomain_eq
    (f₀ : X → WithBotTop 𝕜) (f : Fin m → X → WithBotTop 𝕜) (uStar : U)
    (hdom :
      dom(((L[Finset.univ](f₀, f, uStar))⋆ : XStar → WithBotTop 𝕜)) =
        dom((f₀⋆ : XStar → WithBotTop 𝕜)) +
          ∑ i : Fin m, uStar i • dom(((f i)⋆ : XStar → WithBotTop 𝕜))) :
    (⊥ : WithBotTop 𝕜) < ⨅ x : X, L[Finset.univ](f₀, f, uStar) x ↔
      (0 : XStar) ∈
        dom((f₀⋆ : XStar → WithBotTop 𝕜)) +
          ∑ i : Fin m, uStar i • dom(((f i)⋆ : XStar → WithBotTop 𝕜)) := sorry

end ConjugateDomain

end Function

/-! ### Theorem_6_30_22 (from Chap06) -/
noncomputable section

open scoped BigOperators NNReal Rockafellar

universe u v w

attribute [local instance] Classical.propDecidable

namespace Bifunction

section

variable {E : Type u} {𝕜 : Type w} {ι : Type v}
variable [AddCommGroup E]
variable [Preorder 𝕜]

local notation "U" => (ι → 𝕜) × (E × (ι → E))

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.22 studies the specific enlarged-perturbation bifunction
  `G_w (x) = f₀ (x - x₀) + δ(x | f_i (x - x_i) ≤ v_i)`.
- `core/canonical`: the chapter owners on the dual side are already
  `Bifunction.adjoint` from Definition 6.30.14 and the right scalar multiple `•ʳ` from
  Text 5.4.2, so the main theorem should be a direct formula on those owners rather than on a
  parallel local scaled-conjugate wrapper.
- `bridge/view`: the theorem also has a zero-slice dual-objective specialization, recorded here as
  a companion theorem through the existing zero-slice owner `Bifunction.objective`.

Domain-style sampling used here:
- `Bifunction.adjoint` from `Definition_6_30_14`;
- `Bifunction.objective` from `Definition_6_29_12`;
- `Function.rightScalarMul` / `•ʳ` from `Chap01.Text_5_4_2`;
- `convexConjugate` / `(·)⋆` and the Chapter 1 indicator owner `δ(· | ·)`;
- product and inner-product pairing owners from `Chap01.HasPairing`, reused implicitly through the
  existing chapter notation `⟪·, ·⟫ₚ`.

Primitive data vs derived API:
- primitive function data: the objective branch `f₀` and the finite family of constraints `f`;
- primitive source-facing objects introduced here: the feasible slice
  `enlargedPerturbationFeasibleSet` and the bifunction `enlargedPerturbationProgram`;
- derived API: the adjoint formula and its zero-slice dual-objective specialization.
-/

/-- The feasible slice cut out by the enlarged-perturbation thresholds `u` and shifts `xs`: it is
the set of all `x` satisfying `f i (x - xs i) ≤ u i` for every constraint index `i`. -/
def enlargedPerturbationFeasibleSet
    (f : ι → E → WithBotTop 𝕜) (u : ι → 𝕜) (xs : ι → E) : Set E :=
  {x | ∀ i : ι, f i (x - xs i) ≤ (u i : WithBotTop 𝕜)}

-- Proof sketch: unfold `enlargedPerturbationFeasibleSet`; membership in the defining set-builder
-- is exactly the displayed family of shifted inequality constraints.
/-- Membership in the enlarged-perturbation feasible slice is the coordinatewise family of
inequalities `f i (x - xs i) ≤ u i`. -/
@[simp] theorem mem_enlargedPerturbationFeasibleSet
    (f : ι → E → WithBotTop 𝕜) (u : ι → 𝕜) (xs : ι → E) (x : E) :
    x ∈ enlargedPerturbationFeasibleSet f u xs ↔
      ∀ i : ι, f i (x - xs i) ≤ (u i : WithBotTop 𝕜) :=
  Iff.rfl

/-- The enlarged-perturbation bifunction of Theorem 6.30.22, with perturbation variable
`w = (u, x₀, (xᵢ)ᵢ)` represented as `(u, (x₀, xs))`. -/
def enlargedPerturbationProgram
    [Add 𝕜] [Zero 𝕜]
    (f0 : E → WithBotTop 𝕜) (f : ι → E → WithBotTop 𝕜) :
    U → E → WithBotTop 𝕜 :=
  fun w x ↦
    f0 (x - w.2.1) + δ[𝕜](x | enlargedPerturbationFeasibleSet f w.1 w.2.2)

-- Proof sketch: unfold `enlargedPerturbationProgram`; evaluation at `(u, xs, x)` is exactly the
-- displayed objective-shift plus indicator-of-feasible-slice formula.
/-- Evaluating the enlarged-perturbation bifunction gives the shifted objective
`f₀ (x - x₀)` plus the indicator of the slice cut out by the shifted constraints. -/
@[simp] theorem enlargedPerturbationProgram_apply
    [Add 𝕜] [Zero 𝕜]
    (f0 : E → WithBotTop 𝕜) (f : ι → E → WithBotTop 𝕜)
    (u : ι → 𝕜) (x0 : E) (xs : ι → E) (x : E) :
    enlargedPerturbationProgram f0 f (u, (x0, xs)) x =
      f0 (x - x0) + δ[𝕜](x | enlargedPerturbationFeasibleSet f u xs) :=
  rfl

end

section

variable {E : Type u} {EStar : Type v} {𝕜 : Type w} {ι : Type*}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [Fintype ι]
variable [AddCommGroup E] [SMul 𝕜 E]
variable [AddCommMonoid EStar] [Neg EStar] [SMul 𝕜 EStar] [HasPairing E EStar 𝕜]

local notation "U" => (ι → 𝕜) × (E × (ι → E))
local notation "UStar" => (ι → 𝕜) × (EStar × (ι → EStar))
local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-- The multiplier block `𝕜^ι` carries the canonical coordinate pairing used by the perturbation
adjoint owner. -/
local instance : HasPairing (ι → 𝕜) (ι → 𝕜) 𝕜 := instHasPairingOfHasLinearPairing

/-- The perturbation-shift block `(x₀, (xᵢ)ᵢ)` pairs with its dual block
`(x⋆₀, (x⋆ᵢ)ᵢ)` by the distinguished ambient pairing plus the coordinatewise sum. -/
local instance :
    HasPairing (E × (ι → E)) (EStar × (ι → EStar)) 𝕜 where
  pairing xs xsStar := ⟪xs.1, xsStar.1⟫ₚ + ∑ i, ⟪xs.2 i, xsStar.2 i⟫ₚ

-- Proof sketch: expand `adjoint` for the owner
-- `enlargedPerturbationProgram f0 f`, rewrite the product pairing on
-- `((ι → 𝕜) × (E × (ι → E))) × E`, and then perform the source changes of variables
-- `y₀ = x - x₀` and `yᵢ = x - xᵢ`. Taking the infimum over the free `x` variable gives `⊥`
-- unless `x0Star + ∑ i, xsStar i = xStar` in the explicit dual ambient type `EStar`.
-- The remaining terms
-- split into the Fenchel conjugate of `f₀`
-- and the one-constraint scalar cases recorded by the existing right scalar multiple owner `•ʳ`;
-- negative multipliers
-- force the value `⊥`.
/-- Theorem 6.30.22: the adjoint of the enlarged-perturbation program equals the negative sum of
the objective conjugate and the scaled constraint conjugates when the multiplier vector satisfies
the canonical order condition `0 ≤ uStar` and the distinguished-plus-family dual shift block
sums to `x⋆`;
otherwise the adjoint value is `-∞`. -/
theorem adjointFunction_enlargedPerturbationProgram_apply
    (f0 : E → WithBotTop 𝕜) (f : ι → E → WithBotTop 𝕜)
    (hf0_proper : f0.IsProper) (hf0_convex : f0.IsConvex 𝕜)
    (hf_proper : ∀ i : ι, (f i).IsProper)
    (hf_convex : ∀ i : ι, (f i).IsConvex 𝕜)
    (hf_dom : ∀ i : ι, dom(f i) = Set.univ)
    (xStar : EStar) (uStar : ι → 𝕜) (x0Star : EStar) (xsStar : ι → EStar) :
    (enlargedPerturbationProgram f0 f)⋆ xStar (uStar, (x0Star, xsStar)) =
      if hu : 0 ≤ uStar then
        if hsum : x0Star + ∑ i, xsStar i = xStar then
          - (((f0⋆ : EStar → WithBotTop 𝕜) x0Star) +
              ∑ i : ι, ((⟨uStar i, hu i⟩ : 𝕜≥0) •ʳ (f i)⋆) (xsStar i))
        else
          ⊥
      else
        ⊥ := sorry

-- Proof sketch: specialize `adjointFunction_enlargedPerturbationProgram_apply` to `xStar = 0`
-- and rewrite the zero slice through the owner notation `((F⋆)₀) u = F⋆ 0 u`.
/-- The zero-slice dual objective of the enlarged-perturbation program is the source maximization
problem with nonnegative multipliers and vanishing distinguished-plus-family dual shift sum. -/
theorem objective_adjointFunction_enlargedPerturbationProgram_apply
    (f0 : E → WithBotTop 𝕜) (f : ι → E → WithBotTop 𝕜)
    (hf0_proper : f0.IsProper) (hf0_convex : f0.IsConvex 𝕜)
    (hf_proper : ∀ i : ι, (f i).IsProper)
    (hf_convex : ∀ i : ι, (f i).IsConvex 𝕜)
    (hf_dom : ∀ i : ι, dom(f i) = Set.univ)
    (uStar : ι → 𝕜) (x0Star : EStar) (xsStar : ι → EStar) :
    (((enlargedPerturbationProgram f0 f)⋆ : EStar → UStar → WithBotTop 𝕜)₀)
      (uStar, (x0Star, xsStar)) =
      if hu : 0 ≤ uStar then
        if hsum : x0Star + ∑ i, xsStar i = (0 : EStar) then
          - (((f0⋆ : EStar → WithBotTop 𝕜) x0Star) +
              ∑ i : ι, ((⟨uStar i, hu i⟩ : 𝕜≥0) •ʳ (f i)⋆) (xsStar i))
        else
          ⊥
      else
        ⊥ := sorry

end

end Bifunction

/-! ### Theorem_6_30_23 (from Chap06) -/
noncomputable section

open scoped BigOperators Gradient RealInnerProductSpace

universe u

namespace Function

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ}
variable (f₀ : E → ℝ) (f : Fin m → E → ℝ)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.23 characterizes feasible dual multipliers for a pure-inequality
  Lagrange dual by the existence of a point where the weighted objective has zero gradient, and
  then identifies the dual value with the attained primal weighted value.
- `core/canonical`: the project already owns the weighted objective as the finite Lagrange
  combination `L[Finset.univ](f₀, f, uStar)` together with the Chapter 6 minimizer owner
  `minimumSet`, so the theorem should be stated on that owner layer rather than through a new
  dual-feasibility wrapper or repeated `IsMinOn _ Set.univ _` packaging.
- `bridge/view`: the textbook dual-feasibility phrase is expressed here by the bounded-below
  condition from the preceding dual-feasibility criterion, while the Euclidean gradient surface is
  kept directly through `∇`.

Domain-style sampling used here:
- the finite weighted-objective notation `L[s](f₀, f, lam)` from `Corollary_6_28_2`;
- `minimumSet` from `Definition_6_27_3`;
- the Euclidean gradient owner `∇` from `Mathlib.Analysis.Calculus.Gradient.Basic`;
- the Chapter 25 singleton-subdifferential/gradient bridge used later to relate first-order
  conditions to minimizers;
- the Chapter 6 zero-subgradient minimizer criterion that turns vanishing first-order data into
  minimum-set membership for convex functions.

Primitive data vs derived API:
- primitive source data: the ambient space `E`, the objective `f₀`, the constraint family `f`,
  and the multiplier vector `uStar`;
- primitive owner object: the weighted Lagrange combination
  `L[Finset.univ](f₀, f, uStar)` and its minimum-set owner `minimumSet`;
- derived API: bounded-below versus critical-point existence for nonnegative multipliers, the
  minimum-set consequence of vanishing gradient, and the resulting value identity.

Layer target: `bridge/view`, keeping the theorem on the canonical weighted-objective owner rather
than introducing a second public owner for the dual feasible set.
-/

-- Proof sketch: for a nonnegative multiplier vector, the weighted Lagrange combination remains
-- convex. If its infimum is finite, the attainment hypothesis yields a minimizer `x`; the
-- Chapter 25 gradient/subdifferential bridge together with the Chapter 6 zero-subgradient
-- criterion then gives `∇ (L[Finset.univ](f₀, f, uStar)) x = 0`. Conversely, a vanishing
-- gradient gives the zero-subgradient condition at `x`, hence `x` is a global minimizer of the
-- convex weighted objective and its infimum is therefore strictly above `-∞`.
/-- Theorem 6.30.23: under convexity, differentiability, and attainment of every finite infimum
for nonnegative multipliers, the bounded-below condition for the weighted Lagrange combination is
equivalent to the existence of a point where its gradient vanishes. This is the gradient form of
the dual-feasibility criterion for the pure-inequality dual program. -/
theorem boundedBelow_lagrangeCombination_iff_exists_zero_gradient_of_nonneg
    (hf₀_convex : ConvexOn ℝ Set.univ f₀)
    (hf_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (f i))
    (hf₀_diff : Differentiable ℝ f₀)
    (hf_diff : ∀ i : Fin m, Differentiable ℝ (f i))
    (hattain :
      ∀ uStar : Fin m → ℝ, 0 ≤ uStar →
        (⊥ : WithBotTop ℝ) < ⨅ x : E, (((L[Finset.univ](f₀, f, uStar)) x : ℝ) : WithBotTop ℝ) →
          ∃ x : E, x ∈ minimumSet (L[Finset.univ](f₀, f, uStar)))
    (uStar : Fin m → ℝ) (huStar : 0 ≤ uStar) :
    ((⊥ : WithBotTop ℝ) < ⨅ x : E, (((L[Finset.univ](f₀, f, uStar)) x : ℝ) : WithBotTop ℝ)) ↔
      ∃ x : E, ∇ (L[Finset.univ](f₀, f, uStar)) x = 0 := sorry

-- Proof sketch: when `uStar ≥ 0`, the weighted Lagrange combination is convex. A vanishing
-- gradient at `x` yields the zero-subgradient condition there, so `x` is a global minimizer.
-- This owner-level conclusion is the canonical Chapter 6 minimizer statement; the value identity
-- below is a direct companion extracted from it.
/-- For a nonnegative multiplier vector, any point where the gradient of the weighted Lagrange
combination vanishes belongs to the canonical minimum set of that weighted objective. -/
theorem mem_minimumSet_lagrangeCombination_of_nonneg_of_zero_gradient
    (hf₀_convex : ConvexOn ℝ Set.univ f₀)
    (hf_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (f i))
    (hf₀_diff : Differentiable ℝ f₀)
    (hf_diff : ∀ i : Fin m, Differentiable ℝ (f i))
    {uStar : Fin m → ℝ} (huStar : 0 ≤ uStar) {x : E}
    (hx : ∇ (L[Finset.univ](f₀, f, uStar)) x = 0) :
    x ∈ minimumSet (L[Finset.univ](f₀, f, uStar)) := sorry

-- Proof sketch: first pass from the zero-gradient hypothesis to the minimum-set owner above.
-- Then rewrite minimum-set membership as pointwise domination of the weighted objective and
-- identify the corresponding `WithBotTop ℝ` infimum value.
/-- Companion value formula: for a nonnegative multiplier vector, any point where the gradient of
the weighted Lagrange combination vanishes realizes its infimum. -/
theorem lagrangeCombination_eq_iInf_of_nonneg_of_zero_gradient
    (hf₀_convex : ConvexOn ℝ Set.univ f₀)
    (hf_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (f i))
    (hf₀_diff : Differentiable ℝ f₀)
    (hf_diff : ∀ i : Fin m, Differentiable ℝ (f i))
    {uStar : Fin m → ℝ} (huStar : 0 ≤ uStar) {x : E}
    (hx : ∇ (L[Finset.univ](f₀, f, uStar)) x = 0) :
    (((L[Finset.univ](f₀, f, uStar)) x : ℝ) : WithBotTop ℝ) =
      ⨅ y : E, (((L[Finset.univ](f₀, f, uStar)) y : ℝ) : WithBotTop ℝ) := by
  have hxMin : x ∈ minimumSet (L[Finset.univ](f₀, f, uStar)) :=
    mem_minimumSet_lagrangeCombination_of_nonneg_of_zero_gradient
      f₀ f hf₀_convex hf_convex hf₀_diff hf_diff huStar hx
  refine le_antisymm ?_ (iInf_le _ x)
  refine le_iInf fun y ↦ ?_
  exact WithBotTop.coe_le_coe.mpr (mem_minimumSet_iff.mp hxMin y)

end

end Function

/-! ### Theorem_6_30_24 (from Chap06) -/
noncomputable section

open scoped BigOperators Rockafellar

universe u v w u' v' w'

attribute [local instance] Classical.propDecidable

namespace Bifunction

section

variable {𝕜 : Type w}
variable {X : Type u} {XStar : Type u'}
variable {Y₀ : Type v} {Y₀Star : Type v'}
variable {ι : Type*} {Y : ι → Type w} {YStar : ι → Type w'}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [Fintype ι]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup XStar] [Module 𝕜 XStar] [HasPairing X XStar 𝕜]
variable [AddCommGroup Y₀] [Module 𝕜 Y₀]
variable [AddCommGroup Y₀Star] [Module 𝕜 Y₀Star] [HasPairing Y₀ Y₀Star 𝕜]
variable [∀ i, AddCommGroup (Y i)] [∀ i, Module 𝕜 (Y i)]
variable [∀ i, AddCommGroup (YStar i)] [∀ i, Module 𝕜 (YStar i)]
variable [∀ i, HasPairing (Y i) (YStar i) 𝕜]

local notation "U" => (ι → 𝕜) × (Y₀ × ((i : ι) → Y i))
local notation "UStar" => (ι → 𝕜) × (Y₀Star × ((i : ι) → YStar i))

private def intermediateProgramConstraint
    (h : ∀ i : ι, Y i → WithBotTop 𝕜)
    (A : ∀ i : ι, X →ₗ[𝕜] Y i)
    (a : ∀ i : ι, Y i)
    (aStar : ι → XStar) (α : ι → 𝕜)
    (w : U) :
    ι → X → WithBotTop 𝕜 :=
  fun i x ↦
    h i (A i x + a i - w.2.2 i) + ((⟪x, aStar i⟫ₚ : 𝕜) : WithBotTop 𝕜) + α i

private def intermediateProgramBound
    (w : U) : ι → WithBotTop 𝕜 :=
  fun i ↦ w.1 i

/-- The multiplier block `𝕜^ι`, encoded as `ι → 𝕜`, carries the canonical coordinate pairing
used by the intermediate-program adjoint owner. -/
local instance instHasPairingIntermediateProgramMultiplier :
    HasPairing (ι → 𝕜) (ι → 𝕜) 𝕜 :=
  instHasPairingOfHasLinearPairing

/-- The family of perturbation shifts pairs with its dual family by summing the coordinate
pairings. -/
local instance instHasPairingIntermediateProgramShiftFamily :
    HasPairing ((i : ι) → Y i) ((i : ι) → YStar i) 𝕜 where
  pairing p pStar := ∑ i, ⟪p i, pStar i⟫ₚ

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.24 computes the adjoint value of the intermediate-program
  bifunction `H`, where each objective/constraint branch is represented as a closed proper convex
  function after an affine change of variables.
- `core/canonical`: the existing owner for adjoint values is `Bifunction.adjoint`, so the
  source object `H_{x⋆}⋆(w⋆)` is stated directly on that owner rather than through a parallel
  surrogate package.
- `bridge/view`: the primal and dual feasibility conditions are exposed as source-facing feasible
  set owners, and the explicit dual objective is recorded directly on the actual dual
  perturbation-parameter type.

Domain-style sampling used here:
- `Bifunction.adjoint` from `Definition_6_30_14`;
- the canonical dual zero-slice owner `((adjoint XStar UStar F)₀)` from
  `Definition_6_30_16`;
- `convexInequalitySolutionSet` and `mem_convexInequalitySolutionSet` from
  `Chap04.Text_21_0_1`;
- `convexInequalitySolutionSetOn` from `Chap04.Text_21_0_1`, which shows the chapter's
  finite-subsystem owner layer for the same kind of feasible set;
- `convexConjugate` and the notation `f⋆` from `Chap03.Defn_12_2`;
- `HasPairing`-based evaluations `⟪·, ·⟫ₚ` on all primal/dual blocks;
- `indicatorFunction` and the notation `δ[𝕜](· | ·)` from `Chap01.Defintion_4_8_1`;
- the generic ordered-scalar Chapter 6 owner layer in `Theorem_6_30_20`.

Primitive data vs derived API:
- primitive source data: the affine representation data
  `(h₀, h, A₀, A, a₀, a, a₀⋆, a⋆, α₀, α)` and the dual affine maps `(A₀⋆, A⋆)`;
- primitive Chapter 21 owner inputs: `intermediateProgramConstraint` and
  `intermediateProgramBound`, which feed the canonical all-weak feasible-set owner
  `convexInequalitySolutionSet`;
- source-facing owner: `intermediateProgramBifunction`;
- core/canonical dual owner: `adjoint` applied to `intermediateProgramBifunction`;
- bridge/view owners: `intermediateProgramDualObjective` and
  `intermediateProgramDualFeasibleSet`;
- main derived API: the explicit adjoint formula in indicator form, together with its source
  case-split companion and the zero-slice specialization through the canonical owner `(·)₀`.

Layer target: `source-facing`, while keeping the dual-space part on the intrinsic pairing-dual
layer and the primal feasibility side on the Chapter 21 feasible-set owner rather than a local
wrapper or raw `if` guards.
-/

/-- The intermediate-program bifunction `H` attached to an affine representation of the objective
and constraint functions. It is the affine objective branch plus the indicator of the feasible
slice cut out by the shifted threshold constraints, expressed directly on the Chapter 21
feasible-set owner. -/
def intermediateProgramBifunction
    (h₀ : Y₀ → WithBotTop 𝕜) (h : ∀ i : ι, Y i → WithBotTop 𝕜)
    (A₀ : X →ₗ[𝕜] Y₀) (A : ∀ i : ι, X →ₗ[𝕜] Y i)
    (a₀ : Y₀) (a : ∀ i : ι, Y i)
    (a₀Star : XStar) (aStar : ι → XStar)
    (α₀ : 𝕜) (α : ι → 𝕜) :
    U → X → WithBotTop 𝕜 :=
  fun w x ↦
    h₀ (A₀ x + a₀ - w.2.1) + ((⟪x, a₀Star⟫ₚ : 𝕜) : WithBotTop 𝕜) + α₀ +
      δ[𝕜](x |
        convexInequalitySolutionSet
          (fun _ : ι ↦ .le)
          (intermediateProgramConstraint h A a aStar α w)
          (intermediateProgramBound w))

/-- Evaluating the intermediate-program bifunction gives the affine objective branch plus the
indicator of the source feasible slice. -/
@[simp] theorem intermediateProgramBifunction_apply
    (h₀ : Y₀ → WithBotTop 𝕜) (h : ∀ i : ι, Y i → WithBotTop 𝕜)
    (A₀ : X →ₗ[𝕜] Y₀) (A : ∀ i : ι, X →ₗ[𝕜] Y i)
    (a₀ : Y₀) (a : ∀ i : ι, Y i)
    (a₀Star : XStar) (aStar : ι → XStar)
    (α₀ : 𝕜) (α : ι → 𝕜)
    (w : U) (x : X) :
    intermediateProgramBifunction h₀ h A₀ A a₀ a a₀Star aStar α₀ α w x =
      h₀ (A₀ x + a₀ - w.2.1) + ((⟪x, a₀Star⟫ₚ : 𝕜) : WithBotTop 𝕜) + α₀ +
        δ[𝕜](x |
          convexInequalitySolutionSet
            (fun _ : ι ↦ .le)
            (intermediateProgramConstraint h A a aStar α w)
            (intermediateProgramBound w)) :=
  rfl

-- Proof sketch: rewrite `intermediateProgramBifunction` by the indicator owner, then split on
-- membership in the Chapter 21 feasible set
-- `convexInequalitySolutionSet (fun _ : ι ↦ .le)
--    (intermediateProgramConstraint h A a aStar α w) (intermediateProgramBound w)`.
/-- Evaluating the intermediate-program bifunction also yields the textbook two-branch source
formula for `H_w(x)`. -/
theorem intermediateProgramBifunction_apply_eq_ite
    (h₀ : Y₀ → WithBotTop 𝕜) (h : ∀ i : ι, Y i → WithBotTop 𝕜)
    (A₀ : X →ₗ[𝕜] Y₀) (A : ∀ i : ι, X →ₗ[𝕜] Y i)
    (a₀ : Y₀) (a : ∀ i : ι, Y i)
    (a₀Star : XStar) (aStar : ι → XStar)
    (α₀ : 𝕜) (α : ι → 𝕜)
    (w : U) (x : X) :
    intermediateProgramBifunction h₀ h A₀ A a₀ a a₀Star aStar α₀ α w x =
      if
          ∀ i : ι,
            h i (A i x + a i - w.2.2 i) + ((⟪x, aStar i⟫ₚ : 𝕜) : WithBotTop 𝕜) + α i ≤ w.1 i then
        h₀ (A₀ x + a₀ - w.2.1) + ((⟪x, a₀Star⟫ₚ : 𝕜) : WithBotTop 𝕜) + α₀
      else
        ⊤ := sorry

/-- The explicit dual objective appearing in the dual program of the intermediate program, viewed
as a function on the dual perturbation-parameter space. -/
def intermediateProgramDualObjective
    (h₀ : Y₀ → WithBotTop 𝕜) (h : ∀ i : ι, Y i → WithBotTop 𝕜)
    (a₀ : Y₀) (a : ∀ i : ι, Y i)
    (α₀ : 𝕜) (α : ι → 𝕜) :
    UStar →
      WithBotTop 𝕜 :=
  fun wStar ↦
    let uStar := wStar.1
    let p₀Star := wStar.2.1
    let pStar := wStar.2.2
    (α₀ : WithBotTop 𝕜) + ((⟪a₀, p₀Star⟫ₚ : 𝕜) : WithBotTop 𝕜) - (h₀⋆ p₀Star) +
      ∑ i : ι,
        ((((α i) * (uStar i) : 𝕜) : WithBotTop 𝕜) +
            ((⟪a i, pStar i⟫ₚ : 𝕜) : WithBotTop 𝕜) -
          ((fun q : Y i ↦ ((uStar i : 𝕜) : WithBotTop 𝕜) * h i q)⋆ (pStar i)))

/-- Evaluating the dual-objective owner at `(u⋆, p₀⋆, p⋆)` gives the explicit finite-sum formula
from the source. -/
@[simp] theorem intermediateProgramDualObjective_apply
    (h₀ : Y₀ → WithBotTop 𝕜) (h : ∀ i : ι, Y i → WithBotTop 𝕜)
    (a₀ : Y₀) (a : ∀ i : ι, Y i)
    (α₀ : 𝕜) (α : ι → 𝕜)
    (uStar : ι → 𝕜) (p₀Star : Y₀Star)
    (pStar : ∀ i : ι, YStar i) :
    intermediateProgramDualObjective h₀ h a₀ a α₀ α (uStar, (p₀Star, pStar)) =
      (α₀ : WithBotTop 𝕜) + ((⟪a₀, p₀Star⟫ₚ : 𝕜) : WithBotTop 𝕜) - (h₀⋆ p₀Star) +
        ∑ i : ι,
          ((((α i) * (uStar i) : 𝕜) : WithBotTop 𝕜) +
              ((⟪a i, pStar i⟫ₚ : 𝕜) : WithBotTop 𝕜) -
            ((fun q : Y i ↦ ((uStar i : 𝕜) : WithBotTop 𝕜) * h i q)⋆ (pStar i))) :=
  rfl

/-- The dual feasible set for the explicit dual program attached to the intermediate program. -/
def intermediateProgramDualFeasibleSet
    (A₀Star : Y₀Star →ₗ[𝕜] XStar) (AStar : ∀ i : ι, YStar i →ₗ[𝕜] XStar)
    (a₀Star : XStar) (aStar : ι → XStar) (xStar : XStar) :
    Set UStar :=
  {wStar |
    0 ≤ wStar.1 ∧
      a₀Star + A₀Star wStar.2.1 +
          ∑ i, ((wStar.1 i) • aStar i + AStar i (wStar.2.2 i)) = xStar}

/-- Membership in the dual feasible set is the source nonnegativity and adjoint-balance
condition. -/
@[simp] theorem mem_intermediateProgramDualFeasibleSet
    (A₀Star : Y₀Star →ₗ[𝕜] XStar) (AStar : ∀ i : ι, YStar i →ₗ[𝕜] XStar)
    (a₀Star : XStar) (aStar : ι → XStar) (xStar : XStar)
    (wStar : UStar) :
    wStar ∈ intermediateProgramDualFeasibleSet A₀Star AStar a₀Star aStar xStar ↔
      0 ≤ wStar.1 ∧
        a₀Star + A₀Star wStar.2.1 +
            ∑ i, ((wStar.1 i) • aStar i + AStar i (wStar.2.2 i)) = xStar :=
  Iff.rfl

section TheoremSurface

variable
    (h₀ : Y₀ → WithBotTop 𝕜) (h : ∀ i : ι, Y i → WithBotTop 𝕜)
    (A₀ : X →ₗ[𝕜] Y₀) (A : ∀ i : ι, X →ₗ[𝕜] Y i)
    (A₀Star : Y₀Star →ₗ[𝕜] XStar) (AStar : ∀ i : ι, YStar i →ₗ[𝕜] XStar)
    (a₀ : Y₀) (a : ∀ i : ι, Y i)
    (a₀Star : XStar) (aStar : ι → XStar)
    (α₀ : 𝕜) (α : ι → 𝕜)

local notation "H" => intermediateProgramBifunction h₀ h A₀ A a₀ a a₀Star aStar α₀ α
local notation "dualObjective" => intermediateProgramDualObjective h₀ h a₀ a α₀ α
local notation "dualFeasibleSet" => intermediateProgramDualFeasibleSet A₀Star AStar a₀Star aStar

-- Proof sketch: expand the canonical adjoint owner of
-- `H`. Minimizing first over the threshold variables forces
-- `u⋆ ≥ 0`; then substitute `q₀ = A₀ x + a₀ - p₀` and `qᵢ = Aᵢ x + aᵢ - pᵢ`, separate the
-- `x`-term from the `q`-terms, and identify the remaining infima with the relevant conjugate
-- values. The surviving feasibility condition is exactly
-- `dualFeasibleSet xStar`.
/-- Theorem 6.30.24: for the intermediate-program bifunction `H` coming from affine
representations `h₀(A₀ x + a₀) + ⟪x, a₀⋆⟫ₚ + α₀` and
`hᵢ(Aᵢ x + aᵢ) + ⟪x, aᵢ⋆⟫ₚ + αᵢ`, the adjoint value `H_{x⋆}⋆(w⋆)` is the negative of the
explicit dual objective minus the indicator of the dual feasible set. -/
theorem adjointFunction_intermediateProgramBifunction_apply
    (hA₀ :
      ∀ x : X, ∀ p₀Star : Y₀Star, ⟪A₀ x, p₀Star⟫ₚ = ⟪x, A₀Star p₀Star⟫ₚ)
    (hA :
      ∀ i : ι, ∀ x : X, ∀ pStar : YStar i, ⟪A i x, pStar⟫ₚ = ⟪x, AStar i pStar⟫ₚ)
    (xStar : XStar)
    (wStar : UStar) :
    H⋆ xStar wStar =
      -(dualObjective wStar) -
        δ[𝕜](wStar | dualFeasibleSet xStar) := sorry

-- Proof sketch: rewrite `adjointFunction_intermediateProgramBifunction_apply` by splitting on
-- membership in `dualFeasibleSet xStar`.
/-- Source case-split form of Theorem 6.30.24: the adjoint value is the negative of the explicit
dual objective on the dual feasible set, and `-∞` off that set. -/
theorem adjointFunction_intermediateProgramBifunction_apply_eq_ite
    (hA₀ :
      ∀ x : X, ∀ p₀Star : Y₀Star, ⟪A₀ x, p₀Star⟫ₚ = ⟪x, A₀Star p₀Star⟫ₚ)
    (hA :
      ∀ i : ι, ∀ x : X, ∀ pStar : YStar i, ⟪A i x, pStar⟫ₚ = ⟪x, AStar i pStar⟫ₚ)
    (xStar : XStar)
    (wStar : UStar) :
    H⋆ xStar wStar =
      if wStar ∈ dualFeasibleSet xStar then
        -(dualObjective wStar)
      else
        ⊥ := sorry

-- Proof sketch: specialize
-- `adjointFunction_intermediateProgramBifunction_apply_eq_ite` to `x⋆ = 0`. This is the zero
-- slice of the canonical adjoint owner defining the dual
-- program, so the surviving branch is exactly the explicit dual maximand under the source
-- feasibility constraints.
/-- The zero-slice specialization of the adjoint formula describes the dual program `(R⋆)`: the
dual data are feasible exactly when `u⋆ ≥ 0` and
`a₀⋆ + A₀⋆ p₀⋆ + ∑ᵢ (uᵢ⋆ aᵢ⋆ + Aᵢ⋆ pᵢ⋆) = 0`, and on that feasible set the dual program
maximizes `intermediateProgramDualObjective`, expressed on the theorem surface by the canonical
zero-slice owner of the adjoint bifunction. -/
theorem objective_adjointFunction_intermediateProgramBifunction_apply_eq_ite
    (hA₀ :
      ∀ x : X, ∀ p₀Star : Y₀Star, ⟪A₀ x, p₀Star⟫ₚ = ⟪x, A₀Star p₀Star⟫ₚ)
    (hA :
      ∀ i : ι, ∀ x : X, ∀ pStar : YStar i, ⟪A i x, pStar⟫ₚ = ⟪x, AStar i pStar⟫ₚ)
    (wStar : UStar) :
    (((H⋆ : XStar → UStar → WithBotTop 𝕜)₀) wStar) =
      if wStar ∈ dualFeasibleSet (0 : XStar) then
        -(dualObjective wStar)
      else
        ⊥ := sorry

end TheoremSurface

end

end Bifunction
