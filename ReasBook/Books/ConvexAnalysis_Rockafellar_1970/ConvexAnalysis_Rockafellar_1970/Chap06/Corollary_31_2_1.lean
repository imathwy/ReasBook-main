import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Corollary_6_30_5
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_31_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v u' v' w

section

variable {𝕜 : Type w} {E : Type u} {U : Type v} {UStar : Type u'} {EStar : Type v'}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [LinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] [CompleteSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U] [FiniteDimensional 𝕜 U]
variable [AddCommGroup UStar] [Module 𝕜 UStar] [TopologicalSpace UStar]
variable [AddCommGroup EStar] [Module 𝕜 EStar] [TopologicalSpace EStar]
variable [HasPairing U UStar 𝕜] [HasPairing E EStar 𝕜]

local instance : HasPairing U UStar (WithBotTop 𝕜) := instHasPairingWithBotTop
local instance : HasPairing E EStar (WithBotTop 𝕜) := instHasPairingWithBotTop

local notation "IsClosedProperConvex[" 𝕜 "]" => @Function.IsClosedProperConvex 𝕜
local notation "IsClosedProperConcave[" 𝕜 "]" => @Function.IsClosedProperConcave 𝕜

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 31.2.1 is the linear-map Fenchel-duality corollary asserting zero
  duality gap for the primal objective `x ↦ f x - g (A x)` under either of the two relative-
  interior qualification clauses, together with the corresponding attainment conclusions.
- `core/canonical`: the existing owners are the Chapter 31 perturbation program
  `Bifunction.fenchelPerturbation A f g`, the Chapter 31 qualification theorems from
  `Theorem_31_2`, the Chapter 6 attainment owners from `Corollary_6_30_5`, the Chapter 12/6
  conjugate owners `f⋆` and `g∗`, and the Chapter 6 closed-proper-concave owner
  `g.IsClosedProperConcave`.
- `bridge/view`: the source formulas are written directly as the primal infimum
  `⨅ x, f x - g (A x)` and the dual supremum
  `⨆ u⋆, g∗ u⋆ - f⋆ (Astar u⋆)`, while the two source qualification clauses are kept exactly in
  canonical `riDom` language.

Domain-style sampling used here:
- `Bifunction.optimalValue_fenchelPerturbation_eq_iInf`,
  `Bifunction.isStronglyConsistent_fenchelPerturbation_iff_exists_mem_riDom`, and
  `Bifunction.isStronglyConsistent_adjoint_fenchelPerturbation_iff_exists_mem_riDom`
  from `Theorem_31_2`;
- the Chapter 6 primal- and dual-attainment owner theorems from `Corollary_6_30_5`;
- the convex-conjugate owner `(·)⋆`;
- the concave-side owners `Function.IsClosedProperConcave` and `(·)∗`.

Primitive data vs derived API:
- primitive source data: a linear map `A`, a pairing-compatible dual map `Astar`,
  a closed proper convex function `f`, and a closed proper concave function `g`;
- primitive owner object: the Fenchel perturbation bifunction attached to `A`, `f`, and `g`;
- derived source-facing API: the primal objective `x ↦ f x - g (A x)`, the dual objective
  `u⋆ ↦ g∗ u⋆ - f⋆ (Astar u⋆)`, the two qualification predicates, the zero-gap value identity
  under their disjunction, and the two branchwise attainment conclusions.

Layer target: `source-facing`, with direct reuse of the existing Chapter 31 qualification owners
rather than a new packaged Fenchel-program interface.
-/

variable (A : E →ₗ[𝕜] U) (Astar : UStar → EStar) (f : E → WithBotTop 𝕜) (g : U → WithBotTop 𝕜)

local notation "primalObjective" => fun x : E ↦ f x - g (A x)
set_option quotPrecheck false in
local notation "dualObjective" =>
  fun uStar : UStar ↦
    g∗ uStar - (f⋆ : EStar → WithBotTop 𝕜) (Astar uStar)
local notation "primalQualification" =>
  ∃ x : E, x ∈ riDom[𝕜](f) ∧ A x ∈ riDom[𝕜](-g)
set_option quotPrecheck false in
local notation "dualQualification" =>
  ∃ uStar : UStar,
    uStar ∈ riDom[𝕜](-g∗) ∧
      Astar uStar ∈ riDom[𝕜]((f⋆ : EStar → WithBotTop 𝕜))
local notation "primalValue" => (⨅ x : E, primalObjective x)
local notation "dualValue" => (⨆ uStar : UStar, dualObjective uStar)

-- Proof sketch: apply Theorem 31.2 to the perturbation bifunction `Bifunction.fenchelPerturbation
-- A f g`. Clause (a) gives primal strong consistency through
-- `isStronglyConsistent_fenchelPerturbation_iff_exists_mem_riDom`, while clause (b) gives dual
-- strong consistency through
-- `isStronglyConsistent_adjoint_fenchelPerturbation_iff_exists_mem_riDom`. The Chapter 6
-- zero-duality-gap owner then identifies the primal and dual values, and the Chapter 31 zero-
-- slice formulas rewrite those owner values back to the source infimum/supremum expressions.
/-- Corollary 31.2.1: for a closed proper convex function `f`, a closed proper concave function
`g`, a linear map `A`, and a pairing-compatible dual map `Astar`, one has
`inf_x (f x - g (A x)) = sup_u⋆ (g* u⋆ - f* (Astar u⋆))` whenever either
(a) some `x ∈ riDom[𝕜](f)` satisfies `A x ∈ riDom[𝕜](-g)`, or
(b) some `u⋆ ∈ riDom[𝕜](-g∗)` satisfies `Astar u⋆ ∈ riDom[𝕜](f⋆)`. -/
theorem iInf_sub_comp_eq_iSup_concaveConjugate_sub_convexConjugate_of_fenchel_qualification
    (hA : ∀ x : E, ∀ uStar : UStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ)
    (hf : IsClosedProperConvex[𝕜] f)
    (hg : IsClosedProperConcave[𝕜] g)
    (hqual : primalQualification ∨ dualQualification) :
    primalValue = dualValue := sorry

-- Proof sketch: use clause (a) to obtain primal strong consistency from Theorem 31.2, then feed
-- that into the Chapter 6 dual-attainment owner from `Corollary_6_30_5` to extract a maximizer
-- of the dual objective.
/-- Under the qualification condition `∃ x ∈ riDom[𝕜](f), A x ∈ riDom[𝕜](-g)`, the dual supremum
`sup_u⋆ (g* u⋆ - f* (Astar u⋆))` is attained. -/
theorem exists_isMaxOn_concaveConjugate_sub_convexConjugate_comp_of_exists_mem_riDom
    (hA : ∀ x : E, ∀ uStar : UStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ)
    (hf : IsClosedProperConvex[𝕜] f)
    (hg : IsClosedProperConcave[𝕜] g)
    (hqual : primalQualification) :
    ∃ uStar : UStar, IsMaxOn dualObjective Set.univ uStar := sorry

-- Proof sketch: use clause (b) to obtain dual strong consistency from Theorem 31.2 and the same
-- zero-gap identity as above; then apply the Chapter 6 attainment owner
-- `exists_isMinOn_objective_of_isConsistent_of_isStronglyConsistent_adjoint` to extract
-- a minimizer of the primal objective.
/-- Under the qualification condition
`∃ u⋆ ∈ riDom[𝕜](-g∗), Astar u⋆ ∈ riDom[𝕜](f⋆)`, the primal infimum
`inf_x (f x - g (A x))` is attained. -/
theorem exists_isMinOn_sub_comp_of_exists_mem_dual_riDom
    (hA : ∀ x : E, ∀ uStar : UStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ)
    (hf : IsClosedProperConvex[𝕜] f)
    (hg : IsClosedProperConcave[𝕜] g)
    (hqual : dualQualification) :
    ∃ x : E, IsMinOn primalObjective Set.univ x := sorry

end
