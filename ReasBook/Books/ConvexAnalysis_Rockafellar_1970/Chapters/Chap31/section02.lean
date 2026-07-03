import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_31_2_1 (from Chap06) -/
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

/-! ### Definition_31_2_2 (from Chap06) -/
noncomputable section

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 31.2.2 introduces the Fenchel-side functions
  `f x = c x + δ[𝕜](x | x ≥ 0)` and `g u = -δ[𝕜](u | u ≥ a)` for linear-program
  data `(c, a, A)`.
- `core/canonical`: the Chapter 31 owner for the resulting bifunction is already
  `fenchelPerturbation`, while the Section 30 owner for the same LP perturbation and feasible
  slice is `linearProgram` with `linearProgramFeasibleSet`.
- `bridge/view`: this item keeps the source-facing displayed `f` and `g`, uses the canonical
  owner `fenchelPerturbation` for the bifunction itself, and identifies that owner with
  `linearProgram`.

Domain-style sampling used here:
- `linearProgram` and `linearProgramFeasibleSet` from `Definition_6_30_18`;
- `optimalValue` from `Definition_6_29_15`;
- `fenchelPerturbation` and `objective_fenchelPerturbation_apply` from `Lemma_31_0_6`;
- the ordered-module owners `orthant[𝕜](X)` and `Set.Ici`;
- the indicator notation `δ[𝕜](· | C)`.

Primitive data vs derived API:
- primitive source data: the objective dual element `c`, the right-hand side `a`, and the linear
  map `A`;
- primitive source-facing helpers: the displayed functions `f` and `g`;
- main source-facing owner: the resulting bifunction, now exposed through the canonical Chapter 31
  owner `fenchelPerturbation`;
- derived API: the pointwise source formulas for `f` and `g`, the identification of the resulting
  perturbation with the existing Section 30 LP owner `linearProgram`, and the corresponding
  optimal-value formula stated directly on that canonical LP owner.

Layer target: `bridge/view`. The source-facing displayed data `f` and `g` remain explicit, but
the bifunction itself is refined to the existing canonical owner `fenchelPerturbation` instead of
being duplicated as a second local wrapper.
-/

section Primal

variable {𝕜 : Type*} {X : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid X] [PartialOrder X] [IsOrderedAddMonoid X] [Module 𝕜 X]
variable [PosSMulMono 𝕜 X]

/-- The primal-side function in the Fenchel representation of linear-program data `(c, a, A)`:
the linear objective branch `x ↦ c x` plus the indicator of the nonnegative orthant. -/
def linearProgramFenchelPrimal
    (c : Module.Dual 𝕜 X) :
    X → WithBotTop 𝕜 :=
  fun x ↦ ((c x : 𝕜) : WithBotTop 𝕜) + δ[𝕜](x | orthant[𝕜](X))

@[simp] theorem linearProgramFenchelPrimal_apply
    (c : Module.Dual 𝕜 X) (x : X) :
    linearProgramFenchelPrimal c x =
      ((c x : 𝕜) : WithBotTop 𝕜) + δ[𝕜](x | orthant[𝕜](X)) :=
  rfl

end Primal

section Concave

variable {𝕜 : Type*} {U : Type*}
variable [AddGroup 𝕜] [Preorder U]

/-- The concave-side function in the Fenchel representation of linear-program data `(c, a, A)`:
the negative of the indicator of the upper set `{u | a ≤ u}`. -/
def linearProgramFenchelConcave
    (a : U) :
    U → WithBotTop 𝕜 :=
  fun u ↦ -(δ[𝕜](u | Set.Ici a))

@[simp] theorem linearProgramFenchelConcave_apply
    (a : U) (u : U) :
    linearProgramFenchelConcave a u = -(δ[𝕜](u | Set.Ici a)) :=
  rfl

end Concave

section FenchelLinearProgramBridge

variable {𝕜 : Type*} {U X : Type*}
variable [Ring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid X] [PartialOrder X] [IsOrderedAddMonoid X] [Module 𝕜 X]
variable [PosSMulMono 𝕜 X]
variable [AddCommGroup U] [Preorder U] [Module 𝕜 U]

@[simp] theorem fenchelPerturbation_linearProgramFenchel_apply
    (c : Module.Dual 𝕜 X) (a : U) (A : X →ₗ[𝕜] U) (u : U) (x : X) :
    fenchelPerturbation
        A
        (linearProgramFenchelPrimal c)
        (linearProgramFenchelConcave a) u x =
      linearProgram c a A u x := by
  sorry

-- Proof sketch: expand the Chapter 31 owner `fenchelPerturbation`,
-- rewrite the displayed `f` and `g` by definition, and then use
-- `a ≤ A x + u ↔ a - A x ≤ u` to identify the second indicator with the LP feasibility
-- slice `linearProgramFeasibleSet a A u`.
/-- Definition 31.2.2, canonical-owner form: the Fenchel perturbation built from the displayed
LP-side functions `f` and `g` is exactly the existing Section 30 linear-program owner. -/
theorem fenchelPerturbation_linearProgramFenchel_eq_linearProgram
    (c : Module.Dual 𝕜 X) (a : U) (A : X →ₗ[𝕜] U) :
    fenchelPerturbation
        A
        (linearProgramFenchelPrimal c)
        (linearProgramFenchelConcave a) =
      linearProgram c a A := by
  ext u x
  simpa using fenchelPerturbation_linearProgramFenchel_apply c a A u x

-- Proof sketch: once
-- `fenchelPerturbation_linearProgramFenchel_eq_linearProgram` identifies the branch data with the
-- canonical Section 30 owner `linearProgram`, the optimal-value clause should stay on that owner;
-- then use the LP zero-slice description and `optimalValue` as the infimum over the
-- zero-perturbation feasible set.
/-- The optimal value of the canonical LP owner attached to `(c, a, A)` is the infimum of
`c x` over the unperturbed feasible set. -/
theorem optimalValue_linearProgram_eq_iInf_feasibleSet
    [InfSet (WithBotTop 𝕜)]
    (c : Module.Dual 𝕜 X) (a : U) (A : X →ₗ[𝕜] U) :
    optimalValue (linearProgram c a A) =
      ⨅ x : linearProgramFeasibleSet a A 0, ((c x : 𝕜) : WithBotTop 𝕜) := sorry

end FenchelLinearProgramBridge

end Bifunction

/-! ### Theorem_31_2 (from Chap06) -/
noncomputable section

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 31.2 is the main Fenchel-duality setup theorem for the perturbation
  bifunction `F(u, x) = f x - g (A x + u)`, together with its adjoint, its primal and dual
  zero-slice objective formulas, and the strong-consistency criteria for the primal and dual
  programs.
- `core/canonical`: the owner abstractions in the surrounding chapter are already
  `fenchelPerturbation`, `adjoint`, `objective`, `Function.uncurry`, and
  `IsStronglyConsistent`.
- `bridge/view`: the source's displayed infimum and supremum formulas are just the zero-slice
  owners `(fenchelPerturbation A f g)₀` and `((fenchelPerturbation A f g)⋆)₀`, while the
  strong-consistency clauses are thin source-facing reformulations in terms of
  `riDom[𝕜](f)`, `riDom[𝕜](-g)`, `riDom[𝕜](f⋆)`, and `riDom[𝕜](-concaveConjugate g)`.

Domain-style sampling used here:
- `fenchelPerturbation`, `objective_fenchelPerturbation_apply`,
  `uncurry_fenchelPerturbation_isConvex`, `uncurry_fenchelPerturbation_isProper`, and
  `uncurry_fenchelPerturbation_isClosedProperConvex` from `Lemma_31_0_6`;
- `adjoint`,
  `adjoint_fenchelPerturbation_apply`, and
  `objective_adjoint_fenchelPerturbation_apply` from `Lemma_31_0_8`;
- `iSup_objective_adjoint_fenchelPerturbation_eq_iSup` and
  `isStronglyConsistent_adjoint_fenchelPerturbation_iff_exists_mem_riDom` from
  `Lemma_31_0_9`;
- `IsStronglyConsistent` from `Definition_6_29_10`;
- `riDom(·)` / `dom(·)` as the canonical domain owners already used throughout Chapters 1, 3,
  and 6.

Primitive data vs derived API:
- primitive source data: the map `A`, the convex function `f`, and the concave function `g`;
- primitive owner objects: `fenchelPerturbation A f g` and its dual-side owner
  `(fenchelPerturbation A f g)⋆` with source-facing dual objective
  `((fenchelPerturbation A f g)⋆)₀`;
- derived API: the source infimum/supremum formulas and the primal/dual strong-consistency
  criteria.

Layer target: `source-facing`, but with direct reuse of the existing chapter owners instead of a
parallel local package for “proper convex bifunction” or for “dual program data”.

Abstraction notes for this file:
- the primal infimum clause is kept at the generic codomain owner layer `WithTopBot α`,
  independent from the scalar type;
- the qualification clauses stay on the first upstream owner layer that currently supplies them:
  `Lemma_31_0_7` / `Lemma_31_0_9`; they are scalar-generic (`riDom[𝕜](·)`), with the dual clause
  exposed directly on the pairing-based dual-map layer.
-/

/- The source perturbation bifunction `F(u, x) = f x - g (A x + u)` is already owned by the
chapter declaration `fenchelPerturbation`. -/
recall fenchelPerturbation

/- The convexity clause of Theorem 31.2 is already the owner theorem
`uncurry_fenchelPerturbation_isConvex`. -/
recall uncurry_fenchelPerturbation_isConvex

/- The properness clause of Theorem 31.2 is already the owner theorem
`uncurry_fenchelPerturbation_isProper`. -/
recall uncurry_fenchelPerturbation_isProper

/- The closed-proper-convex clause is already owned by
`uncurry_fenchelPerturbation_isClosedProperConvex`. -/
recall uncurry_fenchelPerturbation_isClosedProperConvex

/- The primal zero-slice formula `F 0 x = f x - g (A x)` is already owned by
`objective_fenchelPerturbation_apply`. -/
recall objective_fenchelPerturbation_apply

/- The adjoint bifunction is already owned by `adjoint`, and its pairing-based
Fenchel-perturbation formula is already owned by
`adjoint_fenchelPerturbation_apply`. -/
recall adjoint
recall adjoint_fenchelPerturbation_apply
recall objective_adjoint_fenchelPerturbation_apply

section PrimalValue

universe u v w

variable {𝕜 : Type*} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜]
variable [InfSet (WithTopBot α)]
variable [Add α] [Neg α]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

/-- Theorem 31.2 (primal value clause), canonical owner surface. -/
theorem primalValue_eq_iInf_fenchelPerturbation
    (A : X →ₗ[𝕜] U) (f : X → WithTopBot α) (g : U → WithTopBot α) :
    optimalValue (fenchelPerturbation A f g) = ⨅ x : X, f x - g (A x) := by
  simpa using
    (optimalValue_fenchelPerturbation_eq_iInf (A := A) (f := f) (g := g))

end PrimalValue

section DualValue

universe u v u' v' w

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Semiring 𝕜]
variable [SupSet (WithTopBot 𝕜)] [InfSet (WithTopBot 𝕜)] [Sub (WithTopBot 𝕜)]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Neg UStar] [Zero XStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

variable (A : X →ₗ[𝕜] U) (Astar : UStar → XStar)
variable (f : X → WithTopBot 𝕜) (g : U → WithTopBot 𝕜)

local notation "F" => fenchelPerturbation A f g
local notation "F⋆" =>
  (adjoint XStar UStar F : XStar → UStar → WithTopBot 𝕜)

/-- Theorem 31.2 (dual value clause), canonical owner surface. -/
theorem dualValue_eq_iSup_fenchelPerturbation
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ) :
    (⨆ uStar : UStar, (F⋆)₀ uStar) =
      ⨆ uStar : UStar, g∗ uStar - f⋆ (Astar uStar) := by
  simpa using
    (iSup_objective_adjoint_fenchelPerturbation_eq_iSup
      (A := A) (Astar := Astar) (f := f) (g := g) (hA := hA))

end DualValue

section PrimalConsistency

universe u v

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U] [FiniteDimensional 𝕜 U]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]

/-- Theorem 31.2 (primal strong-consistency clause), canonical owner surface. -/
theorem primalStrongConsistency_iff_exists_mem_riDom_fenchelPerturbation
    (A : X →ₗ[𝕜] U) {f : X → WithTopBot 𝕜} {g : U → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_concave : g.IsConcave 𝕜) (hg_proper : g.IsProperConcave) :
    IsStronglyConsistent 𝕜 (fenchelPerturbation A f g) ↔
      ∃ x : X, x ∈ riDom[𝕜](f) ∧ A x ∈ riDom[𝕜](-g) := by
  simpa using
    (isStronglyConsistent_fenchelPerturbation_iff_exists_mem_riDom
      (A := A) (f := f) (g := g)
      (hf_convex := hf_convex) (hf_proper := hf_proper)
      (hg_concave := hg_concave) (hg_proper := hg_proper))

end PrimalConsistency

section DualConsistency

universe u v u' v' w

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Ring 𝕜]
variable [SupSet (WithTopBot 𝕜)] [InfSet (WithTopBot 𝕜)] [Sub (WithTopBot 𝕜)]
variable [Top (WithTopBot 𝕜)] [LT (WithTopBot 𝕜)] [Neg (WithTopBot 𝕜)]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommGroup UStar] [Module 𝕜 UStar] [TopologicalSpace UStar]
variable [AddCommGroup XStar] [Module 𝕜 XStar] [TopologicalSpace XStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

variable (A : X →ₗ[𝕜] U) (Astar : UStar → XStar)
variable (f : X → WithTopBot 𝕜) (g : U → WithTopBot 𝕜)

local notation "F" => fenchelPerturbation A f g
local notation "F⋆" => adjoint XStar UStar F

/-- Theorem 31.2 (dual strong-consistency clause), canonical owner surface. -/
theorem dualStrongConsistency_iff_exists_mem_riDom_fenchelPerturbation
    (hA : ∀ x : X, ∀ uStar : UStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ) :
    IsStronglyConsistent 𝕜 F⋆ ↔
      ∃ uStar : UStar, uStar ∈ riDom[𝕜](-g∗) ∧
        Astar uStar ∈ riDom[𝕜](f⋆) := by
  simpa using
    (isStronglyConsistent_adjoint_fenchelPerturbation_iff_exists_mem_riDom
      (A := A) (Astar := Astar) (f := f) (g := g) (hA := hA))

end DualConsistency

end Bifunction

/-! ### Definition_31_2_3 (from Chap06) -/
noncomputable section

open scoped Rockafellar
open Bifunction

universe u v u' v' w

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 31.2.3 computes the two conjugate branches attached to the Chapter 31
  LP Fenchel presentation from Definition 31.2.2, and then identifies the resulting dual LP value
  as the supremum over the canonical feasible region.
- `core/canonical`: the owner declarations already present upstream are the conjugation owners
  `(·)⋆` and `(·)∗`, the Chapter 31 branch owners `linearProgramFenchelPrimal` and
  `linearProgramFenchelConcave`, and the Section 30 feasible-set owner
  `linearProgramFeasibleSet`.
- `bridge/view`: the value clause remains the source-facing dual LP formula, but it is expressed on
  those existing owners rather than through longer re-expanded spellings.

Mandatory domain-style sampling used here:
- `convexConjugate` / `(·)⋆` from `Chap03.Defn_12_2`;
- `concaveConjugate` / `(·)∗` from `Chap06.Definition_6_30_4`;
- `linearProgramFenchelPrimal` / `linearProgramFenchelConcave` from `Definition_31_2_2`;
- `linearProgramFeasibleSet` from `Chap06.Definition_6_30_18`, sampled through the canonical LP
  owner stack already reused in `Definition_31_2_2`.

Best owner abstraction:
- branch data stays on `linearProgramFenchelPrimal` / `linearProgramFenchelConcave`;
- feasibility stays on `linearProgramFeasibleSet`;
- no extra local wrapper around the dual objective is introduced here.

Primitive data vs derived API:
- primitive source data: `aStar`, `a`, and the dual-side linear map `Astar`;
- primitive owner-side bridge data: the canonical linear functional
  `HasLinearPairing.pairingLinear.flip aStar` induced by the pairing-side coefficient `aStar`;
- primitive owners reused directly: the branch functions from Definition 31.2.2 and the feasible
  region from Section 30;
- derived API: the conjugate identities and the dual-value equality.

Layer target: `source-facing`, with the theorem surfaces shortened to the existing owner notation.
-/

section PrimalConjugate

variable {𝕜 : Type w} {X : Type u} {XStar : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
variable [AddCommGroup X] [PartialOrder X] [IsOrderedAddMonoid X] [Module 𝕜 X]
variable [PosSMulMono 𝕜 X]
variable [AddCommGroup XStar] [PartialOrder XStar] [Module 𝕜 XStar]
variable [HasLinearPairing X XStar 𝕜]

local notation "pairingObj[" aStar "]" =>
  (LinearMap.flip (HasLinearPairing.pairingLinear : X →ₗ[𝕜] Module.Dual 𝕜 XStar) aStar)

-- Proof sketch: write the primal branch with the canonical pairing-induced functional
-- `HasLinearPairing.pairingLinear.flip aStar`, then apply the chapter translation rule for
-- `convexConjugate_add_inner` to the orthant indicator. The remaining conjugate is the canonical
-- cone-indicator owner theorem for the nonnegative orthant, and `xStar - aStar ∈ Set.Iic 0` is
-- exactly the order condition `xStar ≤ aStar`.
/-- Definition 31.2.3 (1): for the Chapter 31 primal LP function
`f(x) = ⟪a⋆, x⟫ₚ + δ[𝕜](x | x ≥ 0)`, the Fenchel conjugate is the indicator of the lower set
`{x⋆ | x⋆ ≤ a⋆}`. -/
theorem convexConjugate_linearProgramFenchelPrimal_eq_indicator_Iic
    (aStar : XStar) :
    ((linearProgramFenchelPrimal
        pairingObj[aStar])⋆ :
      XStar → WithBotTop 𝕜) =
      (δ[𝕜](· | Set.Iic aStar) : XStar → WithBotTop 𝕜) := sorry

end PrimalConjugate

section DualConjugate

variable {𝕜 : Type w} {U : Type u} {UStar : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
variable [AddCommGroup U] [PartialOrder U] [IsOrderedAddMonoid U] [Module 𝕜 U]
variable [AddCommGroup UStar] [PartialOrder UStar] [IsOrderedAddMonoid UStar] [Module 𝕜 UStar]
variable [HasPairing U UStar 𝕜]

-- Proof sketch: rewrite `Set.Ici a` as the translate of the canonical nonnegative orthant
-- `Set.Ici 0`, identify the corresponding indicator as a translation of the orthant indicator, and
-- apply the chapter translation rule for convex conjugates together with the sign bridge
-- `concaveConjugate_eq_neg_convexConjugate_neg`. The orthant conjugate is clause (1) specialized
-- to `aStar = 0`, and negating the resulting indicator moves `Set.Iic 0` to `Set.Ici 0`.
/-- Definition 31.2.3 (2): for the Chapter 31 concave LP function
`g(u) = -δ[𝕜](u | u ≥ a)`, the concave conjugate is
`u⋆ ↦ ⟪a, u⋆⟫ - δ[𝕜](u⋆ | u⋆ ≥ 0)`. -/
theorem concaveConjugate_linearProgramFenchelConcave_eq_pairing_sub_indicator_Ici_zero
    (a : U) :
    ((linearProgramFenchelConcave a)∗ : UStar → WithBotTop 𝕜) =
      fun uStar ↦ ((⟪a, uStar⟫ₚ : 𝕜) : WithBotTop 𝕜) - δ[𝕜](uStar | Set.Ici (0 : UStar)) := sorry

end DualConjugate

section DualOptimalValue

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
variable [AddCommGroup U] [PartialOrder U] [IsOrderedAddMonoid U] [Module 𝕜 U]
variable [AddCommGroup X] [PartialOrder X] [IsOrderedAddMonoid X] [Module 𝕜 X]
variable [PosSMulMono 𝕜 X]
variable [AddCommGroup UStar] [PartialOrder UStar] [IsOrderedAddMonoid UStar] [Module 𝕜 UStar]
variable [PosSMulMono 𝕜 UStar]
variable [AddCommGroup XStar] [PartialOrder XStar] [Module 𝕜 XStar]
variable [HasPairing U UStar 𝕜] [HasLinearPairing X XStar 𝕜]

local notation "pairingObj[" aStar "]" =>
  (LinearMap.flip (HasLinearPairing.pairingLinear : X →ₗ[𝕜] Module.Dual 𝕜 XStar) aStar)

-- Proof sketch: substitute the two conjugate formulas from the first two clauses into the Chapter
-- 31 dual objective `u⋆ ↦ g∗ u⋆ - f⋆ (A⋆ u⋆)`. The indicator terms combine into the single
-- feasibility condition `u⋆ ∈ linearProgramFeasibleSet (0 : XStar) (-Astar) aStar`, and on that
-- feasible set the objective reduces to the pairing value `⟪a, u⋆⟫`.
/-- Definition 31.2.3 (3): the optimal value of the dual linear program is the supremum of the
pairing `⟪a, u⋆⟫` over the canonical dual feasible set
`linearProgramFeasibleSet (0 : XStar) (-Astar) aStar`, i.e. over `u⋆ ≥ 0` with
`Astar u⋆ ≤ aStar`. -/
theorem iSup_linearProgramFenchelDualObjective_eq_iSup_pairing_dualFeasible
    (aStar : XStar) (a : U) (Astar : UStar →ₗ[𝕜] XStar) :
    (⨆ uStar : UStar,
      ((linearProgramFenchelConcave a)∗) uStar -
        ((linearProgramFenchelPrimal
          pairingObj[aStar])⋆)
          (Astar uStar)) =
      ⨆ uStar : linearProgramFeasibleSet (0 : XStar) (-Astar) aStar,
        ((⟪a, (uStar : UStar)⟫ₚ : 𝕜) : WithBotTop 𝕜) := sorry

end DualOptimalValue
