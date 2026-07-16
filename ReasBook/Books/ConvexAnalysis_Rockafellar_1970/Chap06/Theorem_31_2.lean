import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_7
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_9

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
