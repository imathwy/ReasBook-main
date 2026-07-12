import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_10
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_16
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_8

noncomputable section

open scoped Rockafellar

namespace Bifunction

section

universe u v u' v' w

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Semiring 𝕜]
variable [SupSet (WithTopBot 𝕜)] [InfSet (WithTopBot 𝕜)] [Sub (WithTopBot 𝕜)]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Neg UStar] [Zero XStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.9 records the dual objective of the Fenchel perturbation program and
  the strong-consistency criterion for the dual concave program `(P*)`.
- `core/canonical`: the owner abstractions already present upstream are
  `Bifunction.adjoint`, the zero-slice owner `Bifunction.objective`, the
  Chapter 6 strong-consistency owner `IsStronglyConsistent`, the Chapter 6 concave conjugate owner
  `concaveConjugate`, and the Chapter 12 convex conjugate owner `f⋆`.
- `bridge/view`: the source graph-function condition
  `∃ u⋆, (0, u⋆) ∈ riDom(Function.uncurry F⋆)` is retained only as a companion bridge beneath the
  canonical owner theorem on `IsStronglyConsistent 𝕜 F⋆`, while any `StrongDual` expression is
  handled downstream as a specialization bridge.

Domain-style sampling used here:
- `Bifunction.adjoint`,
  `Bifunction.objective_adjoint_fenchelPerturbation_apply`, and its
  `StrongDual` specialization from `Lemma_31_0_8`;
- `((F⋆)₀)` from `Definition_6_30_16`;
- `Bifunction.IsStronglyConsistent` from `Definition_6_29_10`;
- `concaveConjugate` from `Definition_6_30_4`;
- `riDom(·)` from `Chap01.Definition_4_4`.

Primitive data vs derived API:
- primitive source data for the dual-value layer: the primal map `A`, a dual map `Astar` with
  pairing compatibility, and functions `f`, `g`;
- primitive owner objects: `F⋆ := adjoint XStar UStar (fenchelPerturbation A f g)` and its
  source-facing zero slice `(F⋆)₀`;
- derived API: the dual-objective optimal-value identity, the owner-side strong-consistency
  criterion in relative-interior-domain language, and the lower graph-function bridge theorem.

Layer target: `source-facing`, refined to the existing adjoint-bifunction owners, with the
strong-consistency clause upgraded to the canonical owner `IsStronglyConsistent 𝕜`.
-/

variable (A : X →ₗ[𝕜] U) (Astar : UStar → XStar)
variable (f : X → WithTopBot 𝕜) (g : U → WithTopBot 𝕜)

local notation "F" => fenchelPerturbation A f g
local notation "F⋆" =>
  (adjoint XStar UStar F : XStar → UStar → WithTopBot 𝕜)

/-- Lemma 31.0.9 (dual-value owner clause): the dual value owner `supᵇ(F⋆) 0` equals the
indexed supremum of the source dual objective formula
`⨆ u⋆, g∗ u⋆ - f⋆ (Astar u⋆)`. -/
theorem upperPerturbationFunction_adjoint_fenchelPerturbation_zero_eq_iSup
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ) :
    supᵇ(F⋆) (0 : XStar) =
      ⨆ uStar : UStar, g∗ uStar - f⋆ (Astar uStar) := by
  sorry

/-- Lemma 31.0.9 (optimal-value clause), source objective-slice view: this is the same identity
as `upperPerturbationFunction_adjoint_fenchelPerturbation_zero_eq_iSup`, written as
`⨆ u⋆, (F⋆)₀ u⋆ = ...`. -/
theorem iSup_objective_adjoint_fenchelPerturbation_eq_iSup
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ) :
    (⨆ uStar : UStar, (F⋆)₀ uStar) =
      ⨆ uStar : UStar, g∗ uStar - f⋆ (Astar uStar) := by
  simpa using
    (upperPerturbationFunction_adjoint_fenchelPerturbation_zero_eq_iSup
      (A := A) (Astar := Astar) (f := f) (g := g) (hA := hA))

/-- Lemma 31.0.9 (optimal-value clause), source supremum-of-range view: this is the same owner
identity as `iSup_objective_adjoint_fenchelPerturbation_eq_iSup`, expressed in the
textbook `sup` notation on the range of the dual objective. -/
theorem sSup_range_objective_adjoint_fenchelPerturbation_eq_sSup_range
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ) :
    sSup (Set.range ((F⋆)₀)) =
      sSup (Set.range (fun uStar : UStar ↦ g∗ uStar - f⋆ (Astar uStar))) := by
  simpa [sSup_range] using
    (iSup_objective_adjoint_fenchelPerturbation_eq_iSup A Astar f g hA)

end

section

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
local notation "F⋆" =>
  adjoint XStar UStar F

/-- Lemma 31.0.9 (strong-consistency clause), canonical owner form: the dual concave program
attached to the adjoint bifunction `F*` is strongly consistent exactly when some dual point lies
in the effective relative interior of the dual domain `riDom[𝕜](-g∗)`, and its adjoint image lies
in `riDom[𝕜](f⋆)`. -/
theorem isStronglyConsistent_adjoint_fenchelPerturbation_iff_exists_mem_riDom
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ) :
    IsStronglyConsistent 𝕜 F⋆ ↔
      ∃ uStar : UStar, uStar ∈ riDom[𝕜](-g∗) ∧
        Astar uStar ∈ riDom[𝕜](f⋆) := by
  sorry

/-- Graph-function owner bridge: over the zero fiber `x⋆ = 0`, the relative-interior graph
condition is equivalent to the canonical dual-program owner `IsStronglyConsistent 𝕜 F⋆`. -/
theorem exists_mem_riDom_uncurry_adjoint_fenchelPerturbation_zero_iff_isStronglyConsistent
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ) :
    (∃ uStar : UStar,
      ((0 : XStar), uStar) ∈ riDom[𝕜](Function.uncurry F⋆)) ↔
      IsStronglyConsistent 𝕜 F⋆ := by
  sorry

/-- Graph-function source companion to Lemma 31.0.9: over the zero fiber `x⋆ = 0`, the
relative-interior condition on `Function.uncurry F*` is equivalent to the same dual-domain
criterion as in `isStronglyConsistent_adjoint_fenchelPerturbation_iff_exists_mem_riDom`. -/
theorem exists_mem_riDom_uncurry_adjoint_fenchelPerturbation_zero_iff
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, Astar uStar⟫ₚ) :
    (∃ uStar : UStar,
      ((0 : XStar), uStar) ∈ riDom[𝕜](Function.uncurry F⋆)) ↔
      (∃ uStar : UStar, uStar ∈ riDom[𝕜](-g∗) ∧
        Astar uStar ∈ riDom[𝕜](f⋆)) := by
  simpa [exists_mem_riDom_uncurry_adjoint_fenchelPerturbation_zero_iff_isStronglyConsistent
    (A := A) (Astar := Astar) (f := f) (g := g) (hA := hA)] using
    (isStronglyConsistent_adjoint_fenchelPerturbation_iff_exists_mem_riDom
      (A := A) (Astar := Astar) (f := f) (g := g) (hA := hA))

end

end Bifunction
