import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_6

noncomputable section

universe u v u' v'

open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Semiring 𝕜]
variable [SupSet (WithTopBot 𝕜)] [InfSet (WithTopBot 𝕜)] [Sub (WithTopBot 𝕜)]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Neg UStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]
variable (A : X →ₗ[𝕜] U) (Astar : UStar → XStar)
variable (f : X → WithTopBot 𝕜) (g : U → WithTopBot 𝕜)

local notation "F" => fenchelPerturbation A f g
local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithTopBot 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.8 computes the adjoint bifunction of the Fenchel perturbation
  `F(u, x) = f x - g (A x + u)`.
- `core/canonical`: the owner abstractions are already `fenchelPerturbation`, `adjoint`,
  the zero-slice owner `(·)₀`, and the conjugate owners `(·)∗` and `(·)⋆`.
- `bridge/view`: the pairing-based theorem keeps an explicit dual-side map `Astar` satisfying the
  standard compatibility identity, while the strong-dual theorem below is only the canonical
  specialization `Astar u⋆ = u⋆.comp A`.

Domain-style sampling used here:
- `fenchelPerturbation` and `objective_fenchelPerturbation_apply` from `Lemma_31_0_6`;
- `adjoint` and `objective_adjoint_apply` from `Definition_6_30_14`;
- `concaveConjugate` from `Definition_6_30_4`;
- `convexConjugate` from `Chap03/Defn_12_2`.

Primitive data vs derived API:
- primitive source data: `A`, `f`, `g`;
- primitive owner reused directly: `fenchelPerturbation A f g`;
- derived API in this file: the adjoint-value formula and its zero-slice specialization, first on
  the pairing-based dual-map layer and then on the strong-dual bridge layer.

Layer target: the first theorem is `source-facing`; the second section is `bridge/view`.
-/

/-- Lemma 31.0.8 on the pairing-based dual-map layer: if `Astar` satisfies
`⟪A x, u⋆⟫ = ⟪x, Astar u⋆⟫`, then the adjoint bifunction of the Fenchel perturbation has value
`g∗ u⋆ - f⋆ (Astar u⋆ + x⋆)`. -/
theorem adjoint_fenchelPerturbation_apply
    [Add XStar]
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = (⟪x, Astar uStar⟫ₚ : 𝕜))
    (xStar : XStar) (uStar : UStar) :
    F⋆ xStar uStar =
      g∗ uStar - f⋆ (Astar uStar + xStar) := by
  sorry

/-- Zero-slice specialization of Lemma 31.0.8 at the pairing-based dual-map layer. -/
@[simp] theorem objective_adjoint_fenchelPerturbation_apply
    [AddZeroClass XStar]
    (hA : ∀ x uStar, (⟪A x, uStar⟫ₚ : 𝕜) = (⟪x, Astar uStar⟫ₚ : 𝕜))
    (uStar : UStar) :
    ((F⋆)₀ uStar) =
      g∗ uStar - f⋆ (Astar uStar) := by
  simpa [objective, add_zero] using
    (adjoint_fenchelPerturbation_apply
      (A := A) (Astar := Astar) (f := f) (g := g)
      (hA := hA) (xStar := (0 : XStar)) (uStar := uStar))

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [NormedField 𝕜]
variable [SupSet (WithTopBot 𝕜)] [InfSet (WithTopBot 𝕜)] [Sub (WithTopBot 𝕜)]
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (A : X →L[𝕜] U) (f : X → WithTopBot 𝕜) (g : U → WithTopBot 𝕜)

local notation "F" => fenchelPerturbation A.toLinearMap f g
local notation "F⋆" =>
  (adjoint (StrongDual 𝕜 X) (StrongDual 𝕜 U) F :
    StrongDual 𝕜 X → StrongDual 𝕜 U → WithTopBot 𝕜)

/-- Lemma 31.0.8 strong-dual bridge form. -/
theorem adjoint_fenchelPerturbation_apply_strongDual
    (xStar : StrongDual 𝕜 X) (uStar : StrongDual 𝕜 U) :
    F⋆ xStar uStar =
      g∗ uStar - f⋆ (uStar.comp A + xStar) := by
  simpa using
    (adjoint_fenchelPerturbation_apply
      (A := A.toLinearMap)
      (Astar := fun uStar : StrongDual 𝕜 U ↦ uStar.comp A)
      (hA := by
        intro x uStar
        rfl)
      (f := f) (g := g) (xStar := xStar) (uStar := uStar))

/-- Zero-slice specialization of Lemma 31.0.8 in strong-dual form. -/
@[simp] theorem objective_adjoint_fenchelPerturbation_apply_strongDual
    (uStar : StrongDual 𝕜 U) :
    ((F⋆)₀ uStar) =
      g∗ uStar - f⋆ (uStar.comp A) := by
  simpa using
    (objective_adjoint_fenchelPerturbation_apply
      (A := A.toLinearMap)
      (Astar := fun uStar : StrongDual 𝕜 U ↦ uStar.comp A)
      (hA := by
        intro x uStar
        rfl)
      (f := f) (g := g) (uStar := uStar))

end

end Bifunction
