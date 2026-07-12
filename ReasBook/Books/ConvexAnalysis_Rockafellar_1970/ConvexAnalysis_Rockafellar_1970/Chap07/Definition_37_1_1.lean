import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_0_1

noncomputable section

universe u u' v w z

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {UStar : Type u'} {X : Type v} {XStar : Type w} {L : Type z}
variable [HAdd L L L] [HSub L L L]
variable [HasPairing U UStar L] [HasPairing X XStar L]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 37.1.1 introduces the lower and upper conjugates of a
  concave-convex saddle-function.
- `core/canonical`: the Chapter 36 owner layer already contains the relevant minimax operators
  `Bifunction.maximinValueOn` and `Bifunction.minimaxValueOn`.
- `bridge/view`: the source conjugates are exactly those existing owners applied directly in source
  variable order to the affine perturbation kernel
  `(x⋆, u) ↦ ⟪u, u⋆⟫ + ⟪x, x⋆⟫ - K(u, x⋆)`, yielding the textbook order
  `sup_x⋆ inf_u` / `inf_u sup_x⋆` without an extra swap wrapper.

Domain-style sampling used here:
- `Bifunction.maximinValue` from `Chap07.Definition_36_0_1`;
- `Bifunction.minimaxValue` from `Chap07.Definition_36_0_1`;
- `Bifunction.maximin_le_minimax` from the same owner file.

Primitive data vs derived API:
- primitive data: the saddle-function `K` and the evaluation point `(u⋆, x)`;
- primitive source-facing owners introduced here: `lowerConjugate K` and `upperConjugate K`;
- derived API: the explicit `iSup`/`iInf` formulas and the minimax inequality
  `lowerConjugate K ≤ upperConjugate K`.

Layer target: `source-facing`, implemented directly through the existing Chapter 36 owners rather
than a second minimax wrapper.
-/

/-- Definition 37.1.1: the lower conjugate of a concave-convex saddle-function `K`, expressed
as the Chapter 36 maximin value of the affine perturbation kernel. -/
def lowerConjugate [SupSet L] [InfSet L] (K : U → XStar → L) : UStar → X → L :=
  fun uStar x ↦
    maximinValue (fun xStar u ↦
      (⟪u, uStar⟫ₚ + ⟪x, xStar⟫ₚ) - K u xStar)

/-- Definition 37.1.1: the upper conjugate of a concave-convex saddle-function `K`, expressed
as the Chapter 36 minimax value of the affine perturbation kernel. -/
def upperConjugate [SupSet L] [InfSet L] (K : U → XStar → L) : UStar → X → L :=
  fun uStar x ↦
    minimaxValue (fun xStar u ↦
      (⟪u, uStar⟫ₚ + ⟪x, xStar⟫ₚ) - K u xStar)

/-- Primitive owner-level bridge for Definition 37.1.1: the lower conjugate is the Chapter 36
maximin owner applied to the affine perturbation kernel (in source variable order). -/
theorem lowerConjugate_eq_maximinValue
    [SupSet L] [InfSet L] (K : U → XStar → L) (uStar : UStar) (x : X) :
    lowerConjugate K uStar x = maximinValue (fun xStar u ↦
      (⟪u, uStar⟫ₚ + ⟪x, xStar⟫ₚ) - K u xStar) :=
  rfl

/-- Primitive owner-level bridge for Definition 37.1.1: the upper conjugate is the Chapter 36
minimax owner applied to the affine perturbation kernel (in source variable order). -/
theorem upperConjugate_eq_minimaxValue
    [SupSet L] [InfSet L] (K : U → XStar → L) (uStar : UStar) (x : X) :
    upperConjugate K uStar x = minimaxValue (fun xStar u ↦
      (⟪u, uStar⟫ₚ + ⟪x, xStar⟫ₚ) - K u xStar) :=
  rfl

/- Textbook pointwise notation for Definition 37.1.1. -/
scoped[Rockafellar] notation:max K " _*(" uStar ", " x ")" =>
  Bifunction.lowerConjugate K uStar x

/- Textbook pointwise notation for Definition 37.1.1. -/
scoped[Rockafellar] notation:max K " ^*(" uStar ", " x ")" =>
  Bifunction.upperConjugate K uStar x

section

variable [CompleteLattice L]

@[simp] theorem lowerConjugate_apply
    (K : U → XStar → L) (uStar : UStar) (x : X) :
    K _*(uStar, x) =
      ⨆ xStar : XStar, ⨅ u : U,
        (⟪u, uStar⟫ₚ + ⟪x, xStar⟫ₚ) - K u xStar := by
  simp [lowerConjugate_eq_maximinValue, maximinValue, maximinValueOn]

@[simp] theorem upperConjugate_apply
    (K : U → XStar → L) (uStar : UStar) (x : X) :
    K ^*(uStar, x) =
      ⨅ u : U, ⨆ xStar : XStar,
        (⟪u, uStar⟫ₚ + ⟪x, xStar⟫ₚ) - K u xStar := by
  simp [upperConjugate_eq_minimaxValue, minimaxValue, minimaxValueOn]

/-- Proposition 37.1.2, owner form: the lower conjugate is pointwise bounded above by the upper
conjugate. -/
theorem lowerConjugate_le_upperConjugate
    (K : U → XStar → L) (uStar : UStar) (x : X) :
    K _*(uStar, x) ≤ K ^*(uStar, x) := by
  simpa [lowerConjugate, upperConjugate] using
    maximin_le_minimax (fun xStar u ↦ (⟪u, uStar⟫ₚ + ⟪x, xStar⟫ₚ) - K u xStar)

end

end

end Bifunction
