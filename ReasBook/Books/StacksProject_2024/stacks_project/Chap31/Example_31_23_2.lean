import Mathlib
import StacksProject_2024.Chap31.Definition_31_23_1
import StacksProject_2024.Chap31.Definition_31_23_3

open CategoryTheory
open AlgebraicGeometry
open MvPolynomial
open scoped nonZeroDivisors

noncomputable section

-- Semantic recall: `lean_leansearch` was unavailable here because the endpoint returned HTTP 429,
-- so the owner choice was verified against the local Chapter 31 API in
-- `stacks_project.Chap31.Definition_31_23_1`, which defines
-- `LocallyRingedSpace.meromorphicFunctionSheaf` and `toMeromorphicFunctionSheafHom`.

/-- Variables for the quotient presentation of Example 31.23.2: one variable `x` and one variable
`y_α` for each complex number `α`. -/
inductive Example31232Var
  | x
  | y : ℂ → Example31232Var
  deriving DecidableEq

/-- The ambient polynomial ring
`\mathbf{C}[x, \{y_\alpha\}_{\alpha \in \mathbf{C}}]` of Example 31.23.2. -/
abbrev example31232PolynomialRing :=
  MvPolynomial Example31232Var ℂ

/-- The defining relation `(x - α) y_α` from Example 31.23.2. -/
def example31232XMinusScalarMulYRelation (α : ℂ) : example31232PolynomialRing :=
  (X Example31232Var.x - C α) * X (Example31232Var.y α)

/-- The defining relation `y_α y_β` from Example 31.23.2. -/
def example31232YMulYRelation (α β : ℂ) : example31232PolynomialRing :=
  X (Example31232Var.y α) * X (Example31232Var.y β)

/-- The full family of defining relations for the example ring. -/
def example31232Relations : Set example31232PolynomialRing :=
  Set.range example31232XMinusScalarMulYRelation ∪
    Set.range (fun p : ℂ × ℂ ↦ example31232YMulYRelation p.1 p.2)

/-- The defining ideal
`((x - α) y_α, y_α y_β \mid α, β \in \mathbf{C})` of Example 31.23.2. -/
def example31232Ideal : Ideal example31232PolynomialRing :=
  Ideal.span example31232Relations

/-- The quotient ring
`\mathbf{C}[x, \{ y_\alpha \}_{\alpha \in \mathbf{C}}]/
((x - \alpha)y_\alpha, y_\alpha y_\beta)` from Example 31.23.2. -/
abbrev example31232Ring :=
  example31232PolynomialRing ⧸ example31232Ideal

/-- The affine scheme `X = \operatorname{Spec}(A)` attached to the example ring `A`. -/
abbrev example31232X : Scheme :=
  Scheme.Spec.obj (Opposite.op <| CommRingCat.of example31232Ring)

/-- On every affine basic open `D(f)` of the affine scheme from Example 31.23.2, every
nonzerodivisor in the localization `A_f` is a unit. -/
theorem example31232_isUnit_of_mem_nonZeroDivisors_localizationAway
    (f : example31232Ring) (z : Localization.Away f)
    (hz : z ∈ nonZeroDivisors (Localization.Away f)) :
    IsUnit z := sorry

/-- Example 31.23.2: for
`A = \mathbf{C}[x, \{ y_\alpha \}_{\alpha \in \mathbf{C}}]/
((x - \alpha)y_\alpha, y_\alpha y_\beta)` and `X = \operatorname{Spec}(A)`, the canonical map
`\mathcal O_X \to \mathcal K_X` is an isomorphism. -/
theorem example31232_toMeromorphicFunctionSheafHom_isIso :
    IsIso (example31232X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom) := sorry

/-- Companion bridge for Example 31.23.2 on the underlying presheaf morphism. -/
theorem example31232_toMeromorphicFunctionSheaf_isIso :
    IsIso (example31232X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom) := sorry
