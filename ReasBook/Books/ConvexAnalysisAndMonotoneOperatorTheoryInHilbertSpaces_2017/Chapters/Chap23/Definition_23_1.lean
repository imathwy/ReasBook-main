import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap08.Proposition_8_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [Add H]

-- `source-facing`: Definition 23.1 introduces the resolvent and the Yosida approximation.
-- `core/canonical`: both are built from the Chapter 1 owners `toSetValuedOperator`, `+`, and `⁻¹`.
-- `bridge/view`: later chapter results should reuse these owners rather than redeclaring them.

/-- Definition 23.1 (1): the resolvent of a set-valued operator `A` is the inverse of `Id + A`. -/
abbrev resolvent (A : SetValuedOperator H H) : SetValuedOperator H H :=
  ((id : H → H).toSetValuedOperator + A)⁻¹

/- Lean surface notation for the textbook resolvent `J_A`. -/
scoped notation:max "J[" A:max "]" => SetValuedOperator.resolvent A

/-- The resolvent owner unfolds to the inverse of `Id + A`. -/
theorem resolvent_def (A : SetValuedOperator H H) :
    J[A] = ((id : H → H).toSetValuedOperator + A)⁻¹ :=
  rfl

section

variable [AddCommGroup H] [Module ℝ H]

/-- Definition 23.1 (2): the Yosida approximation of index `γ ∈ ℝ_{++}` is the scaled residual
operator `(γ : ℝ)⁻¹ • (Id - J[γ • A])`. Its pointwise value at `x` is
`(γ : ℝ)⁻¹ • ({x} - J[(γ : ℝ) • A] x)`. The source-facing Lean notation is `{}^[γ] A`. -/
abbrev yosidaApproximation (A : SetValuedOperator H H) (γ : PosReal) :
    SetValuedOperator H H :=
  ((γ : ℝ)⁻¹) • ((id : H → H).toSetValuedOperator - J[((γ : ℝ) • A)])

/- Lean surface notation for the textbook Yosida approximation `{}^γ A`. -/
scoped notation:max "{}^[" γ:max "]" A:max => SetValuedOperator.yosidaApproximation A γ

/-- Evaluating the Yosida approximation is the pointwise scaled residual of the resolvent of
`γ • A`. -/
@[simp] theorem yosidaApproximation_apply
    (A : SetValuedOperator H H) (γ : PosReal) (x : H) :
    ({}^[γ] A) x =
      (γ : ℝ)⁻¹ • (({x} : Set H) - J[((γ : ℝ) • A)] x) :=
  by
    change
      ((γ : ℝ)⁻¹ • (((id : H → H).toSetValuedOperator - J[((γ : ℝ) • A)]) x)) =
        (γ : ℝ)⁻¹ • (({x} : Set H) - J[((γ : ℝ) • A)] x)
    simp

end

end SetValuedOperator
