import BauschkeLean.Chap20.Definition_20_1
import BauschkeLean.Chap23.Proposition_23_7

-- Semantic recall note: `lean_leansearch` surfaced only the unrelated algebra-spectrum
-- resolvent API, so this item follows the verified local Chapter 23 surfaces `J[...]`, `comp`,
-- `toSetValuedOperator`, and pointwise operator addition/scalar multiplication.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: for maximally monotone `A`, Proposition 23.20 identifies the residual
  `Id - J[γ • A]` with `γ • {}^[γ] A`, and at `γ = 1` with the resolvent of the inverse operator.
- `core/canonical`: the Chapter 23 owner for that residual term is the Yosida approximation
  `{}^[γ] A`.
- `bridge/view`: Proposition 23.7 (3) rewrites `{}^[γ] A` using the resolvent of `A⁻¹` and the
  inverse homothety. -/

/-- Proposition 23.20 (1): the book states this for a maximally monotone operator
`A : H → 2^H`, but the identity is the algebraic Yosida decomposition valid for every `A`. -/
theorem id_toSetValuedOperator_eq_resolvent_smul_add_smul_yosidaApproximation
    {A : SetValuedOperator H H} (γ : PosReal) :
    id.toSetValuedOperator = J[((γ : ℝ) • A)] + (γ : ℝ) • {}^[γ] A := sorry

/-- Via Proposition 23.7 (3), the Yosida term in Proposition 23.20 (1) can be rewritten as the
resolvent of `A⁻¹` composed with the inverse homothety; the book's maximal-monotonicity
assumption is not needed for this Chapter 23 operator identity. -/
theorem id_toSetValuedOperator_eq_resolvent_smul_add_smul_resolvent_inverse_comp_inv_smul_id
    {A : SetValuedOperator H H} (γ : PosReal) :
    id.toSetValuedOperator =
      J[((γ : ℝ) • A)] +
        (γ : ℝ) •
          (J[(((γ : ℝ)⁻¹) • A⁻¹)]).comp (((γ : ℝ)⁻¹) • id.toSetValuedOperator) := sorry

/-- Proposition 23.20 (2): the book specializes this to maximally monotone `A : H → 2^H`,
while the Chapter 23 identity itself is the algebraic relation `J[A⁻¹] = Id - J[A]`. -/
theorem resolvent_inverse_eq_id_sub_resolvent
    {A : SetValuedOperator H H} :
    J[A⁻¹] = id.toSetValuedOperator - J[A] := sorry

/-- At `γ = 1`, Proposition 23.20 identifies the Yosida approximation with the resolvent of the
inverse operator. -/
theorem yosidaApproximation_one_eq_resolvent_inverse
    {A : SetValuedOperator H H} :
    {}^[(1 : PosReal)] A = J[A⁻¹] := sorry

end SetValuedOperator
