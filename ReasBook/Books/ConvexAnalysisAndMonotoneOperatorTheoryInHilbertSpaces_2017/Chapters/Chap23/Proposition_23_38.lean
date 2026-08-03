import BauschkeLean.Chap23.Definition_23_1
import BauschkeLean.Chap23.Proposition_23_2

-- Semantic recall note: `lean_leansearch` surfaced only the general owner
-- `Function.fixedPoints`, not a Chapter 23 set-valued fixed-point surface, so this file keeps the
-- textbook `Fix J_{γ A}` as the self-membership set `{x | x ∈ J[((γ : ℝ) • A)] x}` and uses the
-- verified local owners `A.zeros`, `J[...]`, and `{}^[γ]`.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- Proposition 23.38 (1): for `A : H → 2^H` and `γ ∈ ℝ_{++}`, the textbook fixed-point set
`Fix J_{γ A}`, realized as `{x | x ∈ J[(γ : ℝ) • A] x}`, equals `A.zeros`. -/
theorem fixedPointSet_resolvent_smul_eq_zeros
    {A : SetValuedOperator H H} (γ : PosReal) :
    ({x : H | x ∈ J[((γ : ℝ) • A)] x} : Set H) = A.zeros := by
  ext x
  rw [Set.mem_setOf_eq, mem_zeros_iff, mem_resolvent_smul_iff_mem_graph, mem_graph]
  simp

/-- Proposition 23.38 (2): for `A : H → 2^H` and `γ ∈ ℝ_{++}`, the zero set of `A` agrees with
the zero set of the Yosida approximation `{}^γ A`. -/
theorem zeros_eq_zeros_yosidaApproximation
    {A : SetValuedOperator H H} (γ : PosReal) :
    A.zeros = ({}^[γ] A).zeros := by
  ext x
  rw [mem_zeros_iff, mem_zeros_iff, mem_yosidaApproximation_iff_mem]
  simp

end SetValuedOperator
