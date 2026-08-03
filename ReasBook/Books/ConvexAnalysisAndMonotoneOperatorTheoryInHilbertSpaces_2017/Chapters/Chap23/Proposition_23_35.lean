import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap22.Definition_22_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace SetValuedOperator

-- Semantic search note: `lean_leansearch` only surfaced order-theoretic `StrictMono*` owners,
-- so this file uses the chapter-local set-valued-operator API `IsStrictlyMonotone` from
-- Definition 22.1 together with the Chapter 1 zero-set surface `A.zeros`.

/- Source/core/bridge triage:
- `source-facing`: Proposition 23.35 states that the zero set `A.zeros` has at most one point.
- `core/canonical`: strict monotonicity is the Chapter 22 owner `A.IsStrictlyMonotone`.
- `bridge/view`: the reusable downstream form is the pointwise uniqueness statement for two
  members of `A.zeros`. -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Two zeros of a strictly monotone operator coincide. -/
theorem IsStrictlyMonotone.eq_of_mem_zeros
    {A : SetValuedOperator H H} (hA : A.IsStrictlyMonotone)
    {x y : H} (hx : x ∈ A.zeros) (hy : y ∈ A.zeros) :
    x = y := by
  by_contra hxy
  have hx0 : (0 : H) ∈ A x := by simpa using hx
  have hy0 : (0 : H) ∈ A y := by simpa using hy
  have hinner := hA hx0 hy0 hxy
  simp at hinner

/-- Proposition 23.35: if a set-valued operator on a real Hilbert space is strictly monotone,
then its zero set is at most a singleton. -/
theorem zeros_subsingleton_of_isStrictlyMonotone
    {A : SetValuedOperator H H} (hA : A.IsStrictlyMonotone) :
    A.zeros.Subsingleton := by
  intro x hx y hy
  exact hA.eq_of_mem_zeros hx hy

end SetValuedOperator
