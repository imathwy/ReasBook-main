import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.Proposition_20_22
import BauschkeLean.Chap20.Proposition_20_36

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open scoped SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Proposition 23.39 (1): if `A : H → 2^H` is maximally monotone, then its zero set `A.zeros`
is closed. -/
theorem Maximal.zeros_isClosed
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    IsClosed A.zeros := by
  -- Route correction: use Proposition 20.36 on the inverse operator rather than reproving the
  -- value-set geometry of `A.zeros` locally.
  have hAinv : Maximal IsMonotone A⁻¹ := Maximal.inverse hA
  -- The zero set is definitionally the value of `A⁻¹` at `0`.
  simpa [SetValuedOperator.zeros] using Maximal.value_isClosed (A := A⁻¹) hAinv (0 : H)

/-- Helper for Proposition 23.39: if `A : H → 2^H` is maximally monotone, then its zero set
`A.zeros` is convex. -/
theorem Maximal.zeros_convex
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    Convex ℝ A.zeros := by
  -- Pass maximality to the inverse operator so Proposition 20.36 applies at the value `0`.
  have hAinv : Maximal IsMonotone A⁻¹ := Maximal.inverse hA
  -- Normalize the inverse value back to the zero set surface.
  simpa [SetValuedOperator.zeros] using Maximal.value_convex (A := A⁻¹) hAinv (0 : H)

/-- Helper for Proposition 23.39: package the closedness and convexity clauses for `A.zeros`. -/
theorem Maximal.zeros_isClosed_and_convex
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    IsClosed A.zeros ∧ Convex ℝ A.zeros := by
  -- Package the two verified clauses into the textbook statement.
  constructor
  · exact Maximal.zeros_isClosed hA
  · exact Maximal.zeros_convex hA

/-- Helper bridge for Chapter 23 projection results: if `A : H → 2^H` is maximally monotone and
`A.zeros` is nonempty, then the zero set is Chebyshev. -/
theorem Maximal.zeros_isChebyshev
    [CompleteSpace H] {A : SetValuedOperator H H}
    (hA : Maximal IsMonotone A) (hzero : A.zeros.Nonempty) :
    IsChebyshev A.zeros := by
  rcases Maximal.zeros_isClosed_and_convex hA with ⟨hclosed, hconvex⟩
  exact isChebyshev_of_nonempty_isClosed_convex hzero hclosed hconvex

end SetValuedOperator
