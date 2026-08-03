import Mathlib
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap01.Text_1_0_9
import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap01.Text_1_0_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace ContinuousLinearMap

section SetValuedOperatorCalculus

open scoped SetValuedOperator

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Domain sampling:
-- * `source-facing`: Chapter 25 names the parallel composition `L ▷ A`.
-- * `core/canonical`: Chapter 16 already owns the operator calculus
--   `ContinuousLinearMap.adjointImage`.
-- * `bridge/view`: `L ▷ A` is the inverse of the adjoint-image owner applied to `A⁻¹`.

/-- Definition 25.39: the parallel composition of a set-valued operator `A` by a bounded linear
map `L` is the operator `(L ∘ A⁻¹ ∘ L^*)⁻¹`. The core construction `L ∘ A⁻¹ ∘ L^*` is the
Chapter 16 owner `ContinuousLinearMap.adjointImage` for `L.adjoint`, and the source-facing Lean
notation is `L ▷ A`. -/
def parallelComposition
    (L : H →L[ℝ] K) (A : SetValuedOperator H H) : SetValuedOperator K K :=
  (L.adjoint.adjointImage A⁻¹)⁻¹

scoped[SetValuedOperator] infixr:70 " ▷ " => ContinuousLinearMap.parallelComposition

/-- Membership in `(L ▷ A) y` means that `y` is the `L`-image of some
`x : H` at which `A` contains `L^* u`. -/
@[simp] theorem mem_parallelComposition_iff
    (L : H →L[ℝ] K) (A : SetValuedOperator H H) (y u : K) :
    u ∈ (L ▷ A) y ↔ ∃ x : H, L x = y ∧ L.adjoint u ∈ A x := by
  -- Unfold the inverse defining `L ▷ A` so membership is expressed through the Chapter 16 owner.
  rw [parallelComposition, SetValuedOperator.mem_inverse_iff]
  -- Expand the adjoint-image owner and normalize the inverse witness into the textbook order.
  rw [adjointImage_apply, Set.mem_image]
  simpa [SetValuedOperator.mem_inverse_iff, adjoint_adjoint, and_comm]

/-- Evaluating `L ▷ A` at `y` gives the set of `u` whose adjoint image lies in
`A x` for some `x` with `L x = y`. -/
theorem parallelComposition_apply
    (L : H →L[ℝ] K) (A : SetValuedOperator H H) (y : K) :
    (L ▷ A) y = {u : K | ∃ x : H, L x = y ∧ L.adjoint u ∈ A x} := by
  ext u
  -- Reduce the set equality to the pointwise witness characterization proved above.
  simpa using (mem_parallelComposition_iff L A y u)

end SetValuedOperatorCalculus

end ContinuousLinearMap
