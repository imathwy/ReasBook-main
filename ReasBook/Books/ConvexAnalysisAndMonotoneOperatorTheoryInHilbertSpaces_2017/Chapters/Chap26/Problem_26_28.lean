import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap01.Text_1_0_21
import BauschkeLean.Chap16.Proposition_16_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u v

noncomputable section

namespace SetValuedOperator

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Problem 26.28 introduces the primal and dual inclusion solution sets.
- `core/canonical`: the owner declarations are `SetValuedOperator.inverse`,
  `SetValuedOperator.translate`, and `ContinuousLinearMap.adjointImage`.
- `bridge/view`: the solution sets should therefore be source-facing names defined as inverse
  fibers of the canonical operators, rather than bespoke set comprehensions. -/

/-- Problem 26.28 (1): the primal solution set `𝓟` consists of the points `x : H` solving
`z ∈ A x + L^*(B(Lx - r))`, expressed through the canonical translated operator
`B.translate r` and the adjoint-image owner `L.adjointImage`. -/
def composite_primal_inclusion_solution_set
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) : Set H :=
  (A + L.adjointImage (B.translate r))⁻¹ z

/-- Membership in `composite_primal_inclusion_solution_set` is exactly the primal inclusion
`z ∈ A x + L^*(B(Lx - r))`. -/
@[simp] theorem mem_composite_primal_inclusion_solution_set
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (x : H) :
    x ∈ composite_primal_inclusion_solution_set z A r B L ↔
      z ∈ A x + L.adjoint '' (B (L x - r)) := by
  simp [composite_primal_inclusion_solution_set]

/-- Problem 26.28 (2): the dual solution set `𝓓` consists of the points `v : K` solving
`-r ∈ -L(A⁻¹(z - L^*v)) + B⁻¹ v`. -/
def composite_dual_inclusion_solution_set
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) : Set K :=
  (fun v ↦ ((-L) '' (A⁻¹ (z - L.adjoint v))) + (B⁻¹ v))⁻¹ (-r)

/-- Membership in `composite_dual_inclusion_solution_set` is exactly the dual inclusion
`-r ∈ -L(A⁻¹(z - L^*v)) + B⁻¹ v`. -/
@[simp] theorem mem_composite_dual_inclusion_solution_set
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (v : K) :
    v ∈ composite_dual_inclusion_solution_set z A r B L ↔
      -r ∈ ((-L) '' (A⁻¹ (z - L.adjoint v))) + (B⁻¹ v) := by
  simp [composite_dual_inclusion_solution_set]

end SetValuedOperator
