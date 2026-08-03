import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap20.Theorem_20_25
import BauschkeLean.Chap26.Text_26_0_1
import BauschkeLean.Chap26.Definition_26_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator
open SetValuedOperator

universe u

namespace ERealFunction

section VariationalInequalities

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: the Chapter 26 owner is `variationalInequalityProblem f B`.
- `core/canonical`: the operator-theoretic owner is `((∂ f) + B).zeros`.
- `bridge/view`: this remark identifies the source variational-inequality problem with that zero
  set, then recalls Moreau's canonical maximal-monotonicity theorem for `∂ f`.

Primitive data: the bridge uses the Chapter 26 owner `variationalInequalityProblem` together with
the canonical owners `∂`, `+`, and `.zeros`.
Derived API: the existential witness form is already owned by
`mem_variationalInequalityProblem_iff`, so this file should not restate it as a parallel local
theorem. -/

/-- Remark 26.23 (1): rewriting the Chapter 26 variational-inequality owner through Definition
16.1 identifies it with the zero set of `A + B` for `A = ∂ f`. -/
theorem variationalInequalityProblem_eq_zeros_subdifferential_add
    {f : H → Set.Ioi (⊥ : EReal)} (B : SetValuedOperator H H) :
    variationalInequalityProblem f B = ((∂ f) + B).zeros := by
  ext x
  rw [mem_variationalInequalityProblem_iff, mem_zeros_iff]
  constructor
  · intro hx
    rw [Pi.add_apply]
    rcases hx with ⟨u, huB, hu⟩
    refine Set.mem_add.2 ⟨-u, ?_, u, huB, by simp⟩
    rw [mem_subdifferential_iff]
    intro y
    have hxy : y - x = -(x - y) := by
      abel_nf
    have hinner : ⟪y - x, -u⟫_ℝ = ⟪x - y, u⟫_ℝ := by
      calc
        ⟪y - x, -u⟫_ℝ = ⟪-(x - y), -u⟫_ℝ := by rw [hxy]
        _ = - -⟪x - y, u⟫_ℝ := by rw [inner_neg_left, inner_neg_right]
        _ = ⟪x - y, u⟫_ℝ := by rw [neg_neg]
    simpa [hinner] using hu y
  · intro hx
    rw [Pi.add_apply] at hx
    rcases Set.mem_add.mp hx with ⟨u, huSub, v, hvB, huv⟩
    rw [mem_subdifferential_iff] at huSub
    have huv' : u = -v := by
      rw [eq_neg_iff_add_eq_zero]
      exact huv
    refine ⟨v, hvB, ?_⟩
    intro y
    have hxy : y - x = -(x - y) := by
      abel_nf
    have hinner : ⟪y - x, u⟫_ℝ = ⟪x - y, v⟫_ℝ := by
      calc
        ⟪y - x, u⟫_ℝ = ⟪y - x, -v⟫_ℝ := by rw [huv']
        _ = ⟪-(x - y), -v⟫_ℝ := by rw [hxy]
        _ = - -⟪x - y, v⟫_ℝ := by rw [inner_neg_left, inner_neg_right]
        _ = ⟪x - y, v⟫_ℝ := by rw [neg_neg]
    simpa [hinner] using huSub y

/-- The source variational-inequality solution set is exactly the canonical primal inclusion
solution set for the specialization `A = ∂ f`. -/
theorem variationalInequalityProblem_eq_primal_inclusion_solution_set
    {f : H → Set.Ioi (⊥ : EReal)} (B : SetValuedOperator H H) :
    variationalInequalityProblem f B = primal_inclusion_solution_set (∂ f) B := by
  simpa [SetValuedOperator.primal_inclusion_solution_set] using
    variationalInequalityProblem_eq_zeros_subdifferential_add B

variable [CompleteSpace H]

/- Remark 26.23 (2): under the Chapter 26 specialization `A = ∂ f` with `f ∈ Γ₀(H)`, the
maximal-monotonicity claim is exactly Moreau's canonical owner theorem from Chapter 20. -/
#check subdifferential_isMaximallyMonotone_of_mem_gammaZero

end VariationalInequalities

end ERealFunction
