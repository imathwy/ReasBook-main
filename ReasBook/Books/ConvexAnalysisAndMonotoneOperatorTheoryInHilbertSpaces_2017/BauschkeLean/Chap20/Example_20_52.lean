import Mathlib
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap20.Definition_20_51

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Example 20.52: the identity-operator Fitzpatrick supremand is the completed-square
quadratic from the textbook calculation. -/
lemma fitzpatrick_id_supremand_eq_completed_square (x u y : H) :
    ⟪y, u⟫_ℝ + ⟪x, y⟫_ℝ - ⟪y, y⟫_ℝ =
      (1 / 4 : ℝ) * ‖x + u‖ ^ 2 - ‖y - (1 / 2 : ℝ) • (x + u)‖ ^ 2 := by
  -- Expand the midpoint remainder so the quadratic terms can be regrouped explicitly.
  rw [norm_sub_sq_real]
  -- Rewrite the midpoint pairing and midpoint norm in scalar form.
  rw [real_inner_smul_right, inner_add_right]
  rw [← real_inner_self_eq_norm_sq ((1 / 2 : ℝ) • (x + u))]
  rw [real_inner_smul_left, real_inner_smul_right]
  rw [← real_inner_self_eq_norm_sq (x + u)]
  rw [real_inner_self_eq_norm_sq y]
  -- Commute the mixed term so the remaining scalar identity is symmetric in `(x, y)`.
  rw [real_inner_comm y x]
  ring_nf

/-- Helper for Example 20.52: the midpoint pair `((x + u) / 2, (x + u) / 2)` lies in the graph of
the identity singleton-valued operator. -/
lemma half_sum_mem_graph_id (x u : H) :
    (((1 / 2 : ℝ) • (x + u)), ((1 / 2 : ℝ) • (x + u))) ∈
      gra ((id : H → H).toSetValuedOperator) := by
  -- Graph membership for the singleton-valued identity operator is exactly diagonal equality.
  simp [SetValuedOperator.mem_graph, Function.toSetValuedOperator_apply]

/-- Helper for Example 20.52: package the midpoint maximizer as a graph point of the identity
operator. -/
noncomputable def half_sum_graph_point (x u : H) : gra ((id : H → H).toSetValuedOperator) :=
  ⟨(((1 / 2 : ℝ) • (x + u)), ((1 / 2 : ℝ) • (x + u))), half_sum_mem_graph_id x u⟩

/-- Helper for Example 20.52: every graph point of the identity operator contributes at most the
target quadratic to the Fitzpatrick supremum. -/
lemma fitzpatrick_id_supremand_le_target_quadratic (x u : H)
    (p : gra ((id : H → H).toSetValuedOperator)) :
    ((⟪p.1.1, u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal) ≤
      ((1 / 4 : ℝ) * ‖x + u‖ ^ 2 : EReal) := by
  have hp : p.1.2 = p.1.1 := by
    -- Normalize an identity-graph point to the diagonal form `(y, y)`.
    have hp' := p.2
    rw [SetValuedOperator.mem_graph, Function.toSetValuedOperator_apply,
      Set.mem_singleton_iff] at hp'
    exact hp'
  have hreal :
      ⟪p.1.1, u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ ≤
        (1 / 4 : ℝ) * ‖x + u‖ ^ 2 := by
    -- Substitute the diagonal graph identity and drop the nonnegative square remainder.
    rw [hp, fitzpatrick_id_supremand_eq_completed_square]
    nlinarith [sq_nonneg ‖p.1.1 - (1 / 2 : ℝ) • (x + u)‖]
  exact_mod_cast hreal

/-- Helper for Example 20.52: the midpoint graph point attains the target quadratic value of the
identity-operator supremand. -/
lemma fitzpatrick_id_supremand_eq_target_quadratic_at_half_sum (x u : H) :
    ((⟪((1 / 2 : ℝ) • (x + u)), u⟫_ℝ + ⟪x, (1 / 2 : ℝ) • (x + u)⟫_ℝ -
        ⟪((1 / 2 : ℝ) • (x + u)), (1 / 2 : ℝ) • (x + u)⟫_ℝ : ℝ) : EReal) =
      ((1 / 4 : ℝ) * ‖x + u‖ ^ 2 : EReal) := by
  have hreal :
      ⟪((1 / 2 : ℝ) • (x + u)), u⟫_ℝ + ⟪x, (1 / 2 : ℝ) • (x + u)⟫_ℝ -
        ⟪((1 / 2 : ℝ) • (x + u)), (1 / 2 : ℝ) • (x + u)⟫_ℝ =
        (1 / 4 : ℝ) * ‖x + u‖ ^ 2 := by
    -- Evaluate the completed square at its midpoint, where the remainder vanishes.
    rw [fitzpatrick_id_supremand_eq_completed_square]
    simp
  exact congrArg (fun t : ℝ => (t : EReal)) hreal

/-- Example 20.52: for the identity singleton-valued operator, the Fitzpatrick function is the
textbook quadratic map `(x, u) ↦ (1 / 4) * ‖x + u‖ ^ 2`. -/
theorem fitzpatrickFunction_id_apply (x u : H) :
    F[id.toSetValuedOperator] (x, u) = ((1 / 4 : ℝ) * ‖x + u‖ ^ 2 : EReal) := by
  -- Unfold the Fitzpatrick supremum and compare each graph-point contribution with the target
  -- completed square from the source computation.
  rw [SetValuedOperator.fitzpatrickFunction]
  refine le_antisymm ?_ ?_
  · -- Every graph point of the identity operator lies on the diagonal and is bounded above by the
    -- target quadratic.
    refine iSup_le fun p ↦ ?_
    exact fitzpatrick_id_supremand_le_target_quadratic x u p
  · -- The midpoint diagonal graph point realizes the bound, so the supremum attains the textbook
    -- quadratic value.
    refine le_iSup_of_le (half_sum_graph_point x u) ?_
    simpa [half_sum_graph_point] using
      (le_of_eq (fitzpatrick_id_supremand_eq_target_quadratic_at_half_sum x u).symm)
