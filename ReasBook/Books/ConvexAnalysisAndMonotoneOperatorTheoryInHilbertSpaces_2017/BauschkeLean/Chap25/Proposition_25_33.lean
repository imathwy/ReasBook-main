import BauschkeLean.Chap01.Text_1_0_9
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap23.Definition_23_1
import BauschkeLean.Chap25.Definition_25_29

open scoped Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u}

section

variable {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
variable [AddCommMonoid H] [Module 𝕜 H]

/-- Helper for Proposition 25.33: membership in the resolvent is equivalent to an explicit
graph witness. -/
private theorem mem_resolvent_iff_exists_value
    {C : SetValuedOperator H H} {x p : H} :
    p ∈ J[C] x ↔ ∃ c ∈ C p, x = p + c := by
  -- Unfold the resolvent once and rewrite the identity operator as a singleton translate.
  rw [SetValuedOperator.resolvent_def, SetValuedOperator.mem_inverse_iff]
  change x ∈ ((Function.toSetValuedOperator id) p + C p) ↔ ∃ c ∈ C p, x = p + c
  rw [Function.toSetValuedOperator_apply, Set.mem_add]
  constructor
  · rintro ⟨y, hy, c, hc, hEq⟩
    -- The singleton branch forces the intermediate point to be the graph base point.
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact ⟨c, hc, hEq.symm⟩
  · rintro ⟨c, hc, rfl⟩
    -- Repackage the explicit graph witness back into the pointwise sum.
    exact ⟨p, by simp, c, hc, rfl⟩

/-- Helper for Proposition 25.33: membership in the parallel sum of resolvents is equivalent to
two graph witnesses at the same base point. -/
private theorem mem_parallelSum_resolvents_iff_exists_pair
    (A B : SetValuedOperator H H) {x u : H} :
    u ∈ (J[A] □ J[B]) x ↔ ∃ a ∈ A u, ∃ b ∈ B u, x = (u + a) + (u + b) := by
  -- Unfold the parallel sum and read each inverse-resolvent branch through the basic witness
  -- lemma.
  rw [SetValuedOperator.mem_parallelSum_iff]
  change x ∈ (J[A]⁻¹ u + J[B]⁻¹ u) ↔ ∃ a ∈ A u, ∃ b ∈ B u, x = (u + a) + (u + b)
  rw [Set.mem_add]
  constructor
  · rintro ⟨y, hy, z, hz, hEq⟩
    rcases (SetValuedOperator.mem_inverse_iff (J[A]) u y).1 hy with hy'
    rcases (SetValuedOperator.mem_inverse_iff (J[B]) u z).1 hz with hz'
    rcases (mem_resolvent_iff_exists_value.mp hy') with ⟨a, ha, rfl⟩
    rcases (mem_resolvent_iff_exists_value.mp hz') with ⟨b, hb, rfl⟩
    exact ⟨a, ha, b, hb, hEq.symm⟩
  · rintro ⟨a, ha, b, hb, hEq⟩
    -- Package the two graph witnesses as memberships in the inverse resolvents.
    refine ⟨u + a, ?_, u + b, ?_, hEq.symm⟩
    · exact (SetValuedOperator.mem_inverse_iff (J[A]) u (u + a)).2 <|
        mem_resolvent_iff_exists_value.mpr ⟨a, ha, rfl⟩
    · exact (SetValuedOperator.mem_inverse_iff (J[B]) u (u + b)).2 <|
        mem_resolvent_iff_exists_value.mpr ⟨b, hb, rfl⟩

/-- Helper for Proposition 25.33: the half-scaled resolvent equation is equivalent to the doubled
sum equation. -/
private theorem half_smul_eq_base_add_half_smul_sum_iff
    {x u a b : H} :
    ((1 / 2 : 𝕜) • x = u + (1 / 2 : 𝕜) • (a + b)) ↔ x = (u + a) + (u + b) := by
  constructor
  · intro h
    -- Apply `2 •` to recover the unscaled equation and simplify the scalar factors.
    have htwo : (2 : 𝕜) * (1 / 2 : 𝕜) = 1 := by
      norm_num
    have h' := congrArg (fun z ↦ (2 : 𝕜) • z) h
    simpa [smul_add, smul_smul, htwo, two_smul, add_assoc, add_left_comm, add_comm] using h'
  · intro h
    -- Scale the doubled equation by `1 / 2` and regroup the two copies of the base point.
    have hhalf : ((1 / 2 : 𝕜) + (1 / 2 : 𝕜)) = 1 := by
      norm_num
    have h' := congrArg (fun z ↦ (1 / 2 : 𝕜) • z) h
    have hu : (1 / 2 : 𝕜) • u + (1 / 2 : 𝕜) • u = u := by
      calc
        (1 / 2 : 𝕜) • u + (1 / 2 : 𝕜) • u = (((1 / 2 : 𝕜) + (1 / 2 : 𝕜)) : 𝕜) • u := by
          rw [add_smul]
        _ = (1 : 𝕜) • u := by
          rw [hhalf]
        _ = u := by
          simp
    calc
      (1 / 2 : 𝕜) • x = (1 / 2 : 𝕜) • ((u + a) + (u + b)) := h'
      _ = (1 / 2 : 𝕜) • (u + a) + (1 / 2 : 𝕜) • (u + b) := by
            rw [smul_add]
      _ = ((1 / 2 : 𝕜) • u + (1 / 2 : 𝕜) • a) +
            ((1 / 2 : 𝕜) • u + (1 / 2 : 𝕜) • b) := by
            rw [smul_add, smul_add]
      _ = ((1 / 2 : 𝕜) • u + (1 / 2 : 𝕜) • u) +
            ((1 / 2 : 𝕜) • a + (1 / 2 : 𝕜) • b) := by
            simp [add_assoc, add_left_comm]
      _ = u + ((1 / 2 : 𝕜) • a + (1 / 2 : 𝕜) • b) := by
            rw [hu]
      _ = u + (1 / 2 : 𝕜) • (a + b) := by
            rw [smul_add]

/-- Helper for Proposition 25.33: membership in the half-scaled resolvent of `A + B` is
equivalent to the same pair witness as the parallel sum of resolvents. -/
private theorem mem_resolvent_half_smul_add_at_half_iff_exists_pair
    (A B : SetValuedOperator H H) {x u : H} :
    u ∈ J[((1 / 2 : 𝕜) • (A + B))] ((1 / 2 : 𝕜) • x) ↔
      ∃ a ∈ A u, ∃ b ∈ B u, x = (u + a) + (u + b) := by
  constructor
  · intro hu
    -- Unfold the resolvent witness, then unpack the scaled sum witness into separate values of
    -- `A u` and `B u`.
    rcases (mem_resolvent_iff_exists_value.mp hu) with ⟨c, hc, hEq⟩
    change c ∈ (1 / 2 : 𝕜) • ((A + B) u) at hc
    rcases hc with ⟨d, hd, rfl⟩
    change d ∈ A u + B u at hd
    rcases hd with ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, b, hb, ?_⟩
    exact (half_smul_eq_base_add_half_smul_sum_iff).mp hEq
  · rintro ⟨a, ha, b, hb, hEq⟩
    -- Build the half-scaled sum witness in `(1 / 2) • (A + B)` from the pair witness in
    -- `A u × B u`.
    refine mem_resolvent_iff_exists_value.mpr ?_
    refine ⟨(1 / 2 : 𝕜) • (a + b), ?_, ?_⟩
    · change (1 / 2 : 𝕜) • (a + b) ∈ (1 / 2 : 𝕜) • ((A + B) u)
      refine ⟨a + b, ?_, rfl⟩
      change a + b ∈ A u + B u
      exact ⟨a, ha, b, hb, rfl⟩
    · exact (half_smul_eq_base_add_half_smul_sum_iff).mpr hEq

end

/- Source/core/bridge triage:
- `source-facing`: Proposition 25.33 is the resolvent/parallel-sum identity from the text.
- `core/canonical`: the owner-level operators are the Chapter 23 resolvent `J[...]`, the
  Chapter 25 parallel sum `□`, and the Chapter 1 composition owner `.comp`.
- `bridge/view`: the affine reindexing is the singleton-valued operator induced by the
  half-homothety `((1 / 2 : 𝕜) • id)`.
The monotonicity and Hilbert-space hypotheses from the prose are redundant for this operator
identity itself, so the Lean statement keeps only the algebraic structure needed by the owners. -/

/-- Proposition 25.33: the parallel sum of the resolvents of `A` and `B` is the resolvent of
`(1 / 2) • (A + B)`, precomposed with the half-homothety. -/
theorem parallelSum_resolvent_eq_resolvent_half_smul_add_comp_half_id
    (𝕜 : Type*) [DivisionSemiring 𝕜] [CharZero 𝕜] [AddCommMonoid H] [Module 𝕜 H]
    (A B : SetValuedOperator H H) :
    J[A] □ J[B] =
      (J[((1 / 2 : 𝕜) • (A + B))]).comp
        (((1 / 2 : 𝕜) • id).toSetValuedOperator) := by
  ext x u
  -- Normalize the left-hand side and the composed right-hand side to the same pair-witness
  -- description at the common base point `u`.
  rw [mem_parallelSum_resolvents_iff_exists_pair A B, SetValuedOperator.mem_comp]
  -- The singleton-valued half-homothety contributes only the intermediate point `(1 / 2) • x`.
  simp only [Function.toSetValuedOperator_apply, Set.mem_singleton_iff, exists_eq_left]
  exact (mem_resolvent_half_smul_add_at_half_iff_exists_pair (𝕜 := 𝕜) A B).symm

end SetValuedOperator
