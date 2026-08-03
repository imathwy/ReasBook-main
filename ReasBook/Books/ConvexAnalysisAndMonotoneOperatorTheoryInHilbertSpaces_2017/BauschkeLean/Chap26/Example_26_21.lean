import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap26.Definition_26_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section VariationalInequalities

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Example 26.21 is the Chapter 26 specialization
  `variationalInequalityProblem (ι[C]) B.toSetValuedOperator`.
- `core/canonical`: the Chapter 26 owner remains `variationalInequalityProblem`.
- `bridge/view`: the theorems below identify this specialization with the classical variational
  inequality over `C`.

Primitive data: a nonempty set `C` and the canonical singleton-valued operator
`B.toSetValuedOperator`.
Derived API: the membership and set-equality reformulations below. The stronger source-side
`Γ₀(H)` fact for nonempty closed convex `C` is already owned upstream by
`indicator_mem_gammaZero_of_nonempty_isClosed_convex`, so this file should not duplicate it. -/

/-- Membership in the indicator specialization of `variationalInequalityProblem` is exactly the
classical variational inequality condition `x ∈ C` and `∀ y ∈ C, ⟪x - y, B x⟫ ≤ 0`. -/
@[simp] theorem mem_variationalInequalityProblem_indicator_iff
    {C : Set H} (hC_nonempty : C.Nonempty) {B : H → H} {x : H} :
    x ∈ variationalInequalityProblem (ι[C]) B.toSetValuedOperator ↔
      x ∈ C ∧ ∀ y ∈ C, ⟪x - y, B x⟫_ℝ ≤ 0 := by
  rw [mem_variationalInequalityProblem_iff]
  constructor
  · rintro ⟨u, hu, hvar⟩
    have hu' : u = B x := by
      rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hu
      exact hu
    have hxC : x ∈ C := by
      by_contra hxC
      obtain ⟨y, hyC⟩ := hC_nonempty
      have hxy := hvar y
      simp [indicator_apply, hxC, hyC, hu'] at hxy
    refine ⟨hxC, ?_⟩
    intro y hyC
    have hxy := hvar y
    simpa [indicator_apply, hxC, hyC, hu'] using hxy
  · rintro ⟨hxC, hx⟩
    refine ⟨B x, by simp, ?_⟩
    intro y
    by_cases hyC : y ∈ C
    · simpa [indicator_apply, hxC, hyC] using hx y hyC
    · simp [indicator_apply, hxC, hyC]

/-- Example 26.21: for a nonempty set `C`, the indicator specialization of Definition 26.19 is
exactly the classical variational inequality problem `find x ∈ C` such that
`∀ y ∈ C, ⟪x - y, B x⟫ ≤ 0`. -/
theorem variationalInequalityProblem_indicator_eq
    {C : Set H} (hC_nonempty : C.Nonempty) {B : H → H} :
    variationalInequalityProblem (ι[C]) B.toSetValuedOperator =
      {x : H | x ∈ C ∧ ∀ y ∈ C, ⟪x - y, B x⟫_ℝ ≤ 0} := by
  ext x
  exact mem_variationalInequalityProblem_indicator_iff hC_nonempty

end VariationalInequalities

end ERealFunction
