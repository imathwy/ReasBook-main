import BauschkeLean.Chap06.Definition_6_22
import BauschkeLean.Chap06.Proposition_6_2
import BauschkeLean.Chap26.Example_26_21

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace

universe u

namespace ERealFunction

section VariationalInequalities

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Example 26.22 is the cone specialization of
  `variationalInequalityProblem (ι[K]) B.toSetValuedOperator`.
- `core/canonical`: the Chapter 26 owner remains `variationalInequalityProblem`.
- `bridge/view`: the theorems below combine the indicator-set bridge from Example 26.21 with the
  dual-cone API from Definition 6.22 to recover the classical complementarity conditions.

Because the project predicate `IsCone` is the positive-scalar convention from Chapter 1, it does
not force `K` to be nonempty. Example 26.22, however, matches the classical cone-complementarity
problem only for a genuine nonempty cone, so the source-facing specialization below keeps
`K.Nonempty` explicit. -/

/-- In the cone specialization of Example 26.21, membership in the variational inequality problem
is exactly the complementarity conditions `x ∈ K`, `⟪x, B x⟫ = 0`, and `B x ∈ Kᵒ⊕`. Since the
project notion `IsCone K` does not imply `K.Nonempty`, that hypothesis is kept explicit here. -/
@[simp] theorem mem_variationalInequalityProblem_cone_iff
    {K : Set H} (hK_nonempty : K.Nonempty) (hK_cone : IsCone K) {B : H → H} {x : H} :
    x ∈ variationalInequalityProblem (ι[K]) B.toSetValuedOperator ↔
      x ∈ K ∧ ⟪x, B x⟫_ℝ = 0 ∧ B x ∈ Kᵒ⊕ := by
  rw [mem_variationalInequalityProblem_indicator_iff hK_nonempty]
  constructor
  · rintro ⟨hxK, hvi⟩
    have htwo_mem : (2 : ℝ) • x ∈ K :=
      Set.smul_subset_of_isCone hK_cone (by positivity) <| Set.smul_mem_smul_set hxK
    have hhalf_mem : ((1 / 2 : ℝ) • x) ∈ K :=
      Set.smul_subset_of_isCone hK_cone (by positivity) <| Set.smul_mem_smul_set hxK
    have hinner_nonneg : 0 ≤ ⟪x, B x⟫_ℝ := by
      have hscaled : ⟪x - (2 : ℝ) • x, B x⟫_ℝ ≤ 0 := hvi ((2 : ℝ) • x) htwo_mem
      have hineq : ⟪x, B x⟫_ℝ ≤ 2 * ⟪x, B x⟫_ℝ := by
        simpa [sub_eq_add_neg, inner_add_left, real_inner_smul_left] using hscaled
      linarith
    have hinner_nonpos : ⟪x, B x⟫_ℝ ≤ 0 := by
      have hscaled : ⟪x - (1 / 2 : ℝ) • x, B x⟫_ℝ ≤ 0 := hvi ((1 / 2 : ℝ) • x) hhalf_mem
      have hineq : ⟪x, B x⟫_ℝ ≤ (1 / 2 : ℝ) * ⟪x, B x⟫_ℝ := by
        simpa [sub_eq_add_neg, inner_add_left, real_inner_smul_left] using hscaled
      nlinarith
    have hinner_zero : ⟪x, B x⟫_ℝ = 0 := le_antisymm hinner_nonpos hinner_nonneg
    have hdual : B x ∈ Kᵒ⊕ := by
      rw [Set.mem_dualCone_iff, Set.mem_polarCone_iff_forall_inner_nonpos]
      intro y hy
      have hyineq : ⟪x - y, B x⟫_ℝ ≤ 0 := hvi y hy
      have hy_nonneg : 0 ≤ ⟪y, B x⟫_ℝ := by
        have hxy : ⟪x, B x⟫_ℝ - ⟪y, B x⟫_ℝ ≤ 0 := by
          simpa [sub_eq_add_neg, inner_add_left] using hyineq
        rw [hinner_zero] at hxy
        linarith
      simpa [inner_neg_right] using (neg_nonpos.mpr hy_nonneg)
    exact ⟨hxK, hinner_zero, hdual⟩
  · rintro ⟨hxK, hinner_zero, hdual⟩
    refine ⟨hxK, ?_⟩
    rw [Set.mem_dualCone_iff, Set.mem_polarCone_iff_forall_inner_nonpos] at hdual
    intro y hy
    have hy_nonpos : ⟪y, -B x⟫_ℝ ≤ 0 := hdual y hy
    have hy_nonneg : 0 ≤ ⟪y, B x⟫_ℝ := by
      have hneg : -⟪y, B x⟫_ℝ ≤ 0 := by
        simpa [inner_neg_right] using hy_nonpos
      linarith
    calc
      ⟪x - y, B x⟫_ℝ = ⟪x, B x⟫_ℝ + -⟪y, B x⟫_ℝ := by
        rw [sub_eq_add_neg, inner_add_left]
        simp
      _ = ⟪x, B x⟫_ℝ - ⟪y, B x⟫_ℝ := by rw [sub_eq_add_neg]
      _ = -⟪y, B x⟫_ℝ := by simp [hinner_zero]
      _ ≤ 0 := by linarith

/-- Example 26.22: for a nonempty cone `K`, the indicator specialization of Definition 26.19
becomes the complementarity problem `find x ∈ K` such that `⟪x, B x⟫ = 0` and `B x ∈ Kᵒ⊕`. -/
theorem variationalInequalityProblem_cone_eq_complementarity_problem
    {K : Set H} (hK_nonempty : K.Nonempty) (hK_cone : IsCone K) {B : H → H} :
    variationalInequalityProblem (ι[K]) B.toSetValuedOperator =
      {x : H | x ∈ K ∧ ⟪x, B x⟫_ℝ = 0 ∧ B x ∈ Kᵒ⊕} := by
  ext x
  exact mem_variationalInequalityProblem_cone_iff hK_nonempty hK_cone

end VariationalInequalities

end ERealFunction
