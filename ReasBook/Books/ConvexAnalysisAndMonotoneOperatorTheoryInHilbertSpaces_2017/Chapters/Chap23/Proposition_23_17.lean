import BauschkeLean.Chap01.Text_1_0_21
import BauschkeLean.Chap20.Definition_20_1
import BauschkeLean.Chap23.Definition_23_1
import BauschkeLean.Chap23.Proposition_23_2

-- `core/canonical`: part (1) is expressed through the Chapter 1 composition owner `comp`.
-- `source-facing`: parts (2) and (3) use the codomain-translation owner `A.addConst z`.
-- `bridge/view`: the raw constant-singleton sum survives only through
-- `addConst_eq_const_toSetValuedOperator_add`.
-- Semantic recall note: lean_leansearch did not surface relevant monotone-operator resolvent API,
-- so this item stays on the verified local Chapter 23 owners `Maximal IsMonotone`, `J[_]`,
-- `translate`, and `addConst`.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u}

section

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 23.17: in the unscaled `γ = 1` case, resolvent membership is exactly
the residual membership condition `x - p ∈ A p`. -/
private theorem mem_resolvent_iff_sub_mem
    (A : SetValuedOperator H H) (x p : H) :
    p ∈ J[A] x ↔ x - p ∈ A p := by
  -- Specialize Proposition 23.2 to the scale `γ = 1`.
  simpa using (mem_resolvent_smul_iff_sub_mem_smul A (1 : PosReal) x p)

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 23.17: membership in the perturbed residual
`x - u ∈ A.addConst z u` is equivalent to residual membership in `A` at the shifted input
`(x - z) - u`. -/
private theorem sub_mem_addConst_iff
    {A : SetValuedOperator H H} (z x u : H) :
    x - u ∈ A.addConst z u ↔ (x - z) - u ∈ A u := by
  rw [SetValuedOperator.mem_addConst_iff]
  constructor
  · rintro ⟨y, hy, hEq⟩
    -- Cancel the translated codomain constant `z` from the residual equation.
    have hrewrite : (x - z) - u = y := by
      calc
        (x - z) - u = (x - u) - z := by abel_nf
        _ = (z + y) - z := by rw [hEq]
        _ = y := by abel_nf
    simpa [hrewrite] using hy
  · intro hy
    -- Reinsert the constant translation as the explicit `addConst` witness.
    refine ⟨(x - z) - u, hy, ?_⟩
    abel_nf

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 23.17: output-translating a translated operator by `z` is equivalent to
shifting the witness by `z` on the resolvent side. -/
private theorem mem_addConst_translate_iff
    {B : SetValuedOperator H H} (z x u : H) :
    u ∈ (B.translate z).addConst z x ↔ u - z ∈ B (x - z) := by
  rw [SetValuedOperator.mem_addConst_iff]
  constructor
  · rintro ⟨y, hy, hEq⟩
    have hy' : y ∈ B (x - z) := by
      simpa using hy
    -- Cancel the output translation to recover the underlying witness in `B (x - z)`.
    have hrewrite : u - z = y := by
      calc
        u - z = (z + y) - z := by rw [hEq]
        _ = y := by abel_nf
    simpa [hrewrite] using hy'
  · intro hy
    -- The shifted witness `u - z` rebuilds the codomain-translation membership.
    refine ⟨u - z, ?_, ?_⟩
    · simpa using hy
    abel_nf

/-- Helper for Proposition 23.17: the residual criterion for `J[A + α • Id] x` matches the
scaled resolvent criterion for `J[((1 + α)⁻¹) • A] (((1 + α)⁻¹) • x)`. -/
private theorem mem_resolvent_add_smul_id_iff
    {A : SetValuedOperator H H} (α : NNReal) (x u : H) :
    u ∈ J[(A + (α : ℝ) • id.toSetValuedOperator)] x ↔
      u ∈ J[((((1 + (α : ℝ))⁻¹) : ℝ) • A)] ((((1 + (α : ℝ))⁻¹) : ℝ) • x) := by
  let β : PosReal := ⟨((1 + (α : ℝ))⁻¹), by
    have hpos : 0 < 1 + (α : ℝ) := add_pos_of_pos_of_nonneg zero_lt_one α.2
    exact inv_pos.mpr hpos⟩
  have hOnePos : 0 < 1 + (α : ℝ) := add_pos_of_pos_of_nonneg zero_lt_one α.2
  have hOneNe : (1 + (α : ℝ)) ≠ 0 := ne_of_gt hOnePos
  have hleft :
      u ∈ J[(A + (α : ℝ) • id.toSetValuedOperator)] x ↔
        x - ((1 + (α : ℝ)) • u) ∈ A u := by
    rw [mem_resolvent_iff_sub_mem]
    -- Expand `A + α • Id` pointwise and isolate the singleton witness from the identity operator.
    rw [Pi.add_apply, Pi.smul_apply, Function.toSetValuedOperator_apply, Set.mem_add]
    constructor
    · rintro ⟨a, ha, v, hv, hEq⟩
      rw [Set.mem_smul_set] at hv
      rcases hv with ⟨w, hw, rfl⟩
      rw [Set.mem_singleton_iff] at hw
      subst w
      have hEq' : a + (α : ℝ) • u = x - u := by
        simpa using hEq
      have hrewrite : x - ((1 + (α : ℝ)) • u) = a := by
        calc
          x - ((1 + (α : ℝ)) • u) = x - (u + (α : ℝ) • u) := by
            rw [add_smul, one_smul]
          _ = (x - u) - (α : ℝ) • u := by
            abel_nf
          _ = a := by
            rw [← hEq']
            abel_nf
      simpa [hrewrite] using ha
    · intro ha
      refine ⟨x - ((1 + (α : ℝ)) • u), ha, (α : ℝ) • u, ?_, ?_⟩
      · rw [Set.mem_smul_set]
        exact ⟨u, by simp, rfl⟩
      · calc
          x - ((1 + (α : ℝ)) • u) + (α : ℝ) • u = x - (u + (α : ℝ) • u) + (α : ℝ) • u := by
            rw [add_smul, one_smul]
          _ = x - u := by
            abel_nf
  have hright :
      u ∈ J[((((1 + (α : ℝ))⁻¹) : ℝ) • A)] ((((1 + (α : ℝ))⁻¹) : ℝ) • x) ↔
        x - ((1 + (α : ℝ)) • u) ∈ A u := by
    have hres :
        u ∈ J[((((1 + (α : ℝ))⁻¹) : ℝ) • A)] ((((1 + (α : ℝ))⁻¹) : ℝ) • x) ↔
          ((((1 + (α : ℝ))⁻¹) : ℝ) • x - u) ∈ ((((1 + (α : ℝ))⁻¹) : ℝ) • A) u := by
      simpa [β] using
        (mem_resolvent_smul_iff_sub_mem_smul A β ((((1 + (α : ℝ))⁻¹) : ℝ) • x) u)
    -- Cancel the inverse homothety on the residual side.
    rw [hres, Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ β.2.ne']
    constructor <;> intro hu <;>
      simpa [β, smul_sub, smul_smul, inv_inv, hOneNe] using hu
  exact hleft.trans hright.symm

/-- Proposition 23.17 (1): if `A` is maximally monotone and `α ∈ ℝ_+`, then the resolvent of
`A + α Id` is obtained by precomposing `J[((1 + α)⁻¹) • A]` with the homothety
`x ↦ (1 + α)⁻¹ • x`. -/
theorem resolvent_add_smul_id_eq_resolvent_smul_precompose
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (α : NNReal) :
    J[(A + (α : ℝ) • id.toSetValuedOperator)] =
      (J[((((1 + (α : ℝ))⁻¹) : ℝ) • A)]).comp
        ((((1 + (α : ℝ))⁻¹) : ℝ) • id.toSetValuedOperator) := by
  let _ : Maximal IsMonotone A := hA
  ext x u
  -- Collapse the composition witness to the unique scaled point `((1 + α)⁻¹) • x`.
  rw [SetValuedOperator.mem_comp]
  constructor
  · intro hu
    refine ⟨((((1 + (α : ℝ))⁻¹) : ℝ) • x), ?_, ?_⟩
    · simp [Pi.smul_apply, Function.toSetValuedOperator_apply]
    · exact (mem_resolvent_add_smul_id_iff (A := A) α x u).1 hu
  · rintro ⟨y, hy, hu⟩
    have hy' : y = ((((1 + (α : ℝ))⁻¹) : ℝ) • x) := by
      simpa [Pi.smul_apply, Function.toSetValuedOperator_apply] using hy
    subst y
    exact (mem_resolvent_add_smul_id_iff (A := A) α x u).2 hu

end

section

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Proposition 23.17 (2): if `A` is maximally monotone and `z ∈ H`, then the resolvent of the
output-translation `z + A`, realized as `A.addConst z`, is the input-translation of `J[A]`
by `z`. -/
theorem resolvent_const_add_eq_translate
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (z : H) :
    J[(A.addConst z)] = (J[A]).translate z := by
  let _ : Maximal IsMonotone A := hA
  ext x u
  -- Normalize both sides to the same residual membership condition in `A`.
  rw [mem_resolvent_iff_sub_mem, SetValuedOperator.mem_translate_iff, mem_resolvent_iff_sub_mem]
  exact sub_mem_addConst_iff (A := A) z x u

/-- Proposition 23.17 (3): if `A` is maximally monotone and `z ∈ H`, then the
resolvent of the input-translation `A.translate z` is the output-translation by `z` of the
translated resolvent `(J[A]).translate z`, realized as `((J[A]).translate z).addConst z`. -/
theorem resolvent_translate_eq_const_add_translate
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (z : H) :
    J[(A.translate z)] = ((J[A]).translate z).addConst z := by
  let _ : Maximal IsMonotone A := hA
  ext x u
  -- Rewrite both sides to the same shifted residual criterion for `A`.
  rw [mem_resolvent_iff_sub_mem, SetValuedOperator.mem_translate_iff,
    mem_addConst_translate_iff, mem_resolvent_iff_sub_mem]
  have hshift : (x - z) - (u - z) = x - u := by
    abel_nf
  constructor <;> intro hu <;> simpa [hshift] using hu

end

end SetValuedOperator
