import BauschkeLean.Chap01.Text_1_0_12
import BauschkeLean.Chap13.Definition_13_34
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap20.Proposition_20_56
import BauschkeLean.Chap25.Definition_25_10

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Proposition 25.19 (1): a set-valued operator is `3*` monotone if and only if its inverse is
`3*` monotone. -/
theorem isThreeStarMonotone_inverse_iff
    {A : SetValuedOperator H H} :
    A.IsThreeStarMonotone ↔ A⁻¹.IsThreeStarMonotone := by
  constructor
  · intro h
    rw [isThreeStarMonotone_iff] at h ⊢
    rintro ⟨u, x⟩ hx
    rw [ERealFunction.mem_dom_iff_ne_top, fitzpatrickFunction_inverse_eq_transpose A,
      transpose_apply]
    exact (ERealFunction.mem_dom_iff_ne_top _ _).1 <|
      h ⟨by simpa [range_inverse] using hx.2, by simpa [dom_inverse] using hx.1⟩
  · intro h
    rw [isThreeStarMonotone_iff] at h ⊢
    rintro ⟨x, u⟩ hx
    rw [ERealFunction.mem_dom_iff_ne_top]
    have hux : (u, x) ∈ A⁻¹.dom ×ˢ A⁻¹.range := by
      exact ⟨by simpa [dom_inverse] using hx.2, by simpa [range_inverse] using hx.1⟩
    have hmem : (u, x) ∈ ERealFunction.dom (F[A⁻¹]) := h hux
    rw [ERealFunction.mem_dom_iff_ne_top, fitzpatrickFunction_inverse_eq_transpose A,
      transpose_apply] at hmem
    exact hmem

/-- Proposition 25.19 (2): for `γ > 0`, a set-valued operator `A` is `3*` monotone if and only if
the positive scalar multiple `γ • A` is `3*` monotone. -/
theorem isThreeStarMonotone_smul_iff
    {A : SetValuedOperator H H} (γ : Set.Ioi (0 : ℝ)) :
    A.IsThreeStarMonotone ↔ ((γ : ℝ) • A).IsThreeStarMonotone := by
  let hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt (show 0 < (γ : ℝ) from γ.2)
  constructor
  · intro h
    rw [isThreeStarMonotone_iff] at h ⊢
    rintro ⟨x, u⟩ hx
    have hx_dom : x ∈ A.dom := by
      rcases (mem_dom_iff _ _).1 hx.1 with ⟨v, hv⟩
      rcases Set.mem_smul_set.mp hv with ⟨v', hv', rfl⟩
      exact (mem_dom_iff _ _).2 ⟨v', hv'⟩
    have hu_range : (γ : ℝ)⁻¹ • u ∈ A.range := by
      rcases (mem_range_iff _ _).1 hx.2 with ⟨y, hy⟩
      rcases Set.mem_smul_set.mp hy with ⟨v, hv, rfl⟩
      exact (mem_range_iff _ _).2 ⟨y, by simpa [smul_smul, inv_mul_cancel₀ hγ_ne] using hv⟩
    have hxu : (x, (γ : ℝ)⁻¹ • u) ∈ A.dom ×ˢ A.range := ⟨hx_dom, hu_range⟩
    rw [ERealFunction.mem_dom_iff_ne_top, fitzpatrickFunction_smul_apply A]
    exact (EReal.mul_ne_top _ _).2
      ⟨Or.inl (by simp), Or.inl (le_of_lt (EReal.coe_pos.mpr γ.2)), Or.inl (by simp),
        Or.inr ((ERealFunction.mem_dom_iff_ne_top _ _).1 (h hxu))⟩
  · intro h
    rw [isThreeStarMonotone_iff] at h ⊢
    rintro ⟨x, u⟩ hx
    have hx_dom : x ∈ ((γ : ℝ) • A).dom := by
      rcases (mem_dom_iff _ _).1 hx.1 with ⟨v, hv⟩
      exact (mem_dom_iff _ _).2 ⟨(γ : ℝ) • v, Set.smul_mem_smul_set hv⟩
    have hu_range : (γ : ℝ) • u ∈ ((γ : ℝ) • A).range := by
      rcases (mem_range_iff _ _).1 hx.2 with ⟨y, hy⟩
      exact (mem_range_iff _ _).2 ⟨y, Set.smul_mem_smul_set hy⟩
    have hscaled_mem : (x, (γ : ℝ) • u) ∈ ((γ : ℝ) • A).dom ×ˢ ((γ : ℝ) • A).range :=
      ⟨hx_dom, hu_range⟩
    rw [ERealFunction.mem_dom_iff_ne_top]
    have hscaled :
        (((γ : ℝ) : EReal) * F[A] (x, u)) ≠ ⊤ := by
      simpa [fitzpatrickFunction_smul_apply A, inv_smul_smul₀ hγ_ne] using
        (ERealFunction.mem_dom_iff_ne_top _ _).1 (h hscaled_mem)
    intro htop
    exact hscaled <| by rw [htop, EReal.coe_mul_top_of_pos γ.2]

end SetValuedOperator
