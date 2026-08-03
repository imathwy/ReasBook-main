import Mathlib
import BauschkeLean.Chap01.Definition_1_7
import BauschkeLean.Chap07.Exercise_7_1
import BauschkeLean.Chap07.Proposition_7_11
import BauschkeLean.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

namespace ERealFunction

section RealLine

variable (Ω : Set ℝ) (hΩ : Ω.Nonempty)

include hΩ

omit hΩ in
/-- Helper for Example 16 14: on `ℝ`, the support function is the supremum of the image of `Ω`
under the corresponding linear functional. -/
private theorem supportFunction_eq_sSup_image (C : Set ℝ) (ξ : ℝ) :
    σ[C] ξ = sSup ((fun x : ℝ ↦ (⟪x, ξ⟫_ℝ : EReal)) '' C) := by
  rw [supportFunctionEReal_eq_sSup_image]

omit hΩ in
/-- Helper for Example 16 14: the support function of a nonempty subset of `ℝ` vanishes at the
origin. -/
private theorem supportFunction_zero_eq_zero_of_nonempty (C : Set ℝ) (hC_nonempty : C.Nonempty) :
    σ[C] (0 : ℝ) = 0 := by
  rw [supportFunction_eq_sSup_image]
  rcases hC_nonempty with ⟨x, hx⟩
  have himage :
      (fun y : ℝ ↦ (⟪y, (0 : ℝ)⟫_ℝ : EReal)) '' C = ({0} : Set EReal) := by
    ext t
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp
    · intro ht
      simp at ht
      refine ⟨x, hx, ?_⟩
      simp [ht]
  rw [himage]
  simp

omit hΩ in
/-- Helper for Example 16 14: the support function of a nonempty subset of `ℝ` is never `⊥`. -/
private theorem bot_lt_supportFunction_of_nonempty (C : Set ℝ) (hC_nonempty : C.Nonempty)
    (ξ : ℝ) : (⊥ : EReal) < σ[C] ξ := by
  rcases hC_nonempty with ⟨x, hx⟩
  rw [supportFunction_eq_sSup_image]
  exact lt_of_lt_of_le (EReal.bot_lt_coe _) <| (isLUB_sSup _).1 ⟨x, hx, rfl⟩

omit hΩ in
/-- Helper for Example 16 14: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul (x y : ℝ) : ⟪x, y⟫_ℝ = x * y := by
  calc
    ⟪x, y⟫_ℝ = (starRingEnd ℝ) x * y := RCLike.inner_apply' x y
    _ = x * y := by simp

omit hΩ in
/-- Helper for Example 16 14: once the support value at `ξ` is `ξ * x`, the affine contact term
in the subdifferential inequality at test point `y` collapses to `y * x`. -/
private theorem affine_contact_term_eq_mul (x ξ y : ℝ) :
    (⟪y - ξ, x⟫_ℝ : EReal) + ((ξ * x : ℝ) : EReal) = ((y * x : ℝ) : EReal) := by
  -- Rewrite the real inner product as multiplication and then cancel the affine terms.
  rw [real_inner_eq_mul, ← EReal.coe_add]
  exact_mod_cast (by ring : (y - ξ) * x + ξ * x = y * x)

omit hΩ in
/-- Helper for Example 16 14: multiplication by a positive real scalar preserves suprema in
`EReal`. -/
private theorem ereal_pos_mul_sSup (S : Set EReal) {γ : ℝ} (hγ : 0 < γ) :
    sSup ((fun t : EReal ↦ (γ : EReal) * t) '' S) = (γ : EReal) * sSup S := by
  simpa using (_root_.ereal_pos_mul_sSup S hγ)

omit hΩ in
/-- Helper for Example 16 14: the support function is positively homogeneous on the real line. -/
private theorem supportFunction_pos_mul (C : Set ℝ) {γ ξ : ℝ} (hγ : 0 < γ) :
    σ[C] (γ * ξ) = (γ : EReal) * σ[C] ξ := by
  have hcomp := congrArg (fun f : ℝ → EReal ↦ f ξ)
    (_root_.supportFunction_comp_pos_smul_eq_mul_supportFunction C hγ)
  simpa [Function.comp, smul_eq_mul] using hcomp

omit hΩ in
/-- Helper for Example 16 14: a point on the lower-endpoint slice is a lower bound for `Ω`. -/
private theorem lower_bound_of_mem_lower_endpoint_slice {x y : ℝ}
    (hx : (x : EReal) = sInf (Real.toEReal '' Ω)) (hy : y ∈ Ω) :
    x ≤ y := by
  have hyInf : sInf (Real.toEReal '' Ω) ≤ (y : EReal) :=
    (isGLB_sInf_image Real.toEReal Ω).1 (Set.mem_image_of_mem Real.toEReal hy)
  rw [← hx] at hyInf
  exact EReal.coe_le_coe_iff.mp hyInf

omit hΩ in
/-- Helper for Example 16 14: a point on the upper-endpoint slice is an upper bound for `Ω`. -/
private theorem upper_bound_of_mem_upper_endpoint_slice {x y : ℝ}
    (hx : (x : EReal) = sSup (Real.toEReal '' Ω)) (hy : y ∈ Ω) :
    y ≤ x := by
  have hySup : (y : EReal) ≤ sSup (Real.toEReal '' Ω) :=
    (isLUB_sSup_image Real.toEReal Ω).1 (Set.mem_image_of_mem Real.toEReal hy)
  rw [← hx] at hySup
  exact EReal.coe_le_coe_iff.mp hySup

/-- Helper for Example 16 14: the lower-endpoint slice is characterized by being the greatest real
lower bound of `Ω`. -/
private theorem eq_sInf_image_of_isGreatestLowerBound {x : ℝ}
    (hlower : ∀ y ∈ Ω, x ≤ y)
    (hgreatest : ∀ z : ℝ, (∀ y ∈ Ω, z ≤ y) → z ≤ x) :
    (x : EReal) = sInf (Real.toEReal '' Ω) := by
  apply le_antisymm
  · exact (isGLB_sInf_image Real.toEReal Ω).2 <| by
      rintro _ ⟨y, hy, rfl⟩
      exact_mod_cast hlower y hy
  · rw [← sSup_lowerBounds_eq_sInf]
    refine sSup_le ?_
    intro z hz
    have hz_top : z ≠ ⊤ := by
      rcases hΩ with ⟨y, hy⟩
      have hzy : z ≤ (y : EReal) := hz (Set.mem_image_of_mem Real.toEReal hy)
      intro hz'
      rw [hz'] at hzy
      exact not_le_of_gt (EReal.coe_lt_top (x := y)) hzy
    by_cases hz_bot : z = ⊥
    · simp [hz_bot]
    · have hz_eq : ((z.toReal : ℝ) : EReal) = z := EReal.coe_toReal hz_top hz_bot
      have hzreal : ∀ y ∈ Ω, z.toReal ≤ y := by
        intro y hy
        have hzy : z ≤ (y : EReal) := hz (Set.mem_image_of_mem Real.toEReal hy)
        rw [← hz_eq] at hzy
        exact EReal.coe_le_coe_iff.mp hzy
      rw [← hz_eq]
      exact_mod_cast hgreatest z.toReal hzreal

/-- Helper for Example 16 14: the upper-endpoint slice is characterized by being the least real
upper bound of `Ω`. -/
private theorem eq_sSup_image_of_isLeastUpperBound {x : ℝ}
    (hupper : ∀ y ∈ Ω, y ≤ x)
    (hleast : ∀ z : ℝ, (∀ y ∈ Ω, y ≤ z) → x ≤ z) :
    (x : EReal) = sSup (Real.toEReal '' Ω) := by
  apply le_antisymm
  · rw [← sInf_upperBounds_eq_sSup]
    refine le_sInf ?_
    intro z hz
    have hz_bot : z ≠ ⊥ := by
      rcases hΩ with ⟨y, hy⟩
      have hyz : (y : EReal) ≤ z := hz (Set.mem_image_of_mem Real.toEReal hy)
      intro hz'
      rw [hz'] at hyz
      exact not_le_of_gt (EReal.bot_lt_coe y) hyz
    by_cases hz_top : z = ⊤
    · simp [hz_top]
    · have hz_eq : ((z.toReal : ℝ) : EReal) = z := EReal.coe_toReal hz_top hz_bot
      have hzreal : ∀ y ∈ Ω, y ≤ z.toReal := by
        intro y hy
        have hyz : (y : EReal) ≤ z := hz (Set.mem_image_of_mem Real.toEReal hy)
        rw [← hz_eq] at hyz
        exact EReal.coe_le_coe_iff.mp hyz
      rw [← hz_eq]
      exact_mod_cast hleast z.toReal hzreal
  · exact (isLUB_sSup_image Real.toEReal Ω).2 <| by
      rintro _ ⟨y, hy, rfl⟩
      exact_mod_cast hupper y hy

omit hΩ in
/-- Helper for Example 16 14: if `x` is the lower endpoint, then points of `Ω` occur arbitrarily
close above `x`. -/
private theorem exists_mem_lt_add_of_mem_lower_endpoint_slice {x ε : ℝ}
    (hx : (x : EReal) = sInf (Real.toEReal '' Ω)) (hε : 0 < ε) :
    ∃ y ∈ Ω, y < x + ε := by
  by_contra h
  have hbound : ∀ y ∈ Ω, x + ε ≤ y := by
    intro y hy
    by_contra hy'
    exact h ⟨y, hy, not_le.mp hy'⟩
  have hle : ((x + ε : ℝ) : EReal) ≤ sInf (Real.toEReal '' Ω) :=
    (isGLB_sInf_image Real.toEReal Ω).2 <| by
      rintro _ ⟨y, hy, rfl⟩
      exact_mod_cast hbound y hy
  rw [← hx] at hle
  have hreal : x + ε ≤ x := EReal.coe_le_coe_iff.mp hle
  linarith

omit hΩ in
/-- Helper for Example 16 14: if `x` is the upper endpoint, then points of `Ω` occur arbitrarily
close below `x`. -/
private theorem exists_mem_sub_lt_of_mem_upper_endpoint_slice {x ε : ℝ}
    (hx : (x : EReal) = sSup (Real.toEReal '' Ω)) (hε : 0 < ε) :
    ∃ y ∈ Ω, x - ε < y := by
  by_contra h
  have hbound : ∀ y ∈ Ω, y ≤ x - ε := by
    intro y hy
    by_contra hy'
    exact h ⟨y, hy, not_le.mp hy'⟩
  have hle : sSup (Real.toEReal '' Ω) ≤ ((x - ε : ℝ) : EReal) :=
    (isLUB_sSup_image Real.toEReal Ω).2 <| by
      rintro _ ⟨y, hy, rfl⟩
      exact_mod_cast hbound y hy
  rw [← hx] at hle
  have hreal : x ≤ x - ε := EReal.coe_le_coe_iff.mp hle
  linarith

/-- Helper for Example 16 14: at a negative slope, the support value is the slope times the lower
endpoint whenever that endpoint is real. -/
private theorem supportFunction_eq_mul_of_mem_lower_endpoint_slice {x ξ : ℝ}
    (hξ : ξ < 0) (hx : (x : EReal) = sInf (Real.toEReal '' Ω)) :
    σ[Ω] ξ = ((ξ * x : ℝ) : EReal) := by
  have hupper : σ[Ω] ξ ≤ ((ξ * x : ℝ) : EReal) := by
    rw [supportFunction_eq_sSup_image]
    refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    have hxy : x ≤ y := lower_bound_of_mem_lower_endpoint_slice (Ω := Ω) hx hy
    have hmul : y * ξ ≤ ξ * x := by
      have hmul' : ξ * y ≤ ξ * x := mul_le_mul_of_nonpos_left hxy hξ.le
      simpa [mul_comm] using hmul'
    simpa [real_inner_eq_mul] using (show (((y * ξ : ℝ) : EReal) ≤ ((ξ * x : ℝ) : EReal) ) from
      by exact_mod_cast hmul)
  have hσ_bot : σ[Ω] ξ ≠ ⊥ := by
    exact ne_of_gt (bot_lt_supportFunction_of_nonempty Ω hΩ ξ)
  have hσ_top : σ[Ω] ξ ≠ ⊤ := by
    intro htop
    rw [htop] at hupper
    exact not_lt_of_ge hupper (EReal.coe_lt_top (x := ξ * x))
  have hlowerReal : ξ * x ≤ (σ[Ω] ξ).toReal := by
    refine le_iff_forall_pos_lt_add.2 ?_
    intro δ hδ
    have hratio : 0 < δ / (-ξ) := by
      exact div_pos hδ (neg_pos.mpr hξ)
    rcases exists_mem_lt_add_of_mem_lower_endpoint_slice (Ω := Ω) hx hratio with
      ⟨y, hy, hylt⟩
    have hyσ : (((ξ * y : ℝ) : EReal) ≤ σ[Ω] ξ) := by
      rw [supportFunction_eq_sSup_image]
      exact (isLUB_sSup _).1 ⟨y, hy, rfl⟩
    have hyσReal : ξ * y ≤ (σ[Ω] ξ).toReal := by
      rw [← EReal.coe_toReal hσ_top hσ_bot] at hyσ
      exact EReal.coe_le_coe_iff.mp hyσ
    have hstep : ξ * x < ξ * y + δ := by
      have hmul : ξ * (x + δ / (-ξ)) < ξ * y := by
        exact mul_lt_mul_of_neg_left hylt hξ
      have hrewrite : ξ * (x + δ / (-ξ)) = ξ * x - δ := by
        field_simp [hξ.ne]
        ring
      linarith
    linarith
  have hlower : ((ξ * x : ℝ) : EReal) ≤ σ[Ω] ξ := by
    rw [← EReal.coe_toReal hσ_top hσ_bot]
    exact_mod_cast hlowerReal
  exact le_antisymm hupper hlower

/-- Helper for Example 16 14: at a positive slope, the support value is the slope times the upper
endpoint whenever that endpoint is real. -/
private theorem supportFunction_eq_mul_of_mem_upper_endpoint_slice {x ξ : ℝ}
    (hξ : 0 < ξ) (hx : (x : EReal) = sSup (Real.toEReal '' Ω)) :
    σ[Ω] ξ = ((ξ * x : ℝ) : EReal) := by
  have hupper : σ[Ω] ξ ≤ ((ξ * x : ℝ) : EReal) := by
    rw [supportFunction_eq_sSup_image]
    refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    have hxy : y ≤ x := upper_bound_of_mem_upper_endpoint_slice (Ω := Ω) hx hy
    have hmul : y * ξ ≤ ξ * x := by
      have hmul' : ξ * y ≤ ξ * x := mul_le_mul_of_nonneg_left hxy hξ.le
      simpa [mul_comm] using hmul'
    simpa [real_inner_eq_mul] using (show (((y * ξ : ℝ) : EReal) ≤ ((ξ * x : ℝ) : EReal) ) from
      by exact_mod_cast hmul)
  have hσ_bot : σ[Ω] ξ ≠ ⊥ := by
    exact ne_of_gt (bot_lt_supportFunction_of_nonempty Ω hΩ ξ)
  have hσ_top : σ[Ω] ξ ≠ ⊤ := by
    intro htop
    rw [htop] at hupper
    exact not_lt_of_ge hupper (EReal.coe_lt_top (x := ξ * x))
  have hlowerReal : ξ * x ≤ (σ[Ω] ξ).toReal := by
    refine le_iff_forall_pos_lt_add.2 ?_
    intro δ hδ
    have hratio : 0 < δ / ξ := by
      exact div_pos hδ hξ
    rcases exists_mem_sub_lt_of_mem_upper_endpoint_slice (Ω := Ω) hx hratio with
      ⟨y, hy, hylt⟩
    have hyσ : (((ξ * y : ℝ) : EReal) ≤ σ[Ω] ξ) := by
      rw [supportFunction_eq_sSup_image]
      exact (isLUB_sSup _).1 ⟨y, hy, rfl⟩
    have hyσReal : ξ * y ≤ (σ[Ω] ξ).toReal := by
      rw [← EReal.coe_toReal hσ_top hσ_bot] at hyσ
      exact EReal.coe_le_coe_iff.mp hyσ
    have hstep : ξ * x < ξ * y + δ := by
      have hmul : ξ * (x - δ / ξ) < ξ * y := by
        exact mul_lt_mul_of_pos_left hylt hξ
      have hrewrite : ξ * (x - δ / ξ) = ξ * x - δ := by
        field_simp [hξ.ne']
      linarith
    linarith
  have hlower : ((ξ * x : ℝ) : EReal) ≤ σ[Ω] ξ := by
    rw [← EReal.coe_toReal hσ_top hσ_bot]
    exact_mod_cast hlowerReal
  exact le_antisymm hupper hlower

-- Proof sketch: for `ξ < 0`, the support function of `Ω` is the affine map `x ↦ ξ x` maximized at
-- the lower endpoint, so the only supporting slope is the infimum endpoint of `Ω` when that
-- endpoint is real.
/-- Example 16 14 (1): if `ξ < 0`, the subdifferential of the support function of a nonempty
subset `Ω ⊆ ℝ` is the real slice of the singleton containing the infimum endpoint of `Ω`. -/
theorem subdifferential_supportFunction_eq_lowerEndpoint_of_neg
    {ξ : ℝ} (hξ : ξ < 0) :
    (∂ σ[Ω]) ξ =
      {x : ℝ | (x : EReal) = sInf (Real.toEReal '' Ω)} := by
  ext x
  constructor
  · intro hx
    rw [mem_subdifferential_iff] at hx
    have hσ0 : σ[Ω] (0 : ℝ) = 0 :=
      supportFunction_zero_eq_zero_of_nonempty Ω hΩ
    have hσ_bot : σ[Ω] ξ ≠ ⊥ := by
      exact ne_of_gt (bot_lt_supportFunction_of_nonempty Ω hΩ ξ)
    have htest0 :
        (((-ξ * x : ℝ) : EReal) + σ[Ω] ξ ≤ 0) := by
      simpa [hσ0, real_inner_eq_mul, sub_eq_add_neg] using hx 0
    have hσ_top : σ[Ω] ξ ≠ ⊤ := by
      intro htop
      have hsumtop : (((-ξ * x : ℝ) : EReal) + (⊤ : EReal)) = (⊤ : EReal) := by
        simpa using EReal.coe_add_top (-ξ * x)
      have htest0' : (((-ξ * x : ℝ) : EReal) + (⊤ : EReal) ≤ 0) := by
        simpa [htop] using htest0
      rw [hsumtop] at htest0'
      have hcontra : (⊤ : EReal) ≤ 0 := htest0'
      have : ¬ ((⊤ : EReal) ≤ (0 : EReal)) := by simp
      exact this hcontra
    have hσle : σ[Ω] ξ ≤ ((ξ * x : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hσ_top hσ_bot, ← EReal.coe_add] at htest0
      have hreal : -ξ * x + (σ[Ω] ξ).toReal ≤ 0 := EReal.coe_le_coe_iff.mp htest0
      have hbound : (σ[Ω] ξ).toReal ≤ ξ * x := by
        linarith
      rw [← EReal.coe_toReal hσ_top hσ_bot]
      exact_mod_cast hbound
    have hhom :
        σ[Ω] (2 * ξ) = ((2 : ℝ) : EReal) * σ[Ω] ξ := by
      simpa using supportFunction_pos_mul (C := Ω) (γ := 2) (ξ := ξ) (by norm_num)
    have htest2 :
        (((ξ * x : ℝ) : EReal) + σ[Ω] ξ ≤ ((2 : ℝ) : EReal) * σ[Ω] ξ) := by
      have harg : (2 * ξ - ξ) * x = ξ * x := by
        ring
      simpa [hhom, real_inner_eq_mul, harg] using hx (2 * ξ)
    have hσge : ((ξ * x : ℝ) : EReal) ≤ σ[Ω] ξ := by
      rw [← EReal.coe_toReal hσ_top hσ_bot, ← EReal.coe_toReal hσ_top hσ_bot,
        ← EReal.coe_add, ← EReal.coe_mul] at htest2
      have hreal : ξ * x + (σ[Ω] ξ).toReal ≤ 2 * (σ[Ω] ξ).toReal :=
        EReal.coe_le_coe_iff.mp htest2
      have hbound : ξ * x ≤ (σ[Ω] ξ).toReal := by
        linarith
      rw [← EReal.coe_toReal hσ_top hσ_bot]
      exact_mod_cast hbound
    have hσeq : σ[Ω] ξ = ((ξ * x : ℝ) : EReal) := le_antisymm hσle hσge
    have hlower : ∀ y ∈ Ω, x ≤ y := by
      intro y hy
      have hyσ : (((ξ * y : ℝ) : EReal) ≤ σ[Ω] ξ) := by
        rw [supportFunction_eq_sSup_image]
        exact (isLUB_sSup _).1 ⟨y, hy, rfl⟩
      rw [hσeq] at hyσ
      have hreal : ξ * y ≤ ξ * x := EReal.coe_le_coe_iff.mp hyσ
      nlinarith
    have hgreatest : ∀ z : ℝ, (∀ y ∈ Ω, z ≤ y) → z ≤ x := by
      intro z hz
      have hzσ : σ[Ω] ξ ≤ ((ξ * z : ℝ) : EReal) := by
        rw [supportFunction_eq_sSup_image]
        refine sSup_le ?_
        rintro _ ⟨y, hy, rfl⟩
        have hreal : ξ * y ≤ ξ * z := by
          nlinarith [hz y hy]
        have hcast : (((ξ * y : ℝ) : EReal) ≤ ((ξ * z : ℝ) : EReal)) := by
          exact_mod_cast hreal
        simpa [real_inner_eq_mul, mul_comm] using hcast
      rw [hσeq] at hzσ
      have hreal : ξ * x ≤ ξ * z := EReal.coe_le_coe_iff.mp hzσ
      nlinarith
    exact eq_sInf_image_of_isGreatestLowerBound (Ω := Ω) hΩ hlower hgreatest
  · intro hx
    have hσeq :
        σ[Ω] ξ = ((ξ * x : ℝ) : EReal) :=
      supportFunction_eq_mul_of_mem_lower_endpoint_slice (Ω := Ω) hΩ hξ hx
    rw [mem_subdifferential_iff]
    intro y
    by_cases hy : y < 0
    · have hySupport :
          σ[Ω] y = ((y * x : ℝ) : EReal) :=
        supportFunction_eq_mul_of_mem_lower_endpoint_slice (Ω := Ω) hΩ hy hx
      -- The affine contact term collapses to the support value at the test slope `y`.
      rw [hσeq, hySupport, real_inner_eq_mul]
      simpa [real_inner_eq_mul] using (affine_contact_term_eq_mul x ξ y).le
    · rcases hΩ with ⟨z, hz⟩
      have hxz : x ≤ z := lower_bound_of_mem_lower_endpoint_slice (Ω := Ω) hx hz
      have hy' : 0 ≤ y := le_of_not_gt hy
      have hmul : y * x ≤ y * z := by
        exact mul_le_mul_of_nonneg_left hxz hy'
      have hzσ : (((y * z : ℝ) : EReal) ≤ σ[Ω] y) := by
        rw [supportFunction_eq_sSup_image]
        exact (isLUB_sSup _).1 ⟨z, hz, rfl⟩
      have hyx : (((y * x : ℝ) : EReal) ≤ σ[Ω] y) :=
        le_trans (by exact_mod_cast hmul) hzσ
      rw [hσeq, real_inner_eq_mul]
      have hsum_le :
          (((y - ξ) * x : ℝ) : EReal) + ((ξ * x : ℝ) : EReal) ≤ ((y * x : ℝ) : EReal) := by
        simpa [real_inner_eq_mul] using (affine_contact_term_eq_mul x ξ y).le
      exact hsum_le.trans hyx

-- Proof sketch: at `ξ = 0`, the support function is supported by every point of the closed convex
-- hull of `Ω`, and only those points satisfy the global affine minorization inequality defining the
-- subdifferential.
/-- Example 16 14 (2): at `0`, the subdifferential of the support function of a nonempty subset
`Ω ⊆ ℝ` is the closed convex hull of `Ω`. -/
theorem subdifferential_supportFunction_eq_closedConvexHull_at_zero
    : (∂ σ[Ω]) 0 = closedConvexHull ℝ Ω := by
  rw [closedConvexHull_eq_closure_convexHull,
    closure_convexHull_eq_iInter_supportFunctionHalfspace]
  ext x
  constructor
  · intro hx
    rw [Set.mem_iInter]
    intro u
    rw [mem_supportFunctionHalfspace_iff]
    rw [mem_subdifferential_iff] at hx
    have h := hx u
    rw [supportFunction_zero_eq_zero_of_nonempty Ω hΩ] at h
    change ((⟪u - 0, x⟫_ℝ : EReal) + (0 : EReal) ≤ σ[Ω] u) at h
    rw [add_zero] at h
    simpa [real_inner_eq_mul, mul_comm] using h
  · intro hx
    rw [mem_subdifferential_iff]
    intro u
    have hu : x ∈ supportFunctionHalfspace Ω u := by
      rw [Set.mem_iInter] at hx
      exact hx u
    have hxu : (((x : EReal) * (u : EReal)) ≤ σ[Ω] u) := by
      simpa [real_inner_eq_mul, mul_comm] using (mem_supportFunctionHalfspace_iff Ω u x).mp hu
    rw [supportFunction_zero_eq_zero_of_nonempty Ω hΩ]
    change ((⟪u - 0, x⟫_ℝ : EReal) + (0 : EReal) ≤ σ[Ω] u)
    rw [add_zero]
    simpa [real_inner_eq_mul, sub_eq_add_neg, mul_comm] using hxu

-- Proof sketch: for `ξ > 0`, the support function of `Ω` is the affine map `x ↦ ξ x` maximized at
-- the upper endpoint, so the only supporting slope is the supremum endpoint of `Ω` when that
-- endpoint is real.
/-- Example 16 14 (3): if `ξ > 0`, the subdifferential of the support function of a nonempty
subset `Ω ⊆ ℝ` is the real slice of the singleton containing the supremum endpoint of `Ω`. -/
theorem subdifferential_supportFunction_eq_upperEndpoint_of_pos
    {ξ : ℝ} (hξ : 0 < ξ) :
    (∂ σ[Ω]) ξ =
      {x : ℝ | (x : EReal) = sSup (Real.toEReal '' Ω)} := by
  ext x
  constructor
  · intro hx
    rw [mem_subdifferential_iff] at hx
    have hσ0 : σ[Ω] (0 : ℝ) = 0 :=
      supportFunction_zero_eq_zero_of_nonempty Ω hΩ
    have hσ_bot : σ[Ω] ξ ≠ ⊥ := by
      exact ne_of_gt (bot_lt_supportFunction_of_nonempty Ω hΩ ξ)
    have htest0 :
        (((-ξ * x : ℝ) : EReal) + σ[Ω] ξ ≤ 0) := by
      simpa [hσ0, real_inner_eq_mul, sub_eq_add_neg] using hx 0
    have hσ_top : σ[Ω] ξ ≠ ⊤ := by
      intro htop
      have hsumtop : (((-ξ * x : ℝ) : EReal) + (⊤ : EReal)) = (⊤ : EReal) := by
        simpa using EReal.coe_add_top (-ξ * x)
      have htest0' : (((-ξ * x : ℝ) : EReal) + (⊤ : EReal) ≤ 0) := by
        simpa [htop] using htest0
      rw [hsumtop] at htest0'
      have hcontra : (⊤ : EReal) ≤ 0 := htest0'
      have : ¬ ((⊤ : EReal) ≤ (0 : EReal)) := by simp
      exact this hcontra
    have hσle : σ[Ω] ξ ≤ ((ξ * x : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hσ_top hσ_bot, ← EReal.coe_add] at htest0
      have hreal : -ξ * x + (σ[Ω] ξ).toReal ≤ 0 := EReal.coe_le_coe_iff.mp htest0
      have hbound : (σ[Ω] ξ).toReal ≤ ξ * x := by
        linarith
      rw [← EReal.coe_toReal hσ_top hσ_bot]
      exact_mod_cast hbound
    have hhom :
        σ[Ω] (2 * ξ) = ((2 : ℝ) : EReal) * σ[Ω] ξ := by
      simpa using supportFunction_pos_mul (C := Ω) (γ := 2) (ξ := ξ) (by norm_num)
    have htest2 :
        (((ξ * x : ℝ) : EReal) + σ[Ω] ξ ≤ ((2 : ℝ) : EReal) * σ[Ω] ξ) := by
      have harg : (2 * ξ - ξ) * x = ξ * x := by
        ring
      simpa [hhom, real_inner_eq_mul, harg] using hx (2 * ξ)
    have hσge : ((ξ * x : ℝ) : EReal) ≤ σ[Ω] ξ := by
      rw [← EReal.coe_toReal hσ_top hσ_bot, ← EReal.coe_toReal hσ_top hσ_bot,
        ← EReal.coe_add, ← EReal.coe_mul] at htest2
      have hreal : ξ * x + (σ[Ω] ξ).toReal ≤ 2 * (σ[Ω] ξ).toReal :=
        EReal.coe_le_coe_iff.mp htest2
      have hbound : ξ * x ≤ (σ[Ω] ξ).toReal := by
        linarith
      rw [← EReal.coe_toReal hσ_top hσ_bot]
      exact_mod_cast hbound
    have hσeq : σ[Ω] ξ = ((ξ * x : ℝ) : EReal) := le_antisymm hσle hσge
    have hupper : ∀ y ∈ Ω, y ≤ x := by
      intro y hy
      have hyσ : (((ξ * y : ℝ) : EReal) ≤ σ[Ω] ξ) := by
        rw [supportFunction_eq_sSup_image]
        exact (isLUB_sSup _).1 ⟨y, hy, rfl⟩
      rw [hσeq] at hyσ
      have hreal : ξ * y ≤ ξ * x := EReal.coe_le_coe_iff.mp hyσ
      nlinarith
    have hleast : ∀ z : ℝ, (∀ y ∈ Ω, y ≤ z) → x ≤ z := by
      intro z hz
      have hzσ : σ[Ω] ξ ≤ ((ξ * z : ℝ) : EReal) := by
        rw [supportFunction_eq_sSup_image]
        refine sSup_le ?_
        rintro _ ⟨y, hy, rfl⟩
        have hreal : ξ * y ≤ ξ * z := by
          nlinarith [hz y hy]
        have hcast : (((ξ * y : ℝ) : EReal) ≤ ((ξ * z : ℝ) : EReal)) := by
          exact_mod_cast hreal
        simpa [real_inner_eq_mul, mul_comm] using hcast
      rw [hσeq] at hzσ
      have hreal : ξ * x ≤ ξ * z := EReal.coe_le_coe_iff.mp hzσ
      nlinarith
    exact eq_sSup_image_of_isLeastUpperBound (Ω := Ω) hΩ hupper hleast
  · intro hx
    have hσeq :
        σ[Ω] ξ = ((ξ * x : ℝ) : EReal) :=
      supportFunction_eq_mul_of_mem_upper_endpoint_slice (Ω := Ω) hΩ hξ hx
    rw [mem_subdifferential_iff]
    intro y
    by_cases hy : 0 < y
    · have hySupport :
          σ[Ω] y = ((y * x : ℝ) : EReal) :=
        supportFunction_eq_mul_of_mem_upper_endpoint_slice (Ω := Ω) hΩ hy hx
      -- The same affine-contact identity closes the positive-slope branch.
      rw [hσeq, hySupport, real_inner_eq_mul]
      simpa [real_inner_eq_mul] using (affine_contact_term_eq_mul x ξ y).le
    · rcases hΩ with ⟨z, hz⟩
      have hzx : z ≤ x := upper_bound_of_mem_upper_endpoint_slice (Ω := Ω) hx hz
      have hy' : y ≤ 0 := le_of_not_gt hy
      have hmul : y * x ≤ y * z := by
        exact mul_le_mul_of_nonpos_left hzx hy'
      have hzσ : (((y * z : ℝ) : EReal) ≤ σ[Ω] y) := by
        rw [supportFunction_eq_sSup_image]
        exact (isLUB_sSup _).1 ⟨z, hz, rfl⟩
      have hyx : (((y * x : ℝ) : EReal) ≤ σ[Ω] y) :=
        le_trans (by exact_mod_cast hmul) hzσ
      rw [hσeq, real_inner_eq_mul]
      have hsum_le :
          (((y - ξ) * x : ℝ) : EReal) + ((ξ * x : ℝ) : EReal) ≤ ((y * x : ℝ) : EReal) := by
        simpa [real_inner_eq_mul] using (affine_contact_term_eq_mul x ξ y).le
      exact hsum_le.trans hyx

omit hΩ

end RealLine

end ERealFunction
