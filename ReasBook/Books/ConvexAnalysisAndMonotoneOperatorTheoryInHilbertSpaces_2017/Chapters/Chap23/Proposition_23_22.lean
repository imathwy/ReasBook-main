import BauschkeLean.Chap20.Definition_20_1
import BauschkeLean.Chap23.Definition_23_1
import BauschkeLean.Chap23.Proposition_23_2

-- Semantic recall note: `lean_leansearch` surfaced only the unrelated algebra-spectrum resolvent
-- API, so this item follows the verified local Chapter 23 owners
-- `mem_resolvent_smul_iff_mem_graph`, `mem_yosidaApproximation_iff_mem_graph`, `J[...]`,
-- `yosidaApproximation`, and `gra`.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- For a monotone operator, every nonempty resolvent value `J[((γ : ℝ) • A)] x` is already a
singleton. -/
theorem resolvent_smul_eq_singleton_of_mem
    {A : SetValuedOperator H H} (hA : A.IsMonotone) (γ : PosReal) {x y : H}
    (hy : y ∈ J[((γ : ℝ) • A)] x) :
    J[((γ : ℝ) • A)] x = ({y} : Set H) := by
  ext z
  constructor
  · intro hz
    have hy_graph := (mem_resolvent_smul_iff_mem_graph A γ x y).1 hy
    have hz_graph := (mem_resolvent_smul_iff_mem_graph A γ x z).1 hz
    have hyA : (((γ : ℝ)⁻¹ : ℝ) • (x - y)) ∈ A y := by
      simpa [SetValuedOperator.mem_graph] using hy_graph
    have hzA : (((γ : ℝ)⁻¹ : ℝ) • (x - z)) ∈ A z := by
      simpa [SetValuedOperator.mem_graph] using hz_graph
    have hdiff : x - y - (x - z) = -(y - z) := by
      abel_nf
    have hscaled :
        (((γ : ℝ)⁻¹ : ℝ) • (x - y)) - (((γ : ℝ)⁻¹ : ℝ) • (x - z)) =
          (((γ : ℝ)⁻¹ : ℝ) • (-(y - z))) := by
      calc
        (((γ : ℝ)⁻¹ : ℝ) • (x - y)) - (((γ : ℝ)⁻¹ : ℝ) • (x - z))
            = (((γ : ℝ)⁻¹ : ℝ) • ((x - y) - (x - z))) := by
                rw [← smul_sub]
        _ = (((γ : ℝ)⁻¹ : ℝ) • (-(y - z))) := by
              rw [hdiff]
    have hmono := (isMonotone_iff A).1 hA hyA hzA
    have hmono' := hmono
    simp only [hscaled, real_inner_smul_right, inner_neg_right,
      real_inner_self_eq_norm_sq] at hmono'
    have hγ : 0 < (γ : ℝ)⁻¹ := inv_pos.mpr γ.2
    have hyz_norm : ‖y - z‖ = 0 := by
      by_contra hne
      have hsq_pos : 0 < ‖y - z‖ ^ 2 := sq_pos_iff.mpr hne
      have hsq_neg : -(‖y - z‖ ^ 2) < 0 := by
        linarith
      have hneg : (γ : ℝ)⁻¹ * -(‖y - z‖ ^ 2) < 0 :=
        mul_neg_of_pos_of_neg hγ hsq_neg
      linarith
    rw [Set.mem_singleton_iff]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hyz_norm)).symm
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    cases hz
    simpa using hy

/-- For a monotone operator, every nonempty Yosida value `({}^[γ] A) x` is already a singleton. -/
theorem yosidaApproximation_eq_singleton_of_mem
    {A : SetValuedOperator H H} (hA : A.IsMonotone) (γ : PosReal) {x v : H}
    (hv : v ∈ ({}^[γ]A) x) :
    ({}^[γ]A) x = ({v} : Set H) := by
  ext w
  constructor
  · intro hw
    have hv_graph := (mem_yosidaApproximation_iff_mem_graph A γ x v).1 hv
    have hw_graph := (mem_yosidaApproximation_iff_mem_graph A γ x w).1 hw
    have hvA : v ∈ A (x - (γ : ℝ) • v) := by
      simpa [SetValuedOperator.mem_graph] using hv_graph
    have hwA : w ∈ A (x - (γ : ℝ) • w) := by
      simpa [SetValuedOperator.mem_graph] using hw_graph
    have hdiff : (x - (γ : ℝ) • v) - (x - (γ : ℝ) • w) = -((γ : ℝ) • (v - w)) := by
      calc
        (x - (γ : ℝ) • v) - (x - (γ : ℝ) • w) = (γ : ℝ) • w - (γ : ℝ) • v := by
          abel_nf
        _ = -((γ : ℝ) • (v - w)) := by
          rw [smul_sub]
          abel_nf
    have hmono := (isMonotone_iff A).1 hA hvA hwA
    have hmono' := hmono
    simp only [hdiff, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hmono'
    have hvw_norm : ‖v - w‖ = 0 := by
      by_contra hne
      have hsq_pos : 0 < ‖v - w‖ ^ 2 := sq_pos_iff.mpr hne
      have hsq_neg : -(‖v - w‖ ^ 2) < 0 := by
        linarith
      have hmul_pos : 0 < (γ : ℝ) * ‖v - w‖ ^ 2 := mul_pos γ.2 hsq_pos
      have hneg : -((γ : ℝ) * ‖v - w‖ ^ 2) < 0 := by
        linarith
      linarith
    rw [Set.mem_singleton_iff]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hvw_norm)).symm
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    cases hw
    simpa using hv

/-- Proposition 23.22: for a monotone operator `A`, the resolvent value `J[γ • A] x`
and the Yosida value `({}^[γ] A) x` are the singleton values `{y}` and `{v}` exactly
when `(y, v) ∈ gra A` and `x = y + γ • v`. -/
theorem resolvent_yosida_eq_singletons_iff
    {A : SetValuedOperator H H} (hA : A.IsMonotone) (γ : PosReal)
    (x y v : H) :
    (J[((γ : ℝ) • A)] x = ({y} : Set H) ∧ ({}^[γ] A) x = ({v} : Set H)) ↔
      (y, v) ∈ gra A ∧ x = y + (γ : ℝ) • v := by
  constructor
  · rintro ⟨hy, hv⟩
    have hy_mem : y ∈ J[((γ : ℝ) • A)] x := by
      rw [hy]
      simp
    have hv_mem : v ∈ ({}^[γ] A) x := by
      rw [hv]
      simp
    have hy_graph := (mem_resolvent_smul_iff_mem_graph A γ x y).1 hy_mem
    have hbase :
        x - (γ : ℝ) • (((γ : ℝ)⁻¹ : ℝ) • (x - y)) = y := by
      calc
        x - (γ : ℝ) • (((γ : ℝ)⁻¹ : ℝ) • (x - y)) = x - (((γ : ℝ) * ((γ : ℝ)⁻¹)) • (x - y)) := by
          rw [smul_smul]
        _ = x - (x - y) := by
          rw [mul_inv_cancel₀ γ.2.ne', one_smul]
        _ = y := by
          abel_nf
    have hresidual_mem : (γ : ℝ)⁻¹ • (x - y) ∈ ({}^[γ] A) x := by
      refine (mem_yosidaApproximation_iff_mem_graph A γ x _).2 ?_
      simpa [hbase] using hy_graph
    have hresidual_eq : (γ : ℝ)⁻¹ • (x - y) = v := by
      rw [hv] at hresidual_mem
      simpa [Set.mem_singleton_iff] using hresidual_mem
    constructor
    · simpa [hresidual_eq] using hy_graph
    · calc
        x = y + (γ : ℝ) • (((γ : ℝ)⁻¹ : ℝ) • (x - y)) := by
          rw [smul_smul, mul_inv_cancel₀ γ.2.ne', one_smul]
          abel_nf
        _ = y + (γ : ℝ) • v := by
          rw [hresidual_eq]
  · rintro ⟨hyv, hx⟩
    have hresidual_eq : (γ : ℝ)⁻¹ • (x - y) = v := by
      calc
        (γ : ℝ)⁻¹ • (x - y) = (γ : ℝ)⁻¹ • ((γ : ℝ) • v) := by
          congr 1
          calc
            x - y = (y + (γ : ℝ) • v) - y := by
              rw [hx]
            _ = (γ : ℝ) • v := by
              abel_nf
        _ = v := by
          rw [smul_smul, inv_mul_cancel₀ γ.2.ne', one_smul]
    have hy_mem : y ∈ J[((γ : ℝ) • A)] x := by
      refine (mem_resolvent_smul_iff_mem_graph A γ x y).2 ?_
      simpa [hresidual_eq] using hyv
    have hbase_eq : x - (γ : ℝ) • v = y := by
      calc
        x - (γ : ℝ) • v = (y + (γ : ℝ) • v) - (γ : ℝ) • v := by
          rw [hx]
        _ = y := by
          abel_nf
    have hv_mem : v ∈ ({}^[γ] A) x := by
      refine (mem_yosidaApproximation_iff_mem_graph A γ x v).2 ?_
      simpa [hbase_eq] using hyv
    exact ⟨resolvent_smul_eq_singleton_of_mem hA γ hy_mem,
      yosidaApproximation_eq_singleton_of_mem hA γ hv_mem⟩

end SetValuedOperator
