import Mathlib
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap01.Text_1_0_16
import BauschkeLean.Chap23.Proposition_23_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise SetValuedOperator
open ERealFunction
open SetValuedOperator

universe u

-- Owner triage:
-- * `source-facing`: the one-step forward-backward inclusion from Remark 26.15.
-- * `core/canonical`: the Chapter 23 resolvent owner `J[...]` together with the singleton-valued
--   operator owner `id.toSetValuedOperator`.
-- * `bridge/view`: Proposition 23.2 rewrites membership in `J[γ • A]` as the residual inclusion
--   in `γ • A`.
-- The source-facing `Id + γ A` inclusion is therefore proved by passing through the canonical
-- resolvent owner `J[γ • A] = (Id + γ A)⁻¹` and then normalizing the affine term.

section

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- Remark 26.15: for `λₙ = 1`, the forward-backward update with step `γ` can be written in the
affine resolvent form
`x_n - γ • B x_n ∈ x_{n+1} + γ A x_{n+1}`, equivalently
`x_n - γ • B x_n ∈ (Id + γ A) x_{n+1}`, where `Id` is the canonical singleton-valued operator;
equivalently, the discrete residual
satisfies `-γ⁻¹ • (x_{n+1} - x_n) ∈ A x_{n+1} + {B x_n}`. This is the discrete analogue of the
continuous-time inclusion `-x'(t) ∈ A (x(t)) + B (x(t))`, with a forward Euler step for `B` and
a backward Euler step for `A`. -/
theorem forward_backward_step_iff_discrete_residual_mem
    (A : SetValuedOperator H H) (B : H → H) (γ : PosReal)
    (x_n x_np1 : H) :
    x_n - (γ : ℝ) • B x_n ∈ ({x_np1} : Set H) + (γ : ℝ) • A x_np1 ↔
      -((γ : ℝ)⁻¹) • (x_np1 - x_n) ∈ A x_np1 + ({B x_n} : Set H) := by
  have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
  calc
    x_n - (γ : ℝ) • B x_n ∈ ({x_np1} : Set H) + (γ : ℝ) • A x_np1
        ↔ x_np1 ∈ J[((γ : ℝ) • A)] (x_n - (γ : ℝ) • B x_n) := by
          simp only [mem_resolvent_smul_iff_mem_singleton_add_smul]
    _ ↔ (x_n - (γ : ℝ) • B x_n) - x_np1 ∈ (γ : ℝ) • A x_np1 := by
          simpa using
            (mem_resolvent_smul_iff_sub_mem_smul A γ
              (x_n - (γ : ℝ) • B x_n) x_np1)
    _ ↔ -((γ : ℝ)⁻¹) • (x_np1 - x_n) ∈ A x_np1 + ({B x_n} : Set H) := by
          constructor
          · intro hx
            rcases Set.mem_smul_set.mp hx with ⟨a, ha, hEq⟩
            refine Set.mem_add.2 ⟨a, ha, B x_n, by simp, ?_⟩
            calc
              a + B x_n = (γ : ℝ)⁻¹ • ((γ : ℝ) • a + (γ : ℝ) • B x_n) := by
                rw [smul_add, inv_smul_smul₀ hγ_ne, inv_smul_smul₀ hγ_ne]
              _ = (γ : ℝ)⁻¹ • (x_n - x_np1) := by
                congr 1
                calc
                  (γ : ℝ) • a + (γ : ℝ) • B x_n
                      = ((x_n - (γ : ℝ) • B x_n) - x_np1) + (γ : ℝ) • B x_n := by
                          rw [hEq]
                  _ = x_n - x_np1 := by
                        abel_nf
              _ = -((γ : ℝ)⁻¹) • (x_np1 - x_n) := by
                calc
                  (γ : ℝ)⁻¹ • (x_n - x_np1) = (γ : ℝ)⁻¹ • (-(x_np1 - x_n)) := by
                    congr 1
                    abel_nf
                  _ = -((γ : ℝ)⁻¹ • (x_np1 - x_n)) := by
                    rw [smul_neg]
                  _ = -((γ : ℝ)⁻¹) • (x_np1 - x_n) := by
                    rw [← neg_smul]
          · intro hx
            rcases Set.mem_add.mp hx with ⟨a, ha, b, hb, hEq⟩
            rw [Set.mem_singleton_iff] at hb
            subst b
            refine Set.mem_smul_set.mpr ⟨a, ha, ?_⟩
            have hsum : (γ : ℝ) • a + (γ : ℝ) • B x_n = x_n - x_np1 := by
              calc
                (γ : ℝ) • a + (γ : ℝ) • B x_n = (γ : ℝ) • (a + B x_n) := by
                  rw [smul_add]
                _ = (γ : ℝ) • (-((γ : ℝ)⁻¹) • (x_np1 - x_n)) := by
                  rw [hEq]
                _ = -(x_np1 - x_n) := by
                  calc
                    (γ : ℝ) • (-((γ : ℝ)⁻¹) • (x_np1 - x_n))
                        = (((γ : ℝ) * (-(γ : ℝ)⁻¹)) : ℝ) • (x_np1 - x_n) := by
                            rw [smul_smul]
                    _ = -((((γ : ℝ) * (γ : ℝ)⁻¹) : ℝ) • (x_np1 - x_n)) := by
                          rw [mul_neg, neg_smul]
                    _ = -(x_np1 - x_n) := by
                          rw [mul_inv_cancel₀ hγ_ne, one_smul]
                _ = x_n - x_np1 := by
                  abel_nf
            calc
              (γ : ℝ) • a = ((γ : ℝ) • a + (γ : ℝ) • B x_n) - (γ : ℝ) • B x_n := by
                abel_nf
              _ = (x_n - x_np1) - (γ : ℝ) • B x_n := by
                rw [hsum]
              _ = (x_n - (γ : ℝ) • B x_n) - x_np1 := by
                abel_nf

end
