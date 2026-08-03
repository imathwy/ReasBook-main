import Mathlib
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.Corollary_12_31
import BauschkeLean.Chap12.Example_12_25
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap14.Remark_14_4
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap16.Example_16_13
import BauschkeLean.Chap17.Theorem_17_18
import BauschkeLean.Chap23.Definition_23_1
import BauschkeLean.Chap23.Example_23_3

open scoped InnerProductSpace Pointwise Set SetValuedOperator
open ERealFunction SetValuedOperator

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (γ : PosReal)

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

local notation "P_C" => P[C, hC_cheb]

local notation "σ_C" =>
  properIoi (σ[C]) (isProper_supportFunction_of_nonempty C hC_nonempty)

local notation "hι_C" =>
  indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

local notation "hσ_C" =>
  properIoi_mem_gammaZero_of_mem_gamma
    (isProper_supportFunction_of_nonempty C hC_nonempty)
    (supportFunction_mem_gamma_local C)

private theorem conjugate_indicator_proximityOperator_eq_supportFunction_proximityOperator :
    Prox⋆[ι[C], hι_C] = Prox[σ_C, hσ_C] := by
  have hconj : ι[C]∗[hι_C] = σ_C := by
    funext u
    apply Subtype.ext
    change ((ι[C]∗[hι_C] u : EReal)) = (σ_C u : EReal)
    rw [gammaZeroConjugate_apply, conjugate_indicator_eq_supportFunction]
  funext x
  apply eq_proximityOperator_of_isProxPoint σ_C (hasUniqueProxPoint_of_mem_gammaZero σ_C hσ_C)
  simpa [hconj] using
    (proximityOperator_isProxPoint (ι[C]∗[hι_C])
      (hasUniqueProxPoint_of_mem_gammaZero
        (ι[C]∗[hι_C]) (gammaZeroConjugate_mem_gammaZero hι_C))
      x)

/-- Companion bridge for Example 23.4: for a nonempty closed convex subset `C` of a real Hilbert
space and `γ ∈ ℝ_{++}`, the metric projection `P_C` is the resolvent of the scaled normal cone
`γ N[C]`. -/
theorem
    projectionPoint_toSetValuedOperator_eq_resolvent_smul_normalCone_of_nonempty_isClosed_convex :
    (P_C).toSetValuedOperator = J[((γ : ℝ) • N[C])] := by
  have hsmul_indicator : γ • ι[C] = ι[C] := by
    funext x
    apply Subtype.ext
    by_cases hx : x ∈ C
    · simp [ERealFunction.indicator, hx]
    · simpa [ERealFunction.indicator, hx] using
        (EReal.coe_mul_top_of_pos γ.2 : ((γ : ℝ) : EReal) * ⊤ = ⊤)
  have hprox : Prox[γ, ι[C], hι_C] = P_C := by
    change Prox[γ • ι[C], smul_mem_gammaZero (ι[C]) hι_C γ] = P_C
    ext y
    simpa [hsmul_indicator] using
      congrArg (fun f : H → H ↦ f y) <|
        proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex
  calc
    (P_C).toSetValuedOperator =
        (Prox[γ, ι[C], hι_C]).toSetValuedOperator := by
      rw [← hprox]
    _ = J[((γ : ℝ) • (∂ ι[C] : SetValuedOperator H H))] := by
      simpa using
        (resolvent_subdifferential_eq_scaledProximityOperator (ι[C]) hι_C γ).symm
    _ = J[((γ : ℝ) • N[C])] := by
      rw [subdifferential_setIndicator_eq_normalCone C hC_nonempty]

/-- Example 23.4 (1) on the Chapter 23 resolvent surface: for a nonempty closed convex subset
`C` of a real Hilbert space, the resolvent `J[N[C]]` is the singleton-valued operator induced by
the metric projection `P_C`. -/
theorem projectionPoint_toSetValuedOperator_eq_resolvent_normalCone_of_nonempty_isClosed_convex :
    (P_C).toSetValuedOperator = J[N[C]] := by
  simpa using
    (projectionPoint_toSetValuedOperator_eq_resolvent_smul_normalCone_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex (1 : PosReal))

/-- Example 23.4 (1): for a nonempty closed convex subset `C` of a real Hilbert space, the
inverse of `Id + N[C]` is the singleton-valued operator induced by the metric projection `P_C`. -/
theorem
    projectionPoint_toSetValuedOperator_eq_inverse_id_add_normalCone_of_nonempty_isClosed_convex :
    (P_C).toSetValuedOperator = ((id : H → H).toSetValuedOperator + N[C])⁻¹ := by
  simpa [resolvent_def] using
    projectionPoint_toSetValuedOperator_eq_resolvent_normalCone_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex

/-- Example 23.4 (2): for a nonempty closed convex subset `C` of a real Hilbert space, the metric
projection `P_C` is `Id - Prox_{σ_C}`. -/
theorem projectionPoint_eq_id_sub_proximityOperator_supportFunction_of_nonempty_isClosed_convex :
    P_C = id - Prox[σ_C, hσ_C] := by
  funext x
  have hproj : Prox[ι[C], hι_C] x = P_C x := by
    exact congrFun
      (proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex) x
  have hres :
      Prox⋆[ι[C], hι_C] x = x - P_C x := by
    calc
      Prox⋆[ι[C], hι_C] x = x - Prox[ι[C], hι_C] x := by
        simpa using conjugate_proximityOperator_eq_sub_proximityOperator (ι[C]) hι_C x
      _ = x - P_C x := by rw [hproj]
  calc
    P_C x = x - Prox⋆[ι[C], hι_C] x := by
      rw [hres]
      abel_nf
    _ = id x - Prox[σ_C, hσ_C] x := by
      rw [conjugate_indicator_proximityOperator_eq_supportFunction_proximityOperator
        hC_nonempty hC_closed hC_convex]
      simp

include hC_closed hC_convex

/-- Example 23.4 (3) on the Chapter 23 Yosida surface: for a nonempty closed convex subset `C`
of a real Hilbert space and `γ ∈ ℝ_{++}`, the Yosida approximation `{}^[γ] N[C]` is the
singleton-valued operator induced by the scaled proximal map `γ⁻¹ Prox_{σ_C}`. -/
theorem
    yosidaApproximation_normalCone_eq_scaled_prox_supportFunction_of_nonempty_isClosed_convex
    :
    {}^[γ] N[C] =
      (fun x : H ↦ (γ : ℝ)⁻¹ • Prox[σ_C, hσ_C] x).toSetValuedOperator := by
  ext x
  rw [yosidaApproximation_apply,
    ← projectionPoint_toSetValuedOperator_eq_resolvent_smul_normalCone_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex γ,
    Function.toSetValuedOperator_apply]
  have hproj :
      P_C x =
        x - Prox[σ_C, hσ_C] x := by
    simpa using congrFun
      (projectionPoint_eq_id_sub_proximityOperator_supportFunction_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex) x
  simp [hproj]

/-- Companion bridge for Example 23.4 (3): after identifying the canonical Yosida approximation
`{}^[γ] N[C]`, the corresponding singleton-valued realization is the scaled projection residual
`γ⁻¹ (Id - P_C)`, which equals the scaled proximal map `γ⁻¹ Prox_{σ_C}`. -/
theorem
    projectionResidual_eq_scaled_prox_supportFunction_of_nonempty_isClosed_convex
    :
    (fun x : H ↦ (γ : ℝ)⁻¹ • (x - P_C x)) =
      fun x : H ↦ (γ : ℝ)⁻¹ • Prox[σ_C, hσ_C] x := by
  funext x
  have hproj :
      P_C x = x - Prox[σ_C, hσ_C] x := by
    simpa using congrFun
      (projectionPoint_eq_id_sub_proximityOperator_supportFunction_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex) x
  rw [hproj]
  abel_nf

end
