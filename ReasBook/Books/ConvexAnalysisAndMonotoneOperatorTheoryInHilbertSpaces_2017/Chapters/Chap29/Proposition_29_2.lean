import BauschkeLean.Chap12.Corollary_12_31
import BauschkeLean.Chap12.Example_12_25
import BauschkeLean.Chap24.Proposition_24_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise
open ERealFunction

universe u v

section

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
variable {C : Set K}

/- Source/core/bridge triage:
- `source-facing`: Proposition 29.2 identifies the metric projection onto the preimage `L ⁻¹' C`.
- `core/canonical`: Proposition 24.14 already owns the proximal formula for `f ∘ L` under
  `L.comp L.adjoint = γ • Id`.
- `bridge/view`: this file specializes that owner to the indicator `ι[C]`, then rewrites the
  resulting proximal operators through the Chapter 12 projection owner `projectionPoint`. -/

private theorem preimage_nonempty_of_comp_adjoint_eq_smul_id
    (hC_nonempty : C.Nonempty) (L : H →L[ℝ] K) (γ : PosReal)
    (hscalar : L.comp L.adjoint = (γ : ℝ) • (1 : K →L[ℝ] K)) :
    (L ⁻¹' C).Nonempty := by
  rcases hC_nonempty with ⟨y, hy⟩
  refine ⟨(γ : ℝ)⁻¹ • L.adjoint y, ?_⟩
  have happly := congrArg (fun T : K →L[ℝ] K ↦ T y) hscalar
  have hLLstar : L (L.adjoint y) = (γ : ℝ) • y := by
    simpa using happly
  rw [Set.mem_preimage, ContinuousLinearMap.map_smul, hLLstar, smul_smul]
  simpa [inv_mul_cancel₀ (show (γ : ℝ) ≠ 0 from ne_of_gt γ.2)] using hy

namespace ERealFunction

section CompAdjointEqSmulId

variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (L : H →L[ℝ] K) (γ : PosReal)
variable (hscalar : L.comp L.adjoint = (γ : ℝ) • (1 : K →L[ℝ] K))

omit [CompleteSpace H] [CompleteSpace K] in
private theorem indicator_preimage_eq_comp (C : Set K) (L : H →L[ℝ] K) :
    ι[L ⁻¹' C] = (ι[C]) ∘ L := by
  funext x
  by_cases hx : L x ∈ C
  · simp [ERealFunction.indicator, hx]
  · simp [ERealFunction.indicator, hx]

omit [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] in
private theorem scaled_indicator_eq_indicator (C : Set K) (γ : PosReal) :
    γ • ι[C] = ι[C] := by
  funext x
  apply Subtype.ext
  by_cases hx : x ∈ C
  · simp [ERealFunction.indicator, hx]
  · simpa [ERealFunction.indicator, hx] using
      (EReal.coe_mul_top_of_pos γ.2 : ((γ : ℝ) : EReal) * ⊤ = ⊤)

/-- Canonical indicator companion to Proposition 29.2: under the scalar-adjoint hypothesis, the
indicator of the preimage `L ⁻¹' C` belongs to `Γ₀(H)`. -/
theorem indicator_preimage_mem_gammaZero_of_nonempty_isClosed_convex_of_comp_adjoint_eq_smul_id
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (L : H →L[ℝ] K) (γ : PosReal)
    (hscalar : L.comp L.adjoint = (γ : ℝ) • (1 : K →L[ℝ] K)) :
    ι[L ⁻¹' C] ∈ Γ₀(H) := by
  simpa [indicator_preimage_eq_comp C L] using
    comp_continuousLinearMap_mem_gammaZero_of_comp_adjoint_eq_smul_id
      (ι[C]) L γ
      (indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
      hscalar

/-- Canonical proximal companion to Proposition 29.2: after specializing Proposition 24.14 to the
indicator `ι[C]`, the proximity operator of `ι[L ⁻¹' C]` is the projection formula from the
source statement. -/
theorem prox_indicator_preimage_eq_add_inv_smul_adjoint_sub_of_comp_adjoint_eq_smul_id
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (L : H →L[ℝ] K) (γ : PosReal)
    (hscalar : L.comp L.adjoint = (γ : ℝ) • (1 : K →L[ℝ] K))
    (x : H) :
    Prox[
      ι[L ⁻¹' C],
      indicator_preimage_mem_gammaZero_of_nonempty_isClosed_convex_of_comp_adjoint_eq_smul_id
        hC_nonempty hC_closed hC_convex L γ hscalar
    ] x =
      x + (γ : ℝ)⁻¹ •
        L.adjoint
          (projectionPoint C
              (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
            (L x) - L x) := by
  let hC_cheb : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  let hC_gamma : ι[C] ∈ Γ₀(K) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  have hprojC : Prox[γ, ι[C], hC_gamma] = projectionPoint C hC_cheb := by
    change Prox[γ • ι[C], smul_mem_gammaZero (ι[C]) hC_gamma γ] = projectionPoint C hC_cheb
    ext y
    simpa [scaled_indicator_eq_indicator C γ, hC_cheb] using
      congrArg (fun f : K → K ↦ f y) <|
        proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex
  simpa [indicator_preimage_eq_comp C L, hC_cheb, hC_gamma, hprojC] using
    prox_comp_continuousLinearMap_eq_add_inv_smul_adjoint_sub_of_comp_adjoint_eq_smul_id
      (ι[C]) L γ hC_gamma hscalar x

end CompAdjointEqSmulId

end ERealFunction

/-- If `L L* = γ • Id`, then the preimage of a nonempty closed convex set under `L` is
Chebyshev. -/
theorem isChebyshev_preimage_of_nonempty_isClosed_convex_of_comp_adjoint_eq_smul_id
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (L : H →L[ℝ] K) (γ : PosReal)
    (hscalar : L.comp L.adjoint = (γ : ℝ) • (1 : K →L[ℝ] K)) :
    IsChebyshev (L ⁻¹' C) := by
  let hD_gamma :
      ι[L ⁻¹' C] ∈ Γ₀(H) :=
    indicator_preimage_mem_gammaZero_of_nonempty_isClosed_convex_of_comp_adjoint_eq_smul_id
      hC_nonempty hC_closed hC_convex L γ hscalar
  let hD_nonempty : (L ⁻¹' C).Nonempty :=
    preimage_nonempty_of_comp_adjoint_eq_smul_id hC_nonempty L γ hscalar
  exact
    (ERealFunction.hasUniqueProxPoint_indicator_iff_isChebyshev hD_nonempty).1 <|
      ERealFunction.hasUniqueProxPoint_of_mem_gammaZero (ι[L ⁻¹' C]) hD_gamma

section CompAdjointEqSmulId

variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (L : H →L[ℝ] K) (γ : PosReal)
variable (hscalar : L.comp L.adjoint = (γ : ℝ) • (1 : K →L[ℝ] K))

local notation "D" => L ⁻¹' C
local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
local notation "hD_gamma" =>
  indicator_preimage_mem_gammaZero_of_nonempty_isClosed_convex_of_comp_adjoint_eq_smul_id
    hC_nonempty hC_closed hC_convex L γ hscalar
local notation "hD_cheb" =>
  isChebyshev_preimage_of_nonempty_isClosed_convex_of_comp_adjoint_eq_smul_id
    hC_nonempty hC_closed hC_convex L γ hscalar
local notation "P_C" => P[C, hC_cheb]
local notation "P_D" => P[D, hD_cheb]

/-- Proposition 29.2 (1): let `K` be a real Hilbert space, let `C` be a nonempty closed convex
subset of `K`, let `L : H →L[ℝ] K`, let `x ∈ H`, and set `D = L ⁻¹' C`. If
`L ∘L L* = γ • Id` for some `γ ∈ ℝ_{++}`, then
`P_D x = x + γ⁻¹ • L* (P_C (L x) - L x)`. -/
theorem projectionPoint_preimage_eq_add_inv_smul_adjoint_sub_of_comp_adjoint_eq_smul_id
    (x : H) :
    P_D x = x + (γ : ℝ)⁻¹ • (L.adjoint (P_C (L x) - L x)) := by
  have hprojD : Prox[ι[D], hD_gamma] = P_D := by
    simpa [hD_cheb] using ERealFunction.proximityOperator_indicator_eq_projectionPoint hD_cheb
  simpa [hprojD] using
    ERealFunction.prox_indicator_preimage_eq_add_inv_smul_adjoint_sub_of_comp_adjoint_eq_smul_id
      hC_nonempty hC_closed hC_convex L γ hscalar x

end CompAdjointEqSmulId

private theorem comp_adjoint_eq_one_of_inverse_eq_adjoint
    (L : H →L[ℝ] K) (Linv : K →L[ℝ] H)
    (h_right : L.comp Linv = (1 : K →L[ℝ] K))
    (h_adj : Linv = L.adjoint) :
    L.comp L.adjoint = (1 : K →L[ℝ] K) := by
  rw [← h_adj]
  exact h_right

/-- If `L` is invertible with inverse `L*`, then the preimage of a nonempty closed convex set
under `L` is Chebyshev. -/
theorem isChebyshev_preimage_of_nonempty_isClosed_convex_of_inverse_eq_adjoint
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (L : H →L[ℝ] K) (Linv : K →L[ℝ] H)
    (h_right : L.comp Linv = (1 : K →L[ℝ] K))
    (h_adj : Linv = L.adjoint) :
    IsChebyshev (L ⁻¹' C) := by
  simpa using
    isChebyshev_preimage_of_nonempty_isClosed_convex_of_comp_adjoint_eq_smul_id
      hC_nonempty hC_closed hC_convex L (1 : PosReal)
      (by
        simpa using
          comp_adjoint_eq_one_of_inverse_eq_adjoint L Linv h_right h_adj)

section InverseEqAdjoint

variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (L : H →L[ℝ] K) (Linv : K →L[ℝ] H)
variable (h_left : Linv.comp L = (1 : H →L[ℝ] H))
variable (h_right : L.comp Linv = (1 : K →L[ℝ] K))
variable (h_adj : Linv = L.adjoint)

local notation "D" => L ⁻¹' C
local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
local notation "hD_cheb" =>
  isChebyshev_preimage_of_nonempty_isClosed_convex_of_inverse_eq_adjoint
    hC_nonempty hC_closed hC_convex L Linv h_right h_adj
local notation "P_C" => P[C, hC_cheb]
local notation "P_D" => P[D, hD_cheb]

/-- Proposition 29.2 (2): let `K` be a real Hilbert space, let `C` be a nonempty
closed convex subset of `K`, let `L : H →L[ℝ] K`, let `x ∈ H`, and set
`D = L ⁻¹' C`. If `L` is invertible with inverse `L*`, written here as an
explicit inverse map `Linv` with `Linv = L.adjoint`, then
`P_D x = Linv (P_C (L x))`. -/
theorem projectionPoint_preimage_eq_inverse_projectionPoint_of_inverse_eq_adjoint
    (h_left : Linv.comp L = (1 : H →L[ℝ] H))
    (x : H) :
    P_D x = Linv (P_C (L x)) := by
  have hscalar : L.comp L.adjoint = ((1 : PosReal) : ℝ) • (1 : K →L[ℝ] K) := by
    simpa using comp_adjoint_eq_one_of_inverse_eq_adjoint L Linv h_right h_adj
  have hproj :=
    projectionPoint_preimage_eq_add_inv_smul_adjoint_sub_of_comp_adjoint_eq_smul_id
      hC_nonempty hC_closed hC_convex L (1 : PosReal) hscalar x
  have hadj_comp : L.adjoint (L x) = x := by
    calc
      L.adjoint (L x) = Linv (L x) := by rw [h_adj]
      _ = x := by
        simpa using congrArg (fun T : H →L[ℝ] H ↦ T x) h_left
  calc
    P_D x = x + (((1 : PosReal) : ℝ)⁻¹ • (L.adjoint (P_C (L x) - L x))) := hproj
    _ = x + (L.adjoint (P_C (L x) - L x)) := by simp
    _ = x + (L.adjoint (P_C (L x)) - L.adjoint (L x)) := by
      rw [ContinuousLinearMap.map_sub]
    _ = x + (Linv (P_C (L x)) - x) := by rw [h_adj, hadj_comp]
    _ = Linv (P_C (L x)) := by abel_nf

end InverseEqAdjoint

end
