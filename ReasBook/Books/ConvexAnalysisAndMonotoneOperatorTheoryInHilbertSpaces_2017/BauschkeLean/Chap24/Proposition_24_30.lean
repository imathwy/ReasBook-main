import BauschkeLean.Chap11.Example_11_2
import BauschkeLean.Chap13.Corollary_13_40
import BauschkeLean.Chap13.Example_13_26
import BauschkeLean.Chap13.Proposition_13_21
import BauschkeLean.Chap14.Remark_14_4
import BauschkeLean.Chap16.Proposition_16_33
import BauschkeLean.Chap24.Proposition_24_27

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section BasicProperties

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (C : Set H)
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

local notation "P_C" => P[C, hC_cheb]

local notation "σ_C" =>
  properIoi (σ[C]) (isProper_supportFunction_of_nonempty C hC_nonempty)

-- Source/core/bridge triage:
-- - `source-facing`: Proposition 24.30 is the proximal formula for the explicit profile
--   `u ↦ σ[C] u + φ ‖u‖`.
-- - `core/canonical`: the owner declarations are `distanceProfile`, `Γ₀`, `Prox`, `Argmin`,
--   `φ∗[hφ]`, and the Chapter 14 conjugate-prox identity.
-- - `bridge/view`: this file derives Proposition 24.30 from Proposition 24.27 by applying that
--   owner theorem to `φ∗[hφ]` and then transporting back across Fenchel conjugation.

private theorem gammaZeroConjugate_even
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (heven : Function.Even φ) :
    Function.Even (φ∗[hφ]) := by
  have hφ_even_asEReal : Function.Even φ.asEReal := by
    intro t
    exact congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (heven t)
  intro t
  apply Subtype.ext
  simpa [gammaZeroConjugate_apply] using (conjugate_even φ.asEReal hφ_even_asEReal t)

private theorem distanceProfile_conjugate_eq_supportFunction_add_comp_norm
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (heven : Function.Even φ)
    (hdist : distanceProfile C (φ∗[hφ]) ∈ Γ₀(H)) :
    (distanceProfile C (φ∗[hφ]))∗[hdist] = σ_C + (φ ∘ norm) := by
  let φStar : ℝ → Set.Ioi (⊥ : EReal) := φ∗[hφ]
  have hφStar : φStar ∈ Γ₀(ℝ) := by
    simpa [φStar] using gammaZeroConjugate_mem_gammaZero hφ
  have hφStar_even : Function.Even φStar := by
    simpa [φStar] using gammaZeroConjugate_even φ hφ heven
  have hφStar_even_asEReal : Function.Even φStar.asEReal := by
    intro t
    exact congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (hφStar_even t)
  have hφStar_mono : MonotoneOn φStar (Set.Ici (0 : ℝ)) := by
    simpa using
      monotoneOn_nonnegative_of_even_convexOn φStar hφStar.2 hφStar_even_asEReal
  have hscalar_conj : (φStar : ℝ → Set.Ioi (⊥ : EReal)).asEReal∗ = φ.asEReal := by
    funext t
    simpa [φStar, Function.asEReal, gammaZeroConjugate_apply] using
      congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal))
        (congrFun (gammaZeroConjugate_gammaZeroConjugate φ hφ) t)
  let f : H → Set.Ioi (⊥ : EReal) := distanceProfile C φStar
  have hrepr :
      f.asEReal∗ = σ[C] + φ.asEReal ∘ norm := by
    calc
      f.asEReal∗ = σ[C] + (φStar : ℝ → Set.Ioi (⊥ : EReal)).asEReal∗ ∘ norm := by
            simpa [f, φStar, distanceProfile_eq_comp_infDist, Function.comp] using
              fenchelConjugate_comp_infDist_eq_supportFunction_add_comp_norm
                C hC_nonempty hC_closed hC_convex φStar hφStar_mono hφStar_even
      _ = σ[C] + φ.asEReal ∘ norm := by
        rw [hscalar_conj]
  funext u
  apply Subtype.ext
  simpa [f, φStar, Function.comp] using congrFun hrepr u

/-- The support-function-plus-radial profile from Proposition 24.30 belongs to `Γ₀(H)` when the
scalar profile `φ` is an even member of `Γ₀(ℝ)`. -/
theorem supportFunctionAddCompNorm_mem_gammaZero
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (heven : Function.Even φ) :
    σ_C + (φ ∘ norm) ∈ Γ₀(H) := by
  let φStar : ℝ → Set.Ioi (⊥ : EReal) := φ∗[hφ]
  let f : H → Set.Ioi (⊥ : EReal) := distanceProfile C φStar
  have hφStar : φStar ∈ Γ₀(ℝ) := by
    simpa [φStar] using gammaZeroConjugate_mem_gammaZero hφ
  have hφStar_even : Function.Even φStar := by
    simpa [φStar] using gammaZeroConjugate_even φ hφ heven
  have hdist : f ∈ Γ₀(H) := by
    simpa [f, φStar] using
      distanceProfile_mem_gammaZero_of_even
        hC_nonempty hC_closed hC_convex φStar hφStar hφStar_even
  have hrepr :=
    distanceProfile_conjugate_eq_supportFunction_add_comp_norm
      C hC_nonempty hC_closed hC_convex φ hφ heven (by simpa [f, φStar] using hdist)
  have hconj : f∗[hdist] = σ_C + (φ ∘ norm) := by
    simpa [f, φStar] using hrepr
  simpa [hconj] using gammaZeroConjugate_mem_gammaZero hdist

/-- Proposition 24.30: if `C` is a nonempty closed convex subset of `H`,
if `φ ∈ Γ₀(ℝ)` is even, if `φ*` is differentiable on `ℝ \ {0}`,
and if `f = σ_C + φ ∘ ‖·‖`, then `Prox_f x` is the
residual `x - P_C x` below the threshold `max Argmin φ`, written canonically as
`sSup (Argmin φ.asEReal)`, and otherwise equals the radial shrinkage from formula `(24.57)`. -/
  theorem prox_supportFunctionAddCompNorm_eq_piecewise
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hdiff :
      DifferentiableOn ℝ (fun t : ℝ ↦ (((φ∗[hφ]) t : EReal).toReal)) (({0} : Set ℝ)ᶜ))
    (x : H) :
    Prox[σ_C + (φ ∘ norm),
      supportFunctionAddCompNorm_mem_gammaZero C hC_nonempty hC_closed hC_convex φ hφ heven] x =
      if Metric.infDist x C > sSup (Argmin φ.asEReal) then
        ((Prox[φ, hφ] (Metric.infDist x C)) / Metric.infDist x C) • (x - P_C x)
      else
        x - P_C x := by
  let φStar : ℝ → Set.Ioi (⊥ : EReal) := φ∗[hφ]
  let f : H → Set.Ioi (⊥ : EReal) := distanceProfile C φStar
  have hφStar : φStar ∈ Γ₀(ℝ) := by
    simpa [φStar] using gammaZeroConjugate_mem_gammaZero hφ
  have hφStar_even : Function.Even φStar := by
    simpa [φStar] using gammaZeroConjugate_even φ hφ heven
  have hdist : f ∈ Γ₀(H) := by
    simpa [f, φStar] using
      distanceProfile_mem_gammaZero_of_even
        hC_nonempty hC_closed hC_convex φStar hφStar hφStar_even
  have hargmin : Argmin φ.asEReal = (∂ (φ∗[hφ])) 0 := by
    simpa using argmin_eq_subdifferential_gammaZeroConjugate_zero φ hφ
  have hpiece :
      Prox[f, hdist] x =
        if Metric.infDist x C > sSup ((∂ (φ∗[hφ])) 0) then
          x +
            ((Prox[φ, hφ] (Metric.infDist x C)) / Metric.infDist x C) •
              (P_C x - x)
        else
          P_C x := by
    simpa [f, φStar, gammaZeroConjugate_apply] using
      prox_distanceProfile_eq_piecewise
        hC_nonempty hC_closed hC_convex φStar hφStar hφStar_even hdiff
        (by simpa [f, φStar] using hdist) x
  have hrepr :=
    distanceProfile_conjugate_eq_supportFunction_add_comp_norm
      C hC_nonempty hC_closed hC_convex φ hφ heven (by simpa [f, φStar] using hdist)
  have hconj : f∗[hdist] = σ_C + (φ ∘ norm) := by
    simpa [f, φStar] using hrepr
  calc
    Prox[σ_C + (φ ∘ norm),
        supportFunctionAddCompNorm_mem_gammaZero C hC_nonempty hC_closed hC_convex φ hφ heven] x =
      Prox[f∗[hdist], gammaZeroConjugate_mem_gammaZero hdist] x := by
        simp [hconj]
    _ = x - Prox[f, hdist] x := by
      simpa using
        conjugate_proximityOperator_eq_sub_proximityOperator f hdist x
    _ =
        x -
          (if Metric.infDist x C > sSup ((∂ (φ∗[hφ])) 0) then
            x +
              ((Prox[φ, hφ] (Metric.infDist x C)) / Metric.infDist x C) •
                (P_C x - x)
          else
            P_C x) := by
      rw [hpiece]
    _ =
        if Metric.infDist x C > sSup (Argmin φ.asEReal) then
          ((Prox[φ, hφ] (Metric.infDist x C)) / Metric.infDist x C) • (x - P_C x)
        else
          x - P_C x := by
      rw [hargmin]
      by_cases h : Metric.infDist x C > sSup ((∂ (φ∗[hφ])) 0)
      · simp [h, sub_eq_add_neg]
      · simp [h]

end BasicProperties

end

end ERealFunction
