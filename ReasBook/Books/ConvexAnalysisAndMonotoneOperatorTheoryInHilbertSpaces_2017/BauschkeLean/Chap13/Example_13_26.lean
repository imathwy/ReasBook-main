import Mathlib
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap13.Example_13_8
import BauschkeLean.Chap13.Proposition_13_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 13.26: if `y ∈ C`, then monotonicity of `φ` on `[0,∞)` compares
`φ (d(x,C))` with `φ ‖x - y‖`. -/
lemma distance_profile_le_translated_norm_profile_of_mem
    (C : Set H) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hφ_mono : MonotoneOn φ (Set.Ici (0 : ℝ))) {x y : H} (hy : y ∈ C) :
    (φ (Metric.infDist x C) : EReal) ≤ (φ ‖x - y‖ : EReal) := by
  -- Compare `d(x, C)` with the admissible residual `‖x - y‖`, then apply monotonicity on `ℝ≥0`.
  exact hφ_mono Metric.infDist_nonneg (norm_nonneg _) <| by
    simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem hy

/-- Helper for Example 13.26: the projection point realizes the source identity
`φ ∘ d_C = ι[C] □ (φ ∘ ‖·‖)`. -/
lemma comp_infDist_eq_indicator_infimalConvolution_comp_norm
    (C : Set H) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hφ_mono : MonotoneOn φ (Set.Ici (0 : ℝ))) :
    (φ ∘ fun x : H ↦ Metric.infDist x C).asEReal = ι[C] □ (φ ∘ norm) := by
  let hC_cheb := isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  let P : H → H := projectionPoint C hC_cheb
  funext x
  have hPx_mem : P x ∈ C := (projectionPoint_isBestApproximation C hC_cheb x).1
  have hPx_dist : Metric.infDist x C = ‖x - P x‖ := by
    -- The metric projection attains the infimum defining the distance to `C`.
    simpa [P, dist_eq_norm] using (projectionPoint_isBestApproximation C hC_cheb x).2.symm
  rw [infimalConvolution_apply]
  apply le_antisymm
  · -- Every admissible translated norm profile dominates the value at `d(x, C)`.
    refine le_iInf ?_
    intro y
    by_cases hy : y ∈ C
    · simpa [Function.comp_apply, indicator_apply, hy] using
        distance_profile_le_translated_norm_profile_of_mem C φ hφ_mono hy
    · have hterm :
          (ι[C] y : EReal) +
              (((φ ∘ norm) (x - y) : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ := by
        have hne_bot :
            ((((φ ∘ norm) (x - y) : Set.Ioi (⊥ : EReal)) : EReal)) ≠ ⊥ := by
          exact ne_of_gt ((φ ∘ norm) (x - y)).2
        simpa [Function.comp_apply, indicator_apply, hy] using EReal.top_add_of_ne_bot hne_bot
      calc
        (φ (Metric.infDist x C) : EReal) ≤ ⊤ := le_top
        _ = (ι[C] y : EReal) +
              (((φ ∘ norm) (x - y) : Set.Ioi (⊥ : EReal)) : EReal) := hterm.symm
  · -- The projection point gives the matching upper bound in the defining infimum.
    simpa [Function.comp_apply, indicator_apply, hPx_mem, hPx_dist] using
      (iInf_le
        (fun y : H ↦ (ι[C] y : EReal) + (((φ ∘ norm) (x - y) : Set.Ioi (⊥ : EReal)) : EReal))
        (P x))

/-- Helper for Example 13.26: evenness and monotonicity on `[0,∞)` force `0` to minimize `φ`. -/
lemma apply_zero_le_apply_of_monotoneOn_nonnegative_of_even
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ_mono : MonotoneOn φ (Set.Ici (0 : ℝ)))
    (hφ_even : Function.Even φ) :
    ∀ t : ℝ, (φ 0 : EReal) ≤ φ t := by
  intro t
  -- First compare `0` with `|t|` by monotonicity, then rewrite `φ |t|` back to `φ t` by evenness.
  calc
    (φ 0 : EReal) ≤ (φ |t| : EReal) := by
      exact hφ_mono (by simp) (abs_nonneg t) (by simp)
    _ = (φ t : EReal) := (even_apply_norm_eq φ hφ_even t).symm

/-- Example 13.26: if `C` is a nonempty closed convex subset of `H` and `φ` is increasing on
`[0, ∞)` and even, then the Fenchel conjugate of `x ↦ φ (d(x, C))` is
`σ[C] + (u ↦ φ^*(‖u‖))`. -/
theorem fenchelConjugate_comp_infDist_eq_supportFunction_add_comp_norm
    (C : Set H) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hφ_mono : MonotoneOn φ (Set.Ici (0 : ℝ))) (hφ_even : Function.Even φ) :
    (φ ∘ fun x : H ↦ Metric.infDist x C).asEReal∗ =
      σ[C] + φ.asEReal∗ ∘ norm := by
  -- Rewrite `φ ∘ d_C` as the indicator-plus-radial infimal convolution from the source proof.
  rw [comp_infDist_eq_indicator_infimalConvolution_comp_norm
    C hC_nonempty hC_closed hC_convex φ hφ_mono]
  -- Conjugating the infimal convolution splits into the support function and the radial conjugate.
  rw [conjugate_infimalConvolution_eq]
  rw [conjugate_indicator_eq_supportFunction]
  rw [conjugate_comp_norm_eq_comp_norm_conjugate_of_even_all_spaces (H := H) φ hφ_even]
  intro _
  -- In the zero-dimensional branch, the all-spaces radial theorem only needs `φ 0 ≤ φ t`.
  exact apply_zero_le_apply_of_monotoneOn_nonnegative_of_even φ hφ_mono hφ_even

end Conjugation

end ERealFunction
