import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Proposition_12_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set
open scoped Pointwise

variable {H : Type u} [AddCommGroup H]

namespace ERealFunction

-- Proof sketch: if `x ∈ C + D`, choose a decomposition `x = c + d` with `c ∈ C` and `d ∈ D`, so
-- one admissible infimal-convolution value is `0`; if `x ∉ C + D`, every decomposition has either
-- `y ∉ C` or `z ∉ D`, forcing the summand to be `⊤`, hence the infimum is `⊤`.
/-- Example 12.3: the infimal convolution of the extended-real indicators of `C` and `D` is the
indicator of the Minkowski sum `C + D`. -/
theorem indicator_infimalConvolution_eq_indicator_add (C D : Set H) :
    ι[C] □ ι[D] = (ι[C + D]).asEReal := by
  have hdom : dom (ι[C] □ ι[D]) = C + D := by
    simpa using dom_infimalConvolution (ι[C]) (ι[D])
  ext x
  by_cases hx : x ∈ C + D
  · have hle : (ι[C] □ ι[D]) x ≤ 0 := by
      rcases hx with ⟨y, hy, z, hz, rfl⟩
      rw [infimalConvolution_apply]
      refine le_trans (iInf_le _ y) ?_
      simp [hy, hz]
    have hge : 0 ≤ (ι[C] □ ι[D]) x := by
      rw [infimalConvolution_apply]
      refine le_iInf ?_
      intro y
      by_cases hy : y ∈ C
      · by_cases hz : x - y ∈ D
        · simp [indicator, hy, hz]
        · simp [indicator, hy, hz]
      · have hD_ne_bot : ((ι[D] (x - y) : Set.Ioi (⊥ : EReal)) : EReal) ≠ ⊥ :=
          ne_of_gt (ι[D] (x - y)).property
        rw [show (ι[C] y : EReal) = ⊤ by simp [indicator, hy]]
        rw [EReal.top_add_of_ne_bot hD_ne_bot]
        simp
    have hzero : (ι[C] □ ι[D]) x = 0 := le_antisymm hle hge
    simpa [indicator, hx] using hzero
  · have hx_not_dom : x ∉ dom (ι[C] □ ι[D]) := by
      rw [hdom]
      exact hx
    have htop : (ι[C] □ ι[D]) x = ⊤ := (not_mem_dom_iff _ _).1 hx_not_dom
    simpa [indicator, hx] using htop

end ERealFunction
