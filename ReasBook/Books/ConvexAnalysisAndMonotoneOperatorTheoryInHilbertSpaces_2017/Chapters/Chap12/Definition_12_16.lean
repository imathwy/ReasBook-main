import Mathlib
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- The scaled norm kernel `x ↦ β ‖x‖` as an `]-∞,+∞]`-valued function. -/
noncomputable def scaledNormKernel (β : NNReal) : H → Set.Ioi (⊥ : EReal) :=
  (fun x : H ↦ (β : ℝ) * ‖x‖).toEReal

/-- The positive-parameter view of `scaledNormKernel`. The owner abstraction remains
`scaledNormKernel`, whose coefficient may also be `0`; this bridge is for source-facing
statements that naturally use `ρ ∈ ℝ_{++}`. -/
noncomputable abbrev scaledNormKernelOfPos (ρ : Set.Ioi (0 : ℝ)) :
    H → Set.Ioi (⊥ : EReal) :=
  scaledNormKernel ⟨(ρ : ℝ), ρ.2.le⟩

/-- Coercing the scaled norm kernel to `EReal` recovers the formula `x ↦ β ‖x‖`. -/
@[simp]
theorem scaledNormKernel_apply (β : NNReal) (x : H) :
    (scaledNormKernel β x : EReal) = (((β : ℝ) * ‖x‖ : ℝ) : EReal) := by
  simp [scaledNormKernel]

/-- Coercing the positive-parameter scaled norm kernel to `EReal` yields the expected formula
`x ↦ ρ ‖x‖`. -/
@[simp]
theorem scaledNormKernelOfPos_apply (ρ : Set.Ioi (0 : ℝ)) (x : H) :
    (scaledNormKernelOfPos ρ x : EReal) = (((ρ : ℝ) * ‖x‖ : ℝ) : EReal) :=
  scaledNormKernel_apply _ x

section GammaZero

variable [NormedSpace ℝ H]

/-- The scaled norm kernel belongs to `Γ₀(H)`. -/
theorem scaledNormKernel_mem_gammaZero (β : NNReal) :
    scaledNormKernel β ∈ Γ₀(H) := by
  -- Package the real kernel formula directly through the Chapter 9 `Γ(H)` bridge.
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  rw [mem_gamma_iff]
  constructor
  · -- Convexity follows from convexity of the norm and the nonnegativity of `β`.
    intro x y a ha hb
    have hnorm :
        ‖a • x + (1 - a) • y‖ ≤ a * ‖x‖ + (1 - a) * ‖y‖ := by
      simpa [smul_eq_mul] using
        (convexOn_univ_norm.2 (by simp) (by simp) ha (sub_nonneg.mpr hb) (by ring) :
          ‖a • x + (1 - a) • y‖ ≤ a • ‖x‖ + (1 - a) • ‖y‖)
    have hscaled :
        (β : ℝ) * ‖a • x + (1 - a) • y‖ ≤
          a * ((β : ℝ) * ‖x‖) + (1 - a) * ((β : ℝ) * ‖y‖) := by
      calc
        (β : ℝ) * ‖a • x + (1 - a) • y‖ ≤
            (β : ℝ) * (a * ‖x‖ + (1 - a) * ‖y‖) := by
              exact mul_le_mul_of_nonneg_left hnorm β.2
        _ = a * ((β : ℝ) * ‖x‖) + (1 - a) * ((β : ℝ) * ‖y‖) := by ring
    have hscaledE :
        ((((β : ℝ) * ‖a • x + (1 - a) • y‖ : ℝ) : EReal)) ≤
          ((((a * ((β : ℝ) * ‖x‖) + (1 - a) * ((β : ℝ) * ‖y‖) : ℝ) : EReal))) := by
      exact_mod_cast hscaled
    simpa [EReal.coe_mul, EReal.coe_add] using hscaledE
  · -- Continuity of the scaled norm yields lower semicontinuity after coercion to `EReal`.
    simpa using
      (continuous_coe_real_ereal.comp ((continuous_norm).const_mul (β : ℝ))).lowerSemicontinuous

/-- The positive-parameter scaled norm kernel belongs to `Γ₀(H)`. -/
theorem scaledNormKernelOfPos_mem_gammaZero (ρ : Set.Ioi (0 : ℝ)) :
    scaledNormKernelOfPos ρ ∈ Γ₀(H) :=
  scaledNormKernel_mem_gammaZero _

end GammaZero

/-- Definition 12 16: the `β`-Pasch--Hausdorff envelope of `f` is the infimal convolution of `f`
with the scaled norm `x ↦ β ‖x‖`. -/
noncomputable def paschHausdorffEnvelope {α : Type*} [CoeTC α EReal] (f : H → α) (β : NNReal) :
    H → EReal :=
  f □ scaledNormKernel β

/-- The `β`-Pasch--Hausdorff envelope is computed by infimizing the translated sums
`f y + β ‖x - y‖`. -/
-- Proof sketch: unfold `paschHausdorffEnvelope`, then expand the defining formula for
-- `infimalConvolution` and rewrite the kernel with `scaledNormKernel_apply`.
theorem paschHausdorffEnvelope_apply
    {α : Type*} [CoeTC α EReal] (f : H → α) (β : NNReal) (x : H) :
    paschHausdorffEnvelope f β x =
      ⨅ y : H, (f y : EReal) + ((((β : ℝ) * ‖x - y‖ : ℝ) : EReal)) := by
  rw [paschHausdorffEnvelope, infimalConvolution_apply]
  simp [scaledNormKernel_apply]

/-- The real-valued `β`-Lipschitz minorants of an `]-∞,+∞]`-valued function. -/
def betaLipschitzMinorants
    (f : H → Set.Ioi (⊥ : EReal)) (β : NNReal) : Set (H → ℝ) :=
  {h | LipschitzWith β h ∧ h.toEReal.asEReal ≤ f.asEReal}

/-- Membership in `betaLipschitzMinorants f β` is exactly the `β`-Lipschitz minorant condition:
`h` is `β`-Lipschitz and its canonical `EReal` coercion lies below `f`. -/
theorem mem_betaLipschitzMinorants_iff
    (f : H → Set.Ioi (⊥ : EReal)) (β : NNReal) (h : H → ℝ) :
    h ∈ betaLipschitzMinorants f β ↔
      LipschitzWith β h ∧ h.toEReal.asEReal ≤ f.asEReal :=
  Iff.rfl

end ERealFunction
