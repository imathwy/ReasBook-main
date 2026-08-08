import Mathlib

open scoped ENNReal
open MeasureTheory MeasureTheory.Lp ContinuousLinearMap

attribute [local instance] Classical.propDecidable

noncomputable section

universe u₁ u₂

variable {Ω₁ : Type u₁} {Ω₂ : Type u₂}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂)
variable [SFinite μ₁] [SFinite μ₂]

/-- Turn the kernel row `a (t₁, ·)` into an `L²(μ₂)` class when that row is square-integrable,
and use `0` otherwise. -/
private def kernelSection (a : Ω₁ × Ω₂ → ℝ) (t₁ : Ω₁) : Ω₂ →₂[μ₂] ℝ :=
  if h : MemLp (fun t₂ ↦ a (t₁, t₂)) 2 μ₂ then
    h.toLp (fun t₂ ↦ a (t₁, t₂))
  else
    0

-- Proof sketch: on rows that belong to `L²(μ₂)`, the definition unfolds to `MemLp.toLp`, whose
-- coercion is almost everywhere equal to the original section.
/-- The row section agrees almost everywhere with the original kernel whenever the row belongs to
`L²(μ₂)`. -/
private theorem kernelSection_ae_eq (a : Ω₁ × Ω₂ → ℝ)
    (ha : ∀ᵐ t₁ ∂μ₁, MemLp (fun t₂ ↦ a (t₁, t₂)) 2 μ₂) :
    ∀ᵐ t₁ ∂μ₁, kernelSection μ₂ a t₁ =ᵐ[μ₂] fun t₂ ↦ a (t₁, t₂) := sorry

-- Proof sketch: apply Fubini/Tonelli to the square-integrable kernel to show that almost every row
-- is in `L²(μ₂)`, then use the previous sectionwise identification to obtain an `L²(μ₁; L²(μ₂))`
-- function.
/-- A square-integrable kernel on `Ω₁ × Ω₂` gives an `L²(μ₁)` family of `L²(μ₂)` rows. -/
private theorem kernelSection_memLp (a : Ω₁ × Ω₂ → ℝ)
    (ha : MemLp a 2 (μ₁.prod μ₂)) :
    MemLp (kernelSection μ₂ a) 2 μ₁ := sorry

/-- The rowwise `L²(μ₂)` family attached to an `L²(μ₁ ⊗ μ₂)` kernel, viewed as an element of
`L²(μ₁; L²(μ₂))`. This is the bridge from the source-level kernel to the canonical `lpPairing`
owner construction. -/
private def kernelRows (a : Ω₁ × Ω₂ → ℝ) (ha : MemLp a 2 (μ₁.prod μ₂)) :
    Ω₁ →₂[μ₁] (Ω₂ →₂[μ₂] ℝ) :=
  (kernelSection_memLp μ₁ μ₂ a ha).toLp (kernelSection μ₂ a)

/-- The continuous linear operator associated with an `L²` kernel, obtained from the canonical
`L²`-pairing `ContinuousLinearMap.lpPairing` applied to the rowwise `L²(μ₂)` family of the
kernel. -/
def hilbertSchmidtOperator (a : Ω₁ × Ω₂ → ℝ)
    (ha : MemLp a 2 (μ₁.prod μ₂)) :
    (Ω₁ →₂[μ₁] ℝ) →L[ℝ] (Ω₂ →₂[μ₂] ℝ) :=
  ((lsmul ℝ ℝ).flip.lpPairing μ₁ 2 2 (kernelRows μ₁ μ₂ a ha))

-- Proof sketch: rewrite `hilbertSchmidtOperator` via `lpPairing_eq_integral`, replace the row
-- representative by the original kernel section almost everywhere, and conclude with Fubini.
/-- Exercise 14.2.2: a square-integrable measurable kernel defines a continuous linear operator
from `L²(μ₁)` to `L²(μ₂)` by the usual integral formula. -/
theorem hilbertSchmidtOperator_ae_eq (a : Ω₁ × Ω₂ → ℝ)
    (ha : MemLp a 2 (μ₁.prod μ₂)) (f : Ω₁ →₂[μ₁] ℝ) :
    hilbertSchmidtOperator μ₁ μ₂ a ha f =ᵐ[μ₂]
      fun t₂ ↦ ∫ t₁, a (t₁, t₂) * f t₁ ∂μ₁ := sorry
