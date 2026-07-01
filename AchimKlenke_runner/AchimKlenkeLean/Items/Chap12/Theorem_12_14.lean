import Mathlib
import AchimKlenkeLean.Items.Chap02.Definition_2_34

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open OrderDual
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕᵒᵈ mΩ}

/-
Theorem 12.14 is `source-facing`: it states backward-martingale convergence to the textbook tail
`σ`-algebra. Its `core/canonical` owner layer is the martingale and conditional-expectation
convergence API, notably `MeasureTheory.Martingale`,
`MeasureTheory.tendsto_ae_condExp`, and `MeasureTheory.tendsto_eLpNorm_condExp`. Its
`bridge/view` ingredient is the chapter-level uniform-integrability bridge
`backward_martingale_uniformIntegrable`, which converts the backward martingale into the owner
convergence setup after identifying `X (toDual n)` with `μ[X 0 | ℱ (toDual n)]`. The only
primitive data here are the backward martingale `X`, the reversed filtration `ℱ`, and the
measure `μ`; the tail conditional expectation is a derived object, so we keep no extra public
wrapper around it.
-/
section BackwardMartingale

variable {X : ℕᵒᵈ → Ω → ℝ}

local notation "𝓕∞" => tailMeasurableSpace (ℱ ∘ toDual)

-- Proof sketch: use the martingale identity on `ℕᵒᵈ` to rewrite `X (toDual n)` as the
-- conditional expectation of `X 0` with respect to the decreasing σ-algebra `ℱ (toDual n)`, then
-- apply the owner-level Lévy conditional-expectation convergence theorem for the resulting tail
-- `σ`-algebra.
/-- Theorem 12.14 (1): a real-valued backward martingale converges almost surely to the canonical
tail conditional expectation `𝔼[X₀ | 𝓕_{-∞}]`. -/
theorem backward_martingale_ae_tendsto_limit (hX : Martingale X ℱ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (toDual n) ω) atTop
      (𝓝 (μ[X 0 | 𝓕∞] ω)) := sorry

-- Proof sketch: after identifying `X (toDual n)` with `𝔼[X₀ | ℱ (toDual n)]`, apply the
-- `L¹` owner theorem for conditional expectations along the decreasing tail family.
/-- Theorem 12.14 (2): the same backward martingale converges in `L¹` to the canonical tail
conditional expectation `𝔼[X₀ | 𝓕_{-∞}]`. -/
theorem backward_martingale_tendsto_eLpNorm_one_limit (hX : Martingale X ℱ μ) :
    Tendsto
      (fun n ↦ eLpNorm (X (toDual n) - μ[X 0 | 𝓕∞]) 1 μ)
      atTop (𝓝 0) := sorry

end BackwardMartingale
