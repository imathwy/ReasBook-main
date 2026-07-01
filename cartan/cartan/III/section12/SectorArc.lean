import Mathlib

noncomputable section

open scoped Interval

/-- The closed sector with vertex `0`, radii `r ≥ 0`, and arguments in `θ₁ ≤ θ ≤ θ₂`. -/
def closedSector (θ₁ θ₂ : ℝ) : Set ℂ :=
  {z | ∃ r : ℝ, 0 ≤ r ∧ ∃ θ ∈ Set.Icc θ₁ θ₂, z = circleMap 0 r θ}

/-- Helper for `closedSector`: unpack membership in the closed sector. -/
theorem mem_closedSector_iff {θ₁ θ₂ : ℝ} {z : ℂ} :
    z ∈ closedSector θ₁ θ₂ ↔ ∃ r : ℝ, 0 ≤ r ∧ ∃ θ ∈ Set.Icc θ₁ θ₂, z = circleMap 0 r θ :=
  Iff.rfl

/-- The punctured sector obtained from `closedSector θ₁ θ₂` by removing the vertex `0`. -/
def puncturedSector (θ₁ θ₂ : ℝ) : Set ℂ :=
  closedSector θ₁ θ₂ \ {0}

/-- Helper for `puncturedSector`: unpack membership in the punctured sector. -/
theorem mem_puncturedSector_iff {θ₁ θ₂ : ℝ} {z : ℂ} :
    z ∈ puncturedSector θ₁ θ₂ ↔ z ∈ closedSector θ₁ θ₂ ∧ z ≠ 0 :=
  Iff.rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The contour integral of `f` over the radius-`r` circular arc from angle `θ₁` to angle `θ₂`. -/
def sectorArcIntegral (f : ℂ → E) (r θ₁ θ₂ : ℝ) : E :=
  ∫ θ in θ₁..θ₂, deriv (circleMap 0 r) θ • f (circleMap 0 r θ)

/-- For complex-valued integrands, `sectorArcIntegral` is the usual `i z f(z)` interval integral
along the circular arc. -/
theorem sectorArcIntegral_def (f : ℂ → ℂ) (r θ₁ θ₂ : ℝ) :
    sectorArcIntegral f r θ₁ θ₂ =
      ∫ θ in θ₁..θ₂, Complex.I * circleMap 0 r θ * f (circleMap 0 r θ) :=
  by
    simp [sectorArcIntegral, deriv_circleMap, mul_left_comm, mul_comm]
