import Mathlib
import cartan.II.section05.«0001_Definition_II_1_extra_1»
import cartan.II.section05.«0017_Definition_II_1_extra_10»
import cartan.II.section05.«0026_Definition_II_1_extra_16»
import cartan.II.section05.«0033_Definition_II_1_extra_20»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open scoped BigOperators unitInterval

noncomputable section

universe u

section

variable {ι : Type u} [Fintype ι]

attribute [local instance] Classical.propDecidable

/-- The ambient scalar field extending the boundary datum `φ` by `0` away from `frontier K`. -/
def boundaryDatum {K : Set ℂ} (φ : C(frontier K, ℂ)) : ℂ → ℂ :=
  fun z ↦ if hz : z ∈ frontier K then φ ⟨z, hz⟩ else 0

@[simp]
theorem boundaryDatum_of_mem {K : Set ℂ} (φ : C(frontier K, ℂ)) {z : ℂ} (hz : z ∈ frontier K) :
    boundaryDatum φ z = φ ⟨z, hz⟩ := by
  simp [boundaryDatum, hz]

@[simp]
theorem boundaryDatum_of_not_mem {K : Set ℂ} (φ : C(frontier K, ℂ)) {z : ℂ}
    (hz : z ∉ frontier K) :
    boundaryDatum φ z = 0 := by
  simp [boundaryDatum, hz]

/-- The scalar Cauchy density determined by `φ`, with pole of order `n + 1` at `z`. -/
def boundaryCauchyDensity {K : Set ℂ} (φ : C(frontier K, ℂ)) (z : ℂ) (n : ℕ) : ℂ → ℂ :=
  fun ζ ↦ boundaryDatum φ ζ / (ζ - z) ^ (n + 1)

/-- The boundary Cauchy transform attached to boundary datum `φ`, obtained by integrating the
canonical Cauchy density of `φ` along the closed paths of `Γ`. -/
def boundaryCauchyTransform {K : Set ℂ}
    (Γ : ι → ClosedPath ℂ)
    (φ : C(frontier K, ℂ)) : ℂ → ℂ :=
  fun z ↦
    ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ z 0 dz) ζ

variable {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
variable {φ : C(frontier K, ℂ)}

-- Proof sketch: on any closed ball avoiding the boundary image, expand
-- `(ζ - z)⁻¹ = (ζ - a)⁻¹ * (1 - (z - a) / (ζ - a))⁻¹` into the normally convergent geometric series
-- from Theorem 3, interchange the finite sum and the resulting path-parameter integrals with the
-- series, and read off the coefficients of the power series centered at `a`.
/-- Exercise 12 (1): if each closed path of `Γ` is piecewise differentiable, lies in `frontier K`,
and the closed ball `|z - a| ≤ r` avoids `frontier K`, then the boundary Cauchy transform admits a
normally convergent power series expansion on that ball, hence on a neighborhood of `a`. -/
theorem boundaryCauchyTransform_hasFPowerSeriesOnBall
    (hΓ_frontier : ∀ i, Set.range (Γ i).toPath ⊆ frontier K)
    (hΓ_piecewise : ∀ i, (Γ i).toPath.IsPiecewiseDifferentiable)
    {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall a r ⊆ (frontier K)ᶜ) :
    ∃ c : ℕ → ℂ,
      HasFPowerSeriesOnBall (boundaryCauchyTransform Γ φ) (ofScalars ℂ c) a
        (ENNReal.ofReal r) := sorry

-- Proof sketch: apply the previous power-series theorem on some closed ball around `a` contained
-- in the boundary complement, then pass from a convergent local power series representation to
-- analyticity at `a`.
/-- If each closed path of `Γ` is piecewise differentiable and lies in `frontier K`, then the
boundary Cauchy transform is analytic at every point of the complement of `frontier K`. -/
theorem boundaryCauchyTransform_analyticAt
    (hΓ_frontier : ∀ i, Set.range (Γ i).toPath ⊆ frontier K)
    (hΓ_piecewise : ∀ i, (Γ i).toPath.IsPiecewiseDifferentiable)
    {a : ℂ}
    (ha : a ∈ (frontier K)ᶜ) :
    AnalyticAt ℂ (boundaryCauchyTransform Γ φ) a := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isClosed_frontier.isOpen_compl a ha
  have hseries :
      ∃ c : ℕ → ℂ,
        HasFPowerSeriesOnBall (boundaryCauchyTransform Γ φ) (ofScalars ℂ c) a
          (ENNReal.ofReal (r / 2)) :=
    boundaryCauchyTransform_hasFPowerSeriesOnBall hΓ_frontier hΓ_piecewise (half_pos hr)
      ((Metric.closedBall_subset_ball (half_lt_self hr)).trans hball)
  rcases hseries with ⟨c, hc⟩
  exact hc.analyticAt

-- Proof sketch: use the local power-series expansion from part (1) on a ball around `a` disjoint
-- from the boundary, differentiate the geometric series termwise, and keep the resulting boundary
-- integrals on the direct path-pullback surface.
/-- Exercise 12 (2): for every natural number `n` and every point `a` off `frontier K`, the
`n`-th complex derivative of the boundary Cauchy transform is `n!` times the boundary integral
with kernel `(ζ - a)^(-(n + 1))` over the piecewise differentiable paths of `Γ` lying in
`frontier K`. -/
theorem boundaryCauchyTransform_iteratedDeriv_eq
    (hΓ_frontier : ∀ i, Set.range (Γ i).toPath ⊆ frontier K)
    (hΓ_piecewise : ∀ i, (Γ i).toPath.IsPiecewiseDifferentiable)
    {n : ℕ} {a : ℂ}
    (ha : a ∈ (frontier K)ᶜ) :
    iteratedDeriv n (boundaryCauchyTransform Γ φ) a =
      (n.factorial : ℂ) *
        ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ a n dz) ζ := sorry

end
