import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Topology

noncomputable section

universe u

-- Semantic recall note: no `lean_leansearch` MCP tool was exposed in this session, so the
-- statement shape below follows local oriented-boundary precedent and the available Mathlib
-- contour-integral API.

/-- Theorem III.5-extra-2 (1): if the singular points of `f` in `D` are isolated in the
source-text sense, namely the singular set has no accumulation point in `D`, then only finitely
many of them can lie in a fixed compact subset `K ⊆ D`. -/
theorem finite_nondifferentiable_points_in_compact_of_isolated
    {K D : Set ℂ} {f : ℂ → ℂ} (hK : IsCompact K) (hKD : K ⊆ D) (hD : IsOpen D)
    (hdiscrete :
      ∀ z ∈ D, ∃ r > 0,
        Metric.ball z r ∩ {w | w ∈ D ∧ ¬ DifferentiableAt ℂ f w} ⊆ {z})
    (hisolated :
      ∀ z ∈ D, ¬ DifferentiableAt ℂ f z →
        ∃ r > 0,
          Metric.closedBall z r ⊆ D ∧
          DifferentiableOn ℂ f (Metric.ball z r \ ({z} : Set ℂ))) :
    Set.Finite (K ∩ {z | ¬ DifferentiableAt ℂ f z}) := sorry

/-- `LocalResidueCircle K D f z residue_z` means that there exists a positive small circle around
`z`, contained in both `interior K` and `D`, on which the circle integral of `f` realizes the
prescribed residue. -/
def LocalResidueCircle (K D : Set ℂ) (f : ℂ → ℂ) (z residue_z : ℂ) : Prop :=
  ∃ radius > 0,
    Metric.closedBall z radius ⊆ interior K ∧
      Metric.closedBall z radius ⊆ D ∧
        (∮ w in C(z, radius), f w) = (2 * Real.pi * Complex.I : ℂ) * residue_z

/-- `ResidueAtInfinityCircleEq f residue_at_infinity` means that all sufficiently large positive
circles centered at `0` realize the usual residue-at-infinity contour formula for `f`. The owner
stores a positive threshold radius rather than a single auxiliary witness circle. -/
def ResidueAtInfinityCircleEq (f : ℂ → ℂ) (residue_at_infinity : ℂ) : Prop :=
  ∃ R₀ > 0,
    ∀ R ≥ R₀,
      (∮ z in C(0, R), f z) = -(2 * Real.pi * Complex.I : ℂ) * residue_at_infinity

/-- Theorem III.5-extra-2 (2): source-form residue theorem for an oriented boundary, stated with
explicit local residue data at the finitely many interior singularities enclosed by the boundary.
The separate global residue-at-infinity relation is recorded by `ResidueAtInfinityCircleEq`, but
it is not part of this oriented-boundary theorem. -/
theorem orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ) {f : ℂ → ℂ}
    (s : Finset ℂ) (residue : ℂ → ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D)
    (hboundary_disjoint : ∀ i, Disjoint (Set.range (Γ i).toPath) (↑s : Set ℂ))
    (hhol : DifferentiableOn ℂ f (D \ (↑s : Set ℂ)))
    (hres : ∀ z ∈ s, LocalResidueCircle K D f z (residue z)) :
    ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z =
      (2 * Real.pi * Complex.I : ℂ) * Finset.sum s residue := sorry
