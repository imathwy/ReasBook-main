import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.II.section05.«0017_Definition_II_1_extra_10»
import DifferentialForms_Cartan_1970.II.section05.«0032_Lemma_II_1_extra_19»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

noncomputable section

universe u

/-- The real-plane parametrization associated to a closed complex path. -/
def ClosedPath.realCurve (γ : ClosedPath ℂ) : ℝ → Plane :=
  Complex.equivRealProd ∘ γ.toPath.extend

/-- A local straightening chart for a boundary path whose positive transverse side lies in
`interior K` and whose negative transverse side stays outside `K`. -/
class IsBoundaryStraighteningAt
    (K : Set ℂ) (γ : ℝ → Plane) (t₀ : ℝ)
    (δ : OpenPartialHomeomorph Plane Plane) : Prop
    extends IsLocalCurveStraighteningAt γ 0 1 t₀ δ where
  exterior_on_right :
    (Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {p | p.2 < 0}))) ∩ K = ∅
  interior_on_left :
    Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {p | 0 < p.2})) ⊆ interior K

/-- Definition II.1-extra-20: a finite family of closed piecewise differentiable complex paths is
the oriented boundary of a compact set `K` when each path is simple except for the identification
of its endpoints, the path images are pairwise disjoint with union equal to `frontier K`, and near
each differentiable interior parameter value the interior of `K` lies on the left side of the
orientation while the exterior lies on the right. -/
class IsOrientedBoundaryOf {ι : Type u} [Fintype ι] (K : Set ℂ)
    (Γ : ι → ClosedPath ℂ) : Prop where
  isCompact : IsCompact K
  piecewiseDifferentiable (i) : (Γ i).toPath.IsPiecewiseDifferentiable
  simple_loops (i) {s t : I} (h : (Γ i).toPath s = (Γ i).toPath t) :
    s = t ∨ (s, t) = ((0 : I), (1 : I)) ∨ (s, t) = ((1 : I), (0 : I))
  pairwiseDisjoint_ranges :
    Pairwise fun i j ↦
      Disjoint (Set.range (Γ i).toPath) (Set.range (Γ j).toPath)
  iUnion_range_eq_frontier :
    (⋃ i, Set.range (Γ i).toPath) = frontier K
  exists_boundary_chart_at_regular_point (i) {t₀ : ℝ}
      (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
      (hdiff : DifferentiableWithinAt ℝ (Γ i).realCurve (Set.Icc (0 : ℝ) 1) t₀)
      (hderiv : derivWithin (Γ i).realCurve (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
      ∃ δ : OpenPartialHomeomorph Plane Plane,
        IsBoundaryStraighteningAt K (Γ i).realCurve t₀ δ

attribute [instance] IsOrientedBoundaryOf.isCompact

theorem IsOrientedBoundaryOf.range_toPath_subset_frontier {ι : Type u} [Fintype ι] {K : Set ℂ}
    {Γ : ι → ClosedPath ℂ} (hΓ : IsOrientedBoundaryOf K Γ) (i : ι) :
    Set.range (Γ i).toPath ⊆ frontier K := by
  intro z hz
  rw [← hΓ.iUnion_range_eq_frontier]
  exact Set.mem_iUnion.2 ⟨i, hz⟩
