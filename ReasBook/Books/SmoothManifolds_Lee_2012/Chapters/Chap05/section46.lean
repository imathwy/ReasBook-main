

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_5_46 (from Chap05/Sec05_36) -/
open Set
open scoped ContDiff Manifold

noncomputable section

universe uE uH uM

-- Semantic recall note: no `lean_leansearch` tool was available in this environment; local
-- repository and mathlib inspection verified `Set.IsRegularDomain` together with
-- `ModelWithCorners.interior` and `ModelWithCorners.boundary` as the canonical owners here.

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M]

local notation "dimM" => Module.finrank ℝ E

/-- Proposition 5.46 (1): if `D ⊆ M` is a regular domain in a smooth manifold without boundary,
then the ambient topological interior of `D` is exactly the image of the manifold interior of `D`
under the subtype inclusion. -/
theorem regular_domain_manifoldInterior_image_eq_interior
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D] :
    Subtype.val '' (leeBoundaryModelWithCorners dimM).interior D = interior D := sorry

/-- Proposition 5.46 (2): if `D ⊆ M` is a regular domain in a smooth manifold without boundary,
then the ambient topological boundary of `D` is exactly the image of the manifold boundary of `D`
under the subtype inclusion. -/
theorem regular_domain_manifoldBoundary_image_eq_frontier
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D] :
    Subtype.val '' (leeBoundaryModelWithCorners dimM).boundary D = frontier D := sorry
