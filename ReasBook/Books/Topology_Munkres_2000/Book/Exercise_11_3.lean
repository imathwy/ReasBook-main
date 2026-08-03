module

public import Topology_Munkres_2000.Book.Example_11_1.CircularRegion
public import Topology_Munkres_2000.Book.Example_11_2.HorizontalOrder

public section

open Relation
open scoped HorizontalOrder

/-- The elements strictly comparable with `x` under `r`, as displayed in Exercise 11.3. -/
def strictComparables {α : Type u} (r : α → α → Prop) (x : α) : Set α :=
  {y | SymmGen r x y}

/-- Membership in `strictComparables` means comparison with `x` in either direction. -/
theorem mem_strictComparables {α : Type u} (r : α → α → Prop) (x y : α) :
    y ∈ strictComparables r x ↔ r x y ∨ r y x := by
  rfl

/-- An observation for Exercise 11.3: irreflexivity, and hence in particular a strict
partial order, ensures that the displayed set of elements comparable with `x` omits `x`. -/
theorem strictComparables_not_mem {α : Type u} (r : α → α → Prop)
    [Std.Irrefl r] (x : α) :
    x ∉ strictComparables r x := by
  -- Membership would compare `x` strictly with itself in one direction or the other.
  rw [mem_strictComparables]
  exact fun h ↦ h.elim (irrefl x) (irrefl x)

namespace EuclideanPlane.CircularRegion

/-- Helper for Exercise 11.3: every circular region contains two proper subregions
that are incomparable under proper inclusion. -/
theorem existsIncomparableSubregions (U : CircularRegion) :
    ∃ V W : CircularRegion, V < U ∧ W < U ∧ V ≠ W ∧ ¬(V < W ∨ W < V) := by
  have halfRadiusPos : 0 < U.radius / 2 := half_pos U.radius_pos
  let displacement : EuclideanSpace ℝ (Fin 2) :=
    EuclideanSpace.single 0 (U.radius / 2)
  let V : CircularRegion :=
    ⟨U.center + displacement, U.radius / 2, halfRadiusPos⟩
  let W : CircularRegion :=
    ⟨U.center - displacement, U.radius / 2, halfRadiusPos⟩
  -- The displacement has exactly half the original radius.
  have displacementNorm : ‖displacement‖ = U.radius / 2 := by
    rw [show displacement = EuclideanSpace.single 0 (U.radius / 2) by rfl]
    rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos halfRadiusPos]
  have centerVDistance : dist V.center U.center = U.radius / 2 := by
    simp [V, dist_eq_norm, displacementNorm]
  have centerWDistance : dist W.center U.center = U.radius / 2 := by
    simp [W, displacementNorm]
  have centersDistance : dist V.center W.center = U.radius := by
    have displacementSum : displacement + displacement =
        EuclideanSpace.single 0 U.radius := by
      ext i
      fin_cases i
      · simp [displacement]
      · simp [displacement]
    rw [show dist V.center W.center = ‖displacement + displacement‖ by
      simp [V, W, dist_eq_norm]]
    rw [displacementSum, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos U.radius_pos]
  -- Each half-radius ball lies in `U` because its radius plus its center shift is `U.radius`.
  have VsubsetU : V.set ⊆ U.set := by
    rw [set_eq_ball, set_eq_ball]
    apply Metric.ball_subset_ball'
    rw [centerVDistance]
    simp [V]
  have WsubsetU : W.set ⊆ U.set := by
    rw [set_eq_ball, set_eq_ball]
    apply Metric.ball_subset_ball'
    rw [centerWDistance]
    simp [W]
  -- The two centers witness that neither shifted ball contains the other.
  have centerVMemV : V.center ∈ V.set := by
    rw [set_eq_ball]
    exact Metric.mem_ball_self halfRadiusPos
  have centerWMemW : W.center ∈ W.set := by
    rw [set_eq_ball]
    exact Metric.mem_ball_self halfRadiusPos
  have centerVNotMemW : V.center ∉ W.set := by
    rw [mem_set, centersDistance]
    simp [W]
    linarith
  have centerWNotMemV : W.center ∉ V.set := by
    rw [mem_set, dist_comm, centersDistance]
    simp [V]
    linarith
  -- The opposite center also witnesses that both inclusions in `U` are proper.
  have centerVMemU : V.center ∈ U.set := VsubsetU centerVMemV
  have centerWMemU : W.center ∈ U.set := WsubsetU centerWMemW
  have VltU : V < U := by
    rw [lt_iff]
    exact ssubset_of_subset_not_subset VsubsetU fun h ↦ centerWNotMemV (h centerWMemU)
  have WltU : W < U := by
    rw [lt_iff]
    exact ssubset_of_subset_not_subset WsubsetU fun h ↦ centerVNotMemW (h centerVMemU)
  have VneW : V ≠ W := by
    intro hVW
    apply centerVNotMemW
    rw [← hVW]
    exact centerVMemV
  have incomparable : ¬(V < W ∨ W < V) := by
    intro h
    rcases h with hVW | hWV
    · exact centerVNotMemW (((lt_iff V W).mp hVW).1 centerVMemV)
    · exact centerWNotMemV (((lt_iff W V).mp hWV).1 centerWMemW)
  exact ⟨V, W, VltU, WltU, VneW, incomparable⟩

end EuclideanPlane.CircularRegion

/-- The failure in Exercise 11.3 for Example 11.1: even after adjoining the distinguished
circular region, the proposed construction need not be a chain under proper inclusion. -/
theorem circularRegionComparables_not_isChain (U : EuclideanPlane.CircularRegion) :
    ¬IsChain (· < ·) (Set.insert U (strictComparables (· < ·) U)) := by
  -- Two incomparable proper subregions are both strictly comparable with `U`.
  obtain ⟨V, W, VltU, WltU, VneW, incomparable⟩ :=
    EuclideanPlane.CircularRegion.existsIncomparableSubregions U
  intro hChain
  have Vmem : V ∈ Set.insert U (strictComparables (· < ·) U) := by
    right
    rw [mem_strictComparables]
    exact Or.inr VltU
  have Wmem : W ∈ Set.insert U (strictComparables (· < ·) U) := by
    right
    rw [mem_strictComparables]
    exact Or.inr WltU
  exact incomparable (hChain Vmem Wmem VneW)

/-- The proposed construction in Example 11.2 is exactly the horizontal line
through the distinguished point. -/
theorem horizontalComparables_eq_line (p : ℝ × ℝ) :
    Set.insert p (strictComparables (· ≺ ·) p) = HorizontalOrder.line p.2 := by
  -- Comparable points have the same height, and distinct equal-height points are ordered by `x`.
  ext q
  simp only [HorizontalOrder.mem_line]
  constructor
  · intro h
    rcases h with rfl | h
    · rfl
    · exact (HorizontalOrder.comparable_sameHeight h).symm
  · intro sameHeight
    by_cases hqp : q = p
    · exact Or.inl hqp
    · right
      have firstCoordinatesNe : q.1 ≠ p.1 := by
        intro firstCoordinatesEq
        apply hqp
        exact Prod.ext firstCoordinatesEq sameHeight
      rcases lt_or_gt_of_ne firstCoordinatesNe with qltp | pltq
      · exact Or.inr ((HorizontalOrder.lt_iff q p).mpr ⟨sameHeight, qltp⟩)
      · exact Or.inl ((HorizontalOrder.lt_iff p q).mpr ⟨sameHeight.symm, pltq⟩)

/-- Exercise 11.3: In Example 11.2, adjoining the distinguished point to its
strictly comparable points produces the horizontal line through it, hence a maximal chain. -/
theorem horizontalComparables_isMaxChain (p : ℝ × ℝ) :
    IsMaxChain (· ≺ ·) (Set.insert p (strictComparables (· ≺ ·) p)) := by
  -- Replace the proposed set by the horizontal line already known to be maximal.
  rw [horizontalComparables_eq_line]
  exact HorizontalOrder.line_isMaxChain p.2
