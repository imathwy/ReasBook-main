module

public import Mathlib.Analysis.Convex.Segment
public import Topology_Munkres_2000.Book.Definition_26_5
public import Topology_Munkres_2000.Book.Example_37_1

public section

open Set

namespace MovingFocusEllipse

/-- The filled ellipse with foci `FixedFociEllipse.p`, `r` and focal-distance bound `c`. -/
def region (r : FixedFociEllipse.Plane) (c : ℝ) : Set FixedFociEllipse.Plane :=
  {x | dist x FixedFociEllipse.p + dist x r ≤ c}

/-- The family whose second focus ranges over the segment from `FixedFociEllipse.p` to
`FixedFociEllipse.q`. -/
def family : Set (Set FixedFociEllipse.Plane) :=
  {D | ∃ r ∈ segment ℝ FixedFociEllipse.p FixedFociEllipse.q, ∃ c,
    dist FixedFociEllipse.p r < c ∧ region r c ⊆ FixedFociEllipse.unitSquare ∧
      D = region r c}

/-- Membership in a moving-focus region in focal-distance form. -/
theorem mem_region (x r : FixedFociEllipse.Plane) (c : ℝ) :
    x ∈ region r c ↔ dist x FixedFociEllipse.p + dist x r ≤ c := by
  rfl

/-- At the endpoint `FixedFociEllipse.q`, a moving-focus region is the earlier fixed-foci
region. -/
theorem region_q (c : ℝ) : region FixedFociEllipse.q c = FixedFociEllipse.region c := by
  ext x
  rw [mem_region, FixedFociEllipse.mem_region]

/-- Membership in the moving-focus family, with the focus and bound exposed. -/
theorem mem_family (D : Set FixedFociEllipse.Plane) :
    D ∈ family ↔
      ∃ r ∈ segment ℝ FixedFociEllipse.p FixedFociEllipse.q, ∃ c,
        dist FixedFociEllipse.p r < c ∧ region r c ⊆ FixedFociEllipse.unitSquare ∧
          D = region r c := by
  rfl

/-- Every moving-focus region is closed. -/
theorem isClosed_region (r : FixedFociEllipse.Plane) (c : ℝ) : IsClosed (region r c) := by
  -- The focal-distance sum is continuous, so its sublevel set is closed.
  rw [region]
  exact isClosed_le
    ((continuous_id.dist continuous_const).add (continuous_id.dist continuous_const))
    continuous_const

/-- Every member of the moving-focus family is closed. -/
theorem isClosed_of_mem_family {D : Set FixedFociEllipse.Plane} (hD : D ∈ family) :
    IsClosed D := by
  -- Expose the region representing `D`, then use closedness of that region.
  obtain ⟨r, _, c, _, _, rfl⟩ := (mem_family D).mp hD
  exact isClosed_region r c

end MovingFocusEllipse

namespace FixedFociEllipse

/-- The first assertion of Example 37.3: the original elliptical family is contained in the
expanded family. -/
theorem family_subset_movingFocus : family ⊆ MovingFocusEllipse.family := by
  intro D hD
  -- Use `q`, the right endpoint of the focus segment, to recover the fixed-focus region.
  obtain ⟨c, hc, hsubset, rfl⟩ := (mem_family D).mp hD
  refine (MovingFocusEllipse.mem_family _).mpr
    ⟨q, right_mem_segment ℝ p q, c, hc, ?_, (MovingFocusEllipse.region_q c).symm⟩
  rwa [MovingFocusEllipse.region_q]

end FixedFociEllipse

namespace MovingFocusEllipse

/-- Helper for Example 37.3: `p` belongs to a moving-focus region whenever its focal
distance is strictly below the region bound. -/
private lemma p_mem_region_of_dist_lt (r : FixedFociEllipse.Plane) (c : ℝ)
    (h : dist FixedFociEllipse.p r < c) : FixedFociEllipse.p ∈ region r c := by
  -- At `p`, the first focal-distance term vanishes.
  rw [mem_region FixedFociEllipse.p r c, dist_self, zero_add]
  exact h.le

/-- Helper for Example 37.3: both coordinates of `FixedFociEllipse.p` equal `1 / 3`. -/
private lemma p_apply (i : Fin 2) : FixedFociEllipse.p i = (1 / 3 : ℝ) := by
  -- Route correction: use the owner computation theorem instead of unfolding imported data.
  exact FixedFociEllipse.p_apply i

/-- Helper for Example 37.3: membership in `FixedFociEllipse.unitSquare` is the
coordinatewise unit-interval condition. -/
private lemma mem_unitSquare (x : FixedFociEllipse.Plane) :
    x ∈ FixedFociEllipse.unitSquare ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  -- Cross the opaque set boundary through its owner membership theorem.
  exact FixedFociEllipse.mem_unitSquare x

/-- Helper for Example 37.3: `FixedFociEllipse.firstCoordinate` evaluates coordinate `0`. -/
private lemma firstCoordinate_eq_eval :
    FixedFociEllipse.firstCoordinate = fun x : FixedFociEllipse.Plane ↦ x 0 := by
  -- Upgrade the owner pointwise computation theorem to equality of functions.
  funext x
  exact FixedFociEllipse.firstCoordinate_apply x

/-- Helper for Example 37.3: `FixedFociEllipse.secondCoordinate` evaluates coordinate `1`. -/
private lemma secondCoordinate_eq_eval :
    FixedFociEllipse.secondCoordinate = fun x : FixedFociEllipse.Plane ↦ x 1 := by
  -- Upgrade the owner pointwise computation theorem to equality of functions.
  funext x
  exact FixedFociEllipse.secondCoordinate_apply x

/-- Helper for Example 37.3: a sufficiently small self-focus region around `p` lies in
the unit square. -/
private lemma region_p_subset_unitSquare {c : ℝ} (hc : c ≤ 2 / 3) :
    region FixedFociEllipse.p c ⊆ FixedFociEllipse.unitSquare := by
  intro x hx
  rw [mem_unitSquare]
  intro i
  -- The region inequality bounds each coordinate's distance from `1 / 3` by `1 / 3`.
  have hregion := (mem_region x FixedFociEllipse.p c).mp hx
  have hcoordinate := PiLp.dist_apply_le x FixedFociEllipse.p i
  have hcoordinate' : dist (x i) (FixedFociEllipse.p i) ≤ 1 / 3 := by
    linarith
  rw [Real.dist_eq, p_apply, abs_le] at hcoordinate'
  constructor
  · linarith
  · linarith

/-- Helper for Example 37.3: every positive scale supplies a self-focus region in the
moving-focus family. -/
private lemma smallRegion_mem_family {ε : ℝ} (hε : 0 < ε) :
    region FixedFociEllipse.p (min ε (1 / 3)) ∈ family := by
  -- Choose `p` itself as the second focus and use the preceding unit-square bound.
  refine (mem_family _).mpr
    ⟨FixedFociEllipse.p, left_mem_segment ℝ FixedFociEllipse.p FixedFociEllipse.q,
      min ε (1 / 3), ?_, ?_, rfl⟩
  · rw [dist_self]
    exact lt_min hε (by norm_num)
  · apply region_p_subset_unitSquare
    exact (min_le_right ε (1 / 3)).trans (by norm_num)

/-- Helper for Example 37.3: the closure of a coordinate image of a self-focus region
is contained in the corresponding closed ball. -/
private lemma closure_coordinateImage_region_p_subset_closedBall (i : Fin 2) (c : ℝ) :
    closure ((fun x : FixedFociEllipse.Plane ↦ x i) '' region FixedFociEllipse.p c) ⊆
      Metric.closedBall (FixedFociEllipse.p i) (c / 2) := by
  -- First bound the coordinate image itself; closedness of the ball then extends the bound.
  apply closure_minimal
  · rintro y ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall]
    have hregion := (mem_region x FixedFociEllipse.p c).mp hx
    have hcoordinate := PiLp.dist_apply_le x FixedFociEllipse.p i
    linarith
  · exact Metric.isClosed_closedBall

/-- The second assertion of Example 37.3: the expanded elliptical family has the finite
intersection property. -/
theorem finiteIntersectionProperty : family.FiniteIntersectionProperty := by
  rw [Set.FiniteIntersectionProperty.finset_iff]
  intro s hs
  -- The common point `p` witnesses every subfamily intersection, finite or otherwise.
  refine ⟨FixedFociEllipse.p, ?_⟩
  rw [Set.mem_iInter]
  intro D
  rw [Set.mem_iInter]
  intro hD
  obtain ⟨r, _, c, hpc, _, rfl⟩ := (mem_family D).mp (hs D hD)
  exact p_mem_region_of_dist_lt r c hpc

/-- Helper for Example 37.3: intersecting all closed coordinate images forces the
corresponding coordinate of `p`. -/
private lemma iInter_closure_coordinate (i : Fin 2) :
    (⋂ D ∈ family, closure ((fun x : FixedFociEllipse.Plane ↦ x i) '' D)) =
      {FixedFociEllipse.p i} := by
  apply Set.Subset.antisymm
  · intro y hy
    -- Membership in every shrinking self-focus region makes `y` arbitrarily close to `p i`.
    have hyEq : y = FixedFociEllipse.p i := by
      apply eq_of_forall_dist_le
      intro ε hε
      have hsmall := smallRegion_mem_family hε
      have hyClosure := Set.mem_iInter.mp
        (Set.mem_iInter.mp hy (region FixedFociEllipse.p (min ε (1 / 3)))) hsmall
      have hyBall := closure_coordinateImage_region_p_subset_closedBall
        i (min ε (1 / 3)) hyClosure
      rw [Metric.mem_closedBall] at hyBall
      have hmin : min ε (1 / 3) ≤ ε := min_le_left _ _
      linarith
    exact Set.mem_singleton_iff.mpr hyEq
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    -- The point `p` lies in every region, so its coordinate lies in every image closure.
    rw [Set.mem_iInter]
    intro D
    rw [Set.mem_iInter]
    intro hD
    apply subset_closure
    obtain ⟨r, _, c, hpc, _, rfl⟩ := (mem_family D).mp hD
    exact ⟨FixedFociEllipse.p, p_mem_region_of_dist_lt r c hpc, rfl⟩

/-- Example 37.3 (3). The first-coordinate closures force the value `1 / 3`. -/
theorem iInter_closure_firstCoordinate :
    (⋂ D ∈ family, closure (FixedFociEllipse.firstCoordinate '' D)) = {(1 / 3 : ℝ)} := by
  -- Specialize the generic coordinate result to coordinate `0`.
  rw [firstCoordinate_eq_eval]
  simpa only [p_apply] using iInter_closure_coordinate (0 : Fin 2)

/-- The fourth assertion of Example 37.3: the second-coordinate closures force the value
`1 / 3`. -/
theorem iInter_closure_secondCoordinate :
    (⋂ D ∈ family, closure (FixedFociEllipse.secondCoordinate '' D)) = {(1 / 3 : ℝ)} := by
  -- Specialize the generic coordinate result to coordinate `1`.
  rw [secondCoordinate_eq_eval]
  simpa only [p_apply] using iInter_closure_coordinate (1 : Fin 2)

/-- The fifth assertion of Example 37.3: the point `p` belongs to every member of the expanded
family. -/
theorem p_mem_of_mem_family {D : Set FixedFociEllipse.Plane} (hD : D ∈ family) :
    FixedFociEllipse.p ∈ D := by
  -- Expose the defining region and apply the common-point membership criterion.
  obtain ⟨r, _, c, hpc, _, rfl⟩ := (mem_family D).mp hD
  exact p_mem_region_of_dist_lt r c hpc

end MovingFocusEllipse

namespace FixedFociEllipse

/-- The sixth assertion of Example 37.3: the point `p` belongs to every member of the original
family. -/
theorem p_mem_of_mem_family {A : Set Plane} (hA : A ∈ family) : p ∈ A := by
  -- Regard the original region as a member of the expanded family.
  exact MovingFocusEllipse.p_mem_of_mem_family (family_subset_movingFocus hA)

end FixedFociEllipse
