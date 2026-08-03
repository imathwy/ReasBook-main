module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

public section

namespace Set

/-- A set is star convex if it contains a point from which every segment to
another point of the set remains in the set. -/
def IsStarConvex (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] (s : Set E) : Prop :=
  ∃ x ∈ s, StarConvex 𝕜 x s

/-- A specified star center exhibits a set as star convex. -/
theorem IsStarConvex.of_starConvex {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] {s : Set E} {x : E} (hx : x ∈ s)
    (hs : StarConvex 𝕜 x s) : IsStarConvex 𝕜 s :=
  ⟨x, hx, hs⟩

/-- A star-convex subset of a real topological vector space is simply connected. -/
theorem IsStarConvex.isSimplyConnected {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] {s : Set E}
    (hs : IsStarConvex ℝ s) : IsSimplyConnected s := by
  -- Choose a star center, whose contraction makes the subtype contractible.
  rcases hs with ⟨x, hx, hstar⟩
  -- Contractible spaces are simply connected through the canonical instance.
  exact @SimplyConnectedSpace.ofContractible s _ (hstar.contractibleSpace ⟨x, hx⟩)

end Set

/-- The union of the two nonnegative coordinate rays in `ℝ × ℝ`. -/
def nonnegativeCoordinateAxes : Set (ℝ × ℝ) :=
  (Set.Ici 0 ×ˢ ({0} : Set ℝ)) ∪ (({0} : Set ℝ) ×ˢ Set.Ici 0)

/-- Helper for Exercise 52.1: the nonnegative coordinate axes are star convex at the origin. -/
lemma nonnegativeCoordinateAxes_starConvex :
    Set.IsStarConvex ℝ nonnegativeCoordinateAxes := by
  -- Each ray is convex, hence star convex at their common origin.
  have hhorizontal : Convex ℝ (Set.Ici (0 : ℝ) ×ˢ ({0} : Set ℝ)) :=
    (convex_Ici 0).prod (convex_singleton 0)
  have hvertical : Convex ℝ (({0} : Set ℝ) ×ˢ Set.Ici (0 : ℝ)) :=
    (convex_singleton 0).prod (convex_Ici 0)
  have horiginHorizontal : (0, 0) ∈ (Set.Ici (0 : ℝ) ×ˢ ({0} : Set ℝ)) := by
    simp
  have horiginVertical : (0, 0) ∈ (({0} : Set ℝ) ×ˢ Set.Ici (0 : ℝ)) := by
    simp
  -- The union remains star convex because both pieces use the same center.
  refine Set.IsStarConvex.of_starConvex (Or.inl horiginHorizontal) ?_
  exact (hhorizontal.starConvex horiginHorizontal).union
    (hvertical.starConvex horiginVertical)

/-- Helper for Exercise 52.1: the nonnegative coordinate axes are not convex. -/
lemma nonnegativeCoordinateAxes_not_convex :
    ¬ Convex ℝ nonnegativeCoordinateAxes := by
  intro hconvex
  -- Convexity would force the midpoint of the two unit-axis points into the set.
  have hhorizontal : (1, 0) ∈ nonnegativeCoordinateAxes := by
    simp [nonnegativeCoordinateAxes]
  have hvertical : (0, 1) ∈ nonnegativeCoordinateAxes := by
    simp [nonnegativeCoordinateAxes]
  have hmidpoint := (convex_iff_add_mem.mp hconvex) hhorizontal hvertical
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  -- Its two positive coordinates place the midpoint on neither axis.
  norm_num [nonnegativeCoordinateAxes] at hmidpoint

/-- Exercise 52.1 (a). The nonnegative coordinate axes are star convex but not convex. -/
theorem nonnegativeCoordinateAxes_example :
    Set.IsStarConvex ℝ nonnegativeCoordinateAxes ∧ ¬ Convex ℝ nonnegativeCoordinateAxes := by
  -- Combine the shared-center construction with the midpoint obstruction.
  exact ⟨nonnegativeCoordinateAxes_starConvex, nonnegativeCoordinateAxes_not_convex⟩

/- Exercise 52.1 (b). -/
#check Set.IsStarConvex.isSimplyConnected
