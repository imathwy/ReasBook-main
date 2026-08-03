module

public import Topology_Munkres_2000.Book.Definition_3_6
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

/-- The equivalence relation in Example 3.3 on the Euclidean plane given by equality of
distance from the origin. -/
noncomputable def originDistanceSetoid : Setoid (EuclideanSpace ℝ (Fin 2)) :=
  Setoid.ker (fun p ↦ dist p 0)

/-- Two points are related by `originDistanceSetoid` exactly when their distances from the
origin agree. -/
theorem originDistanceSetoid_rel_iff (p q : EuclideanSpace ℝ (Fin 2)) :
    originDistanceSetoid p q ↔ dist p 0 = dist q 0 :=
  Setoid.ker_def

/-- The collection of positive-radius circles in the Euclidean plane centered at the origin. -/
def originCenteredCircles : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
  {s | ∃ r : ℝ, 0 < r ∧ s = Metric.sphere 0 r}

/-- A set is an origin-centered circle exactly when it is a metric sphere about the origin
with positive radius. -/
theorem mem_originCenteredCircles (s : Set (EuclideanSpace ℝ (Fin 2))) :
    s ∈ originCenteredCircles ↔ ∃ r : ℝ, 0 < r ∧ s = Metric.sphere 0 r :=
  Iff.rfl

/-- Helper for Example 3.3: the class represented by a point is the sphere through that point. -/
lemma originDistanceClass_eq_sphere (p : EuclideanSpace ℝ (Fin 2)) :
    {q | originDistanceSetoid q p} = Metric.sphere 0 (dist p 0) := by
  -- Compare membership using the distance characterization of the kernel relation.
  ext q
  simp only [Set.mem_setOf_eq, Metric.mem_sphere, originDistanceSetoid_rel_iff]

/-- Helper for Example 3.3: the equivalence class represented by the origin is the
singleton origin. -/
lemma originDistanceClass_zero :
    {q | originDistanceSetoid q 0} = ({0} : Set (EuclideanSpace ℝ (Fin 2))) := by
  -- The sphere of radius zero consists only of its center.
  rw [originDistanceClass_eq_sphere, dist_self, Metric.sphere_zero]

/-- Helper for Example 3.3: every positive-radius sphere centered at the origin is an
equivalence class. -/
lemma originCenteredSphere_mem_classes (r : ℝ) (hr : 0 < r) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) r ∈ originDistanceSetoid.classes := by
  -- Choose a point on the sphere, then identify its represented class with that sphere.
  obtain ⟨p, hp⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) r).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hr.le
  rw [Metric.mem_sphere] at hp
  rw [← hp, ← originDistanceClass_eq_sphere]
  exact originDistanceSetoid.mem_classes p

/-- Example 3.3: The equivalence classes are the positive-radius circles centered at the
origin together with the singleton origin. -/
theorem originDistanceSetoid_classes :
    originDistanceSetoid.classes =
      Set.insert ({0} : Set (EuclideanSpace ℝ (Fin 2))) originCenteredCircles := by
  -- Describe a represented class according to whether its representative is the origin.
  apply Set.Subset.antisymm
  · rintro s ⟨p, rfl⟩
    by_cases hp : p = 0
    · left
      simpa [hp] using originDistanceClass_zero
    · right
      rw [mem_originCenteredCircles]
      exact ⟨dist p 0, dist_pos.mpr hp, originDistanceClass_eq_sphere p⟩
  -- The singleton is the zero class, while each positive-radius circle has a representative.
  · intro s hs
    rcases hs with rfl | hs
    · rw [← originDistanceClass_zero]
      exact originDistanceSetoid.mem_classes 0
    · rw [mem_originCenteredCircles] at hs
      obtain ⟨r, hr, rfl⟩ := hs
      exact originCenteredSphere_mem_classes r hr
