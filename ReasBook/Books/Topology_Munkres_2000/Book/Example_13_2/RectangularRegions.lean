module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Bases

public section

namespace EuclideanPlane

/-- The open rectangle with coordinate bounds `a < x 0 < b` and `c < x 1 < d`. -/
def openRectangle (a b c d : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | a < x 0 ∧ x 0 < b ∧ c < x 1 ∧ x 1 < d}

/-- Membership in an open rectangle is coordinatewise membership in its two open intervals. -/
@[simp] theorem mem_openRectangle (x : EuclideanSpace ℝ (Fin 2)) (a b c d : ℝ) :
    x ∈ openRectangle a b c d ↔ a < x 0 ∧ x 0 < b ∧ c < x 1 ∧ x 1 < d := by
  rfl

/-- The axis-parallel open rectangular regions in the Euclidean plane. -/
def rectangularRegions : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
  {U | ∃ a b c d, a < b ∧ c < d ∧ U = openRectangle a b c d}

/-- Membership in `rectangularRegions` is witnessed by strictly ordered coordinate bounds. -/
theorem mem_rectangularRegions (U : Set (EuclideanSpace ℝ (Fin 2))) :
    U ∈ rectangularRegions ↔
      ∃ a b c d, a < b ∧ c < d ∧ U = openRectangle a b c d := by
  rfl

/-- Helper for Example 13.2: an open rectangle is an intersection of coordinate half-spaces. -/
lemma openRectangle_eq_inter (a b c d : ℝ) :
    openRectangle a b c d =
      {x | a < x 0} ∩ {x | x 0 < b} ∩ {x | c < x 1} ∩ {x | x 1 < d} := by
  -- Extensionality reduces the set identity to the four defining inequalities.
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_openRectangle]
  tauto

/-- Helper for Example 13.2: every axis-parallel open rectangle is open. -/
lemma isOpen_openRectangle (a b c d : ℝ) : IsOpen (openRectangle a b c d) := by
  -- Rewrite the rectangle as an intersection of four open coordinate half-spaces.
  rw [openRectangle_eq_inter]
  -- Coordinate evaluation is continuous, so each half-space is open.
  have h0 : Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) :=
    @PiLp.continuous_apply 2 (Fin 2) (fun _ ↦ ℝ) _ 0
  have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1) :=
    @PiLp.continuous_apply 2 (Fin 2) (fun _ ↦ ℝ) _ 1
  exact (((isOpen_lt continuous_const h0).inter
    (isOpen_lt h0 continuous_const)).inter
    (isOpen_lt continuous_const h1)).inter
    (isOpen_lt h1 continuous_const)

/-- Helper for Example 13.2: a sufficiently narrow centered rectangle lies in a metric ball. -/
lemma openRectangle_centered_subset_ball (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) :
    openRectangle (x 0 - r / 3) (x 0 + r / 3)
      (x 1 - r / 3) (x 1 + r / 3) ⊆ Metric.ball x r := by
  intro y hy
  rw [Metric.mem_ball]
  -- Rectangle membership bounds each coordinate distance by one third of the radius.
  have hy' := (mem_openRectangle y (x 0 - r / 3) (x 0 + r / 3)
    (x 1 - r / 3) (x 1 + r / 3)).mp hy
  have h0 : dist (y 0) (x 0) < r / 3 := by
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [hy'.1]
    · linarith [hy'.2.1]
  have h1 : dist (y 1) (x 1) < r / 3 := by
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [hy'.2.2.1]
    · linarith [hy'.2.2.2]
  -- The two coordinate bounds give a strict bound on the Euclidean squared distance.
  have hdist_sq : dist y x ^ 2 = dist (y 0) (x 0) ^ 2 + dist (y 1) (x 1) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  have h0_nonneg : 0 ≤ dist (y 0) (x 0) := dist_nonneg
  have h1_nonneg : 0 ≤ dist (y 1) (x 1) := dist_nonneg
  have hdist_nonneg : 0 ≤ dist y x := dist_nonneg
  nlinarith

/-- The intersection of two rectangular regions is rectangular or empty. -/
theorem inter_mem_rectangularRegions_or_empty
    {U V : Set (EuclideanSpace ℝ (Fin 2))} (hU : U ∈ rectangularRegions)
    (hV : V ∈ rectangularRegions) :
    U ∩ V ∈ rectangularRegions ∨ U ∩ V = ∅ := by
  rcases hU with ⟨a, b, c, d, hab, hcd, rfl⟩
  rcases hV with ⟨e, f, g, h, hef, hgh, rfl⟩
  by_cases hx : max a e < min b f
  · by_cases hy : max c g < min d h
    · left
      refine ⟨max a e, min b f, max c g, min d h, hx, hy, ?_⟩
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, openRectangle]
      constructor
      · rintro ⟨⟨ha, hb, hc, hd⟩, he, hf, hg, hh⟩
        exact ⟨(max_lt_iff).2 ⟨ha, he⟩, (lt_min_iff).2 ⟨hb, hf⟩,
          (max_lt_iff).2 ⟨hc, hg⟩, (lt_min_iff).2 ⟨hd, hh⟩⟩
      · rintro ⟨hae, hbf, hcg, hdh⟩
        exact ⟨⟨(max_lt_iff.mp hae).1, (lt_min_iff.mp hbf).1,
          (max_lt_iff.mp hcg).1, (lt_min_iff.mp hdh).1⟩,
          (max_lt_iff.mp hae).2, (lt_min_iff.mp hbf).2,
          (max_lt_iff.mp hcg).2, (lt_min_iff.mp hdh).2⟩
    · right
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false, openRectangle]
      rintro ⟨⟨_, _, hc, hd⟩, _, _, hg, hh⟩
      exact hy (lt_trans ((max_lt_iff).2 ⟨hc, hg⟩) ((lt_min_iff).2 ⟨hd, hh⟩))
  · right
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, openRectangle]
    rintro ⟨⟨ha, hb, _, _⟩, he, hf, _, _⟩
    exact hx (lt_trans ((max_lt_iff).2 ⟨ha, he⟩) ((lt_min_iff).2 ⟨hb, hf⟩))

end EuclideanPlane
