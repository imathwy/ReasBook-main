module

public import Topology_Munkres_2000.Book.Definition_46_3.CompactBall

public section

open Set
open scoped CompactConvergence

universe u v

namespace Metric

variable {X : Type u} {Y : Type v} [PseudoMetricSpace Y]

/-- Helper for Exercise 46.12: pointwise triangle inequalities preserve boundedness of
distance images on a set. -/
private lemma bddAbove_distImage_of_triangle {C : Set X} {f g h : X → Y}
    (hfg : BddAbove ((fun x ↦ dist (f x) (g x)) '' C))
    (hgh : BddAbove ((fun x ↦ dist (g x) (h x)) '' C)) :
    BddAbove ((fun x ↦ dist (f x) (h x)) '' C) := by
  -- Add upper bounds for the two legs of the pointwise triangle inequality.
  obtain ⟨a, ha⟩ := hfg
  obtain ⟨b, hb⟩ := hgh
  refine ⟨a + b, ?_⟩
  intro d hd
  obtain ⟨x, hx, rfl⟩ := hd
  calc
    dist (f x) (h x) ≤ dist (f x) (g x) + dist (g x) (h x) := dist_triangle _ _ _
    _ ≤ a + b := add_le_add (ha ⟨x, hx, rfl⟩) (hb ⟨x, hx, rfl⟩)

/-- Helper for Exercise 46.12: the supremum distance on any set is nonnegative. -/
private lemma supDistOn_nonneg (C : Set X) (f g : X → Y) :
    0 ≤ supDistOn C f g := by
  -- Every value in the distance image is nonnegative, including when the image is empty.
  rw [supDistOn_eq_sSup]
  refine Real.sSup_nonneg ?_
  intro d hd
  obtain ⟨x, hx, rfl⟩ := hd
  exact dist_nonneg

/-- Helper for Exercise 46.12: bounded pointwise distance images give the triangle
inequality for `supDistOn`. -/
private lemma supDistOn_triangle {C : Set X} {f g h : X → Y}
    (hfg : BddAbove ((fun x ↦ dist (f x) (g x)) '' C))
    (hgh : BddAbove ((fun x ↦ dist (g x) (h x)) '' C)) :
    supDistOn C f h ≤ supDistOn C f g + supDistOn C g h := by
  -- Lift the pointwise triangle inequality through the three relevant suprema.
  have hfg_nonneg := supDistOn_nonneg C f g
  have hgh_nonneg := supDistOn_nonneg C g h
  rw [supDistOn_eq_sSup] at hfg_nonneg hgh_nonneg
  rw [supDistOn_eq_sSup, supDistOn_eq_sSup, supDistOn_eq_sSup]
  refine Real.sSup_le ?_ (add_nonneg hfg_nonneg hgh_nonneg)
  intro d hd
  obtain ⟨x, hx, rfl⟩ := hd
  calc
    dist (f x) (h x) ≤ dist (f x) (g x) + dist (g x) (h x) := dist_triangle _ _ _
    _ ≤ sSup ((fun y ↦ dist (f y) (g y)) '' C) +
        sSup ((fun y ↦ dist (g y) (h y)) '' C) :=
      add_le_add (le_csSup hfg ⟨x, hx, rfl⟩) (le_csSup hgh ⟨x, hx, rfl⟩)

/-- Exercise 46.12: If `g` belongs to the uniform ball on `C` centered at `f` with
radius `ε`, then the uniform ball centered at `g` with radius
`ε - supDistOn C f g` is contained in the original ball. The statement applies in
particular when `C` is compact, as in the compact-convergence basis. -/
theorem uniformBallOn_subset {C : Set X} {f g : X → Y} {ε : ℝ}
    (hg : g ∈ B_[C](f, ε)) :
    B_[C](g, ε - supDistOn C f g) ⊆ B_[C](f, ε) := by
  -- Expand ball membership, then control boundedness and the supremum separately.
  intro h hh
  rw [mem_uniformBallOn] at hg hh ⊢
  constructor
  · exact bddAbove_distImage_of_triangle hg.1 hh.1
  · calc
      supDistOn C f h ≤ supDistOn C f g + supDistOn C g h :=
        supDistOn_triangle hg.1 hh.1
      _ < ε := by
        -- The smaller radius was chosen to make this sum strictly below `ε`.
        simpa only [add_comm] using (lt_sub_iff_add_lt.mp hh.2)

end Metric
