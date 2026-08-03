module

public import Topology_Munkres_2000.Book.Example_3_11.Order
public import Topology_Munkres_2000.Book.Example_16_3.OrderedSquare

public section

open scoped Topology

namespace LexUnitSquare

/-- The coordinatewise order embedding of the lexicographic unit square into
the lexicographic plane. -/
def inclusion : LexUnitSquare ↪o LexPlane where
  toFun p := toLex ((ofLex p).1.1, (ofLex p).2.1)
  inj' := by
    intro p q h
    apply ofLex_inj.mp
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun x ↦ (ofLex x).1) h)
    · exact Subtype.ext (congrArg (fun x ↦ (ofLex x).2) h)
  map_rel_iff' := by
    intro p q
    change
      toLex ((ofLex p).1.1, (ofLex p).2.1) ≤
          toLex ((ofLex q).1.1, (ofLex q).2.1) ↔ p ≤ q
    rw [Prod.Lex.toLex_le_toLex, Prod.Lex.le_iff]
    simp only [Subtype.ext_iff, Subtype.coe_lt_coe, Subtype.coe_le_coe]

/-- Helper for Example 16.3: `inclusion` sends a square point to the plane point
with the same two real coordinates. -/
lemma inclusion_apply (p : LexUnitSquare) :
    inclusion p = toLex (((ofLex p).1 : ℝ), ((ofLex p).2 : ℝ)) := by
  -- Expose only the value field of the bundled order embedding.
  rfl

/-- The upper half of the vertical segment in `LexUnitSquare` whose first
coordinate is `1 / 2`. -/
def upperVerticalSegment : Set LexUnitSquare :=
  {p | (ofLex p).1.1 = (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < (ofLex p).2.1}

/-- Helper for Example 16.3: the upper vertical segment is the inverse image of
an open interval in the lexicographic plane. -/
private lemma inclusion_preimage_Ioo_eq_upperVerticalSegment :
    inclusion ⁻¹' Set.Ioo
        (toLex ((1 / 2 : ℝ), (1 / 2 : ℝ)))
        (toLex ((1 / 2 : ℝ), (2 : ℝ))) =
      upperVerticalSegment := by
  -- Reduce both ambient lexicographic comparisons to coordinate inequalities.
  ext p
  simp only [Set.mem_preimage, Set.mem_Ioo, inclusion_apply,
    Prod.Lex.toLex_lt_toLex, upperVerticalSegment, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hlower, hupper⟩
    rcases hlower with hfirst | ⟨hfirst, hsecond⟩
    · rcases hupper with hupper | ⟨hupper, -⟩
      · exact (lt_asymm hfirst hupper).elim
      · exact (ne_of_lt hfirst hupper.symm).elim
    · exact ⟨hfirst.symm, hsecond⟩
  · rintro ⟨hfirst, hsecond⟩
    -- Every second coordinate of the square is at most `1`, hence below `2`.
    have hsecondUpper : ((ofLex p).2 : ℝ) < 2 := by
      linarith [(ofLex p).2.2.2]
    exact ⟨Or.inr ⟨hfirst.symm, hsecond⟩, Or.inr ⟨hfirst, hsecondUpper⟩⟩

/-- Helper for Example 16.3: the upper vertical segment separates the induced
topology from the intrinsic order topology. -/
private lemma upperVerticalSegmentTopologyWitness :
    IsOpen[TopologicalSpace.induced inclusion (Preorder.topology LexPlane)]
        upperVerticalSegment ∧
      ¬ IsOpen[Preorder.topology LexUnitSquare] upperVerticalSegment := by
  constructor
  · -- Realize the segment as the induced preimage of an ambient open interval.
    letI : TopologicalSpace LexPlane := Preorder.topology LexPlane
    letI : OrderTopology LexPlane := ⟨rfl⟩
    rw [← inclusion_preimage_Ioo_eq_upperVerticalSegment]
    exact isOpen_induced isOpen_Ioo
  · -- Test intrinsic openness at the top of the fiber over `1 / 2`.
    letI : TopologicalSpace LexUnitSquare := Preorder.topology LexUnitSquare
    letI : OrderTopology LexUnitSquare := ⟨rfl⟩
    have hmidpoint : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      norm_num
    let midpoint : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, hmidpoint⟩
    let center : LexUnitSquare := toLex (midpoint, ⊤)
    have hcenterSegment : center ∈ upperVerticalSegment := by
      norm_num [center, midpoint, upperVerticalSegment]
    have hlower : ∃ l : LexUnitSquare, l < center := by
      refine ⟨toLex (midpoint, ⊥), ?_⟩
      dsimp only [center]
      refine Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, ?_⟩)
      norm_num
    have hmidpoint_lt_one : (1 / 2 : ℝ) < 1 := by
      norm_num
    have hupper : ∃ u : LexUnitSquare, center < u := by
      refine ⟨toLex (⊤, ⊥), ?_⟩
      dsimp only [center]
      refine Prod.Lex.toLex_lt_toLex.mpr (Or.inl ?_)
      exact hmidpoint_lt_one
    intro hopen
    have hsegmentNhds : upperVerticalSegment ∈ 𝓝 center :=
      hopen.mem_nhds hcenterSegment
    obtain ⟨l, u, hcenterInterval, hinterval⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' hlower hupper).mp hsegmentNhds
    -- The upper endpoint of this interval must lie in a strictly later fiber.
    have hcenterUpper : center < u := hcenterInterval.2
    dsimp only [center] at hcenterUpper
    rw [← toLex_ofLex u] at hcenterUpper
    have hmidpoint_lt_uFirst : midpoint < (ofLex u).1 := by
      rcases Prod.Lex.toLex_lt_toLex.mp hcenterUpper with hfirst | ⟨-, hsecond⟩
      · exact hfirst
      · have hsecond_le_top : (ofLex u).2 ≤ (⊤ : Set.Icc (0 : ℝ) 1) := le_top
        exact (not_lt_of_ge hsecond_le_top hsecond).elim
    obtain ⟨x, hmidpointX, hxU⟩ := exists_between hmidpoint_lt_uFirst
    let q : LexUnitSquare := toLex (x, ⊥)
    have hcenterQ : center < q := by
      dsimp only [center, q]
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hmidpointX)
    have hqU : q < u := by
      dsimp only [q]
      rw [← toLex_ofLex u]
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hxU)
    -- The later-fiber point lies in the neighborhood but not in the segment.
    have hqInterval : q ∈ Set.Ioo l u :=
      ⟨hcenterInterval.1.trans hcenterQ, hqU⟩
    have hqSegment : q ∈ upperVerticalSegment := hinterval hqInterval
    have hqFirst : (x : ℝ) = 1 / 2 := by
      simpa only [upperVerticalSegment, q, ofLex_toLex, Set.mem_setOf_eq] using
        hqSegment.1
    have hxValue : (1 / 2 : ℝ) < x := hmidpointX
    exact (ne_of_gt hxValue) hqFirst

/- Example 16.3 (1): The lexicographic order on the unit square is the
restriction of the lexicographic order on the real plane. -/
#check inclusion

/-- Example 16.3 (2): The intrinsic order topology on the lexicographic unit
square differs from the topology induced from the lexicographic plane. -/
theorem topology_ne_induced :
    Preorder.topology LexUnitSquare ≠
      TopologicalSpace.induced inclusion (Preorder.topology LexPlane) := by
  -- Equality would transfer induced openness to the intrinsic topology.
  intro htopology
  apply upperVerticalSegmentTopologyWitness.2
  rw [htopology]
  exact upperVerticalSegmentTopologyWitness.1

/-- Example 16.3 (3): The upper vertical segment is open in the topology induced
from the order topology on the lexicographic plane. -/
theorem upperVerticalSegment_isOpen_induced :
    IsOpen[TopologicalSpace.induced inclusion (Preorder.topology LexPlane)]
      upperVerticalSegment := by
  -- Project the induced-open half of the separating witness.
  exact upperVerticalSegmentTopologyWitness.1

/-- Example 16.3 (4): The upper vertical segment is not open in the intrinsic
order topology on the lexicographic unit square. -/
theorem upperVerticalSegment_not_isOpen_order :
    ¬ IsOpen[Preorder.topology LexUnitSquare] upperVerticalSegment := by
  -- Project the intrinsic non-openness half of the separating witness.
  exact upperVerticalSegmentTopologyWitness.2

end LexUnitSquare
