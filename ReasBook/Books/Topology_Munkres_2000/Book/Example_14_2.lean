module

public import Topology_Munkres_2000.Book.Example_3_11.Order
public import Mathlib.Topology.Order.Basic
import Topology_Munkres_2000.Book.Remark_14_2

public section

#synth NoMinOrder LexPlane
#synth NoMaxOrder LexPlane

/-- Helper for Example 14.2: every point of a lexicographic open interval admits
same-fiber endpoints that remain inside the interval. -/
private lemma exists_vertical_bounds_in_lexInterval {p : ℝ × ℝ}
    {lower upper : LexPlane} (hlower : lower < toLex p) (hupper : toLex p < upper) :
    ∃ b d : ℝ, b < p.2 ∧ p.2 < d ∧
      lower < toLex (p.1, b) ∧ toLex (p.1, d) < upper := by
  -- Normalize the endpoints to ordinary pairs, then split the two lexicographic comparisons.
  rw [← toLex_ofLex lower] at hlower
  rw [← toLex_ofLex upper] at hupper
  rcases Prod.Lex.toLex_lt_toLex.mp hlower with hLowerFirst | ⟨hLowerFirst, hLowerSecond⟩
  · obtain ⟨b, hb⟩ := exists_lt p.2
    have hLowerEndpoint : toLex (ofLex lower) < toLex (p.1, b) :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl hLowerFirst)
    rcases Prod.Lex.toLex_lt_toLex.mp hupper with hUpperFirst | ⟨hUpperFirst, hUpperSecond⟩
    · obtain ⟨d, hd⟩ := exists_gt p.2
      have hUpperEndpoint : toLex (p.1, d) < toLex (ofLex upper) :=
        Prod.Lex.toLex_lt_toLex.mpr (Or.inl hUpperFirst)
      exact ⟨b, d, hb, hd, hLowerEndpoint, hUpperEndpoint⟩
    · obtain ⟨d, hd, hdUpper⟩ := exists_between hUpperSecond
      have hUpperEndpoint : toLex (p.1, d) < toLex (ofLex upper) :=
        Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hUpperFirst, hdUpper⟩)
      exact ⟨b, d, hb, hd, hLowerEndpoint, hUpperEndpoint⟩
  · obtain ⟨b, hLowerB, hb⟩ := exists_between hLowerSecond
    have hLowerEndpoint : toLex (ofLex lower) < toLex (p.1, b) :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hLowerFirst, hLowerB⟩)
    rcases Prod.Lex.toLex_lt_toLex.mp hupper with hUpperFirst | ⟨hUpperFirst, hUpperSecond⟩
    · obtain ⟨d, hd⟩ := exists_gt p.2
      have hUpperEndpoint : toLex (p.1, d) < toLex (ofLex upper) :=
        Prod.Lex.toLex_lt_toLex.mpr (Or.inl hUpperFirst)
      exact ⟨b, d, hb, hd, hLowerEndpoint, hUpperEndpoint⟩
    · obtain ⟨d, hd, hdUpper⟩ := exists_between hUpperSecond
      have hUpperEndpoint : toLex (p.1, d) < toLex (ofLex upper) :=
        Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hUpperFirst, hdUpper⟩)
      exact ⟨b, d, hb, hd, hLowerEndpoint, hUpperEndpoint⟩

/-- Helper for Example 14.2: membership in a same-fiber lexicographic interval is
exactly membership in the corresponding real open interval. -/
private lemma toLex_mem_verticalIoo_iff (a b y d : ℝ) :
    toLex (a, y) ∈ Set.Ioo (toLex (a, b)) (toLex (a, d)) ↔ b < y ∧ y < d := by
  -- Both endpoint comparisons have equal first coordinates.
  simp only [Set.mem_Ioo, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, false_or, true_and]

/-- Example 14.2: In the dictionary-ordered real plane, the open intervals whose
endpoints have the same first coordinate form a basis for the order topology. -/
theorem lexicographicPlane_verticalIntervals_isTopologicalBasis
    [TopologicalSpace LexPlane] [OrderTopology LexPlane] :
    TopologicalSpace.IsTopologicalBasis
      {s | ∃ a b d : ℝ, b < d ∧ s = Set.Ioo (toLex (a, b)) (toLex (a, d))} := by
  have openIntervals_isTopologicalBasis :
      TopologicalSpace.IsTopologicalBasis (OrderTopology.openIntervals LexPlane) := by
    rw [← OrderTopology.basis_eq_openIntervals LexPlane]
    exact OrderTopology.isTopologicalBasis_basis
  refine openIntervals_isTopologicalBasis.isTopologicalBasis_of_exists_subset ?_ ?_
  · rintro _ ⟨a, b, d, _, rfl⟩
    exact isOpen_Ioo
  · -- Refine an arbitrary interval at a chosen point by a smaller interval in its vertical fiber.
    rintro _ hs x hx
    rcases OrderTopology.mem_openIntervals.mp hs with ⟨lower, upper, _, rfl⟩
    rw [← toLex_ofLex x] at hx
    obtain ⟨b, d, hb, hd, hLowerEndpoint, hUpperEndpoint⟩ :=
      exists_vertical_bounds_in_lexInterval hx.1 hx.2
    refine ⟨Set.Ioo (toLex ((ofLex x).1, b)) (toLex ((ofLex x).1, d)), ?_, ?_, ?_⟩
    · exact ⟨(ofLex x).1, b, d, hb.trans hd, rfl⟩
    · exact (toLex_mem_verticalIoo_iff (ofLex x).1 b (ofLex x).2 d).mpr ⟨hb, hd⟩
    · exact Set.Ioo_subset_Ioo hLowerEndpoint.le hUpperEndpoint.le
