module

public import Topology_Munkres_2000.Book.Example_30_5.Compactness
public import Mathlib.Analysis.Real.Cardinality

public section

namespace OrderedSquare

/-- The subspace `I × (0, 1)` of the ordered square. -/
-- Route correction: use the exposed lexicographic coordinates instead of the opaque `toProd` map.
def openHorizontalStrip : Set Iₒ² :=
  {p | 0 < (ofLex p).2 ∧ (ofLex p).2 < 1}

/-- Helper for Example 30.5: the vertical fiber of the open horizontal strip over `x`. -/
private def openHorizontalStripFiber (x : unitInterval) : Set openHorizontalStrip :=
  {p | (ofLex p.1).1 = x}

/-- Helper for Example 30.5: a strip fiber is the preimage of a lexicographic open interval. -/
private lemma openHorizontalStripFiber_eq_preimage_Ioo (x : unitInterval) :
    openHorizontalStripFiber x =
      (fun p : openHorizontalStrip ↦ p.1) ⁻¹'
        @Set.Ioo Iₒ² instLinearOrder.toPreorder (toLex (x, ⊥)) (toLex (x, ⊤)) := by
  -- Translate equality of first coordinates into the two strict lexicographic inequalities.
  ext p
  constructor
  · intro hp
    change (ofLex p.1).1 = x at hp
    subst x
    have hpStrip : 0 < (ofLex p.1).2 ∧ (ofLex p.1).2 < 1 := p.2
    constructor
    · exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hpStrip.1⟩)
    · exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hpStrip.2⟩)
  · rintro ⟨hpLower, hpUpper⟩
    change (toLex (x, ⊥) : LexUnitSquare) < p.1 at hpLower
    change p.1 < (toLex (x, ⊤) : LexUnitSquare) at hpUpper
    rcases Prod.Lex.lt_iff.mp hpLower with hpFirstLower | ⟨hpFirst, _⟩
    · rcases Prod.Lex.lt_iff.mp hpUpper with hpFirstUpper | ⟨hpFirstUpper, _⟩
      · exact (hpFirstLower.trans hpFirstUpper).false.elim
      · exact (hpFirstLower.trans_eq hpFirstUpper).false.elim
    · rcases Prod.Lex.lt_iff.mp hpUpper with hpFirstUpper | ⟨_, _⟩
      · exact (hpFirst.trans_lt hpFirstUpper).false.elim
      · change (ofLex p.1).1 = x
        exact hpFirst.symm

/-- Helper for Example 30.5: every vertical fiber of the strip is open. -/
private lemma openHorizontalStripFiber_isOpen (x : unitInterval) :
    IsOpen (openHorizontalStripFiber x) := by
  -- Pull the canonical open interval back along the subtype inclusion.
  rw [openHorizontalStripFiber_eq_preimage_Ioo]
  exact isOpen_Ioo.preimage continuous_subtype_val

/-- Helper for Example 30.5: the vertical fibers cover the open horizontal strip. -/
private lemma iUnion_openHorizontalStripFiber :
    (⋃ x : unitInterval, openHorizontalStripFiber x) =
      (Set.univ : Set openHorizontalStrip) := by
  -- Each point belongs to the fiber indexed by its first coordinate.
  ext p
  constructor
  · intro _
    exact Set.mem_univ p
  · intro _
    apply Set.mem_iUnion.mpr
    exact ⟨(ofLex p.1).1, rfl⟩

/-- Helper for Example 30.5: any subfamily covering the strip contains every fiber index. -/
private lemma eq_univ_of_openHorizontalStripFiber_cover {s : Set unitInterval}
    (hcover : (Set.univ : Set openHorizontalStrip) ⊆
      ⋃ x ∈ s, openHorizontalStripFiber x) :
    s = Set.univ := by
  -- Test the cover at an interior point of the fiber over an arbitrary index.
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    have hhalfMem : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      norm_num
    let y : unitInterval := ⟨1 / 2, hhalfMem⟩
    have hy : (0 : unitInterval) < y ∧ y < 1 := by
      constructor
      · apply Subtype.mk_lt_mk.mpr
        norm_num [y]
      · apply Subtype.mk_lt_mk.mpr
        norm_num [y]
    have hpointMem : toLex (x, y) ∈ openHorizontalStrip := by
      change 0 < (ofLex (toLex (x, y))).2 ∧ (ofLex (toLex (x, y))).2 < 1
      simpa only [ofLex_toLex] using hy
    let p : openHorizontalStrip := ⟨toLex (x, y), hpointMem⟩
    have hpCover := hcover (Set.mem_univ p)
    rcases Set.mem_iUnion.mp hpCover with ⟨z, hpCover⟩
    rcases Set.mem_iUnion.mp hpCover with ⟨hz, hpFiber⟩
    have hxz : x = z := by
      change (ofLex (toLex (x, y))).1 = z at hpFiber
      simpa only [p, ofLex_toLex] using hpFiber
    simpa only [hxz] using hz

/- Example 30.5 (1): The ordered square is Lindelöf. -/
#check (inferInstance : LindelofSpace Iₒ²)

/-- Example 30.5 (2): The subspace `I × (0, 1)` of the ordered square is not Lindelöf. -/
instance instNonLindelofSpaceOpenHorizontalStrip :
    NonLindelofSpace openHorizontalStrip := by
  -- A hypothetical Lindelöf cover reduction would make all fiber indices countable.
  refine ⟨?_⟩
  intro hLindelof
  obtain ⟨s, hsCountable, hsCover⟩ := hLindelof.elim_countable_subcover
    openHorizontalStripFiber openHorizontalStripFiber_isOpen
    iUnion_openHorizontalStripFiber.symm.subset
  have hsUniv : s = Set.univ := eq_univ_of_openHorizontalStripFiber_cover hsCover
  have hUnitInterval : Countable unitInterval := by
    apply Set.countable_univ_iff.mp
    simpa only [hsUniv] using hsCountable
  have hRealInterval : (Set.Icc (0 : ℝ) 1).Countable :=
    Set.countable_coe_iff.mp hUnitInterval
  have hle : (1 : ℝ) ≤ 0 := Cardinal.Real.Icc_countable_iff.mp hRealInterval
  exact (not_le_of_gt zero_lt_one) hle

/-- The ordered square with its horizontal boundary edges removed is not Lindelöf. -/
theorem openHorizontalStrip_notLindelof : ¬ LindelofSpace openHorizontalStrip := by
  -- The companion proposition is exactly the instance proved above.
  exact not_LindelofSpace_iff.mpr inferInstance

end OrderedSquare
