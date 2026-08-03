module

public import Topology_Munkres_2000.Book.Example_24_1.LinearContinuum
public import Topology_Munkres_2000.Book.Definition_24_3.PathConnectedness
public import Topology_Munkres_2000.Book.Theorem_24_1
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Topology.Bases

public section

namespace OrderedSquare

/- Example 24.6 (1): The ordered square is connected because it is a linear continuum. -/
#synth ConnectedSpace OrderedSquare

/-- Helper for Example 24.6: the canonical parametrization of a vertical fiber. -/
private def verticalMap (x : unitInterval) : unitInterval → OrderedSquare :=
  fun y ↦ toLex (x, y)

/-- Helper for Example 24.6: the interior of a vertical fiber is a lexicographic open interval. -/
private lemma verticalFiberInterior_eq_Ioo (x : unitInterval) :
    {q : OrderedSquare | q.1 = x ∧ q.2 ∈ Set.Ioo (⊥ : unitInterval) ⊤} =
      @Set.Ioo OrderedSquare instLinearOrder.toPreorder
        (verticalMap x ⊥) (verticalMap x ⊤) := by
  -- Strict lexicographic comparison fixes the first coordinate and bounds the second.
  ext q
  constructor
  · rintro ⟨hq_first, hq_second⟩
    subst x
    constructor
    · change (toLex (q.1, ⊥) : LexUnitSquare) < q
      exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hq_second.1⟩)
    · change q < (toLex (q.1, ⊤) : LexUnitSquare)
      exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hq_second.2⟩)
  · rintro ⟨hq_lower, hq_upper⟩
    change (toLex (x, ⊥) : LexUnitSquare) < q at hq_lower
    change q < (toLex (x, ⊤) : LexUnitSquare) at hq_upper
    have hq_lower' := Prod.Lex.lt_iff.mp hq_lower
    have hq_upper' := Prod.Lex.lt_iff.mp hq_upper
    rcases hq_lower' with hq_lower | ⟨hq_first, hq_second_lower⟩
    · rcases hq_upper' with hq_upper | ⟨hq_first, _⟩
      · exact (hq_lower.trans hq_upper).false.elim
      · exact (hq_lower.trans_eq hq_first).false.elim
    · rcases hq_upper' with hq_upper | ⟨_, hq_second_upper⟩
      · exact (hq_first.trans_lt hq_upper).false.elim
      · exact ⟨hq_first.symm, hq_second_lower, hq_second_upper⟩

/-- Helper for Example 24.6: joined points cannot have strictly increasing first coordinates. -/
private lemma not_joined_of_first_lt {p q : OrderedSquare} (hpq : p.1 < q.1) :
    ¬ Joined p q := by
  -- A joining path would meet every vertical fiber indexed between the endpoint coordinates.
  intro hpq_joined
  classical
  let γ : Path p q := hpq_joined.somePath
  let xUnit (x : Set.Ioo (p.1 : ℝ) q.1) : unitInterval :=
    ⟨x, ⟨p.1.property.1.trans x.property.1.le, x.property.2.le.trans q.1.property.2⟩⟩
  let slice (x : Set.Ioo (p.1 : ℝ) q.1) : Set unitInterval :=
    γ ⁻¹' @Set.Ioo OrderedSquare instLinearOrder.toPreorder
      (verticalMap (xUnit x) ⊥) (verticalMap (xUnit x) ⊤)
  -- Continuity makes every vertical slice open in the path domain.
  have hslice_open (x : Set.Ioo (p.1 : ℝ) q.1) : IsOpen (slice x) := by
    exact γ.continuous.isOpen_preimage _ isOpen_Ioo
  -- Connectedness of the path range forces it through an interior point of each slice.
  have hslice_nonempty (x : Set.Ioo (p.1 : ℝ) q.1) : (slice x).Nonempty := by
    obtain ⟨y, hy⟩ := Set.nonempty_Ioo.mpr (bot_lt_top : (⊥ : unitInterval) < ⊤)
    have hp_range : p ∈ Set.range γ := ⟨0, γ.source⟩
    have hq_range : q ∈ Set.range γ := ⟨1, γ.target⟩
    have hpoint_lower : p ≤ verticalMap (xUnit x) y := by
      change p ≤ (toLex (xUnit x, y) : LexUnitSquare)
      exact Prod.Lex.le_iff.mpr (Or.inl x.property.1)
    have hpoint_upper : verticalMap (xUnit x) y ≤ q := by
      change (toLex (xUnit x, y) : LexUnitSquare) ≤ q
      exact Prod.Lex.le_iff.mpr (Or.inl x.property.2)
    have hpoint_range : verticalMap (xUnit x) y ∈ Set.range γ :=
      (isPreconnected_range γ.continuous).Icc_subset hp_range hq_range
        ⟨hpoint_lower, hpoint_upper⟩
    obtain ⟨t, ht⟩ := hpoint_range
    refine ⟨t, ?_⟩
    change γ t ∈ @Set.Ioo OrderedSquare instLinearOrder.toPreorder
      (verticalMap (xUnit x) ⊥) (verticalMap (xUnit x) ⊤)
    rw [ht]
    constructor
    · unfold verticalMap
      exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hy.1⟩)
    · unfold verticalMap
      exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hy.2⟩)
  -- Distinct first coordinates give disjoint vertical fibers and hence disjoint slices.
  have hslice_disjoint : Pairwise (Function.onFun Disjoint slice) := by
    intro x y hxy
    unfold Function.onFun
    rw [Set.disjoint_left]
    intro t htx hty
    change γ t ∈ @Set.Ioo OrderedSquare instLinearOrder.toPreorder
      (verticalMap (xUnit x) ⊥) (verticalMap (xUnit x) ⊤) at htx
    change γ t ∈ @Set.Ioo OrderedSquare instLinearOrder.toPreorder
      (verticalMap (xUnit y) ⊥) (verticalMap (xUnit y) ⊤) at hty
    rw [← verticalFiberInterior_eq_Ioo] at htx hty
    apply hxy
    apply Subtype.ext
    simpa only [xUnit] using congrArg Subtype.val (htx.1.symm.trans hty.1)
  -- A separable interval has only countably many such open sets, contradicting the real interval.
  have hcountable : Countable (Set.Ioo (p.1 : ℝ) q.1) :=
    hslice_disjoint.countable_of_isOpen_disjoint hslice_open hslice_nonempty
  have hreal_countable : (Set.Ioo (p.1 : ℝ) q.1).Countable :=
    Set.countable_coe_iff.mp hcountable
  exact (not_le_of_gt hpq) ((Cardinal.Real.Ioo_countable_iff).mp hreal_countable)

/-- Example 24.6 (2): The ordered square is not path connected in the sense of Definition 24.3. -/
theorem notPathPreconnected : ¬PathPreconnectedSpace OrderedSquare := by
  -- Path preconnectedness would join the bottom-left and top-right corners.
  intro h
  let p : OrderedSquare := toLex ((⊥ : unitInterval), (⊥ : unitInterval))
  let q : OrderedSquare := toLex ((⊤ : unitInterval), (⊤ : unitInterval))
  apply not_joined_of_first_lt (p := p) (q := q)
  · change (⊥ : unitInterval) < ⊤
    exact bot_lt_top
  · exact h.joined p q

end OrderedSquare
