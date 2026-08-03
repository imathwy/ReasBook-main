module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Definition_61_4.ClosedCurve
public import Topology_Munkres_2000.Book.Example_24_7.Connectedness
public import Topology_Munkres_2000.Book.Theorem_61_4
public import Mathlib.Analysis.Convex.Topology

public section

open Set

namespace TopologistsSineCurve

/-- Helper for Exercise 61.2: the topologist's sine-curve carrier is compact. -/
private lemma carrier_isCompact : IsCompact carrier := by
  -- Enclose the graph in a compact rectangle and then pass to its closure.
  have hrectangle : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hcurve : curve ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    rintro p ⟨x, hx, rfl⟩
    exact ⟨⟨hx.1.le, hx.2⟩, Real.neg_one_le_sin _, Real.sin_le_one _⟩
  exact hrectangle.of_isClosed_subset isClosed_closure
    (closure_minimal hcurve hrectangle.isClosed)

/-- Helper for Exercise 61.2: every real line segment in the plane is compact. -/
private lemma segment_isCompact (a b : ℝ × ℝ) : IsCompact (segment ℝ a b) := by
  -- Identify the segment with the convex hull of its finite endpoint set.
  rw [← convexHull_pair]
  exact ((Set.finite_singleton b).insert a).isCompact_convexHull ℝ

/-- Helper for Exercise 61.2: every real line segment in the plane is connected. -/
private lemma segment_isConnected (a b : ℝ × ℝ) : IsConnected (segment ℝ a b) := by
  -- Convexity and the left endpoint provide connectedness and nonemptiness.
  exact (convex_segment a b).isConnected ⟨a, left_mem_segment ℝ a b⟩

/-- Helper for Exercise 61.2: the added three-segment broken line is compact. -/
private lemma brokenLine_isCompact : IsCompact brokenLine := by
  -- Compactness is preserved by the two finite unions of segments.
  have hbroken : brokenLine =
      segment ℝ (0, -1) (0, -2) ∪ (segment ℝ (0, -2) (1, -2) ∪
        segment ℝ (1, -2) (1, Real.sin 1)) := by
    ext p
    rw [mem_brokenLine_iff]
    simp only [mem_union]
  rw [hbroken]
  exact (segment_isCompact (0, -1) (0, -2)).union
    ((segment_isCompact (0, -2) (1, -2)).union
      (segment_isCompact (1, -2) (1, Real.sin 1)))

/-- Helper for Exercise 61.2: the added three-segment broken line is connected. -/
private lemma brokenLine_isConnected : IsConnected brokenLine := by
  -- Join the last two segments at `(1, -2)`, then attach the first at `(0, -2)`.
  have hlast : IsConnected
      (segment ℝ ((0, -2) : ℝ × ℝ) (1, -2) ∪
        segment ℝ (1, -2) (1, Real.sin 1)) := by
    refine IsConnected.union ?_ (segment_isConnected (0, -2) (1, -2))
      (segment_isConnected (1, -2) (1, Real.sin 1))
    exact ⟨((1, -2) : ℝ × ℝ), right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  have hbroken : brokenLine =
      segment ℝ (0, -1) (0, -2) ∪ (segment ℝ (0, -2) (1, -2) ∪
        segment ℝ (1, -2) (1, Real.sin 1)) := by
    ext p
    rw [mem_brokenLine_iff]
    simp only [mem_union]
  rw [hbroken]
  refine IsConnected.union ?_ (segment_isConnected _ _) hlast
  exact ⟨((0, -2) : ℝ × ℝ), right_mem_segment ℝ _ _,
    Or.inl (left_mem_segment ℝ _ _)⟩

/-- Helper for Exercise 61.2: the carrier meets the broken line only at its two endpoints. -/
private lemma carrier_inter_brokenLine :
    carrier ∩ brokenLine = {((0, -1) : ℝ × ℝ), (1, Real.sin 1)} := by
  -- Analyze a common point using the graph/vertical and three-segment decompositions.
  ext p
  constructor
  · rintro ⟨hpCarrier, hpBroken⟩
    rw [carrier_eq_curve_union_vertical] at hpCarrier
    rw [mem_brokenLine_iff] at hpBroken
    rcases hpCarrier with hpCurve | hpVertical
    · rcases hpCurve with ⟨x, hx, rfl⟩
      rcases hpBroken with hpFirst | hpSecond | hpThird
      · have hcoords := Prod.segment_subset ((0, -1) : ℝ × ℝ) (0, -2) hpFirst
        simp only [segment_same] at hcoords
        exact False.elim (hx.1.ne' hcoords.1)
      · have hcoords := Prod.segment_subset ((0, -2) : ℝ × ℝ) (1, -2) hpSecond
        have hy : Real.sin (1 / x) = -2 := by
          simpa only [segment_same, mem_singleton_iff] using hcoords.2
        linarith [Real.neg_one_le_sin (1 / x)]
      · have hcoords := Prod.segment_subset ((1, -2) : ℝ × ℝ)
          (1, Real.sin 1) hpThird
        have hxOne : x = 1 := by
          simpa only [segment_same, mem_singleton_iff] using hcoords.1
        subst x
        simp
    · rw [mem_vertical_iff] at hpVertical
      rcases hpBroken with hpFirst | hpSecond | hpThird
      · have hcoords := Prod.segment_subset ((0, -1) : ℝ × ℝ) (0, -2) hpFirst
        have hySegment : p.2 ∈ segment ℝ (-1) (-2) := hcoords.2
        have hyUpper : p.2 ≤ -1 := by
          have horder : (-2 : ℝ) ≤ -1 := by norm_num
          rw [segment_eq_uIcc, uIcc_of_ge horder] at hySegment
          exact hySegment.2
        have hy : p.2 = -1 := le_antisymm hyUpper hpVertical.2.1
        left
        exact Prod.ext hpVertical.1 hy
      · have hcoords := Prod.segment_subset ((0, -2) : ℝ × ℝ) (1, -2) hpSecond
        have hy : p.2 = -2 := by
          simpa only [segment_same, mem_singleton_iff] using hcoords.2
        linarith [hpVertical.2.1]
      · have hcoords := Prod.segment_subset ((1, -2) : ℝ × ℝ)
          (1, Real.sin 1) hpThird
        have hxOne : p.1 = 1 := by
          simpa only [segment_same, mem_singleton_iff] using hcoords.1
        norm_num [hpVertical.1] at hxOne
  · intro hp
    rcases hp with rfl | rfl
    · constructor
      · rw [carrier_eq_curve_union_vertical]
        right
        rw [mem_vertical_iff]
        have hbounds : (-1 : ℝ) ∈ Icc (-1) 1 := by norm_num
        exact ⟨rfl, hbounds⟩
      · rw [mem_brokenLine_iff]
        exact Or.inl (left_mem_segment ℝ _ _)
    · constructor
      · rw [carrier_eq_curve_union_vertical]
        left
        refine ⟨1, ?_, ?_⟩
        · exact ⟨zero_lt_one, le_rfl⟩
        · norm_num
      · rw [mem_brokenLine_iff]
        exact Or.inr (Or.inr (right_mem_segment ℝ _ _))

end TopologistsSineCurve

/-- Helper for Exercise 61.2: a compact connected two-piece cover with a two-point
intersection separates the sphere after transport through a subspace homeomorphism. -/
private lemma separatesOfHomeomorphicCompactPairCover
    {Y : Type*} [TopologicalSpace Y]
    (C : Set (StandardSphere 2)) (e : C ≃ₜ Y)
    (A₁ A₂ : Set Y) (a b : Y)
    (ha_ne_b : a ≠ b) (hcover : A₁ ∪ A₂ = univ)
    (hinter : A₁ ∩ A₂ = {a, b})
    (hA₁compact : IsCompact A₁) (hA₂compact : IsCompact A₂)
    (hA₁connected : IsConnected A₁) (hA₂connected : IsConnected A₂) :
    C.Separates := by
  -- Embed the source space into the sphere through the inverse homeomorphism.
  let f : Y → StandardSphere 2 := fun y ↦ (e.symm y).val
  have hfContinuous : Continuous f := continuous_subtype_val.comp e.symm.continuous
  have hfInjective : Function.Injective f := by
    intro x y hxy
    apply e.symm.injective
    exact Subtype.ext hxy
  have hA₁closed : IsClosed (f '' A₁) :=
    (hA₁compact.image hfContinuous).isClosed
  have hA₂closed : IsClosed (f '' A₂) :=
    (hA₂compact.image hfContinuous).isClosed
  have hA₁connectedImage : IsConnected (f '' A₁) :=
    hA₁connected.image f hfContinuous.continuousOn
  have hA₂connectedImage : IsConnected (f '' A₂) :=
    hA₂connected.image f hfContinuous.continuousOn
  -- Injectivity preserves both the two-point intersection and distinctness.
  have hinterImage : f '' A₁ ∩ f '' A₂ = {f a, f b} := by
    rw [← image_inter hfInjective, hinter, image_pair]
  have hfa_ne_fb : f a ≠ f b := hfInjective.ne ha_ne_b
  have hseparates : (f '' A₁ ∪ f '' A₂).Separates :=
    union_separates_of_inter_pair (f '' A₁) (f '' A₂) (f a) (f b)
      hfa_ne_fb hinterImage hA₁closed hA₂closed hA₁connectedImage hA₂connectedImage
  -- The transported cover is exactly the original subspace `C`.
  have hfun : f = (Subtype.val : C → StandardSphere 2) ∘ e.symm := rfl
  have himageUniv : f '' (univ : Set Y) = C := by
    rw [image_univ, hfun, e.symm.surjective.range_comp, Subtype.range_val]
  have himageCover : f '' A₁ ∪ f '' A₂ = C := by
    rw [← image_union, hcover, himageUniv]
  rwa [himageCover] at hseparates

/-- Exercise 61.2: Every subspace of the standard two-sphere homeomorphic to the
closed topologist's sine curve separates the sphere. -/
theorem closedTopologistsSineCurve_separates
    (C : Set (StandardSphere 2))
    (hC : Nonempty (C ≃ₜ TopologistsSineCurve.ClosedSpace)) :
    C.Separates := by
  -- Pull the carrier and broken line back to the closed-curve subtype.
  obtain ⟨e⟩ := hC
  let A₁ : Set TopologistsSineCurve.ClosedSpace :=
    Subtype.val ⁻¹' TopologistsSineCurve.carrier
  let A₂ : Set TopologistsSineCurve.ClosedSpace :=
    Subtype.val ⁻¹' TopologistsSineCurve.brokenLine
  have hleftCarrier : ((0, -1) : ℝ × ℝ) ∈ TopologistsSineCurve.carrier := by
    rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
    right
    rw [TopologistsSineCurve.mem_vertical_iff]
    have hbounds : (-1 : ℝ) ∈ Icc (-1) 1 := by norm_num
    exact ⟨rfl, hbounds⟩
  have hrightCarrier : ((1, Real.sin 1) : ℝ × ℝ) ∈
      TopologistsSineCurve.carrier := by
    rw [TopologistsSineCurve.carrier_eq_curve_union_vertical]
    left
    refine ⟨1, ⟨zero_lt_one, le_rfl⟩, ?_⟩
    norm_num
  have hleftClosed : ((0, -1) : ℝ × ℝ) ∈ TopologistsSineCurve.closedCarrier :=
    (TopologistsSineCurve.mem_closedCarrier_iff _).2 (Or.inl hleftCarrier)
  have hrightClosed : ((1, Real.sin 1) : ℝ × ℝ) ∈
      TopologistsSineCurve.closedCarrier :=
    (TopologistsSineCurve.mem_closedCarrier_iff _).2 (Or.inl hrightCarrier)
  let a : TopologistsSineCurve.ClosedSpace := ⟨(0, -1), hleftClosed⟩
  let b : TopologistsSineCurve.ClosedSpace := ⟨(1, Real.sin 1), hrightClosed⟩
  -- Cache the ambient images, which expose the compactness and connectedness APIs.
  have hA₁image :
      (Subtype.val : TopologistsSineCurve.ClosedSpace → ℝ × ℝ) '' A₁ =
        TopologistsSineCurve.carrier := by
    dsimp [A₁]
    rw [Subtype.image_preimage_coe, inter_eq_right]
    intro p hp
    exact (TopologistsSineCurve.mem_closedCarrier_iff p).2 (Or.inl hp)
  have hA₂image :
      (Subtype.val : TopologistsSineCurve.ClosedSpace → ℝ × ℝ) '' A₂ =
        TopologistsSineCurve.brokenLine := by
    dsimp [A₂]
    rw [Subtype.image_preimage_coe, inter_eq_right]
    intro p hp
    exact (TopologistsSineCurve.mem_closedCarrier_iff p).2 (Or.inr hp)
  have hA₁compact : IsCompact A₁ := by
    rw [Subtype.isCompact_iff, hA₁image]
    exact TopologistsSineCurve.carrier_isCompact
  have hA₂compact : IsCompact A₂ := by
    rw [Subtype.isCompact_iff, hA₂image]
    exact TopologistsSineCurve.brokenLine_isCompact
  have hleftBroken : ((0, -1) : ℝ × ℝ) ∈ TopologistsSineCurve.brokenLine := by
    rw [TopologistsSineCurve.mem_brokenLine_iff]
    exact Or.inl (left_mem_segment ℝ _ _)
  have haA₁ : a ∈ A₁ := hleftCarrier
  have haA₂ : a ∈ A₂ := hleftBroken
  have hA₁connected : IsConnected A₁ := by
    refine ⟨⟨a, haA₁⟩, ?_⟩
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, hA₁image]
    exact TopologistsSineCurve.carrier_isConnected.isPreconnected
  have hA₂connected : IsConnected A₂ := by
    refine ⟨⟨a, haA₂⟩, ?_⟩
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, hA₂image]
    exact TopologistsSineCurve.brokenLine_isConnected.isPreconnected
  -- The subtype pieces cover the closed curve and retain the exact endpoint intersection.
  have hcover : A₁ ∪ A₂ = univ := by
    ext z
    change (z.val ∈ TopologistsSineCurve.carrier ∨
      z.val ∈ TopologistsSineCurve.brokenLine) ↔ True
    rw [iff_true]
    exact (TopologistsSineCurve.mem_closedCarrier_iff z.val).1 z.property
  have hinter : A₁ ∩ A₂ = {a, b} := by
    ext z
    change (z.val ∈ TopologistsSineCurve.carrier ∧
      z.val ∈ TopologistsSineCurve.brokenLine) ↔ z = a ∨ z = b
    rw [← mem_inter_iff, TopologistsSineCurve.carrier_inter_brokenLine]
    simp only [mem_insert_iff, mem_singleton_iff, Subtype.ext_iff]
    dsimp [a, b]
    rfl
  have ha_ne_b : a ≠ b := by
    intro hab
    have hfirst := congrArg (fun z : TopologistsSineCurve.ClosedSpace ↦ z.val.1) hab
    norm_num [a, b] at hfirst
  -- Apply the transport interface and Theorem 61.4 to the two source pieces.
  exact separatesOfHomeomorphicCompactPairCover C e A₁ A₂ a b ha_ne_b hcover hinter
    hA₁compact hA₂compact hA₁connected hA₂connected
