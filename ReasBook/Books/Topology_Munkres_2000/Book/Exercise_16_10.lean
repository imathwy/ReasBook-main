module

public import Topology_Munkres_2000.Book.Exercise_16_9
public import Mathlib.Topology.UnitInterval

public section

open Prod.Lex

namespace UnitSquareTopology

/-- The product topology on the unit square `unitInterval × unitInterval`. -/
@[reducible] def product : TopologicalSpace (unitInterval × unitInterval) :=
  inferInstance

/-- The topology transported from the lexicographic order topology on the unit square. -/
@[reducible] def dictionary : TopologicalSpace (unitInterval × unitInterval) :=
  TopologicalSpace.induced toLex
    (Preorder.topology (Lex (unitInterval × unitInterval)))

/-- The topology inherited by the unit square from the lexicographically ordered real plane. -/
@[reducible] def ambientDictionarySubspace :
    TopologicalSpace (unitInterval × unitInterval) :=
  TopologicalSpace.induced
    (fun p ↦ ((p.1 : ℝ), (p.2 : ℝ)))
    RealPlaneTopology.dictionary

/-- Helper for Exercise 16.10: coordinatewise inclusion of the unit square reflects the
lexicographic strict order. -/
lemma lexSubtypeCoe_lt_iff {p q : Lex (unitInterval × unitInterval)} :
    toLex (((ofLex p).1 : ℝ), ((ofLex p).2 : ℝ)) <
      toLex (((ofLex q).1 : ℝ), ((ofLex q).2 : ℝ)) ↔ p < q := by
  -- Reduce both lexicographic comparisons to their coordinate formulas.
  rw [← toLex_ofLex p, ← toLex_ofLex q]
  simp only [Prod.Lex.toLex_lt_toLex, ofLex_toLex, Subtype.coe_lt_coe,
    Subtype.coe_injective.eq_iff]

/-- Helper for Exercise 16.10: the ambient dictionary subspace topology is finer than the
product topology on the unit square. -/
lemma ambientDictionarySubspace_le_product : ambientDictionarySubspace ≤ product := by
  -- First compare the ambient dictionary topology with the standard real product topology.
  unfold ambientDictionarySubspace product
  refine le_trans (induced_mono RealPlaneTopology.dictionary_lt_standardProduct.le) ?_
  -- The coordinate inclusion of the two subtype factors induces their product topology.
  have hInducing : Topology.IsInducing
      (Prod.map (fun x : unitInterval ↦ (x : ℝ)) (fun y : unitInterval ↦ (y : ℝ))) :=
    Topology.IsInducing.subtypeVal.prodMap Topology.IsInducing.subtypeVal
  have heq := hInducing.eq_induced
  have hmap : (Prod.map (fun x : unitInterval ↦ (x : ℝ))
      (fun y : unitInterval ↦ (y : ℝ))) = (fun p ↦ ((p.1 : ℝ), (p.2 : ℝ))) := by
    funext p
    rfl
  rw [← hmap, ← heq]

/-- Helper for Exercise 16.10: an upper lexicographic ray is open in the dictionary topology
on the real plane. -/
lemma ambientLexUpperRay_open (a : Lex (ℝ × ℝ)) :
    @IsOpen _ RealPlaneTopology.dictionary (toLex ⁻¹' Set.Ioi a) := by
  -- Refine each point of the ray to a same-fiber interval that remains above `a`.
  rw [@isOpen_iff_mem_nhds _ RealPlaneTopology.dictionary]
  intro p hp
  have ha : a < toLex p := hp
  obtain ⟨upper, hpUpper⟩ := exists_gt (toLex p)
  obtain ⟨lowerSecond, upperSecond, hlp, hpu, haLower, -⟩ :=
    RealPlaneTopology.exists_sameFiber_Ioo_subset ha hpUpper
  apply (RealPlaneTopology.dictionary_nhds_basis_verticalIntervals p).mem_iff.mpr
  refine ⟨(lowerSecond, upperSecond), ⟨hlp, hpu⟩, ?_⟩
  intro q hq
  have hqLower : toLex (p.1, lowerSecond) < toLex q :=
    Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hq.1.symm, hq.2.1⟩)
  exact lt_trans haLower hqLower

/-- Helper for Exercise 16.10: a lower lexicographic ray is open in the dictionary topology
on the real plane. -/
lemma ambientLexLowerRay_open (a : Lex (ℝ × ℝ)) :
    @IsOpen _ RealPlaneTopology.dictionary (toLex ⁻¹' Set.Iio a) := by
  -- Refine each point of the ray to a same-fiber interval that remains below `a`.
  rw [@isOpen_iff_mem_nhds _ RealPlaneTopology.dictionary]
  intro p hp
  have ha : toLex p < a := hp
  obtain ⟨lower, hLowerp⟩ := exists_lt (toLex p)
  obtain ⟨lowerSecond, upperSecond, hlp, hpu, -, hUpperA⟩ :=
    RealPlaneTopology.exists_sameFiber_Ioo_subset hLowerp ha
  apply (RealPlaneTopology.dictionary_nhds_basis_verticalIntervals p).mem_iff.mpr
  refine ⟨(lowerSecond, upperSecond), ⟨hlp, hpu⟩, ?_⟩
  intro q hq
  have hqFiberUpper : toLex q < toLex (p.1, upperSecond) :=
    Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hq.1, hq.2.2⟩)
  exact lt_trans hqFiberUpper hUpperA

/-- Helper for Exercise 16.10: the ambient dictionary subspace topology is finer than the
dictionary order topology intrinsic to the unit square. -/
lemma ambientDictionarySubspace_le_dictionary : ambientDictionarySubspace ≤ dictionary := by
  -- Check continuity into the unit-square order topology on its generating upper and lower rays.
  unfold ambientDictionarySubspace dictionary
  rw [← @continuous_iff_le_induced (unitInterval × unitInterval)
    (Lex (unitInterval × unitInterval)) toLex
    (TopologicalSpace.induced
      (fun p : unitInterval × unitInterval ↦ ((p.1 : ℝ), (p.2 : ℝ)))
      RealPlaneTopology.dictionary)
    (Preorder.topology (Lex (unitInterval × unitInterval)))]
  letI : TopologicalSpace (unitInterval × unitInterval) :=
    TopologicalSpace.induced
      (fun p : unitInterval × unitInterval ↦ ((p.1 : ℝ), (p.2 : ℝ)))
      RealPlaneTopology.dictionary
  letI : TopologicalSpace (Lex (unitInterval × unitInterval)) :=
    Preorder.topology (Lex (unitInterval × unitInterval))
  letI : OrderTopology (Lex (unitInterval × unitInterval)) := ⟨rfl⟩
  rw [OrderTopology.continuous_iff]
  intro a
  constructor
  · -- Pull back the corresponding ambient upper ray along the coordinate inclusion.
    rw [@isOpen_induced_iff (unitInterval × unitInterval) (ℝ × ℝ)
      RealPlaneTopology.dictionary]
    let realA : Lex (ℝ × ℝ) :=
      toLex (((ofLex a).1 : ℝ), ((ofLex a).2 : ℝ))
    refine ⟨toLex ⁻¹' Set.Ioi realA, ambientLexUpperRay_open realA, ?_⟩
    ext p
    simp only [Set.mem_preimage, Set.mem_Ioi]
    exact lexSubtypeCoe_lt_iff
  · -- Pull back the corresponding ambient lower ray along the coordinate inclusion.
    rw [@isOpen_induced_iff (unitInterval × unitInterval) (ℝ × ℝ)
      RealPlaneTopology.dictionary]
    let realA : Lex (ℝ × ℝ) :=
      toLex (((ofLex a).1 : ℝ), ((ofLex a).2 : ℝ))
    refine ⟨toLex ⁻¹' Set.Iio realA, ambientLexLowerRay_open realA, ?_⟩
    ext p
    simp only [Set.mem_preimage, Set.mem_Iio]
    exact lexSubtypeCoe_lt_iff

/-- Helper for Exercise 16.10: the open vertical interior of the left edge is dictionary-open
but not product-open. -/
lemma verticalInterior_open_dictionary_not_product :
    @IsOpen _ dictionary {p : unitInterval × unitInterval |
      p.1 = 0 ∧ p.2 ∈ Set.Ioo 0 1} ∧
      ¬ @IsOpen _ product {p : unitInterval × unitInterval |
        p.1 = 0 ∧ p.2 ∈ Set.Ioo 0 1} := by
  constructor
  · -- Identify the set with the lexicographic interval from `(0, 0)` to `(0, 1)`.
    letI : TopologicalSpace (Lex (unitInterval × unitInterval)) :=
      Preorder.topology (Lex (unitInterval × unitInterval))
    letI : OrderTopology (Lex (unitInterval × unitInterval)) := ⟨rfl⟩
    unfold dictionary
    rw [isOpen_induced_iff]
    refine ⟨Set.Ioo (toLex ((0 : unitInterval), (0 : unitInterval)))
      (toLex ((0 : unitInterval), (1 : unitInterval))), isOpen_Ioo, ?_⟩
    ext p
    rcases p with ⟨x, y⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioo,
      Prod.Lex.toLex_lt_toLex]
    constructor
    · rintro ⟨hleft, hright⟩
      rcases hright with hfirst | ⟨hfirst, hsecond1⟩
      · exact False.elim
          (not_lt_of_ge (show (0 : unitInterval) ≤ x by exact bot_le) hfirst)
      · subst x
        rcases hleft with hfirst | ⟨-, hsecond0⟩
        · exact False.elim (lt_irrefl (0 : unitInterval) hfirst)
        · exact ⟨rfl, hsecond0, hsecond1⟩
    · rintro ⟨hfirst, hsecond0, hsecond1⟩
      subst x
      exact ⟨Or.inr ⟨rfl, hsecond0⟩, Or.inr ⟨rfl, hsecond1⟩⟩
  · -- A horizontal section through an interior height pulls this set back to the singleton `{0}`.
    intro hopen
    obtain ⟨y, hy0, hy1⟩ := exists_between (show (0 : unitInterval) < 1 by simp)
    have hcontinuous : @Continuous unitInterval (unitInterval × unitInterval)
        inferInstance product (fun x ↦ (x, y)) :=
      continuous_id.prodMk continuous_const
    have hpreOpen := hcontinuous.isOpen_preimage _ hopen
    have hpre : (fun x : unitInterval ↦ (x, y)) ⁻¹'
        {p : unitInterval × unitInterval | p.1 = 0 ∧ p.2 ∈ Set.Ioo 0 1} =
        ({0} : Set unitInterval) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_singleton_iff]
      exact and_iff_left ⟨hy0, hy1⟩
    rw [hpre] at hpreOpen
    exact not_isOpen_singleton (0 : unitInterval) hpreOpen

/-- Helper for Exercise 16.10: the horizontal strip below height one is product-open but not
dictionary-open. -/
lemma lowerStrip_open_product_not_dictionary :
    @IsOpen _ product {p : unitInterval × unitInterval | p.2 < 1} ∧
      ¬ @IsOpen _ dictionary {p : unitInterval × unitInterval | p.2 < 1} := by
  constructor
  · -- The strip is the inverse image of the open lower ray under the second projection.
    unfold product
    have hopen : @IsOpen _ (inferInstance : TopologicalSpace (unitInterval × unitInterval))
        (Prod.snd ⁻¹' Set.Iio (1 : unitInterval)) :=
      continuous_snd.isOpen_preimage (Set.Iio (1 : unitInterval)) isOpen_Iio
    exact hopen
  · -- Any dictionary neighborhood of `(1, 0)` reaches the top of a preceding vertical fiber.
    letI : TopologicalSpace (Lex (unitInterval × unitInterval)) :=
      Preorder.topology (Lex (unitInterval × unitInterval))
    letI : OrderTopology (Lex (unitInterval × unitInterval)) := ⟨rfl⟩
    intro hopen
    unfold dictionary at hopen
    rw [isOpen_induced_iff] at hopen
    rcases hopen with ⟨t, htOpen, htPreimage⟩
    let center : Lex (unitInterval × unitInterval) :=
      toLex ((1 : unitInterval), (0 : unitInterval))
    have hcenter : center ∈ t := by
      have hp : ((1 : unitInterval), (0 : unitInterval)) ∈
          {p : unitInterval × unitInterval | p.2 < 1} := by
        simp
      rw [← htPreimage] at hp
      exact hp
    have hlower : ∃ l, l < center := by
      refine ⟨toLex ((0 : unitInterval), (0 : unitInterval)), ?_⟩
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by simp))
    have hupper : ∃ u, center < u := by
      refine ⟨toLex ((1 : unitInterval), (1 : unitInterval)), ?_⟩
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, by simp⟩)
    rcases (mem_nhds_iff_exists_Ioo_subset' hlower hupper).mp
        (htOpen.mem_nhds hcenter) with ⟨l, u, ⟨hlc, hcu⟩, hlu⟩
    have hlfirst : (ofLex l).1 < (1 : unitInterval) := by
      rcases Prod.Lex.toLex_lt_toLex.mp (show l < center from hlc) with hfirst | hsame
      · exact hfirst
      · exact False.elim
          (not_lt_of_ge (show (0 : unitInterval) ≤ (ofLex l).2 by exact bot_le) hsame.2)
    obtain ⟨x, hlx, hx1⟩ := exists_between hlfirst
    have hqLower : l < toLex (x, (1 : unitInterval)) := by
      rw [← toLex_ofLex l]
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlx)
    have hqCenter : toLex (x, (1 : unitInterval)) < center :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl hx1)
    have hqt : toLex (x, (1 : unitInterval)) ∈ t :=
      hlu ⟨hqLower, lt_trans hqCenter hcu⟩
    have hqStrip : (x, (1 : unitInterval)) ∈
        {p : unitInterval × unitInterval | p.2 < 1} := by
      rw [← htPreimage]
      exact hqt
    exact (lt_irrefl (1 : unitInterval)) hqStrip

/-- Exercise 16.10 (1): The topology inherited from the lexicographically ordered real
plane is strictly finer than the product topology on the unit square. -/
theorem ambient_lt_product : ambientDictionarySubspace < product := by
  -- The vertical dictionary interval separates the ambient topology from the product topology.
  refine lt_of_le_of_ne ambientDictionarySubspace_le_product ?_
  intro heq
  have hopenAmbient : @IsOpen _ ambientDictionarySubspace
      {p : unitInterval × unitInterval | p.1 = 0 ∧ p.2 ∈ Set.Ioo 0 1} :=
    TopologicalSpace.le_def.mp ambientDictionarySubspace_le_dictionary _
      verticalInterior_open_dictionary_not_product.1
  have hopenProduct : @IsOpen _ product
      {p : unitInterval × unitInterval | p.1 = 0 ∧ p.2 ∈ Set.Ioo 0 1} :=
    heq ▸ hopenAmbient
  exact verticalInterior_open_dictionary_not_product.2 hopenProduct

/-- Exercise 16.10 (2): The topology inherited from the lexicographically ordered real
plane is strictly finer than the dictionary order topology on the unit square. -/
theorem ambient_lt_dictionary : ambientDictionarySubspace < dictionary := by
  -- The lower strip separates the ambient topology from the intrinsic dictionary topology.
  refine lt_of_le_of_ne ambientDictionarySubspace_le_dictionary ?_
  intro heq
  have hopenAmbient : @IsOpen _ ambientDictionarySubspace
      {p : unitInterval × unitInterval | p.2 < 1} :=
    TopologicalSpace.le_def.mp ambientDictionarySubspace_le_product _
      lowerStrip_open_product_not_dictionary.1
  have hopenDictionary : @IsOpen _ dictionary
      {p : unitInterval × unitInterval | p.2 < 1} :=
    heq ▸ hopenAmbient
  exact lowerStrip_open_product_not_dictionary.2 hopenDictionary

/-- Exercise 16.10 (3): The product topology on the unit square is not finer than its
dictionary order topology. -/
theorem product_not_le_dictionary : ¬product ≤ dictionary := by
  -- The vertical interior is dictionary-open and fails to be product-open.
  intro hle
  exact verticalInterior_open_dictionary_not_product.2
    (TopologicalSpace.le_def.mp hle _ verticalInterior_open_dictionary_not_product.1)

/-- Exercise 16.10 (4): The dictionary order topology on the unit square is not finer
than its product topology. -/
theorem dictionary_not_le_product : ¬dictionary ≤ product := by
  -- The lower strip is product-open and fails to be dictionary-open.
  intro hle
  exact lowerStrip_open_product_not_dictionary.2
    (TopologicalSpace.le_def.mp hle _ lowerStrip_open_product_not_dictionary.1)


end UnitSquareTopology
