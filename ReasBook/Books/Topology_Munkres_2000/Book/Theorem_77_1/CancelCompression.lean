module

public import Topology_Munkres_2000.Book.Theorem_77_1.EdgeCompression
public import Topology_Munkres_2000.Book.Theorem_77_1.SourceComparison
public import Topology_Munkres_2000.Book.Algorithm_76_3.Cancel

public section

namespace CyclicPolygon.EdgeCompression

/-- Helper for Theorem 77.1: reflecting a lower-half parameter gives the
upper-half parameter of the reflected point. -/
theorem symm_lowerHalfParameter (t : unitInterval) :
    unitInterval.symm (lowerHalfParameter t) =
      upperHalfParameter (unitInterval.symm t) := by
  -- Compare real coordinates; reflection exchanges the two affine halves.
  apply Subtype.ext
  rw [unitInterval.coe_symm_eq, lowerHalfParameter_coe,
    upperHalfParameter_coe, unitInterval.coe_symm_eq]
  ring

/-- Helper for Theorem 77.1: reflecting an upper-half parameter gives the
lower-half parameter of the reflected point. -/
theorem symm_upperHalfParameter (t : unitInterval) :
    unitInterval.symm (upperHalfParameter t) =
      lowerHalfParameter (unitInterval.symm t) := by
  -- Apply the lower-half identity at the reflected parameter and use involutivity.
  apply unitInterval.symm_bijective.injective
  rw [unitInterval.symm_symm, symm_lowerHalfParameter,
    unitInterval.symm_symm]

/-- Helper for Theorem 77.1: the region identification for a cyclic rotation
sends an indexed rotated edge to its original cyclic index. -/
theorem rotateFrom_region_edgePoint {n : ℕ} (poly : CyclicPolygon n)
    (start i : Fin n) (t : unitInterval) :
    Homeomorph.setCongr (CyclicPolygon.rotateFrom_region poly start)
        ((CyclicPolygon.rotateFrom poly start).boundaryToRegion
          ((CyclicPolygon.rotateFrom poly start).edgePoint i t)) =
      poly.boundaryToRegion (poly.edgePoint (CyclicPolygon.rotatedIndex start i) t) := by
  -- Both region points have the same ambient affine edge point after reindexing.
  apply Subtype.ext
  change (((CyclicPolygon.rotateFrom poly start).boundaryToRegion
      ((CyclicPolygon.rotateFrom poly start).edgePoint i t) :
        (CyclicPolygon.rotateFrom poly start).region) :
      EuclideanSpace ℝ (Fin 2)) = _
  rw [(CyclicPolygon.rotateFrom poly start).boundaryToRegion_coe,
    poly.boundaryToRegion_coe,
    (CyclicPolygon.rotateFrom poly start).edgePoint_coe_eq_lineMap,
    poly.edgePoint_coe_eq_lineMap,
    CyclicPolygon.rotateFrom_vertices, CyclicPolygon.rotateFrom_vertices,
    CyclicPolygon.rotatedIndex_finRotate]

/-- Helper for Theorem 77.1: after deleting one of the first two edges, every
retained source index shifts down by one to a valid target index. -/
theorem combiningFirstTwoIndex_lt {k : ℕ} (i : Fin (k + 2))
    (hi : 2 ≤ i.val) : i.val - 1 < k + 1 := by
  -- The source bound loses one on both sides.
  omega

/-- Helper for Theorem 77.1: the first two source edges can be combined into
the lower and upper halves of the first target edge. -/
theorem existsRegionHomeomorphCombiningFirstTwoEdges {k : ℕ}
    (source : CyclicPolygon (k + 2)) (target : CyclicPolygon (k + 1)) :
    ∃ H : source.region ≃ₜ target.region,
      (∀ s : unitInterval,
        H (source.boundaryToRegion (source.edgePoint 0 s)) =
          target.boundaryToRegion
            (target.edgePoint 0 (lowerHalfParameter s))) ∧
      (∀ s : unitInterval,
        H (source.boundaryToRegion (source.edgePoint 1 s)) =
          target.boundaryToRegion
            (target.edgePoint 0 (upperHalfParameter s))) ∧
      ∀ (i : Fin (k + 2)) (hi : 2 ≤ i.val) (s : unitInterval),
        H (source.boundaryToRegion (source.edgePoint i s)) =
          target.boundaryToRegion
            (target.edgePoint ⟨i.val - 1, combiningFirstTwoIndex_lt i hi⟩ s) := by
  have hsourceStart : 2 < k + 2 := by
    -- The target polygon has at least three sides, so the shifted start exists.
    have hthree := target.three_le
    omega
  have htargetStart : 1 < k + 1 := by
    -- The target's intrinsic side bound makes index one valid.
    have hthree := target.three_le
    omega
  let sourceStart : Fin (k + 2) := ⟨2, hsourceStart⟩
  let targetStart : Fin (k + 1) := ⟨1, htargetStart⟩
  let rotatedSource := CyclicPolygon.rotateFrom source sourceStart
  let rotatedTarget := CyclicPolygon.rotateFrom target targetStart
  obtain ⟨core, hretained, hlower, hupper⟩ :=
    existsRegionHomeomorph rotatedSource rotatedTarget
  let sourceIdentification : rotatedSource.region ≃ₜ source.region :=
    Homeomorph.setCongr (CyclicPolygon.rotateFrom_region source sourceStart)
  let targetIdentification : rotatedTarget.region ≃ₜ target.region :=
    Homeomorph.setCongr (CyclicPolygon.rotateFrom_region target targetStart)
  let H : source.region ≃ₜ target.region :=
    sourceIdentification.symm.trans (core.trans targetIdentification)
  have hsourceZeroIndex :
      CyclicPolygon.rotatedIndex sourceStart (Fin.last k).castSucc = 0 := by
    -- Rotation by two sends the penultimate rotated edge to source edge zero.
    rw [CyclicPolygon.rotatedIndex_eq_add]
    apply Fin.ext
    simp only [sourceStart, Fin.val_add, Fin.val_castSucc, Fin.val_last,
      Fin.val_zero]
    rw [Nat.add_comm 2 k, Nat.mod_self]
  have hsourceOneIndex :
      CyclicPolygon.rotatedIndex sourceStart (Fin.last (k + 1)) = 1 := by
    -- The final rotated edge is source edge one after wrapping.
    rw [CyclicPolygon.rotatedIndex_eq_add]
    apply Fin.ext
    simp only [sourceStart, Fin.val_add, Fin.val_last, Fin.val_one]
    have hsum : 2 + (k + 1) = (k + 2) + 1 := by
      omega
    rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt]
    omega
  have htargetZeroIndex :
      CyclicPolygon.rotatedIndex targetStart (Fin.last k) = 0 := by
    -- Rotation by one sends the final rotated edge to target edge zero.
    rw [CyclicPolygon.rotatedIndex_eq_add]
    apply Fin.ext
    simp only [targetStart, Fin.val_add, Fin.val_last, Fin.val_zero]
    rw [Nat.add_comm 1 k, Nat.mod_self]
  have hsourceZero (s : unitInterval) :
      sourceIdentification
          (rotatedSource.boundaryToRegion
            (rotatedSource.edgePoint (Fin.last k).castSucc s)) =
        source.boundaryToRegion (source.edgePoint 0 s) := by
    -- Apply the general rotation formula and normalize its cyclic index.
    dsimp only [sourceIdentification, rotatedSource]
    rw [rotateFrom_region_edgePoint, hsourceZeroIndex]
  have hsourceOne (s : unitInterval) :
      sourceIdentification
          (rotatedSource.boundaryToRegion
            (rotatedSource.edgePoint (Fin.last (k + 1)) s)) =
        source.boundaryToRegion (source.edgePoint 1 s) := by
    -- Apply the same formula to the final edge.
    dsimp only [sourceIdentification, rotatedSource]
    rw [rotateFrom_region_edgePoint, hsourceOneIndex]
  have htargetZero (s : unitInterval) :
      targetIdentification
          (rotatedTarget.boundaryToRegion
            (rotatedTarget.edgePoint (Fin.last k) s)) =
        target.boundaryToRegion (target.edgePoint 0 s) := by
    -- Transport the compressed target's final edge back to edge zero.
    dsimp only [targetIdentification, rotatedTarget]
    rw [rotateFrom_region_edgePoint, htargetZeroIndex]
  refine ⟨H, ?_, ?_, ?_⟩
  · intro s
    -- Feed source edge zero through the lower-half formula of the rotated compression.
    calc
      H (source.boundaryToRegion (source.edgePoint 0 s)) =
          targetIdentification
            (core (sourceIdentification.symm
              (source.boundaryToRegion (source.edgePoint 0 s)))) := rfl
      _ = targetIdentification
          (core (rotatedSource.boundaryToRegion
            (rotatedSource.edgePoint (Fin.last k).castSucc s))) := by
          rw [← hsourceZero s, sourceIdentification.symm_apply_apply]
      _ = targetIdentification
          (rotatedTarget.boundaryToRegion
            (rotatedTarget.edgePoint (Fin.last k) (lowerHalfParameter s))) := by
          rw [hlower]
      _ = target.boundaryToRegion
          (target.edgePoint 0 (lowerHalfParameter s)) := htargetZero _
  · intro s
    -- Feed source edge one through the upper-half formula.
    calc
      H (source.boundaryToRegion (source.edgePoint 1 s)) =
          targetIdentification
            (core (sourceIdentification.symm
              (source.boundaryToRegion (source.edgePoint 1 s)))) := rfl
      _ = targetIdentification
          (core (rotatedSource.boundaryToRegion
            (rotatedSource.edgePoint (Fin.last (k + 1)) s))) := by
          rw [← hsourceOne s, sourceIdentification.symm_apply_apply]
      _ = targetIdentification
          (rotatedTarget.boundaryToRegion
            (rotatedTarget.edgePoint (Fin.last k) (upperHalfParameter s))) := by
          rw [hupper]
      _ = target.boundaryToRegion
          (target.edgePoint 0 (upperHalfParameter s)) := htargetZero _
  · intro i hi s
    have hrotatedEdge : i.val - 2 < k + 2 := by
      omega
    let rotatedEdge : Fin (k + 2) := ⟨i.val - 2, hrotatedEdge⟩
    have hretainedEdge : rotatedEdge.val < k := by
      dsimp only [rotatedEdge]
      omega
    let compressedRotatedEdge : Fin (k + 1) :=
      ⟨rotatedEdge.val, Nat.lt_succ_of_lt hretainedEdge⟩
    have hsourceRetainedIndex :
        CyclicPolygon.rotatedIndex sourceStart rotatedEdge = i := by
      rw [CyclicPolygon.rotatedIndex_eq_add]
      apply Fin.ext
      simp only [sourceStart, rotatedEdge, Fin.val_add]
      rw [Nat.mod_eq_of_lt]
      · omega
      · omega
    have htargetRetainedIndex :
        CyclicPolygon.rotatedIndex targetStart compressedRotatedEdge =
          ⟨i.val - 1, combiningFirstTwoIndex_lt i hi⟩ := by
      rw [CyclicPolygon.rotatedIndex_eq_add]
      apply Fin.ext
      simp only [targetStart, compressedRotatedEdge, rotatedEdge,
        Fin.val_add]
      rw [Nat.mod_eq_of_lt]
      · omega
      · omega
    have hsourceRetained :
        sourceIdentification
            (rotatedSource.boundaryToRegion
              (rotatedSource.edgePoint rotatedEdge s)) =
          source.boundaryToRegion (source.edgePoint i s) := by
      dsimp only [sourceIdentification, rotatedSource]
      rw [rotateFrom_region_edgePoint, hsourceRetainedIndex]
    have htargetRetained :
        targetIdentification
            (rotatedTarget.boundaryToRegion
              (rotatedTarget.edgePoint compressedRotatedEdge s)) =
          target.boundaryToRegion
            (target.edgePoint ⟨i.val - 1, combiningFirstTwoIndex_lt i hi⟩ s) := by
      dsimp only [targetIdentification, rotatedTarget]
      rw [rotateFrom_region_edgePoint, htargetRetainedIndex]
    -- The unchanged branch of final-edge compression now supplies the middle step.
    calc
      H (source.boundaryToRegion (source.edgePoint i s)) =
          targetIdentification
            (core (sourceIdentification.symm
              (source.boundaryToRegion (source.edgePoint i s)))) := rfl
      _ = targetIdentification
          (core (rotatedSource.boundaryToRegion
            (rotatedSource.edgePoint rotatedEdge s))) := by
          rw [← hsourceRetained, sourceIdentification.symm_apply_apply]
      _ = targetIdentification
          (rotatedTarget.boundaryToRegion
            (rotatedTarget.edgePoint compressedRotatedEdge s)) := by
          exact congrArg targetIdentification
            (hretained rotatedEdge hretainedEdge s)
      _ = target.boundaryToRegion
          (target.edgePoint ⟨i.val - 1, combiningFirstTwoIndex_lt i hi⟩ s) :=
        htargetRetained

end CyclicPolygon.EdgeCompression

namespace LabellingScheme.PolygonalRegions

universe u v w z

/-- Helper for Theorem 77.1: a realization transports across a source
homeomorphism that preserves and reflects the generated edge identifications. -/
theorem Realizes.precomposeSourceHomeomorph {α : Type u}
    {leftScheme rightScheme : LabellingScheme α}
    (left : PolygonalRegions.{u, v} leftScheme)
    (right : PolygonalRegions.{u, w} rightScheme)
    {X : Type z} [TopologicalSpace X] (q : left.Source → X)
    (hrealizes : left.Realizes q) (H : left.Source ≃ₜ right.Source)
    (hidentified : ∀ x y,
      right.Identified.r (H x) (H y) ↔ left.Identified.r x y) :
    right.Realizes (q ∘ H.symm) := by
  constructor
  · -- Precomposition with the inverse homeomorphism preserves quotientness.
    exact hrealizes.isQuotientMap.comp H.symm.isQuotientMap
  · intro x y
    -- Cancel the inverse source map and apply the supplied relation bridge.
    simp only [Function.comp_apply]
    rw [hrealizes.fibers]
    simpa only [Homeomorph.apply_symm_apply] using
      (hidentified (H.symm x) (H.symm y)).symm

end LabellingScheme.PolygonalRegions

namespace LabellingScheme.CancelCompression

universe u

/-- Helper for Theorem 77.1: appending one letter preserves the two-letter
lower bound needed to perform a cut. -/
theorem two_le_length_append_singleton {α : Type u} (word : List (α × Bool))
    (letter : α × Bool) (hword : 2 ≤ word.length) :
    2 ≤ (word ++ [letter]).length := by
  -- Appending a singleton increases the length by one.
  simp only [List.length_append, List.length_singleton]
  omega

/-- Helper for Theorem 77.1: prepending one letter preserves the two-letter
lower bound needed to perform a cut. -/
theorem two_le_length_cons {α : Type u} (letter : α × Bool)
    (word : List (α × Bool)) (hword : 2 ≤ word.length) :
    2 ≤ (letter :: word).length := by
  -- Prepending a letter increases the length by one.
  simp only [List.length_cons]
  omega

/-- Helper for Theorem 77.1: the first polygon after cutting around an
adjacent cancellation pair. -/
def expandedFirstWord {α : Type u} (y₀ : List (α × Bool))
    (a c : α) (b : Bool) (hy₀Length : 2 ≤ y₀.length) : PolygonWord α :=
  ⟨(y₀ ++ [(a, b)]) ++ [(c, false)],
    PolygonWord.appendLetter_length (y₀ ++ [(a, b)]) (c, false)
      (two_le_length_append_singleton y₀ (a, b) hy₀Length)⟩

/-- Helper for Theorem 77.1: the second polygon after cutting around an
adjacent cancellation pair. -/
def expandedSecondWord {α : Type u} (y₁ : List (α × Bool))
    (a c : α) (b : Bool) (hy₁Length : 2 ≤ y₁.length) : PolygonWord α :=
  ⟨(c, true) :: (a, !b) :: y₁,
    PolygonWord.consLetter_length (c, true) ((a, !b) :: y₁)
      (two_le_length_cons (a, !b) y₁ hy₁Length)⟩

/-- Helper for Theorem 77.1: the first cut polygon after compressing the
adjacent cancellation pair. -/
def compressedFirstWord {α : Type u} (y₀ : List (α × Bool))
    (d : α) (hy₀Length : 2 ≤ y₀.length) : PolygonWord α :=
  ⟨y₀ ++ [(d, false)],
    PolygonWord.appendLetter_length y₀ (d, false) hy₀Length⟩

/-- Helper for Theorem 77.1: the second cut polygon after compressing the
adjacent cancellation pair. -/
def compressedSecondWord {α : Type u} (y₁ : List (α × Bool))
    (d : α) (hy₁Length : 2 ≤ y₁.length) : PolygonWord α :=
  ⟨(d, true) :: y₁,
    PolygonWord.consLetter_length (d, true) y₁ hy₁Length⟩

/-- Helper for Theorem 77.1: the two-polygon scheme obtained by cutting on
both sides of an adjacent cancellation pair. -/
def expandedCutScheme {α : Type u} (y₀ y₁ : List (α × Bool))
    (a c : α) (b : Bool) (rest : LabellingScheme α)
    (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length) :
    LabellingScheme α :=
  expandedFirstWord y₀ a c b hy₀Length ::ₘ
    expandedSecondWord y₁ a c b hy₁Length ::ₘ rest

/-- Helper for Theorem 77.1: the corresponding two-polygon scheme after
combining each exposed pair of edges. -/
def compressedCutScheme {α : Type u} (y₀ y₁ : List (α × Bool))
    (d : α) (rest : LabellingScheme α)
    (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length) :
    LabellingScheme α :=
  compressedFirstWord y₀ d hy₀Length ::ₘ
    compressedSecondWord y₁ d hy₁Length ::ₘ rest

/-- Helper for Theorem 77.1: the finite set of unsigned labels appearing in
a labelling scheme. -/
noncomputable def labelSupport {α : Type u}
    (scheme : LabellingScheme α) : Finset α :=
  @Multiset.toFinset α (Classical.decEq α)
    (scheme.bind fun word ↦ word.1.map Prod.fst)

/-- Helper for Theorem 77.1: avoiding a label is equivalent to absence from
the finite unsigned-label support. -/
theorem not_mem_labelSupport_iff {α : Type u}
    (scheme : LabellingScheme α) (c : α) :
    c ∉ labelSupport scheme ↔ scheme.AvoidsLabel c := by
  -- Expand multiset bind membership into a word and then a letter occurrence.
  classical
  rw [LabellingScheme.avoidsLabel_iff]
  constructor
  · intro hsupport word hword letter hletter heq
    apply hsupport
    rw [labelSupport, Multiset.mem_toFinset, Multiset.mem_bind]
    refine ⟨word, hword, ?_⟩
    exact List.mem_map.mpr ⟨letter, hletter, heq⟩
  · intro havoid hsupport
    rw [labelSupport, Multiset.mem_toFinset, Multiset.mem_bind] at hsupport
    obtain ⟨word, hword, hletter⟩ := hsupport
    rw [Multiset.mem_coe, List.mem_map] at hletter
    obtain ⟨letter, hletter, heq⟩ := hletter
    exact havoid word hword letter hletter heq

end LabellingScheme.CancelCompression

namespace LabellingScheme

open CancelCompression

universe u w

/-- Helper for Theorem 77.1: compressing the two exposed polygons around an
adjacent cancellation pair preserves the presented space. -/
theorem presents_iff_of_cancelCutCompression {α : Type u}
    (y₀ y₁ : List (α × Bool)) (a c d : α) (b : Bool)
    (rest : LabellingScheme α) (hy₀Length : 2 ≤ y₀.length)
    (hy₁Length : 2 ≤ y₁.length)
    (hy₀a : ∀ letter ∈ y₀, letter.1 ≠ a)
    (hy₁a : ∀ letter ∈ y₁, letter.1 ≠ a)
    (hresta : rest.AvoidsLabel a)
    (hy₀c : ∀ letter ∈ y₀, letter.1 ≠ c)
    (hy₁c : ∀ letter ∈ y₁, letter.1 ≠ c)
    (hrestc : rest.AvoidsLabel c) (hca : c ≠ a)
    (hy₀d : ∀ letter ∈ y₀, letter.1 ≠ d)
    (hy₁d : ∀ letter ∈ y₁, letter.1 ≠ d)
    (hrestd : rest.AvoidsLabel d) (hda : d ≠ a) (hdc : d ≠ c)
    {X : Type w} [TopologicalSpace X] :
    (expandedCutScheme y₀ y₁ a c b rest hy₀Length hy₁Length).Presents X ↔
      (compressedCutScheme y₀ y₁ d rest hy₀Length hy₁Length).Presents X := by
  -- TODO: assemble the two edge-compression component maps and prove that the
  -- resulting source homeomorphism preserves and reflects `EdgeRelated`.
  sorry

/-- Helper for Theorem 77.1: deleting one adjacent inverse pair preserves every
topological space presented by the labelling scheme. -/
theorem presents_iff_of_cancel {α : Type u} [Infinite α]
    {before after : LabellingScheme α} (step : Cancel before after)
    {X : Type w} [TopologicalSpace X] :
    before.Presents X ↔ after.Presents X := by
  classical
  rcases step with
    ⟨y₀, y₁, a, b, rest, hy₀Length, hy₁Length, hy₀a, hy₁a, hresta⟩
  let fixedLabels : Finset α :=
    (y₀.map Prod.fst).toFinset ∪ (y₁.map Prod.fst).toFinset ∪
      labelSupport rest ∪ {a}
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset fixedLabels
  obtain ⟨d, hd⟩ := Infinite.exists_notMem_finset (insert c fixedLabels)
  have hy₀c : ∀ letter ∈ y₀, letter.1 ≠ c := by
    -- Membership of `c` in the first fragment would contradict its fresh choice.
    intro letter hletter heq
    apply hc
    simp only [fixedLabels, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨letter, hletter, heq⟩))))
  have hy₁c : ∀ letter ∈ y₁, letter.1 ≠ c := by
    -- The same support argument excludes `c` from the second fragment.
    intro letter hletter heq
    apply hc
    simp only [fixedLabels, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨letter, hletter, heq⟩))))
  have hrestc : rest.AvoidsLabel c := by
    -- Absence from the scheme-support component is exactly label avoidance.
    apply (not_mem_labelSupport_iff rest c).mp
    intro hsupport
    apply hc
    simp only [fixedLabels, Finset.mem_union]
    exact Or.inl (Or.inr hsupport)
  have hca : c ≠ a := by
    -- The cancelled label itself was included in the forbidden support.
    intro h
    apply hc
    simp only [fixedLabels, Finset.mem_union]
    exact Or.inr (Finset.mem_singleton.mpr h)
  have hy₀d : ∀ letter ∈ y₀, letter.1 ≠ d := by
    -- The second fresh label avoids the entire fixed support.
    intro letter hletter heq
    apply hd
    rw [Finset.mem_insert]
    dsimp only [fixedLabels]
    simp only [Finset.mem_union]
    exact Or.inr (Or.inl (Or.inl (Or.inl
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨letter, hletter, heq⟩)))))
  have hy₁d : ∀ letter ∈ y₁, letter.1 ≠ d := by
    -- In particular, it avoids the second unchanged fragment.
    intro letter hletter heq
    apply hd
    rw [Finset.mem_insert]
    dsimp only [fixedLabels]
    simp only [Finset.mem_union]
    exact Or.inr (Or.inl (Or.inl (Or.inr
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨letter, hletter, heq⟩)))))
  have hrestd : rest.AvoidsLabel d := by
    -- Its absence from the retained-scheme support yields avoidance there.
    apply (not_mem_labelSupport_iff rest d).mp
    intro hsupport
    apply hd
    rw [Finset.mem_insert]
    dsimp only [fixedLabels]
    simp only [Finset.mem_union]
    exact Or.inr (Or.inl (Or.inr hsupport))
  have hda : d ≠ a := by
    -- The fixed support also contains the cancelled label.
    intro h
    apply hd
    rw [Finset.mem_insert]
    dsimp only [fixedLabels]
    simp only [Finset.mem_union]
    exact Or.inr (Or.inr (Finset.mem_singleton.mpr h))
  have hdc : d ≠ c := by
    -- The second choice explicitly forbids the first fresh label.
    intro h
    apply hd
    subst d
    exact Finset.mem_insert_self c fixedLabels
  have hy₀Extended : 2 ≤ (y₀ ++ [(a, b)]).length :=
    two_le_length_append_singleton y₀ (a, b) hy₀Length
  have hy₁Extended : 2 ≤ ((a, !b) :: y₁).length :=
    two_le_length_cons (a, !b) y₁ hy₁Length
  have hy₀Extendedc :
      ∀ letter ∈ y₀ ++ [(a, b)], letter.1 ≠ c := by
    -- Combine freshness on `y₀` with the inequality `c ≠ a`.
    intro letter hletter
    rw [List.mem_append] at hletter
    rcases hletter with hletter | hletter
    · exact hy₀c letter hletter
    · simp only [List.mem_singleton] at hletter
      subst letter
      exact hca.symm
  have hy₁Extendedc :
      ∀ letter ∈ (a, !b) :: y₁, letter.1 ≠ c := by
    -- Combine the same two facts on the second cut fragment.
    intro letter hletter
    rw [List.mem_cons] at hletter
    rcases hletter with rfl | hletter
    · exact hca.symm
    · exact hy₁c letter hletter
  have hcutBefore :
      Cut
        (⟨y₀ ++ [(a, b), (a, !b)] ++ y₁,
          PolygonWord.insertCancelPair_length y₀ y₁ a b hy₀Length⟩ ::ₘ rest)
        (expandedCutScheme y₀ y₁ a c b rest hy₀Length hy₁Length) := by
    -- Cut immediately before and after the inverse pair using the first fresh label.
    simpa only [expandedCutScheme, expandedFirstWord, expandedSecondWord,
      List.append_assoc, List.singleton_append, List.cons_append,
      List.nil_append] using
      (Cut.ofNegativePositive (y₀ ++ [(a, b)]) ((a, !b) :: y₁) c rest
        hy₀Extended hy₁Extended hy₀Extendedc hy₁Extendedc hrestc)
  have hcutAfter :
      Cut
        (⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest)
        (compressedCutScheme y₀ y₁ d rest hy₀Length hy₁Length) := by
    -- Cut the shortened word at the same location using the second fresh label.
    simpa only [compressedCutScheme, compressedFirstWord,
      compressedSecondWord] using
      (Cut.ofNegativePositive y₀ y₁ d rest hy₀Length hy₁Length
        hy₀d hy₁d hrestd)
  -- The source proof is now the flat cut–compress–paste chain.
  calc
    _ ↔ (expandedCutScheme y₀ y₁ a c b rest hy₀Length hy₁Length).Presents X :=
      presents_iff_of_cut hcutBefore
    _ ↔ (compressedCutScheme y₀ y₁ d rest hy₀Length hy₁Length).Presents X :=
      presents_iff_of_cancelCutCompression y₀ y₁ a c d b rest
        hy₀Length hy₁Length hy₀a hy₁a hresta hy₀c hy₁c hrestc hca
        hy₀d hy₁d hrestd hda hdc
    _ ↔ _ := (presents_iff_of_cut hcutAfter).symm

end LabellingScheme

end
