module

public import Topology_Munkres_2000.Book.Theorem_77_1.CancelPresentation
public import Topology_Munkres_2000.Book.Definition_74_3.EdgePairing
public import Topology_Munkres_2000.Book.Definition_76_6.Renumbering
public import Topology_Munkres_2000.Book.Theorem_74_2.Presentation

import all Topology_Munkres_2000.Book.Definition_74_3
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization

public section

universe u

namespace CyclicPolygon.EdgePasting

variable {n : ℕ} {S : Type u} {poly : CyclicPolygon n}

/-- Helper for Theorem 77.1: every direct pasting relation is represented by a
common positive parameter on two equally labelled oriented edges. -/
theorem related_iff_orientedPoints (pasting : poly.EdgePasting S)
    (x y : poly.region) :
    pasting.Related x y ↔
      ∃ (i j : Fin n) (t : unitInterval), pasting.label i = pasting.label j ∧
        x = pasting.orientedPoint i t ∧ y = pasting.orientedPoint j t := by
  constructor
  · rw [pasting.related_iff]
    rintro ⟨i, j, hlabel, z, hx, hy⟩
    let t := (pasting.orientation i).paramHomeomorph.symm z
    have hz : z = (pasting.orientation i).point t := by
      calc
        z = (pasting.orientation i).paramHomeomorph t :=
          ((pasting.orientation i).paramHomeomorph.apply_symm_apply z).symm
        _ = (pasting.orientation i).point t := by
          apply Subtype.ext
          rw [OrientedSegment.paramHomeomorph_apply,
            OrientedSegment.point_coe]
    refine ⟨i, j, t, hlabel, ?_, ?_⟩
    · -- Replace the arbitrary carrier witness by its canonical affine parameter.
      calc
        x = pasting.includePoint i z := hx
        _ = pasting.includePoint i ((pasting.orientation i).point t) :=
          congrArg (pasting.includePoint i) hz
        _ = pasting.orientedPoint i t := (pasting.orientedPoint_apply i t).symm
    · -- Positive identification preserves that same affine parameter.
      calc
        y = pasting.includePoint j (pasting.positiveIdentification i j z) := hy
        _ = pasting.includePoint j
            (pasting.positiveIdentification i j ((pasting.orientation i).point t)) :=
          congrArg (fun point ↦ pasting.includePoint j
            (pasting.positiveIdentification i j point)) hz
        _ = pasting.includePoint j ((pasting.orientation j).point t) :=
          congrArg (pasting.includePoint j)
            (pasting.positiveIdentification_point i j t)
        _ = pasting.orientedPoint j t := (pasting.orientedPoint_apply j t).symm
  · rintro ⟨i, j, t, hlabel, hx, hy⟩
    rw [pasting.related_iff]
    refine ⟨i, j, hlabel, (pasting.orientation i).point t, ?_, ?_⟩
    · exact hx.trans (pasting.orientedPoint_apply i t)
    · -- Reuse the positive-identification computation in the reverse direction.
      calc
        y = pasting.orientedPoint j t := hy
        _ = pasting.includePoint j ((pasting.orientation j).point t) :=
          pasting.orientedPoint_apply j t
        _ = pasting.includePoint j
            (pasting.positiveIdentification i j ((pasting.orientation i).point t)) :=
          congrArg (pasting.includePoint j)
            (pasting.positiveIdentification_point i j t).symm

/-- Helper for Theorem 77.1: the unique occurrence of a singleton scheme. -/
noncomputable def singletonBoundaryOccurrence (word : PolygonWord S) :
    LabellingScheme.Occurrence ({word} : LabellingScheme S) :=
  (LabellingScheme.consOccurrenceEquiv word 0).symm none

/-- Helper for Theorem 77.1: every occurrence in a singleton scheme is its
distinguished boundary occurrence. -/
theorem singletonBoundaryOccurrence_eq (word : PolygonWord S)
    (region : LabellingScheme.Occurrence ({word} : LabellingScheme S)) :
    region = singletonBoundaryOccurrence word := by
  -- The remainder of a singleton multiset has no occurrence.
  unfold singletonBoundaryOccurrence
  apply (LabellingScheme.consOccurrenceEquiv word 0).injective
  rw [Equiv.apply_symm_apply]
  cases hregion : LabellingScheme.consOccurrenceEquiv word 0 region with
  | none => rfl
  | some remaining =>
      exact (Nat.not_lt_zero remaining.2 remaining.2.isLt).elim

/-- Helper for Theorem 77.1: the unique singleton occurrence carries the given
polygon word. -/
theorem singletonBoundaryOccurrence_word (word : PolygonWord S)
    (region : LabellingScheme.Occurrence ({word} : LabellingScheme S)) :
    region.1 = word := by
  -- Normalize the occurrence and project the head word of the singleton multiset.
  rw [singletonBoundaryOccurrence_eq word region]
  exact LabellingScheme.PolygonalRegions.Renumbering.consOccurrenceEquiv_symm_none_word
    word 0

/-- Helper for Theorem 77.1: every singleton occurrence has the prescribed
number of polygon sides. -/
theorem singletonBoundaryOccurrence_length (word : PolygonWord S)
    {n : ℕ} (hlength : word.val.length = n)
    (region : LabellingScheme.Occurrence ({word} : LabellingScheme S)) :
    region.1.1.length = n := by
  -- Project list length from the occurrence-word computation.
  exact (congrArg (fun boundary : PolygonWord S ↦ boundary.val.length)
    (singletonBoundaryOccurrence_word word region)).trans hlength

/-- Helper for Theorem 77.1: lookup in a singleton occurrence agrees with the
given original-edge lookup after the canonical side-count cast. -/
theorem singletonBoundaryOccurrence_get {T : Type u} (word : PolygonWord T)
    {n : ℕ} (hlength : word.val.length = n)
    (f : Fin n → T × Bool)
    (hget : ∀ i : Fin n, word.val.get (Fin.cast hlength.symm i) = f i)
    (region : LabellingScheme.Occurrence ({word} : LabellingScheme T))
    (edge : Fin region.1.1.length) :
    region.1.1.get edge =
      f (Fin.cast (singletonBoundaryOccurrence_length word hlength region) edge) := by
  let hword := singletonBoundaryOccurrence_word word region
  let wordEdge := Fin.cast
    (congrArg (fun boundary : PolygonWord T ↦ boundary.val.length) hword) edge
  let originalEdge := Fin.cast hlength wordEdge
  have hletter := hget originalEdge
  rw [Fin.leftInverse_cast hlength wordEdge] at hletter
  have hboundary :
      (⟨region.1, edge⟩ : (boundary : PolygonWord T) × Fin boundary.val.length) =
        ⟨word, wordEdge⟩ := by
    apply Sigma.ext hword
    rw [Fin.heq_ext_iff
      (congrArg (fun boundary : PolygonWord T ↦ boundary.val.length) hword)]
    rfl
  have hsource := congrArg
    (fun pair : (boundary : PolygonWord T) × Fin boundary.val.length ↦
      pair.1.val.get pair.2) hboundary
  have hedge : originalEdge =
      Fin.cast (singletonBoundaryOccurrence_length word hlength region) edge := by
    apply Fin.ext
    rfl
  -- Compare through the word-level lookup, then identify the two equal-valued casts.
  calc
    region.1.1.get edge = word.val.get wordEdge := hsource
    _ = f originalEdge := hletter
    _ = f (Fin.cast (singletonBoundaryOccurrence_length word hlength region) edge) :=
      congrArg f hedge

/-- Helper for Theorem 77.1: convert a cyclic boundary parameter to the
parameter selected by an oriented edge sign. -/
def correctedBoundaryParameter (sign : Bool) (t : unitInterval) : unitInterval :=
  if sign then t else unitInterval.symm t

/-- Helper for Theorem 77.1: correcting twice by the same edge sign restores
the original parameter. -/
theorem correctedBoundaryParameter_involutive (sign : Bool) (t : unitInterval) :
    correctedBoundaryParameter sign (correctedBoundaryParameter sign t) = t := by
  -- The positive case is the identity and the negative case reverses twice.
  cases sign <;> simp only [correctedBoundaryParameter, Bool.false_eq_true,
    if_false, if_true, unitInterval.symm_symm]

/-- Helper for Theorem 77.1: the labelling-scheme sign comparison converts a
first cyclic parameter to the same common oriented parameter on the second edge. -/
theorem correctedBoundaryParameter_pair (first second : Bool)
    (t : unitInterval) :
    correctedBoundaryParameter second
        (if first = second then t else unitInterval.symm t) =
      correctedBoundaryParameter first t := by
  -- Check the four possible pairs of orientation signs.
  cases first <;> cases second <;>
    simp [correctedBoundaryParameter, unitInterval.symm_symm]

/-- Helper for Theorem 77.1: starting from a common oriented parameter, the
scheme's sign rule produces the cyclic parameter of the second edge. -/
theorem pairedCyclicParameter_eq (first second : Bool) (t : unitInterval) :
    (if first = second then correctedBoundaryParameter first t
      else unitInterval.symm (correctedBoundaryParameter first t)) =
      correctedBoundaryParameter second t := by
  -- The four sign pairs reduce to identity or double reversal.
  cases first <;> cases second <;>
    simp [correctedBoundaryParameter, unitInterval.symm_symm]

/-- Helper for Theorem 77.1: the singleton polygonal-region family uses the
original filled polygon and its cyclic edge parametrizations. -/
@[expose]
noncomputable def singletonBoundaryRegions (pasting : poly.EdgePasting S)
    (word : PolygonWord pasting.UsedLabel)
    (hlength : word.val.length = n) :
    LabellingScheme.PolygonalRegions ({word} : LabellingScheme pasting.UsedLabel) where
  Point _ := poly.region
  topology _ := inferInstance
  edge region edge t :=
    poly.boundaryToRegion
      (poly.edgePoint
        (Fin.cast (singletonBoundaryOccurrence_length word hlength region) edge) t)

/-- Helper for Theorem 77.1: the canonical singleton family's edge map is the
cyclic edge map at the corresponding original polygon index. -/
theorem singletonBoundaryRegions_edge (pasting : poly.EdgePasting S)
    (word : PolygonWord pasting.UsedLabel)
    (hlength : word.val.length = n)
    (region : LabellingScheme.Occurrence ({word} : LabellingScheme pasting.UsedLabel))
    (edge : Fin region.1.1.length) (t : unitInterval) :
    (pasting.singletonBoundaryRegions word hlength).edge region edge t =
      poly.boundaryToRegion
        (poly.edgePoint
          (Fin.cast (singletonBoundaryOccurrence_length word hlength region) edge) t) := by
  -- Expose the sole edge projection of the canonical family.
  rfl

/-- Helper for Theorem 77.1: the canonical singleton family is genuinely
polygonal. -/
theorem singletonBoundaryRegions_isPolygonal (pasting : poly.EdgePasting S)
    (word : PolygonWord pasting.UsedLabel)
    (hlength : word.val.length = n) :
    (pasting.singletonBoundaryRegions word hlength).IsPolygonal := by
  rw [LabellingScheme.PolygonalRegions.isPolygonal_iff]
  intro region
  let hcount := singletonBoundaryOccurrence_length word hlength region
  let targetPolygon := CyclicPolygon.transportSides hcount.symm poly
  obtain ⟨H, hH⟩ :=
    CyclicPolygon.existsRegionHomeomorphPreservingEdgeParameters_of_eq
      hcount.symm poly targetPolygon
  refine ⟨LabellingScheme.PolygonalRegions.CyclicRegion.ofHomeomorph
    targetPolygon H ?_⟩
  intro edge t
  -- Follow the cyclic edge through the side-count comparison homeomorphism.
  rw [singletonBoundaryRegions_edge]
  calc
    (H (poly.boundaryToRegion
        (poly.edgePoint (Fin.cast hcount edge) t)) : EuclideanSpace ℝ (Fin 2)) =
        (targetPolygon.boundaryToRegion
          (targetPolygon.edgePoint edge t) : EuclideanSpace ℝ (Fin 2)) :=
      congrArg Subtype.val (hH edge t)
    _ = (targetPolygon.edgePoint edge t : EuclideanSpace ℝ (Fin 2)) :=
      targetPolygon.boundaryToRegion_coe (targetPolygon.edgePoint edge t)
    _ = _ := targetPolygon.edgePoint_coe_eq_lineMap edge t

/-- Helper for Theorem 77.1: project the source of the singleton boundary
family to its original filled polygon. -/
def singletonBoundarySourceProjection (pasting : poly.EdgePasting S)
    (word : PolygonWord pasting.UsedLabel)
    (hlength : word.val.length = n) :
    (pasting.singletonBoundaryRegions word hlength).Source → poly.region :=
  fun point ↦ point.2

/-- Helper for Theorem 77.1: the singleton source projection retains the
underlying point of each region summand. -/
theorem singletonBoundarySourceProjection_apply (pasting : poly.EdgePasting S)
    (word : PolygonWord pasting.UsedLabel)
    (hlength : word.val.length = n)
    (point : (pasting.singletonBoundaryRegions word hlength).Source) :
    pasting.singletonBoundarySourceProjection word hlength point = point.2 := by
  -- Expose the stable point projection without unfolding it downstream.
  rfl

/-- Helper for Theorem 77.1: projection from the source of the singleton
boundary family to the original filled polygon is a homeomorphism. -/
theorem singletonBoundarySourceProjection_isHomeomorph
    (pasting : poly.EdgePasting S)
    (word : PolygonWord pasting.UsedLabel)
    (hlength : word.val.length = n) :
    IsHomeomorph (pasting.singletonBoundarySourceProjection word hlength) := by
  let regions := pasting.singletonBoundaryRegions word hlength
  rw [isHomeomorph_iff_exists_inverse]
  constructor
  · -- Projection is continuous on each summand of the source topology.
    have hcontinuous :
        @Continuous regions.Source poly.region regions.sourceTopology inferInstance
          (pasting.singletonBoundarySourceProjection word hlength) := by
      change @Continuous regions.Source poly.region
        (⨆ region, TopologicalSpace.coinduced (Sigma.mk region)
          (regions.topology region)) inferInstance
        (pasting.singletonBoundarySourceProjection word hlength)
      rw [continuous_iSup_dom]
      intro region
      rw [continuous_coinduced_dom]
      letI : TopologicalSpace (regions.Point region) := regions.topology region
      dsimp only [regions, singletonBoundaryRegions,
        singletonBoundarySourceProjection, Function.comp_apply]
      exact continuous_id
    exact hcontinuous
  · -- Insert points into the unique occurrence and verify both inverse equations.
    let region := singletonBoundaryOccurrence word
    have hinclusion :
        @Continuous (regions.Point region) regions.Source
          (regions.topology region) regions.sourceTopology
          (Sigma.mk region) := by
      change @Continuous (regions.Point region) regions.Source
        (regions.topology region)
        (⨆ otherRegion, TopologicalSpace.coinduced (Sigma.mk otherRegion)
          (regions.topology otherRegion)) (Sigma.mk region)
      exact continuous_iSup_rng (i := region) (f := Sigma.mk region)
        (continuous_coinduced_rng (f := Sigma.mk region))
    refine ⟨fun point ↦
      (⟨region, point⟩ : regions.Source),
      ?_, ?_, ?_⟩
    · rintro ⟨otherRegion, point⟩
      rw [singletonBoundarySourceProjection_apply,
        singletonBoundaryOccurrence_eq word otherRegion]
    · intro point
      exact singletonBoundarySourceProjection_apply pasting word hlength ⟨region, point⟩
    · dsimp only [regions, singletonBoundaryRegions] at hinclusion ⊢
      exact hinclusion

/-- Helper for Theorem 77.1: correcting the chosen orientation parameter by
the edge sign recovers the cyclic boundary parameter. -/
theorem orientedPoint_corrected (pasting : poly.EdgePasting S)
    (edge : Fin n) (t : unitInterval) :
    pasting.orientedPoint edge (correctedBoundaryParameter (pasting.sign edge) t) =
      poly.boundaryToRegion (poly.edgePoint edge t) := by
  -- Split on the sign; reversing both the segment and parameter restores the cyclic point.
  apply Subtype.ext
  rw [pasting.orientedPoint_apply, pasting.includePoint_coe,
    pasting.orientation_eq, poly.boundaryToRegion_coe,
    poly.edgePoint_coe_eq_lineMap, OrientedSegment.point_coe,
    correctedBoundaryParameter]
  cases hsign : pasting.sign edge
  · simp only [Bool.false_eq_true, if_false,
      CyclicPolygon.signedOrientation, OrientedSegment.reverse_initial,
      OrientedSegment.reverse_final, CyclicPolygon.cyclicOrientation,
      unitInterval.coe_symm_eq]
    rw [AffineMap.lineMap_apply_one_sub]
  · simp only [if_true, CyclicPolygon.signedOrientation,
      CyclicPolygon.cyclicOrientation]

/-- Helper for Theorem 77.1: direct labelled-edge relatedness in the singleton
boundary family is exactly the edge-pasting relation after source projection. -/
theorem singletonBoundaryRegions_edgeRelated_iff (pasting : poly.EdgePasting S)
    (word : PolygonWord pasting.UsedLabel)
    (hlength : word.val.length = n)
    (hget : ∀ i : Fin n,
      word.val.get (Fin.cast hlength.symm i) =
        (⟨pasting.label i, Set.mem_range_self i⟩, pasting.sign i))
    (x y : (pasting.singletonBoundaryRegions word hlength).Source) :
    (pasting.singletonBoundaryRegions word hlength).EdgeRelated x y ↔
      pasting.Related x.2 y.2 := by
  rw [LabellingScheme.PolygonalRegions.edgeRelated_iff_witness,
    pasting.related_iff_orientedPoints]
  constructor
  · rintro ⟨firstRegion, secondRegion, firstEdge, secondEdge, t,
      hlabels, hx, hy⟩
    let first := Fin.cast
      (singletonBoundaryOccurrence_length word hlength firstRegion) firstEdge
    let second := Fin.cast
      (singletonBoundaryOccurrence_length word hlength secondRegion) secondEdge
    have hfirstLetter : firstRegion.1.1.get firstEdge =
        (⟨pasting.label first, Set.mem_range_self first⟩, pasting.sign first) := by
      exact singletonBoundaryOccurrence_get word hlength
        (fun i : Fin n ↦
          (⟨pasting.label i, Set.mem_range_self i⟩, pasting.sign i))
        hget firstRegion firstEdge
    have hsecondLetter : secondRegion.1.1.get secondEdge =
        (⟨pasting.label second, Set.mem_range_self second⟩, pasting.sign second) := by
      exact singletonBoundaryOccurrence_get word hlength
        (fun i : Fin n ↦
          (⟨pasting.label i, Set.mem_range_self i⟩, pasting.sign i))
        hget secondRegion secondEdge
    have hlabelUsed :
        (⟨pasting.label first, Set.mem_range_self first⟩ : pasting.UsedLabel) =
          ⟨pasting.label second, Set.mem_range_self second⟩ := by
      calc
        _ = (firstRegion.1.1.get firstEdge).1 :=
          (congrArg Prod.fst hfirstLetter).symm
        _ = (secondRegion.1.1.get secondEdge).1 := hlabels
        _ = _ := congrArg Prod.fst hsecondLetter
    have hlabel : pasting.label first = pasting.label second :=
      congrArg Subtype.val hlabelUsed
    have hxPoint : x.2 =
        poly.boundaryToRegion (poly.edgePoint first t) := by
      have hxSecond := congrArg
        (fun point : (pasting.singletonBoundaryRegions word hlength).Source ↦ point.2) hx
      dsimp only [singletonBoundaryRegions] at hxSecond ⊢
      simpa only [first] using hxSecond
    have hyPoint : y.2 = poly.boundaryToRegion
        (poly.edgePoint second
          (if pasting.sign first = pasting.sign second then t
            else unitInterval.symm t)) := by
      have hySecond := congrArg
        (fun point : (pasting.singletonBoundaryRegions word hlength).Source ↦ point.2) hy
      dsimp only [singletonBoundaryRegions] at hySecond ⊢
      rw [hfirstLetter, hsecondLetter] at hySecond
      simpa only [first, second] using hySecond
    refine ⟨first, second, correctedBoundaryParameter (pasting.sign first) t,
      hlabel, ?_, ?_⟩
    · -- Convert the first cyclic boundary point to its chosen oriented parameter.
      exact hxPoint.trans (pasting.orientedPoint_corrected first t).symm
    · -- The sign comparison makes the second cyclic point use the same oriented parameter.
      calc
        y.2 = poly.boundaryToRegion
            (poly.edgePoint second
              (if pasting.sign first = pasting.sign second then t
                else unitInterval.symm t)) := hyPoint
        _ = pasting.orientedPoint second
            (correctedBoundaryParameter (pasting.sign second)
              (if pasting.sign first = pasting.sign second then t
                else unitInterval.symm t)) :=
          (pasting.orientedPoint_corrected second _).symm
        _ = pasting.orientedPoint second
            (correctedBoundaryParameter (pasting.sign first) t) :=
          congrArg (pasting.orientedPoint second)
            (correctedBoundaryParameter_pair
              (pasting.sign first) (pasting.sign second) t)
  · intro hrelated
    rcases x with ⟨firstRegion, firstPoint⟩
    rcases y with ⟨secondRegion, secondPoint⟩
    have hfirstRegion := singletonBoundaryOccurrence_eq word firstRegion
    have hsecondRegion := singletonBoundaryOccurrence_eq word secondRegion
    subst firstRegion
    subst secondRegion
    obtain ⟨first, second, t, hlabel, hx, hy⟩ := hrelated
    let region := singletonBoundaryOccurrence word
    let hcount := singletonBoundaryOccurrence_length word hlength region
    let firstEdge := Fin.cast hcount.symm first
    let secondEdge := Fin.cast hcount.symm second
    let firstParameter := correctedBoundaryParameter (pasting.sign first) t
    have hfirstIndex : Fin.cast hcount firstEdge = first :=
      Fin.rightInverse_cast hcount first
    have hsecondIndex : Fin.cast hcount secondEdge = second :=
      Fin.rightInverse_cast hcount second
    have hfirstLetter : region.1.1.get firstEdge =
        (⟨pasting.label first, Set.mem_range_self first⟩, pasting.sign first) := by
      have hletter := singletonBoundaryOccurrence_get word hlength
        (fun i : Fin n ↦
          (⟨pasting.label i, Set.mem_range_self i⟩, pasting.sign i))
        hget region firstEdge
      rwa [hfirstIndex] at hletter
    have hsecondLetter : region.1.1.get secondEdge =
        (⟨pasting.label second, Set.mem_range_self second⟩, pasting.sign second) := by
      have hletter := singletonBoundaryOccurrence_get word hlength
        (fun i : Fin n ↦
          (⟨pasting.label i, Set.mem_range_self i⟩, pasting.sign i))
        hget region secondEdge
      rwa [hsecondIndex] at hletter
    refine ⟨region, region, firstEdge, secondEdge, firstParameter, ?_, ?_, ?_⟩
    · -- The word-level labels are the underlying equal pasting labels.
      calc
        (region.1.1.get firstEdge).1 =
            (⟨pasting.label first, Set.mem_range_self first⟩ : pasting.UsedLabel) :=
          congrArg Prod.fst hfirstLetter
        _ = ⟨pasting.label second, Set.mem_range_self second⟩ :=
          Subtype.ext hlabel
        _ = (region.1.1.get secondEdge).1 :=
          (congrArg Prod.fst hsecondLetter).symm
    · -- Insert the first source point into the unique occurrence and undo sign correction.
      apply congrArg (Sigma.mk region)
      dsimp only [singletonBoundaryRegions]
      rw [hfirstIndex]
      calc
        firstPoint = pasting.orientedPoint first t := hx
        _ = pasting.orientedPoint first
            (correctedBoundaryParameter (pasting.sign first) firstParameter) :=
          congrArg (pasting.orientedPoint first)
            (correctedBoundaryParameter_involutive (pasting.sign first) t).symm
        _ = poly.boundaryToRegion (poly.edgePoint first firstParameter) :=
          pasting.orientedPoint_corrected first firstParameter
    · -- The scheme's sign rule supplies the second edge's corrected cyclic parameter.
      apply congrArg (Sigma.mk region)
      let secondParameter :=
        if (region.1.1.get firstEdge).2 = (region.1.1.get secondEdge).2 then
          firstParameter else unitInterval.symm firstParameter
      change secondPoint = (pasting.singletonBoundaryRegions word hlength).edge
        region secondEdge secondParameter
      dsimp only [singletonBoundaryRegions]
      rw [hsecondIndex]
      have hparameter : secondParameter =
          correctedBoundaryParameter (pasting.sign second) t := by
        dsimp only [secondParameter]
        rw [hfirstLetter, hsecondLetter]
        exact pairedCyclicParameter_eq (pasting.sign first) (pasting.sign second) t
      calc
        secondPoint = pasting.orientedPoint second t := hy
        _ = pasting.orientedPoint second
            (correctedBoundaryParameter (pasting.sign second)
              (correctedBoundaryParameter (pasting.sign second) t)) :=
          congrArg (pasting.orientedPoint second)
            (correctedBoundaryParameter_involutive (pasting.sign second) t).symm
        _ = poly.boundaryToRegion
            (poly.edgePoint second (correctedBoundaryParameter (pasting.sign second) t)) :=
          pasting.orientedPoint_corrected second _
        _ = poly.boundaryToRegion (poly.edgePoint second secondParameter) :=
          congrArg (fun parameter ↦
            poly.boundaryToRegion (poly.edgePoint second parameter)) hparameter.symm

/-- Helper for Theorem 77.1: a singleton polygon word that records an edge
pasting's labels and signs presents the pasting's canonical realization. -/
theorem singletonBoundaryWord_presents (pasting : poly.EdgePasting S)
    (word : PolygonWord pasting.UsedLabel)
    (hlength : word.val.length = n)
    (hget : ∀ i : Fin n,
      word.val.get (Fin.cast hlength.symm i) =
        (⟨pasting.label i, Set.mem_range_self i⟩, pasting.sign i)) :
    ({word} : LabellingScheme pasting.UsedLabel).Presents pasting.Realization := by
  let regions := pasting.singletonBoundaryRegions word hlength
  let projection : regions.Source → poly.region :=
    pasting.singletonBoundarySourceProjection word hlength
  have hprojection : IsHomeomorph projection :=
    pasting.singletonBoundarySourceProjection_isHomeomorph word hlength
  let sourceHomeomorph : regions.Source ≃ₜ poly.region :=
    IsHomeomorph.homeomorph projection hprojection
  let q : regions.Source → pasting.Realization := pasting.quotientMap ∘ projection
  rw [LabellingScheme.presents_iff]
  refine ⟨regions, pasting.singletonBoundaryRegions_isPolygonal word hlength, q, ?_⟩
  constructor
  · -- Compose the source homeomorphism's quotient map with the pasting quotient.
    exact pasting.isQuotientMap_quotientMap.comp hprojection.isQuotientMap
  · intro x y
    have hgenerated : pasting.Identified x.2 y.2 ↔ regions.Identified.r x y := by
      rw [LabellingScheme.PolygonalRegions.identified_iff_eqvGen]
      change Relation.EqvGen pasting.Related x.2 y.2 ↔
        Relation.EqvGen regions.EdgeRelated x y
      have hdirect (first second : regions.Source) :
          pasting.Related (sourceHomeomorph first) (sourceHomeomorph second) ↔
            regions.EdgeRelated first second := by
        simpa only [sourceHomeomorph, IsHomeomorph.homeomorph_apply,
          projection, singletonBoundarySourceProjection_apply, regions] using
          (pasting.singletonBoundaryRegions_edgeRelated_iff
            word hlength hget first second).symm
      have hsourceApply (point : regions.Source) :
          sourceHomeomorph.toEquiv point = point.2 := by
        change pasting.singletonBoundarySourceProjection word hlength point = point.2
        exact pasting.singletonBoundarySourceProjection_apply word hlength point
      simpa only [sourceHomeomorph, IsHomeomorph.homeomorph_apply,
        projection, singletonBoundarySourceProjection_apply, hsourceApply] using
        (LabellingScheme.PolygonalRegions.eqvGen_equiv_iff
          sourceHomeomorph.toEquiv hdirect x y)
    -- Equality in the canonical pasting quotient is its generated edge relation.
    simpa only [q, Function.comp_apply, projection,
      singletonBoundarySourceProjection_apply,
      CyclicPolygon.EdgePasting.quotientMap] using
      (Quotient.eq''.trans hgenerated)

end CyclicPolygon.EdgePasting
