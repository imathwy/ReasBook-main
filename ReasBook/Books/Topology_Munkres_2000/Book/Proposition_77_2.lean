module

public import Topology_Munkres_2000.Book.Proposition_77_1
public import Topology_Munkres_2000.Book.Definition_74_6.Presentation
public import Topology_Munkres_2000.Book.Theorem_74_2.Presentation
public import Topology_Munkres_2000.Book.Theorem_77_1.BoundaryPresentation

import all Topology_Munkres_2000.Book.Definition_74_6.Presentation

public section

universe u v

namespace PolygonWord

/-- Helper for Proposition 77.2: a proper polygon word is either of torus type or equivalent to
a same-length projective normal form. The two branches of `ProjectiveNormalForm` are respectively
a nonempty duplicated-pair prefix followed by a torus-type tail and such a prefix with empty
tail. -/
theorem properNormalFormCases {α : Type u} [Infinite α]
    (word : PolygonWord α) (hproper : ({word} : LabellingScheme α).Proper) :
    word.TorusType ∨
      ∃ normalized : PolygonWord α,
        LabellingScheme.Equivalent
            ({word} : LabellingScheme α) ({normalized} : LabellingScheme α) ∧
          normalized.length = word.length ∧ normalized.ProjectiveNormalForm := by
  by_cases htorus : word.TorusType
  · exact Or.inl htorus
  · apply Or.inr
    exact ProjectiveType.existsEquivalentNormalForm
      (projectiveType_iff.mpr ⟨hproper, htorus⟩)

end PolygonWord

namespace CyclicPolygon.EdgePasting

/-- Helper for Proposition 77.2: duplicating every entry of a list doubles its length. -/
private theorem duplicatedPairs_length {A : Type*} (pairs : List A) :
    (pairs.flatMap (fun x ↦ [x, x])).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons x pairs ih =>
      -- Remove the leading duplicated block and apply the induction hypothesis.
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil, zero_add, ih]
      omega

/-- Helper for Proposition 77.2: a position in a duplicated list lies over a
valid position of the original list after division by two. -/
private theorem duplicatedPairsBlock_lt {A : Type*} (pairs : List A)
    {i : ℕ} (hi : i < 2 * pairs.length) : i / 2 < pairs.length := by
  -- Division by the positive block size preserves the strict length bound.
  omega

/-- Helper for Proposition 77.2: the original-list block containing a position
of the corresponding duplicated list. -/
private def duplicatedPairsBlockIndex {A : Type*} (pairs : List A)
    (i : Fin (2 * pairs.length)) : Fin pairs.length :=
  ⟨i / 2, duplicatedPairsBlock_lt pairs i.isLt⟩

/-- Helper for Proposition 77.2: lookup in a duplicated list is lookup in the
original list at the position divided by two. -/
private theorem duplicatedPairs_getElem {A : Type*} (pairs : List A)
    (i : ℕ) (hi : i < 2 * pairs.length) :
    (pairs.flatMap (fun x ↦ [x, x]))[i]'(duplicatedPairs_length pairs ▸ hi) =
      pairs[i / 2]'(duplicatedPairsBlock_lt pairs hi) := by
  induction pairs generalizing i with
  | nil =>
      simp only [List.length_nil, mul_zero] at hi
      omega
  | cons x pairs ih =>
      by_cases hiZero : i = 0
      · -- The first position is the first copy of the head entry.
        subst i
        rfl
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hiZero
      by_cases hjZero : j = 0
      · -- The second position is the second copy of the head entry.
        subst j
        rfl
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjZero
      have hk : k < 2 * pairs.length := by
        simp only [List.length_cons] at hi
        omega
      have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
      -- Past the first block, both lookups reduce to the induction hypothesis.
      simpa only [List.flatMap_cons, List.singleton_append, List.cons_append,
        List.nil_append, List.getElem_cons_succ, hdiv] using ih k hk

/-- Helper for Proposition 77.2: finite lookup in a duplicated list is indexed
by the corresponding original-list block. -/
private theorem duplicatedPairs_get {A : Type*} (pairs : List A)
    (i : Fin (2 * pairs.length)) :
    (pairs.flatMap (fun x ↦ [x, x])).get
        (Fin.cast (duplicatedPairs_length pairs).symm i) =
      pairs.get (duplicatedPairsBlockIndex pairs i) := by
  -- The finite-index statement is the preceding element-index computation.
  exact duplicatedPairs_getElem pairs i i.isLt

/-- Helper for Proposition 77.2: with distinct block labels, two entries of a
duplicated pair list have the same first component exactly in the same block. -/
private theorem duplicatedPairs_fst_eq_iff {A B : Type u}
    (pairs : List (A × B)) (hdistinct : (pairs.map Prod.fst).Pairwise (· ≠ ·))
    (i j : Fin (2 * pairs.length)) :
    ((pairs.flatMap (fun x ↦ [x, x])).get
          (Fin.cast (duplicatedPairs_length pairs).symm i)).1 =
        ((pairs.flatMap (fun x ↦ [x, x])).get
          (Fin.cast (duplicatedPairs_length pairs).symm j)).1 ↔
      duplicatedPairsBlockIndex pairs i = duplicatedPairsBlockIndex pairs j := by
  -- Normalize both duplicated lookups, then use injectivity of lookup in a nodup list.
  rw [duplicatedPairs_get, duplicatedPairs_get]
  have hnodup : (pairs.map Prod.fst).Nodup := hdistinct
  simpa only [List.get_eq_getElem, List.getElem_map, Fin.val_cast,
    Fin.cast_inj] using
    (hnodup.get_inj_iff
      (i := Fin.cast (pairs.length_map Prod.fst).symm
        (duplicatedPairsBlockIndex pairs i))
      (j := Fin.cast (pairs.length_map Prod.fst).symm
        (duplicatedPairsBlockIndex pairs j)))

/-- Helper for Proposition 77.2: when a pasting boundary is a duplicated-pair
list, its indexed boundary entry is the entry of the corresponding pair block. -/
private theorem boundaryEntry_eq_pairBlock
    {S : Type u} {n : ℕ} {poly : CyclicPolygon n}
    (pasting : poly.EdgePasting S)
    (pairs : List (pasting.UsedLabel × Bool))
    (hboundary : pasting.boundaryWord =
      pairs.flatMap (fun letter ↦ [letter, letter]))
    (hcount : n = 2 * pairs.length) (i : Fin n) :
    (⟨pasting.label i, Set.mem_range_self i⟩, pasting.sign i) =
      pairs.get (duplicatedPairsBlockIndex pairs (Fin.cast hcount i)) := by
  -- Read the edge through `boundaryWord`, transport across `hboundary`, and normalize lookup.
  calc
    (⟨pasting.label i, Set.mem_range_self i⟩, pasting.sign i) =
        pasting.boundaryWord.get
          (Fin.cast pasting.boundaryWord_length.symm i) :=
      (pasting.boundaryWord_get i).symm
    _ = (pairs.flatMap (fun letter ↦ [letter, letter])).get
          (Fin.cast (duplicatedPairs_length pairs).symm (Fin.cast hcount i)) :=
      LabellingScheme.PolygonalRegions.Renumbering.get_eq_of_list_eq_of_val_eq
        _ _ hboundary rfl
    _ = pairs.get (duplicatedPairsBlockIndex pairs (Fin.cast hcount i)) :=
      duplicatedPairs_get pairs (Fin.cast hcount i)

/-- Helper for Proposition 77.2: distinct duplicated pair blocks make source
edge-label equality equivalent to equality of block indices. -/
private theorem pasting_label_eq_iff_pairBlock
    {S : Type u} {n : ℕ} {poly : CyclicPolygon n}
    (pasting : poly.EdgePasting S)
    (pairs : List (pasting.UsedLabel × Bool))
    (hboundary : pasting.boundaryWord =
      pairs.flatMap (fun letter ↦ [letter, letter]))
    (hdistinct : (pairs.map Prod.fst).Pairwise (· ≠ ·))
    (hcount : n = 2 * pairs.length) (i j : Fin n) :
    pasting.label i = pasting.label j ↔
      duplicatedPairsBlockIndex pairs (Fin.cast hcount i) =
        duplicatedPairsBlockIndex pairs (Fin.cast hcount j) := by
  have hi := congrArg Prod.fst
    (boundaryEntry_eq_pairBlock pasting pairs hboundary hcount i)
  have hj := congrArg Prod.fst
    (boundaryEntry_eq_pairBlock pasting pairs hboundary hcount j)
  have hnodup : (pairs.map Prod.fst).Nodup := hdistinct
  have hblocks :
      (pairs.get (duplicatedPairsBlockIndex pairs (Fin.cast hcount i))).1 =
          (pairs.get (duplicatedPairsBlockIndex pairs (Fin.cast hcount j))).1 ↔
        duplicatedPairsBlockIndex pairs (Fin.cast hcount i) =
          duplicatedPairsBlockIndex pairs (Fin.cast hcount j) := by
    -- Distinct first components make block lookup injective.
    simpa only [List.get_eq_getElem, List.getElem_map, Fin.val_cast,
      Fin.cast_inj] using
      (hnodup.get_inj_iff
        (i := Fin.cast (pairs.length_map Prod.fst).symm
          (duplicatedPairsBlockIndex pairs (Fin.cast hcount i)))
        (j := Fin.cast (pairs.length_map Prod.fst).symm
          (duplicatedPairsBlockIndex pairs (Fin.cast hcount j))))
  constructor
  · intro hlabel
    apply hblocks.mp
    -- Lift raw-label equality to the used-label subtype recorded in the boundary word.
    calc
      (pairs.get (duplicatedPairsBlockIndex pairs (Fin.cast hcount i))).1 =
          (⟨pasting.label i, Set.mem_range_self i⟩ : pasting.UsedLabel) := hi.symm
      _ = ⟨pasting.label j, Set.mem_range_self j⟩ := Subtype.ext hlabel
      _ = (pairs.get (duplicatedPairsBlockIndex pairs (Fin.cast hcount j))).1 := hj
  · intro hblock
    have hused :
        (⟨pasting.label i, Set.mem_range_self i⟩ : pasting.UsedLabel) =
          ⟨pasting.label j, Set.mem_range_self j⟩ := by
      calc
        (⟨pasting.label i, Set.mem_range_self i⟩ : pasting.UsedLabel) =
            (pairs.get (duplicatedPairsBlockIndex pairs (Fin.cast hcount i))).1 := hi
        _ = (pairs.get (duplicatedPairsBlockIndex pairs (Fin.cast hcount j))).1 :=
          hblocks.mpr hblock
        _ = ⟨pasting.label j, Set.mem_range_self j⟩ := hj.symm
    exact congrArg Subtype.val hused

/-- Helper for Proposition 77.2: a duplicated-pair boundary with distinct
labels has constant orientation sign on every label fiber. -/
private theorem pasting_sign_eq_of_label_eq
    {S : Type u} {n : ℕ} {poly : CyclicPolygon n}
    (pasting : poly.EdgePasting S)
    (pairs : List (pasting.UsedLabel × Bool))
    (hboundary : pasting.boundaryWord =
      pairs.flatMap (fun letter ↦ [letter, letter]))
    (hdistinct : (pairs.map Prod.fst).Pairwise (· ≠ ·))
    (hcount : n = 2 * pairs.length) (i j : Fin n)
    (hlabel : pasting.label i = pasting.label j) :
    pasting.sign i = pasting.sign j := by
  have hblock :=
    (pasting_label_eq_iff_pairBlock pasting pairs hboundary hdistinct hcount i j).mp hlabel
  have hi := congrArg Prod.snd
    (boundaryEntry_eq_pairBlock pasting pairs hboundary hcount i)
  have hj := congrArg Prod.snd
    (boundaryEntry_eq_pairBlock pasting pairs hboundary hcount j)
  -- Equal blocks contain the same signed letter, so their sign projections agree.
  calc
    pasting.sign i =
        (pairs.get (duplicatedPairsBlockIndex pairs (Fin.cast hcount i))).2 := hi
    _ = (pairs.get (duplicatedPairsBlockIndex pairs (Fin.cast hcount j))).2 :=
      congrArg (fun block ↦ (pairs.get block).2) hblock
    _ = pasting.sign j := hj.symm

/-- Helper for Proposition 77.2: labels in the standard nonorientable pasting
agree exactly when their edge indices have the same quotient by two. -/
private theorem standardPasting_label_eq_iff_div (m : ℕ) (hm : 1 < m)
    (i j : Fin (2 * m)) :
    (NonorientableSurfacePresentation.pasting m hm).label i =
        (NonorientableSurfacePresentation.pasting m hm).label j ↔
      i.val / 2 = j.val / 2 := by
  -- The standard label in position `i` is `i / 2 + 1`.
  simp only [NonorientableSurfacePresentation.pasting,
    NonorientableSurfacePresentation.boundaryLetter]
  omega

/-- Helper for Proposition 77.2: an edge-parameter-preserving region homeomorphism
maps direct edge pairings when the indexed label pattern and fiber signs agree. -/
theorem related_map_of_pairingPattern
    {S : Type u} {T : Type v} {n m : ℕ} {leftPoly : CyclicPolygon n}
    {rightPoly : CyclicPolygon m}
    (left : leftPoly.EdgePasting S) (right : rightPoly.EdgePasting T)
    (hcount : n = m)
    (H : leftPoly.region ≃ₜ rightPoly.region)
    (hH : ∀ (i : Fin m) (t : unitInterval),
      H (leftPoly.boundaryToRegion
          (leftPoly.edgePoint (Fin.cast hcount.symm i) t)) =
        rightPoly.boundaryToRegion (rightPoly.edgePoint i t))
    (hlabels : ∀ i j, left.label i = left.label j →
      right.label (Fin.cast hcount i) = right.label (Fin.cast hcount j))
    (hleftSigns : ∀ i j, left.label i = left.label j →
      left.sign i = left.sign j)
    (hrightSigns : ∀ i j, right.label i = right.label j →
      right.sign i = right.sign j)
    {x y : leftPoly.region} (hxy : left.Related x y) :
    right.Related (H x) (H y) := by
  rw [left.related_iff_orientedPoints] at hxy
  rw [right.related_iff_orientedPoints]
  obtain ⟨i, j, t, hlabel, hx, hy⟩ := hxy
  let s := correctedBoundaryParameter (left.sign i) t
  have hleftSign := hleftSigns i j hlabel
  have hrightLabel := hlabels i j hlabel
  have hrightSign := hrightSigns
    (Fin.cast hcount i) (Fin.cast hcount j) hrightLabel
  have hHsource (edge : Fin n) (parameter : unitInterval) :
      H (leftPoly.boundaryToRegion (leftPoly.edgePoint edge parameter)) =
        rightPoly.boundaryToRegion
          (rightPoly.edgePoint (Fin.cast hcount edge) parameter) := by
    -- Cancel the round-trip cast in the side-count comparison formula.
    calc
      H (leftPoly.boundaryToRegion (leftPoly.edgePoint edge parameter)) =
          H (leftPoly.boundaryToRegion
            (leftPoly.edgePoint
              (Fin.cast hcount.symm (Fin.cast hcount edge)) parameter)) :=
        congrArg
          (fun index ↦ H (leftPoly.boundaryToRegion
            (leftPoly.edgePoint index parameter)))
          (Fin.leftInverse_cast hcount edge).symm
      _ = rightPoly.boundaryToRegion
          (rightPoly.edgePoint (Fin.cast hcount edge) parameter) :=
        hH (Fin.cast hcount edge) parameter
  have hxCyclic :
      x = leftPoly.boundaryToRegion (leftPoly.edgePoint i s) := by
    -- Undo the source orientation and expose the underlying cyclic parameter.
    calc
      x = left.orientedPoint i t := hx
      _ = left.orientedPoint i
          (correctedBoundaryParameter (left.sign i) s) :=
        congrArg (left.orientedPoint i)
          (correctedBoundaryParameter_involutive (left.sign i) t).symm
      _ = leftPoly.boundaryToRegion (leftPoly.edgePoint i s) :=
        left.orientedPoint_corrected i s
  have htSecond :
      t = correctedBoundaryParameter (left.sign j) s := by
    -- Constancy of the source sign gives the same corrected parameter on the mate.
    calc
      t = correctedBoundaryParameter (left.sign i) s :=
        (correctedBoundaryParameter_involutive (left.sign i) t).symm
      _ = correctedBoundaryParameter (left.sign j) s :=
        congrArg (fun sign ↦ correctedBoundaryParameter sign s) hleftSign
  have hyCyclic :
      y = leftPoly.boundaryToRegion (leftPoly.edgePoint j s) := by
    -- Normalize the second source edge to the same cyclic parameter.
    calc
      y = left.orientedPoint j t := hy
      _ = left.orientedPoint j
          (correctedBoundaryParameter (left.sign j) s) :=
        congrArg (left.orientedPoint j) htSecond
      _ = leftPoly.boundaryToRegion (leftPoly.edgePoint j s) :=
        left.orientedPoint_corrected j s
  refine ⟨Fin.cast hcount i, Fin.cast hcount j,
    correctedBoundaryParameter (right.sign (Fin.cast hcount i)) s,
    hrightLabel, ?_, ?_⟩
  · -- Map the first normalized cyclic point and restore the target orientation.
    calc
      H x = H (leftPoly.boundaryToRegion (leftPoly.edgePoint i s)) :=
        congrArg H hxCyclic
      _ = rightPoly.boundaryToRegion
          (rightPoly.edgePoint (Fin.cast hcount i) s) := hHsource i s
      _ = right.orientedPoint (Fin.cast hcount i)
          (correctedBoundaryParameter (right.sign (Fin.cast hcount i)) s) :=
        (right.orientedPoint_corrected (Fin.cast hcount i) s).symm
  · -- The target sign is constant on the matching label fiber as well.
    calc
      H y = H (leftPoly.boundaryToRegion (leftPoly.edgePoint j s)) :=
        congrArg H hyCyclic
      _ = rightPoly.boundaryToRegion
          (rightPoly.edgePoint (Fin.cast hcount j) s) := hHsource j s
      _ = right.orientedPoint (Fin.cast hcount j)
          (correctedBoundaryParameter (right.sign (Fin.cast hcount j)) s) :=
        (right.orientedPoint_corrected (Fin.cast hcount j) s).symm
      _ = right.orientedPoint (Fin.cast hcount j)
          (correctedBoundaryParameter (right.sign (Fin.cast hcount i)) s) :=
        congrArg (right.orientedPoint (Fin.cast hcount j))
          (congrArg (fun sign ↦ correctedBoundaryParameter sign s) hrightSign.symm)

/-- Helper for Proposition 77.2: the direct pairing relation is preserved and
reflected by an edge-parameter-preserving comparison with the same pairing pattern. -/
theorem related_regionHomeomorph_iff_of_pairingPattern
    {S : Type u} {T : Type v} {n m : ℕ} {leftPoly : CyclicPolygon n}
    {rightPoly : CyclicPolygon m}
    (left : leftPoly.EdgePasting S) (right : rightPoly.EdgePasting T)
    (hcount : n = m)
    (H : leftPoly.region ≃ₜ rightPoly.region)
    (hH : ∀ (i : Fin m) (t : unitInterval),
      H (leftPoly.boundaryToRegion
          (leftPoly.edgePoint (Fin.cast hcount.symm i) t)) =
        rightPoly.boundaryToRegion (rightPoly.edgePoint i t))
    (hlabels : ∀ i j,
      left.label i = left.label j ↔
        right.label (Fin.cast hcount i) = right.label (Fin.cast hcount j))
    (hleftSigns : ∀ i j, left.label i = left.label j →
      left.sign i = left.sign j)
    (hrightSigns : ∀ i j, right.label i = right.label j →
      right.sign i = right.sign j)
    (x y : leftPoly.region) :
    right.Related (H x) (H y) ↔ left.Related x y := by
  have hHsource (i : Fin n) (t : unitInterval) :
      H (leftPoly.boundaryToRegion (leftPoly.edgePoint i t)) =
        rightPoly.boundaryToRegion
          (rightPoly.edgePoint (Fin.cast hcount i) t) := by
    -- Cancel the round-trip cast in the forward edge formula.
    calc
      H (leftPoly.boundaryToRegion (leftPoly.edgePoint i t)) =
          H (leftPoly.boundaryToRegion
            (leftPoly.edgePoint
              (Fin.cast hcount.symm (Fin.cast hcount i)) t)) :=
        congrArg
          (fun index ↦ H (leftPoly.boundaryToRegion (leftPoly.edgePoint index t)))
          (Fin.leftInverse_cast hcount i).symm
      _ = rightPoly.boundaryToRegion
          (rightPoly.edgePoint (Fin.cast hcount i) t) := hH (Fin.cast hcount i) t
  have hHsymm (i : Fin n) (t : unitInterval) :
      H.symm (rightPoly.boundaryToRegion
          (rightPoly.edgePoint (Fin.cast hcount i) t)) =
        leftPoly.boundaryToRegion (leftPoly.edgePoint i t) := by
    -- Reflect the edge formula through injectivity of the region homeomorphism.
    apply H.injective
    rw [H.apply_symm_apply]
    exact (hHsource i t).symm
  have hlabelsSymm : ∀ i j,
      right.label i = right.label j →
        left.label (Fin.cast hcount.symm i) =
          left.label (Fin.cast hcount.symm j) := by
    intro i j hij
    apply (hlabels (Fin.cast hcount.symm i) (Fin.cast hcount.symm j)).mpr
    calc
      right.label (Fin.cast hcount (Fin.cast hcount.symm i)) = right.label i :=
        congrArg right.label (Fin.rightInverse_cast hcount i)
      _ = right.label j := hij
      _ = right.label (Fin.cast hcount (Fin.cast hcount.symm j)) :=
        congrArg right.label (Fin.rightInverse_cast hcount j).symm
  constructor
  · intro hxy
    -- Apply the directional comparison to the inverse homeomorphism.
    simpa only [H.symm_apply_apply] using
      related_map_of_pairingPattern right left hcount.symm H.symm hHsymm
        hlabelsSymm hrightSigns hleftSigns hxy
  · intro hxy
    -- Apply the directional comparison to the forward homeomorphism.
    exact related_map_of_pairingPattern left right hcount H hH
      (fun i j hij ↦ (hlabels i j).mp hij) hleftSigns hrightSigns hxy

/-- Helper for Proposition 77.2: edge pastings with the same indexed pairing
pattern and fiberwise-constant signs have homeomorphic quotient realizations. -/
theorem realizationHomeomorphicOfPairingPattern
    {S : Type u} {T : Type v} {n m : ℕ} {leftPoly : CyclicPolygon n}
    {rightPoly : CyclicPolygon m}
    (left : leftPoly.EdgePasting S) (right : rightPoly.EdgePasting T)
    (hcount : n = m)
    (hlabels : ∀ i j,
      left.label i = left.label j ↔
        right.label (Fin.cast hcount i) = right.label (Fin.cast hcount j))
    (hleftSigns : ∀ i j, left.label i = left.label j →
      left.sign i = left.sign j)
    (hrightSigns : ∀ i j, right.label i = right.label j →
      right.sign i = right.sign j) :
    Nonempty (left.Realization ≃ₜ right.Realization) := by
  obtain ⟨H, hH⟩ :=
    leftPoly.existsRegionHomeomorphPreservingEdgeParameters_of_eq hcount rightPoly
  have hidentified (x y : leftPoly.region) :
      left.Identified x y ↔ right.Identified (H x) (H y) := by
    -- Lift direct pairing preservation through the generated equivalence relation.
    exact (LabellingScheme.PolygonalRegions.eqvGen_equiv_iff H.toEquiv
      (related_regionHomeomorph_iff_of_pairingPattern
        left right hcount H hH hlabels hleftSigns hrightSigns) x y).symm
  -- Quotient congruence now consumes only the stable generated-relation interface.
  exact ⟨Homeomorph.Quotient.congr H hidentified⟩

/-- Proposition 77.2 (2): A one-polygon edge pasting whose boundary word consists of
distinct duplicated letters realizes the corresponding connected sum of projective planes. -/
theorem pairedNormalFormRealizationHomeomorphicProjectivePlane
    {α : Type u} {n : ℕ} {poly : CyclicPolygon n}
    (pasting : poly.EdgePasting α) (pairs : List (pasting.UsedLabel × Bool))
    (hboundary : pasting.boundaryWord = pairs.flatMap (fun letter ↦ [letter, letter]))
    (hdistinct : (pairs.map Prod.fst).Pairwise (· ≠ ·)) :
    ∃ hm : 1 < pairs.length,
      Nonempty
        (pasting.Realization ≃ₜ
          NonorientableSurfacePresentation.mFoldProjectivePlane pairs.length hm) := by
  have hcount : n = 2 * pairs.length := by
    -- Compare the intrinsic boundary length with the duplicated-list length.
    calc
      n = pasting.boundaryWord.length := pasting.boundaryWord_length.symm
      _ = (pairs.flatMap (fun letter ↦ [letter, letter])).length :=
        congrArg List.length hboundary
      _ = 2 * pairs.length := duplicatedPairs_length pairs
  have hm : 1 < pairs.length := by
    -- A cyclic polygon has at least three sides, hence at least two two-edge blocks.
    have hthree := poly.three_le
    omega
  refine ⟨hm, ?_⟩
  refine realizationHomeomorphicOfPairingPattern pasting
    (NonorientableSurfacePresentation.pasting pairs.length hm) hcount ?_ ?_ ?_
  · intro i j
    rw [pasting_label_eq_iff_pairBlock pasting pairs hboundary hdistinct hcount,
      standardPasting_label_eq_iff_div]
    -- Equality of the finite block indices is equality of their quotient values.
    constructor
    · intro hblock
      exact congrArg Fin.val hblock
    · intro hdiv
      exact Fin.ext hdiv
  · -- The duplicated source word assigns one signed letter to each label fiber.
    exact pasting_sign_eq_of_label_eq pasting pairs hboundary hdistinct hcount
  · intro i j _hlabel
    -- Every edge of the standard nonorientable presentation has positive sign.
    rfl

end CyclicPolygon.EdgePasting
