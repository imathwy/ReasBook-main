module

public import Topology_Munkres_2000.Book.Definition_76_6.Flip
public import Topology_Munkres_2000.Book.Definition_76_6.RelabelRealization
public import Topology_Munkres_2000.Book.Definition_76_6.Renumbering
public import Topology_Munkres_2000.Book.Proposition_76_1.Realization
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Quotient
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization
import all Topology_Munkres_2000.Book.Definition_76_6.RelabelRealization

public section

universe u v w

namespace LabellingScheme.PolygonalRegions

variable {α : Type u} {word : PolygonWord α}
  {rest : LabellingScheme α}

/-- The occurrence equivalence for a flip maps the selected polygon to its formal inverse
and fixes every occurrence in the remainder. -/
noncomputable def flipRegionEquiv :
    Occurrence (word ::ₘ rest) ≃ Occurrence (word.formalInverse ::ₘ rest) :=
  (consOccurrenceEquiv word rest).trans (consOccurrenceEquiv word.formalInverse rest).symm

/-- Corresponding polygon occurrences before and after a flip have equal edge counts. -/
theorem flipRegion_length
    (region : Occurrence (word.formalInverse ::ₘ rest)) :
    region.1.1.length = (flipRegionEquiv.symm region).1.1.length := by
  -- Split the target occurrence into the flipped polygon or an unchanged remainder polygon.
  let sourceEquiv := consOccurrenceEquiv word rest
  let targetEquiv := consOccurrenceEquiv word.formalInverse rest
  cases hposition : targetEquiv region with
  | none =>
      have hregion : region = targetEquiv.symm none :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      have horiginal : flipRegionEquiv.symm (targetEquiv.symm none) =
          sourceEquiv.symm none := by
        change sourceEquiv.symm (targetEquiv (targetEquiv.symm none)) = sourceEquiv.symm none
        rw [targetEquiv.apply_symm_apply]
      rw [horiginal, Renumbering.consOccurrenceEquiv_symm_none_length,
        Renumbering.consOccurrenceEquiv_symm_none_length]
      rw [PolygonWord.formalInverse_val]
      simp
  | some remainder =>
      have hregion : region = targetEquiv.symm (some remainder) :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      have horiginal : flipRegionEquiv.symm (targetEquiv.symm (some remainder)) =
          sourceEquiv.symm (some remainder) := by
        change sourceEquiv.symm (targetEquiv (targetEquiv.symm (some remainder))) =
          sourceEquiv.symm (some remainder)
        rw [targetEquiv.apply_symm_apply]
      rw [horiginal, Renumbering.consOccurrenceEquiv_symm_some_length,
        Renumbering.consOccurrenceEquiv_symm_some_length]

/-- The numerical edge index for a flip reverses the selected polygon and fixes the remainder. -/
noncomputable def flipEdgeValue
    (region : Occurrence (word.formalInverse ::ₘ rest))
    (edge : Fin region.1.1.length) : ℕ :=
  match consOccurrenceEquiv word.formalInverse rest region with
  | none => region.1.1.length - 1 - edge
  | some _ => edge

/-- The edge index for a flip lies in the corresponding original polygon's edge range. -/
theorem flipEdgeValue_lt
    (region : Occurrence (word.formalInverse ::ₘ rest))
    (edge : Fin region.1.1.length) :
    flipEdgeValue region edge < (flipRegionEquiv.symm region).1.1.length := by
  -- In both occurrence cases, use the common boundary length; subtraction reverses a valid index.
  have hlength := flipRegion_length region
  unfold flipEdgeValue
  split <;> omega

/-- The edge index associated to an edge after flipping the selected polygon. -/
noncomputable def flipEdgeIndex
    (region : Occurrence (word.formalInverse ::ₘ rest))
    (edge : Fin region.1.1.length) : Fin (flipRegionEquiv.symm region).1.1.length :=
  ⟨flipEdgeValue region edge, flipEdgeValue_lt region edge⟩

/-- Helper for Definition 76.6: the canonical edge equivalence reverses the selected
polygon's indices and fixes the indices of every retained polygon. -/
noncomputable def flipEdgeEquiv
    (region : Occurrence (word.formalInverse ::ₘ rest)) :
    Fin (flipRegionEquiv.symm region).1.1.length ≃ Fin region.1.1.length :=
  match consOccurrenceEquiv word.formalInverse rest region with
  | none => ((finCongr (flipRegion_length region)).trans Fin.revPerm).symm
  | some _ => (finCongr (flipRegion_length region)).symm

/-- The edge parameter is reversed on the selected polygon and fixed on the remainder. -/
noncomputable def flipParameter
    (region : Occurrence (word.formalInverse ::ₘ rest))
    (t : unitInterval) : unitInterval :=
  match consOccurrenceEquiv word.formalInverse rest region with
  | none => unitInterval.symm t
  | some _ => t

/-- On the selected formally inverted word, the flip edge index is reversal
after the canonical length cast. -/
theorem flipEdgeIndex_selected
    (edge : Fin (((consOccurrenceEquiv word.formalInverse rest).symm none).1.1.length)) :
    flipEdgeIndex
        (region := (consOccurrenceEquiv word.formalInverse rest).symm none) edge =
      (Fin.cast (flipRegion_length
        ((consOccurrenceEquiv word.formalInverse rest).symm none)) edge).rev := by
  -- Both sides have value `length - 1 - edge`; the cast preserves the value.
  apply Fin.ext
  simp only [flipEdgeIndex, flipEdgeValue, Fin.val_rev, Fin.val_cast]
  rw [(consOccurrenceEquiv word.formalInverse rest).apply_symm_apply]
  change ((consOccurrenceEquiv word.formalInverse rest).symm none).1.1.length -
      1 - edge.1 =
    (flipRegionEquiv.symm
      ((consOccurrenceEquiv word.formalInverse rest).symm none)).1.1.length -
        (edge.1 + 1)
  have hlength := flipRegion_length
    ((consOccurrenceEquiv word.formalInverse rest).symm none)
  omega

/-- On the selected formally inverted word, the flip reverses the affine edge
parameter. -/
theorem flipParameter_selected (t : unitInterval) :
    flipParameter
        (region := (consOccurrenceEquiv word.formalInverse rest).symm none) t =
      unitInterval.symm t := by
  -- The selected occurrence takes the `none` branch of the flip definition.
  unfold flipParameter
  rw [(consOccurrenceEquiv word.formalInverse rest).apply_symm_apply]

/-- On an unchanged remainder occurrence, the flip edge index is only the
canonical length cast. -/
theorem flipEdgeIndex_remainder (region : Occurrence rest)
    (edge : Fin (((consOccurrenceEquiv word.formalInverse rest).symm
      (some region)).1.1.length)) :
    flipEdgeIndex
        (region := (consOccurrenceEquiv word.formalInverse rest).symm
          (some region)) edge =
      Fin.cast (flipRegion_length
        ((consOccurrenceEquiv word.formalInverse rest).symm (some region))) edge := by
  -- The unchanged occurrence takes the identity-index branch.
  apply Fin.ext
  simp only [flipEdgeIndex, flipEdgeValue, Fin.val_cast]
  rw [(consOccurrenceEquiv word.formalInverse rest).apply_symm_apply]

/-- On an unchanged remainder occurrence, the flip preserves the affine edge
parameter. -/
theorem flipParameter_remainder (region : Occurrence rest) (t : unitInterval) :
    flipParameter
        (region := (consOccurrenceEquiv word.formalInverse rest).symm
          (some region)) t = t := by
  -- The unchanged occurrence takes the `some` branch of the flip definition.
  unfold flipParameter
  rw [(consOccurrenceEquiv word.formalInverse rest).apply_symm_apply]

/-- Helper for Definition 76.6: the inverse edge equivalence computes to the existing
target-to-source flip index. -/
theorem flipEdgeEquiv_symm_apply
    (region : Occurrence (word.formalInverse ::ₘ rest))
    (edge : Fin region.1.1.length) :
    (flipEdgeEquiv region).symm edge = flipEdgeIndex region edge := by
  -- Split the target occurrence into the selected polygon and the retained remainder.
  let targetEquiv := consOccurrenceEquiv word.formalInverse rest
  cases hposition : targetEquiv region with
  | none =>
      have hregion : region = targetEquiv.symm none :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      unfold flipEdgeEquiv
      rw [targetEquiv.apply_symm_apply]
      rw [flipEdgeIndex_selected]
      rfl
  | some remainder =>
      have hregion : region = targetEquiv.symm (some remainder) :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      unfold flipEdgeEquiv
      rw [targetEquiv.apply_symm_apply]
      rw [flipEdgeIndex_remainder]
      rfl

/-- Helper for Definition 76.6: the selected target occurrence pulls back to the selected
original occurrence. -/
theorem flipRegionEquiv_symm_selected :
    flipRegionEquiv.symm
        ((consOccurrenceEquiv word.formalInverse rest).symm none) =
      (consOccurrenceEquiv word rest).symm none := by
  -- Both occurrence equivalences use `none` for the distinguished polygon.
  change (consOccurrenceEquiv word rest).symm
      (consOccurrenceEquiv word.formalInverse rest
        ((consOccurrenceEquiv word.formalInverse rest).symm none)) =
    (consOccurrenceEquiv word rest).symm none
  rw [(consOccurrenceEquiv word.formalInverse rest).apply_symm_apply]

/-- Helper for Definition 76.6: every retained target occurrence pulls back to the same
remainder occurrence in the original scheme. -/
theorem flipRegionEquiv_symm_remainder (region : Occurrence rest) :
    flipRegionEquiv.symm
        ((consOccurrenceEquiv word.formalInverse rest).symm (some region)) =
      (consOccurrenceEquiv word rest).symm (some region) := by
  -- Both occurrence equivalences use `some region` for a retained polygon.
  change (consOccurrenceEquiv word rest).symm
      (consOccurrenceEquiv word.formalInverse rest
        ((consOccurrenceEquiv word.formalInverse rest).symm (some region))) =
    (consOccurrenceEquiv word rest).symm (some region)
  rw [(consOccurrenceEquiv word.formalInverse rest).apply_symm_apply]

/-- Helper for Definition 76.6: a selected formally inverted edge has the original label
and the opposite orientation at the reversed source edge. -/
theorem flipLetter_selected
    (edge : Fin (((consOccurrenceEquiv word.formalInverse rest).symm none).1.1.length)) :
    ((consOccurrenceEquiv word.formalInverse rest).symm none).1.1.get edge =
      ((((consOccurrenceEquiv word rest).symm none).1.1.get
          (Fin.cast
            (congrArg (fun region : Occurrence (word ::ₘ rest) ↦ region.1.1.length)
              flipRegionEquiv_symm_selected)
            (flipEdgeIndex
              ((consOccurrenceEquiv word.formalInverse rest).symm none) edge))).1,
       !(((consOccurrenceEquiv word rest).symm none).1.1.get
          (Fin.cast
            (congrArg (fun region : Occurrence (word ::ₘ rest) ↦ region.1.1.length)
              flipRegionEquiv_symm_selected)
            (flipEdgeIndex
              ((consOccurrenceEquiv word.formalInverse rest).symm none) edge))).2) := by
  -- Normalize both dependent lookups to the concrete selected words before reversing.
  let target := (consOccurrenceEquiv word.formalInverse rest).symm none
  let source := (consOccurrenceEquiv word rest).symm none
  have htargetList : target.1.1 = word.formalInverse.1 :=
    congrArg (fun polygon : PolygonWord α ↦ polygon.1)
      (Renumbering.consOccurrenceEquiv_symm_none_word word.formalInverse rest)
  have hsourceList : source.1.1 = word.1 :=
    congrArg (fun polygon : PolygonWord α ↦ polygon.1)
      (Renumbering.consOccurrenceEquiv_symm_none_word word rest)
  let targetIndex := Fin.cast (congrArg List.length htargetList) edge
  let inverseList := word.1.reverse.map (fun letter ↦ (letter.1, !letter.2))
  let inverseIndex := Fin.cast
    (congrArg List.length (PolygonWord.formalInverse_val word)) targetIndex
  let reverseIndex : Fin word.1.reverse.length :=
    Fin.cast (by simp only [List.length_map]) inverseIndex
  let sourceIndex := Fin.cast
    (congrArg (fun region : Occurrence (word ::ₘ rest) ↦ region.1.1.length)
      flipRegionEquiv_symm_selected) (flipEdgeIndex target edge)
  let originalIndex := Fin.cast (congrArg List.length hsourceList) sourceIndex
  have htargetLookup : target.1.1.get edge =
      word.formalInverse.1.get targetIndex :=
    Renumbering.get_eq_of_list_eq_of_val_eq edge targetIndex htargetList rfl
  have hinverseLookup : word.formalInverse.1.get targetIndex =
      inverseList.get inverseIndex :=
    Renumbering.get_eq_of_list_eq_of_val_eq targetIndex inverseIndex
      (PolygonWord.formalInverse_val word) rfl
  have hsourceLookup : source.1.1.get sourceIndex = word.1.get originalIndex :=
    Renumbering.get_eq_of_list_eq_of_val_eq sourceIndex originalIndex hsourceList rfl
  let mappedReverseIndex : Fin inverseList.length :=
    Fin.cast (by simp only [inverseList, List.length_map]) reverseIndex
  have hinverseIndex : inverseIndex = mappedReverseIndex := by
    apply Fin.ext
    rfl
  have hmapLookup : inverseList.get inverseIndex =
      (fun letter : α × Bool ↦ (letter.1, !letter.2))
        (word.1.reverse.get reverseIndex) := by
    -- Remove the outer map without changing the reversed lookup to `getElem` form.
    rw [hinverseIndex]
    simp only [inverseList, mappedReverseIndex, List.get_eq_getElem, List.getElem_map,
      Fin.val_cast]
  have hreverseLt : word.1.length - 1 - reverseIndex < word.1.length := by
    -- A valid reverse-list index gives the arithmetic side condition for `get_reverse'`.
    have hindex := reverseIndex.isLt
    simp only [List.length_reverse] at hindex
    omega
  calc
    target.1.1.get edge = word.formalInverse.1.get targetIndex := htargetLookup
    _ = inverseList.get inverseIndex := hinverseLookup
    _ = (fun letter : α × Bool ↦ (letter.1, !letter.2))
        (word.1.reverse.get reverseIndex) := hmapLookup
    _ = ((word.1.get originalIndex).1, !(word.1.get originalIndex).2) := by
      rw [List.get_reverse' word.1 reverseIndex hreverseLt]
      apply congrArg (fun letter : α × Bool ↦ (letter.1, !letter.2))
      apply Renumbering.get_eq_of_list_eq_of_val_eq
      · rfl
      · dsimp only [reverseIndex, inverseIndex, targetIndex, originalIndex, sourceIndex,
          target]
        rw [flipEdgeIndex_selected]
        simp only [Fin.val_cast, Fin.val_rev]
        have htargetLength := congrArg List.length htargetList
        have hsourceLength := congrArg List.length hsourceList
        have hflipLength := flipRegion_length target
        have hsourceRegion : flipRegionEquiv.symm target = source :=
          flipRegionEquiv_symm_selected
        have hboundaryLength : (flipRegionEquiv.symm target).1.1.length =
            word.1.length := by
          rw [hsourceRegion]
          exact hsourceLength
        simp only [PolygonWord.formalInverse_val, List.length_map,
          List.length_reverse] at htargetLength
        rw [hboundaryLength]
        omega
    _ = ((source.1.1.get sourceIndex).1, !(source.1.1.get sourceIndex).2) := by
      rw [hsourceLookup]

/-- Helper for Definition 76.6: a retained target edge has exactly the same signed letter
as its source edge. -/
theorem flipLetter_remainder (region : Occurrence rest)
    (edge : Fin (((consOccurrenceEquiv word.formalInverse rest).symm
      (some region)).1.1.length)) :
    ((consOccurrenceEquiv word.formalInverse rest).symm (some region)).1.1.get edge =
      ((consOccurrenceEquiv word rest).symm (some region)).1.1.get
        (Fin.cast
          (congrArg (fun source : Occurrence (word ::ₘ rest) ↦ source.1.1.length)
            (flipRegionEquiv_symm_remainder region))
          (flipEdgeIndex
            ((consOccurrenceEquiv word.formalInverse rest).symm (some region)) edge)) := by
  -- Compare retained dependent lookups through their common remainder word.
  let target := (consOccurrenceEquiv word.formalInverse rest).symm (some region)
  let source := (consOccurrenceEquiv word rest).symm (some region)
  let sourceIndex := Fin.cast
    (congrArg (fun source : Occurrence (word ::ₘ rest) ↦ source.1.1.length)
      (flipRegionEquiv_symm_remainder region)) (flipEdgeIndex target edge)
  have htargetList : target.1.1 = region.1.1 :=
    congrArg (fun polygon : PolygonWord α ↦ polygon.1)
      (Renumbering.consOccurrenceEquiv_symm_some_word word.formalInverse rest region)
  have hsourceList : source.1.1 = region.1.1 :=
    congrArg (fun polygon : PolygonWord α ↦ polygon.1)
      (Renumbering.consOccurrenceEquiv_symm_some_word word rest region)
  apply Renumbering.get_eq_of_list_eq_of_val_eq edge sourceIndex
  · exact htargetList.trans hsourceList.symm
  · dsimp only [sourceIndex, target]
    rw [flipEdgeIndex_remainder]
    simp only [Fin.val_cast]

/-- Flip one selected polygonal region while retaining every region in the remainder. -/
@[expose]
noncomputable def flipped (original : PolygonalRegions.{u, v} (word ::ₘ rest)) :
    PolygonalRegions (word.formalInverse ::ₘ rest) where
  Point region := original.Point (flipRegionEquiv.symm region)
  topology region := original.topology (flipRegionEquiv.symm region)
  edge region edge t :=
    original.edge (flipRegionEquiv.symm region) (flipEdgeIndex region edge)
      (flipParameter region t)

/-- The edge map of a flipped family is the original edge map at the computed
reversed index and parameter. -/
theorem flipped_edge (original : PolygonalRegions.{u, v} (word ::ₘ rest))
    (region : Occurrence (word.formalInverse ::ₘ rest))
    (edge : Fin region.1.1.length) (t : unitInterval) :
    original.flipped.edge region edge t =
      original.edge (flipRegionEquiv.symm region) (flipEdgeIndex region edge)
        (flipParameter region t) := by
  -- This is the edge projection of the flipped family.
  rfl

/-- The occurrence equivalence induces an equivalence of sources before and after a flip. -/
noncomputable def flipSourceEquiv (original : PolygonalRegions.{u, v} (word ::ₘ rest)) :
    original.Source ≃ original.flipped.Source :=
  Equiv.sigmaCongr flipRegionEquiv fun region ↦
    Equiv.cast (congrArg original.Point (flipRegionEquiv.left_inv region).symm)

/-- Helper for Definition 76.6: the source equivalence induced by a polygon flip is
continuous. -/
theorem continuous_flipSourceEquiv
    (original : PolygonalRegions.{u, v} (word ::ₘ rest)) :
    Continuous original.flipSourceEquiv := by
  -- Check continuity separately on each original polygonal-region component.
  change @Continuous _ _ original.sourceTopology original.flipped.sourceTopology _
  rw [continuous_iSup_dom]
  intro region
  rw [continuous_coinduced_dom]
  let target := flipRegionEquiv region
  have hregion := flipRegionEquiv.left_inv region
  have hcast := continuous_regionPointCast original hregion
  have hinclusion :
      @Continuous (original.flipped.Point target) original.flipped.Source
        (original.flipped.topology target) original.flipped.sourceTopology
        (Sigma.mk target) :=
    continuous_iSup_rng (i := target) (f := Sigma.mk target)
      (continuous_coinduced_rng (f := Sigma.mk target))
  dsimp [flipSourceEquiv, Equiv.sigmaCongr]
  exact @Continuous.comp
    (original.Point region) (original.flipped.Point target) original.flipped.Source
    (original.topology region) (original.flipped.topology target)
    original.flipped.sourceTopology _ _ hinclusion hcast

/-- Helper for Definition 76.6: the inverse source equivalence induced by a polygon flip
is continuous. -/
theorem continuous_flipSourceEquiv_symm
    (original : PolygonalRegions.{u, v} (word ::ₘ rest)) :
    Continuous original.flipSourceEquiv.symm := by
  -- Each inverse component is the canonical inclusion of the corresponding original region.
  change @Continuous _ _ original.flipped.sourceTopology original.sourceTopology _
  rw [continuous_iSup_dom]
  intro region
  rw [continuous_coinduced_dom]
  let source := flipRegionEquiv.symm region
  letI : TopologicalSpace (original.Point source) := original.topology source
  have hinclusion : Continuous
      (Sigma.mk source : original.Point source → original.Source) :=
    continuous_iSup_rng (i := source) (f := Sigma.mk source)
      (continuous_coinduced_rng (f := Sigma.mk source))
  have hinverse :
      original.flipSourceEquiv.symm ∘ Sigma.mk region =
        (Sigma.mk source : original.Point source → original.Source) := by
    funext point
    dsimp only [Function.comp_apply]
    dsimp [flipped, source] at point
    apply original.flipSourceEquiv.injective
    rw [original.flipSourceEquiv.apply_symm_apply]
    apply Sigma.ext
    · exact flipRegionEquiv.apply_symm_apply region |>.symm
    · exact (cast_heq _ _).symm
  rw [hinverse]
  exact hinclusion

/-- The source equivalence for a flip preserves the disjoint-union topologies. -/
theorem flipSourceEquiv_isOpen_iff
    (original : PolygonalRegions.{u, v} (word ::ₘ rest))
    (s : Set original.flipped.Source) :
    IsOpen (original.flipSourceEquiv ⁻¹' s) ↔ IsOpen s := by
  constructor
  · intro hopen
    -- Pull the open preimage back through the continuous inverse and cancel the equivalence.
    have hpreimage :
        original.flipSourceEquiv.symm ⁻¹' (original.flipSourceEquiv ⁻¹' s) = s := by
      ext point
      simp only [Set.mem_preimage, Equiv.apply_symm_apply]
    rw [← hpreimage]
    exact original.continuous_flipSourceEquiv_symm.isOpen_preimage _ hopen
  · intro hopen
    exact original.continuous_flipSourceEquiv.isOpen_preimage _ hopen

/-- Flipping a polygon induces a homeomorphism of disjoint-union sources. -/
noncomputable def flipSourceHomeomorph (original : PolygonalRegions.{u, v} (word ::ₘ rest)) :
    original.Source ≃ₜ original.flipped.Source :=
  original.flipSourceEquiv.toHomeomorph (original.flipSourceEquiv_isOpen_iff)

/-- The inverse flip source homeomorphism has the same underlying function as
the inverse source equivalence. -/
theorem flipSourceHomeomorph_symm_apply
    (original : PolygonalRegions.{u, v} (word ::ₘ rest))
    (x : original.flipped.Source) :
    original.flipSourceHomeomorph.symm x = original.flipSourceEquiv.symm x := by
  -- `toHomeomorph` retains both functions of the source equivalence.
  rfl

/-- Helper for Definition 76.6: a Boolean flag records whether an occurrence is the
polygon whose orientation is reversed. -/
private noncomputable def flipIndicator
    (region : Occurrence (word.formalInverse ::ₘ rest)) : Bool :=
  match consOccurrenceEquiv word.formalInverse rest region with
  | none => true
  | some _ => false

/-- Helper for Definition 76.6: reverse a boundary orientation exactly when the flag is
set. -/
private def orientationAfterFlip (flipped : Bool) (sign : Bool) : Bool :=
  if flipped then !sign else sign

/-- Helper for Definition 76.6: reverse an affine edge parameter exactly when the flag is
set. -/
private def parameterAfterFlip (flipped : Bool) (t : unitInterval) : unitInterval :=
  if flipped then unitInterval.symm t else t

/-- Helper for Definition 76.6: the selected occurrence has its flip flag set. -/
private theorem flipIndicator_selected :
    flipIndicator ((consOccurrenceEquiv word.formalInverse rest).symm none) = true := by
  -- The distinguished occurrence is represented by `none` under the cons equivalence.
  unfold flipIndicator
  rw [(consOccurrenceEquiv word.formalInverse rest).apply_symm_apply]

/-- Helper for Definition 76.6: every retained occurrence has its flip flag unset. -/
private theorem flipIndicator_remainder (region : Occurrence rest) :
    flipIndicator
        ((consOccurrenceEquiv word.formalInverse rest).symm (some region)) = false := by
  -- Retained occurrences are represented by `some region` under the cons equivalence.
  unfold flipIndicator
  rw [(consOccurrenceEquiv word.formalInverse rest).apply_symm_apply]

/-- Helper for Definition 76.6: the existing parameter map is the flag-controlled affine
reversal. -/
private theorem flipParameter_eq_parameterAfterFlip
    (region : Occurrence (word.formalInverse ::ₘ rest)) (t : unitInterval) :
    flipParameter region t = parameterAfterFlip (flipIndicator region) t := by
  -- Normalize the selected and retained occurrence branches separately.
  let targetEquiv := consOccurrenceEquiv word.formalInverse rest
  cases hposition : targetEquiv region with
  | none =>
      have hregion : region = targetEquiv.symm none :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      rw [flipParameter_selected, flipIndicator_selected]
      rfl
  | some remainder =>
      have hregion : region = targetEquiv.symm (some remainder) :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      rw [flipParameter_remainder, flipIndicator_remainder]
      rfl

/-- Helper for Definition 76.6: each flipped boundary letter keeps its label and changes
its sign exactly on the selected polygon. -/
private theorem flipLetter_eq_orientationAfterFlip
    (region : Occurrence (word.formalInverse ::ₘ rest))
    (edge : Fin region.1.1.length) :
    region.1.1.get edge =
      (((flipRegionEquiv.symm region).1.1.get (flipEdgeIndex region edge)).1,
        orientationAfterFlip (flipIndicator region)
          ((flipRegionEquiv.symm region).1.1.get (flipEdgeIndex region edge)).2) := by
  -- Reduce to the concrete selected-letter and retained-letter computation rules.
  let targetEquiv := consOccurrenceEquiv word.formalInverse rest
  cases hposition : targetEquiv region with
  | none =>
      have hregion : region = targetEquiv.symm none :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      have hboundary :
          (⟨flipRegionEquiv.symm (targetEquiv.symm none),
              flipEdgeIndex (targetEquiv.symm none) edge⟩ :
            (r : Occurrence (word ::ₘ rest)) × Fin r.1.1.length) =
            ⟨(consOccurrenceEquiv word rest).symm none,
              Fin.cast
                (congrArg (fun r : Occurrence (word ::ₘ rest) ↦ r.1.1.length)
                  flipRegionEquiv_symm_selected)
                (flipEdgeIndex (targetEquiv.symm none) edge)⟩ := by
        apply Sigma.ext flipRegionEquiv_symm_selected
        exact (Fin.heq_ext_iff
          (congrArg (fun r : Occurrence (word ::ₘ rest) ↦ r.1.1.length)
            flipRegionEquiv_symm_selected)).mpr rfl
      have hsourceLetter := congrArg
        (fun p : (r : Occurrence (word ::ₘ rest)) × Fin r.1.1.length ↦
          p.1.1.1.get p.2) hboundary
      rw [hsourceLetter, flipIndicator_selected]
      exact flipLetter_selected edge
  | some remainder =>
      have hregion : region = targetEquiv.symm (some remainder) :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      have hboundary :
          (⟨flipRegionEquiv.symm (targetEquiv.symm (some remainder)),
              flipEdgeIndex (targetEquiv.symm (some remainder)) edge⟩ :
            (r : Occurrence (word ::ₘ rest)) × Fin r.1.1.length) =
            ⟨(consOccurrenceEquiv word rest).symm (some remainder),
              Fin.cast
                (congrArg (fun r : Occurrence (word ::ₘ rest) ↦ r.1.1.length)
                  (flipRegionEquiv_symm_remainder remainder))
                (flipEdgeIndex (targetEquiv.symm (some remainder)) edge)⟩ := by
        apply Sigma.ext (flipRegionEquiv_symm_remainder remainder)
        exact (Fin.heq_ext_iff
          (congrArg (fun r : Occurrence (word ::ₘ rest) ↦ r.1.1.length)
            (flipRegionEquiv_symm_remainder remainder))).mpr rfl
      have hsourceLetter := congrArg
        (fun p : (r : Occurrence (word ::ₘ rest)) × Fin r.1.1.length ↦
          p.1.1.1.get p.2) hboundary
      rw [hsourceLetter, flipIndicator_remainder]
      exact flipLetter_remainder remainder edge

/-- Helper for Definition 76.6: pulling a forward-reindexed flipped edge back to the
original boundary recovers the original signed letter. -/
private theorem flipOriginalLetter_eq (region : Occurrence (word ::ₘ rest))
    (edge : Fin region.1.1.length) :
    let target := flipRegionEquiv region
    let sourceEdge := Fin.cast
      (congrArg (fun r : Occurrence (word ::ₘ rest) ↦ r.1.1.length)
        (flipRegionEquiv.left_inv region)).symm edge
    (flipRegionEquiv.symm target).1.1.get
        (flipEdgeIndex target (flipEdgeEquiv target sourceEdge)) =
      region.1.1.get edge := by
  -- Cancel both equivalences as one dependent boundary-position equality.
  dsimp only
  rw [← flipEdgeEquiv_symm_apply]
  have hregion := flipRegionEquiv.left_inv region
  let sourceEdge := Fin.cast
    (congrArg (fun r : Occurrence (word ::ₘ rest) ↦ r.1.1.length) hregion).symm edge
  have hsourceEdge : HEq sourceEdge edge :=
    (Fin.heq_ext_iff
      (congrArg (fun r : Occurrence (word ::ₘ rest) ↦ r.1.1.length) hregion)).mpr rfl
  have hboundary :
      (⟨flipRegionEquiv.symm (flipRegionEquiv region),
          (flipEdgeEquiv (flipRegionEquiv region)).symm
            (flipEdgeEquiv (flipRegionEquiv region) sourceEdge)⟩ :
        (r : Occurrence (word ::ₘ rest)) × Fin r.1.1.length) = ⟨region, edge⟩ := by
    apply Sigma.ext hregion
    exact (heq_of_eq
      ((flipEdgeEquiv (flipRegionEquiv region)).symm_apply_apply sourceEdge)).trans
        hsourceEdge
  exact congrArg
    (fun p : (r : Occurrence (word ::ₘ rest)) × Fin r.1.1.length ↦
      p.1.1.1.get p.2) hboundary

/-- Helper for Definition 76.6: independently reversing either boundary orientation
preserves the sign-dependent affine pairing rule in both directions. -/
private theorem parameterPairing_afterFlips (flipped₁ flipped₂ sign₁ sign₂ : Bool)
    (t : unitInterval) :
    parameterAfterFlip flipped₂
        (if orientationAfterFlip flipped₁ sign₁ = orientationAfterFlip flipped₂ sign₂
          then t else unitInterval.symm t) =
      (if sign₁ = sign₂ then parameterAfterFlip flipped₁ t
        else unitInterval.symm (parameterAfterFlip flipped₁ t)) ∧
    parameterAfterFlip flipped₂
        (if sign₁ = sign₂ then t else unitInterval.symm t) =
      (if orientationAfterFlip flipped₁ sign₁ = orientationAfterFlip flipped₂ sign₂
        then parameterAfterFlip flipped₁ t
        else unitInterval.symm (parameterAfterFlip flipped₁ t)) := by
  -- The four flag combinations and four sign combinations reduce to involutivity.
  cases flipped₁ <;> cases flipped₂ <;> cases sign₁ <;> cases sign₂ <;>
    simp [orientationAfterFlip, parameterAfterFlip, unitInterval.symm_symm]

/-- Helper for Definition 76.6: flipped boundary data preserves labels and transports both
forms of the sign-dependent parameter equation. -/
private theorem flipBoundaryPairingData
    (region₁ region₂ : Occurrence (word.formalInverse ::ₘ rest))
    (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
    (t : unitInterval) :
    let targetLetter₁ := region₁.1.1.get edge₁
    let targetLetter₂ := region₂.1.1.get edge₂
    let sourceLetter₁ :=
      (flipRegionEquiv.symm region₁).1.1.get (flipEdgeIndex region₁ edge₁)
    let sourceLetter₂ :=
      (flipRegionEquiv.symm region₂).1.1.get (flipEdgeIndex region₂ edge₂)
    (targetLetter₁.1 = targetLetter₂.1 ↔ sourceLetter₁.1 = sourceLetter₂.1) ∧
      flipParameter region₂
          (if targetLetter₁.2 = targetLetter₂.2 then t else unitInterval.symm t) =
        (if sourceLetter₁.2 = sourceLetter₂.2 then flipParameter region₁ t
          else unitInterval.symm (flipParameter region₁ t)) ∧
      flipParameter region₂
          (if sourceLetter₁.2 = sourceLetter₂.2 then t else unitInterval.symm t) =
        (if targetLetter₁.2 = targetLetter₂.2 then flipParameter region₁ t
          else unitInterval.symm (flipParameter region₁ t)) := by
  -- Rewrite both target letters and parameters to the common flag-controlled normal form.
  dsimp only
  rw [flipLetter_eq_orientationAfterFlip, flipLetter_eq_orientationAfterFlip,
    flipParameter_eq_parameterAfterFlip, flipParameter_eq_parameterAfterFlip,
    flipParameter_eq_parameterAfterFlip]
  exact ⟨Iff.rfl, parameterPairing_afterFlips
    (flipIndicator region₁) (flipIndicator region₂)
    ((flipRegionEquiv.symm region₁).1.1.get (flipEdgeIndex region₁ edge₁)).2
    ((flipRegionEquiv.symm region₂).1.1.get (flipEdgeIndex region₂ edge₂)).2 t⟩

/-- Helper for Definition 76.6: reversing the selected edge parameter twice recovers the
original parameter. -/
private theorem flipParameter_involutive
    (region : Occurrence (word.formalInverse ::ₘ rest)) (t : unitInterval) :
    flipParameter region (flipParameter region t) = t := by
  -- Split according to whether this is the flipped polygon or a retained polygon.
  let targetEquiv := consOccurrenceEquiv word.formalInverse rest
  cases hposition : targetEquiv region with
  | none =>
      have hregion : region = targetEquiv.symm none :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      rw [flipParameter_selected, flipParameter_selected, unitInterval.symm_symm]
  | some remainder =>
      have hregion : region = targetEquiv.symm (some remainder) :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      rw [flipParameter_remainder, flipParameter_remainder]

/-- Helper for Definition 76.6: pulling a flipped boundary point back through the source
equivalence recovers its original edge index and reversed parameter. -/
theorem flipSourceEquiv_symm_edge
    (original : PolygonalRegions.{u, v} (word ::ₘ rest))
    (region : Occurrence (word.formalInverse ::ₘ rest))
    (edge : Fin region.1.1.length) (t : unitInterval) :
    original.flipSourceEquiv.symm
        ⟨region, original.flipped.edge region edge t⟩ =
      ⟨flipRegionEquiv.symm region,
        original.edge (flipRegionEquiv.symm region) (flipEdgeIndex region edge)
          (flipParameter region t)⟩ := by
  -- Apply the forward equivalence, then compare the two dependent sigma components.
  apply original.flipSourceEquiv.injective
  rw [original.flipSourceEquiv.apply_symm_apply]
  apply Sigma.ext
  · exact flipRegionEquiv.apply_symm_apply region |>.symm
  · dsimp [flipSourceEquiv, Equiv.sigmaCongr, flipped]
    exact (cast_heq _ _).symm

/-- Helper for Definition 76.6: the source equivalence sends an original boundary point to
the reversed target edge and parameter. -/
theorem flipSourceEquiv_edge
    (original : PolygonalRegions.{u, v} (word ::ₘ rest))
    (region : Occurrence (word ::ₘ rest)) (edge : Fin region.1.1.length)
    (t : unitInterval) :
    original.flipSourceEquiv ⟨region, original.edge region edge t⟩ =
      let target := flipRegionEquiv region
      let sourceEdge := Fin.cast
        (congrArg (fun r : Occurrence (word ::ₘ rest) ↦ r.1.1.length)
          (flipRegionEquiv.left_inv region)).symm edge
      ⟨target, original.flipped.edge target
        (flipEdgeEquiv target sourceEdge) (flipParameter target t)⟩ := by
  -- Cancel the occurrence and edge equivalences before comparing the edge-map values.
  apply Sigma.ext
  · rfl
  · have hregion := flipRegionEquiv.left_inv region
    let target := flipRegionEquiv region
    let sourceEdge := Fin.cast
      (congrArg (fun r : Occurrence (word ::ₘ rest) ↦ r.1.1.length) hregion).symm edge
    have hsourceEdge : HEq sourceEdge edge :=
      (Fin.heq_ext_iff
        (congrArg (fun r : Occurrence (word ::ₘ rest) ↦ r.1.1.length) hregion)).mpr rfl
    have hboundary :
        (⟨flipRegionEquiv.symm target,
            (flipEdgeEquiv target).symm (flipEdgeEquiv target sourceEdge)⟩ :
          (r : Occurrence (word ::ₘ rest)) × Fin r.1.1.length) = ⟨region, edge⟩ := by
      apply Sigma.ext hregion
      exact (heq_of_eq ((flipEdgeEquiv target).symm_apply_apply sourceEdge)).trans
        hsourceEdge
    have hedge := congr_arg_heq
      (fun p : (r : Occurrence (word ::ₘ rest)) × Fin r.1.1.length ↦
        original.edge p.1 p.2 t) hboundary
    dsimp [flipSourceEquiv, Equiv.sigmaCongr, flipped, target, sourceEdge]
    rw [← flipEdgeEquiv_symm_apply, flipParameter_involutive]
    exact (cast_heq _ _).trans hedge.symm

/-- Helper for Definition 76.6: flipping preserves and reflects direct labelled-edge pairings. -/
theorem edgeRelated_flipped_iff (original : PolygonalRegions.{u, v} (word ::ₘ rest))
    (x y : original.Source) :
    original.EdgeRelated x y ↔
      original.flipped.EdgeRelated (original.flipSourceEquiv x)
        (original.flipSourceEquiv y) := by
  rw [edgeRelated_iff_exists_boundaryData, edgeRelated_iff_exists_boundaryData]
  constructor
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabel, hx, hy⟩
    let mapped₁ := flipRegionEquiv region₁
    let mapped₂ := flipRegionEquiv region₂
    let sourceEdge₁ := Fin.cast
      (congrArg (fun r : Occurrence (word ::ₘ rest) ↦ r.1.1.length)
        (flipRegionEquiv.left_inv region₁)).symm edge₁
    let sourceEdge₂ := Fin.cast
      (congrArg (fun r : Occurrence (word ::ₘ rest) ↦ r.1.1.length)
        (flipRegionEquiv.left_inv region₂)).symm edge₂
    let mappedEdge₁ := flipEdgeEquiv mapped₁ sourceEdge₁
    let mappedEdge₂ := flipEdgeEquiv mapped₂ sourceEdge₂
    have hpairing := flipBoundaryPairingData mapped₁ mapped₂ mappedEdge₁ mappedEdge₂ t
    have hmappedLabel :
        (mapped₁.1.1.get mappedEdge₁).1 = (mapped₂.1.1.get mappedEdge₂).1 := by
      apply hpairing.1.mpr
      simpa only [mapped₁, mapped₂, mappedEdge₁, mappedEdge₂, sourceEdge₁,
        sourceEdge₂, flipOriginalLetter_eq] using hlabel
    have hmappedParameter :
        flipParameter mapped₂
            (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
              else unitInterval.symm t) =
          (if (mapped₁.1.1.get mappedEdge₁).2 =
              (mapped₂.1.1.get mappedEdge₂).2 then flipParameter mapped₁ t
            else unitInterval.symm (flipParameter mapped₁ t)) := by
      simpa only [mapped₁, mapped₂, mappedEdge₁, mappedEdge₂, sourceEdge₁,
        sourceEdge₂, flipOriginalLetter_eq] using hpairing.2.2
    refine ⟨mapped₁, mapped₂, mappedEdge₁, mappedEdge₂, flipParameter mapped₁ t,
      hmappedLabel, ?_, ?_⟩
    · -- The forward source equivalence computes on the first original edge point.
      rw [hx, flipSourceEquiv_edge]
    · -- Transport the second parameter through both independent orientation reversals.
      rw [hy, flipSourceEquiv_edge]
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (congrArg (original.flipped.edge mapped₂ mappedEdge₂)
          hmappedParameter)
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabel, hx, hy⟩
    let source₁ := flipRegionEquiv.symm region₁
    let source₂ := flipRegionEquiv.symm region₂
    let sourceEdge₁ := flipEdgeIndex region₁ edge₁
    let sourceEdge₂ := flipEdgeIndex region₂ edge₂
    have hpairing := flipBoundaryPairingData region₁ region₂ edge₁ edge₂ t
    refine ⟨source₁, source₂, sourceEdge₁, sourceEdge₂, flipParameter region₁ t,
      hpairing.1.mp hlabel, ?_, ?_⟩
    · -- Pull the first flipped boundary point back through the source equivalence.
      have hx' := congrArg original.flipSourceEquiv.symm hx
      simpa only [Equiv.symm_apply_apply, flipSourceEquiv_symm_edge, source₁,
        sourceEdge₁] using hx'
    · -- Pull back the second point and use the backward affine pairing computation.
      have hy' := congrArg original.flipSourceEquiv.symm hy
      simpa only [Equiv.symm_apply_apply, flipSourceEquiv_symm_edge, source₁, source₂,
        sourceEdge₁, sourceEdge₂, hpairing.2.1] using hy'

/-- Flipping preserves and reflects the generated labelled-edge identification relation. -/
theorem identified_flip_iff (original : PolygonalRegions.{u, v} (word ::ₘ rest))
    (x y : original.Source) :
    original.Identified.r x y ↔
      original.flipped.Identified.r (original.flipSourceEquiv x)
        (original.flipSourceEquiv y) := by
  -- Lift the direct flip relation through the equivalence closure.
  rw [identified_iff_generatedEdgeRelated, identified_iff_generatedEdgeRelated]
  exact (eqvGen_equiv_iff original.flipSourceEquiv
    (fun first second ↦ (original.edgeRelated_flipped_iff first second).symm) x y).symm

/-- The source equivalence for a flip descends to an equivalence of quotient realizations. -/
noncomputable def flipRealizationEquiv (original : PolygonalRegions.{u, v} (word ::ₘ rest)) :
    Quotient original.Identified ≃ Quotient original.flipped.Identified :=
  Quotient.congr original.flipSourceEquiv original.identified_flip_iff

/-- The quotient equivalence induced by a flip preserves the quotient topologies. -/
theorem flipRealizationEquiv_isOpen_iff
    (original : PolygonalRegions.{u, v} (word ::ₘ rest))
    (s : Set (Quotient original.flipped.Identified)) :
    IsOpen (original.flipRealizationEquiv ⁻¹' s) ↔ IsOpen s := by
  -- Quotient congruence applied to the source homeomorphism is the displayed quotient map.
  exact (Homeomorph.Quotient.congr original.flipSourceHomeomorph
    original.identified_flip_iff).isOpen_preimage

/-- Flipping one polygon induces a homeomorphism of quotient realizations. -/
noncomputable def flipRealizationHomeomorph
    (original : PolygonalRegions.{u, v} (word ::ₘ rest)) :
    Quotient original.Identified ≃ₜ Quotient original.flipped.Identified :=
  original.flipRealizationEquiv.toHomeomorph
    (original.flipRealizationEquiv_isOpen_iff)

/-- Relabelling preserves and reflects generated labelled-edge identifications. -/
theorem identified_relabel_iff {β : Type w}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    (e : α ≃ β) (x y : regions.Source) :
    (regions.relabel e).Identified.r (relabelSourceEquiv regions e x)
        (relabelSourceEquiv regions e y) ↔
      regions.Identified.r x y := by
  -- Lift the proved direct relabelling relation through its equivalence closure.
  rw [identified_iff_generatedEdgeRelated, identified_iff_generatedEdgeRelated]
  exact eqvGen_equiv_iff (relabelSourceEquiv regions e)
    (edgeRelated_relabel_iff regions e) x y

/-- The relabelling quotient equivalence preserves the quotient topologies. -/
theorem relabelRealizationEquiv_isOpen_iff {β : Type w}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    (e : α ≃ β) (s : Set (Quotient (regions.relabel e).Identified)) :
    IsOpen ((Quotient.congr (relabelSourceEquiv regions e) fun x y ↦
      (identified_relabel_iff regions e x y).symm) ⁻¹' s) ↔ IsOpen s := by
  -- Quotient congruence applied to the source homeomorphism has the displayed map.
  have hidentified (x y : regions.Source) :
      regions.Identified.r x y ↔
        (regions.relabel e).Identified.r (relabelSourceHomeomorph regions e x)
          (relabelSourceHomeomorph regions e y) := by
    simpa only [relabelSourceHomeomorph_apply] using
      (identified_relabel_iff regions e x y).symm
  exact (Homeomorph.Quotient.congr (relabelSourceHomeomorph regions e)
    hidentified).isOpen_preimage

/-- Relabelling induces a homeomorphism of quotient realizations. -/
noncomputable def relabelRealizationHomeomorph {β : Type w}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme) (e : α ≃ β) :
    Quotient regions.Identified ≃ₜ
      Quotient (regions.relabel e).Identified :=
  (Quotient.congr (relabelSourceEquiv regions e) fun x y ↦
    (identified_relabel_iff regions e x y).symm).toHomeomorph
      (relabelRealizationEquiv_isOpen_iff regions e)

/-- Fresh replacement of one label preserves and reflects labelled-edge identifications. -/
theorem identified_renameLabel_iff {scheme : LabellingScheme α}
    (regions : PolygonalRegions.{u, v} scheme) (a c : α) (h_ac : a ≠ c)
    (h_fresh : scheme.AvoidsLabel c) (x y : regions.Source) :
    (regions.renameLabel a c).Identified.r
        (renameLabelSourceEquiv regions a c x) (renameLabelSourceEquiv regions a c y) ↔
      regions.Identified.r x y := by
  -- Fresh renaming is the relabelling identification theorem at the label transposition.
  exact identified_relabel_iff regions (PolygonWord.swapLabels a c) x y

/-- The fresh-renaming quotient equivalence preserves the quotient topologies. -/
theorem renameLabelRealizationEquiv_isOpen_iff {scheme : LabellingScheme α}
    (regions : PolygonalRegions.{u, v} scheme) (a c : α) (h_ac : a ≠ c)
    (h_fresh : scheme.AvoidsLabel c)
    (s : Set (Quotient (regions.renameLabel a c).Identified)) :
    IsOpen ((Quotient.congr (renameLabelSourceEquiv regions a c) fun x y ↦
      (identified_renameLabel_iff regions a c h_ac h_fresh x y).symm) ⁻¹' s) ↔
      IsOpen s := by
  -- Normalize the rename construction before invoking the canonical relabelling theorem.
  unfold renameLabel renameLabelSourceEquiv
  exact relabelRealizationEquiv_isOpen_iff regions (PolygonWord.swapLabels a c) s

/-- Fresh replacement of one label induces a homeomorphism of realizations. -/
noncomputable def renameLabelRealizationHomeomorph {scheme : LabellingScheme α}
    (regions : PolygonalRegions.{u, v} scheme) (a c : α) (h_ac : a ≠ c)
    (h_fresh : scheme.AvoidsLabel c) :
    Quotient regions.Identified ≃ₜ
      Quotient (regions.renameLabel a c).Identified :=
  (Quotient.congr (renameLabelSourceEquiv regions a c) fun x y ↦
    (identified_renameLabel_iff regions a c h_ac h_fresh x y).symm).toHomeomorph
      (renameLabelRealizationEquiv_isOpen_iff regions a c h_ac h_fresh)

/-- Reversing one label's signs preserves and reflects labelled-edge identifications. -/
theorem identified_reverseLabel_iff {scheme : LabellingScheme α}
    (regions : PolygonalRegions.{u, v} scheme) (a : α) (x y : regions.Source) :
    (regions.reverseLabel a).Identified.r (reverseLabelSourceEquiv regions a x)
        (reverseLabelSourceEquiv regions a y) ↔
      regions.Identified.r x y := by
  -- Lift the proved direct sign-reversal relation through its equivalence closure.
  rw [identified_iff_generatedEdgeRelated, identified_iff_generatedEdgeRelated]
  exact eqvGen_equiv_iff (reverseLabelSourceEquiv regions a)
    (edgeRelated_reverseLabel_iff regions a) x y

/-- The sign-reversal quotient equivalence preserves the quotient topologies. -/
theorem reverseLabelRealizationEquiv_isOpen_iff {scheme : LabellingScheme α}
    (regions : PolygonalRegions.{u, v} scheme) (a : α)
    (s : Set (Quotient (regions.reverseLabel a).Identified)) :
    IsOpen ((Quotient.congr (reverseLabelSourceEquiv regions a) fun x y ↦
      (identified_reverseLabel_iff regions a x y).symm) ⁻¹' s) ↔ IsOpen s := by
  -- Quotient congruence transports the sign-reversal source homeomorphism.
  have hidentified (x y : regions.Source) :
      regions.Identified.r x y ↔
        (regions.reverseLabel a).Identified.r (reverseLabelSourceHomeomorph regions a x)
          (reverseLabelSourceHomeomorph regions a y) := by
    simpa only [reverseLabelSourceHomeomorph_apply] using
      (identified_reverseLabel_iff regions a x y).symm
  exact (Homeomorph.Quotient.congr (reverseLabelSourceHomeomorph regions a)
    hidentified).isOpen_preimage

/-- Reversing every occurrence of one label induces a homeomorphism of realizations. -/
noncomputable def reverseLabelRealizationHomeomorph {scheme : LabellingScheme α}
    (regions : PolygonalRegions.{u, v} scheme) (a : α) :
    Quotient regions.Identified ≃ₜ
      Quotient (regions.reverseLabel a).Identified :=
  (Quotient.congr (reverseLabelSourceEquiv regions a) fun x y ↦
    (identified_reverseLabel_iff regions a x y).symm).toHomeomorph
      (reverseLabelRealizationEquiv_isOpen_iff regions a)


end LabellingScheme.PolygonalRegions
