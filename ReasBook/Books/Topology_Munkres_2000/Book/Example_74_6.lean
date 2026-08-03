module

public import Topology_Munkres_2000.Book.Example_74_2.UnitSquare
public import Topology_Munkres_2000.Book.Notation_74_1.SignedLetter
public import Topology_Munkres_2000.Book.Proposition_76_1.Realization
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization

public section

open scoped SignedLetter

namespace DisconnectedSquares

/- Figure data transcribed from the Internet Archive scan `munkres2`, leaf 232
   (printed page 450), Figure 74.7. Starting at each lower-left corner and
   traversing counterclockwise gives `d a c⁻¹ a⁻¹` and `f b e⁻¹ b⁻¹`. -/

/-- The six edge labels appearing in Figure 74.7. -/
inductive Label
  | a
  | b
  | c
  | d
  | e
  | f
  deriving DecidableEq

/-- The signed boundary letters `d a c⁻¹ a⁻¹` of the first square in Figure 74.7. -/
def firstBoundaryLetters : List (Label × Bool) :=
  [Label.d, Label.a, Label.c⁻¹, Label.a⁻¹]

/-- The signed boundary letters `f b e⁻¹ b⁻¹` of the second square in Figure 74.7. -/
def secondBoundaryLetters : List (Label × Bool) :=
  [Label.f, Label.b, Label.e⁻¹, Label.b⁻¹]

/-- Helper for Example 74.6: both displayed boundary lists have enough letters to be
polygon words. -/
lemma boundaryLettersLengthBounds :
    3 ≤ firstBoundaryLetters.length ∧ 3 ≤ secondBoundaryLetters.length := by
  -- Both length conditions reduce to the four explicitly displayed letters.
  decide

/-- The polygon word `d a c⁻¹ a⁻¹` of the first square in Figure 74.7. -/
def firstBoundaryWord : PolygonWord Label :=
  ⟨firstBoundaryLetters, boundaryLettersLengthBounds.1⟩

/-- The polygon word `f b e⁻¹ b⁻¹` of the second square in Figure 74.7. -/
def secondBoundaryWord : PolygonWord Label :=
  ⟨secondBoundaryLetters, boundaryLettersLengthBounds.2⟩

/-- The two-square labelling scheme depicted in Figure 74.7. -/
def scheme : LabellingScheme Label :=
  firstBoundaryWord ::ₘ secondBoundaryWord ::ₘ 0

/-- The two unit squares with ordered boundary edges prescribed by Figure 74.7. -/
@[expose]
def regions : LabellingScheme.PolygonalRegions scheme where
  Point _ := unitInterval × unitInterval
  topology _ := inferInstance
  edge _ edge t := UnitSquare.edge edge t

/-- The labelled-edge realization of the two squares in Figure 74.7. -/
abbrev Realization := regions.Realization

/-- Helper for Example 74.6: the canonical occurrence of the first displayed square. -/
noncomputable def firstRegion : LabellingScheme.Occurrence scheme :=
  (LabellingScheme.consOccurrenceEquiv firstBoundaryWord
    (secondBoundaryWord ::ₘ 0)).symm none

/-- Helper for Example 74.6: the canonical occurrence of the second displayed square. -/
noncomputable def secondRegion : LabellingScheme.Occurrence scheme :=
  (LabellingScheme.consOccurrenceEquiv firstBoundaryWord
    (secondBoundaryWord ::ₘ 0)).symm
      (some ((LabellingScheme.consOccurrenceEquiv secondBoundaryWord 0).symm none))

/-- Helper for Example 74.6: the canonical occurrences project to the two displayed words. -/
lemma distinguishedRegionWordSpecs :
    firstRegion.1 = firstBoundaryWord ∧ secondRegion.1 = secondBoundaryWord := by
  -- The two projections are the computation rules for adjoining multiset occurrences.
  constructor
  · unfold firstRegion LabellingScheme.consOccurrenceEquiv LabellingScheme.Occurrence
    rfl
  · unfold secondRegion LabellingScheme.consOccurrenceEquiv LabellingScheme.Occurrence
    rfl

/-- Helper for Example 74.6: every occurrence is one of the two displayed squares. -/
lemma occurrence_eq_first_or_second (region : LabellingScheme.Occurrence scheme) :
    region = firstRegion ∨ region = secondRegion := by
  classical
  -- First split off the head occurrence of the two-word multiset.
  cases hfirst : LabellingScheme.consOccurrenceEquiv firstBoundaryWord
      (secondBoundaryWord ::ₘ 0) region with
  | none =>
      left
      apply (LabellingScheme.consOccurrenceEquiv firstBoundaryWord
        (secondBoundaryWord ::ₘ 0)).injective
      simpa only [firstRegion, Equiv.apply_symm_apply] using hfirst
  | some remaining =>
      -- The remainder is the unique occurrence in the singleton tail.
      cases hsecond : LabellingScheme.consOccurrenceEquiv secondBoundaryWord 0 remaining with
      | none =>
          right
          have hremaining : remaining =
              (LabellingScheme.consOccurrenceEquiv secondBoundaryWord 0).symm none := by
            apply (LabellingScheme.consOccurrenceEquiv secondBoundaryWord 0).injective
            simpa only [Equiv.apply_symm_apply] using hsecond
          apply (LabellingScheme.consOccurrenceEquiv firstBoundaryWord
            (secondBoundaryWord ::ₘ 0)).injective
          simpa only [secondRegion, Equiv.apply_symm_apply, hremaining] using hfirst
      | some impossible =>
          exact (Nat.not_lt_zero impossible.2 impossible.2.isLt).elim

/-- Helper for Example 74.6: a Boolean tag distinguishing the two square occurrences. -/
noncomputable def regionComponent (region : LabellingScheme.Occurrence scheme) : Bool :=
  match LabellingScheme.consOccurrenceEquiv firstBoundaryWord
      (secondBoundaryWord ::ₘ 0) region with
  | none => false
  | some _ => true

/-- Helper for Example 74.6: the two distinguished occurrences have opposite Boolean tags. -/
lemma distinguishedRegionComponentSpecs :
    regionComponent firstRegion = false ∧ regionComponent secondRegion = true := by
  -- Each tag follows directly from the corresponding branch of `consOccurrenceEquiv`.
  constructor
  · simp only [regionComponent, firstRegion, Equiv.apply_symm_apply]
  · simp only [regionComponent, secondRegion, Equiv.apply_symm_apply]

/-- Helper for Example 74.6: no unsigned boundary label occurs on both displayed squares. -/
lemma firstSecondBoundaryLabels_ne
    : ∀ (i : Fin firstBoundaryWord.1.length) (j : Fin secondBoundaryWord.1.length),
      (firstBoundaryWord.1.get i).1 ≠ (secondBoundaryWord.1.get j).1 := by
  -- Exhaustive computation checks the sixteen pairs of displayed boundary letters.
  decide

/-- Helper for Example 74.6: equal boundary labels can occur only within one square component. -/
lemma regionComponent_eq_of_boundaryLabel_eq
    (region₁ region₂ : LabellingScheme.Occurrence scheme)
    (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
    (hlabel : (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1) :
    regionComponent region₁ = regionComponent region₂ := by
  -- Classify both occurrences; the two cross cases contradict label disjointness.
  rcases occurrence_eq_first_or_second region₁ with hfirst₁ | hsecond₁
  · rcases occurrence_eq_first_or_second region₂ with hfirst₂ | hsecond₂
    · subst region₁
      subst region₂
      rfl
    · subst region₁
      subst region₂
      exact (firstSecondBoundaryLabels_ne edge₁ edge₂ hlabel).elim
  · rcases occurrence_eq_first_or_second region₂ with hfirst₂ | hsecond₂
    · subst region₁
      subst region₂
      exact (firstSecondBoundaryLabels_ne edge₂ edge₁ hlabel.symm).elim
    · subst region₁
      subst region₂
      rfl

/-- Helper for Example 74.6: the occurrence tag extended to the disjoint-union source. -/
noncomputable def sourceComponent (x : regions.Source) : Bool :=
  regionComponent x.1

/-- Helper for Example 74.6: directly paired points with the same unsigned edge label
have the same source component. -/
lemma sourceComponent_eq_of_edgePairing
    (region₁ region₂ : LabellingScheme.Occurrence scheme)
    (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
    (t : unitInterval)
    (hlabel : (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1) :
    sourceComponent ⟨region₁, regions.edge region₁ edge₁ t⟩ =
      sourceComponent ⟨region₂, regions.edge region₂ edge₂
        (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
          else unitInterval.symm t)⟩ := by
  -- The component tag depends only on the region, so label disjointness closes the pairing.
  exact regionComponent_eq_of_boundaryLabel_eq region₁ region₂ edge₁ edge₂ hlabel

/-- Helper for Example 74.6: the source tag is invariant under every generated identification. -/
lemma sourceComponent_eq_of_identified (x y : regions.Source)
    (hxy : regions.Identified.r x y) : sourceComponent x = sourceComponent y := by
  -- Route correction: work through the generated setoid's universal property instead of
  -- trying to induct on the opaque imported definition of `Identified` downstream.
  apply Setoid.eqvGen_le (s := Setoid.ker sourceComponent) ?_ hxy
  -- Every generating edge pairing preserves the component tag by label disjointness.
  intro x y hxy
  rcases hxy with ⟨region₁, region₂, edge₁, edge₂, t, hlabel, rfl, rfl⟩
  exact sourceComponent_eq_of_edgePairing region₁ region₂ edge₁ edge₂ t hlabel

/-- Helper for Example 74.6: a chosen source representative of a realization point. -/
noncomputable def realizationRepresentative (x : Realization) : regions.Source :=
  Classical.choose (regions.quotientMap_realizes.isQuotientMap.surjective x)

/-- Helper for Example 74.6: the chosen representative maps back to its realization point. -/
lemma realizationRepresentative_spec (x : Realization) :
    regions.quotientMap (realizationRepresentative x) = x := by
  -- This is the specification of the representative chosen from quotient-map surjectivity.
  exact Classical.choose_spec (regions.quotientMap_realizes.isQuotientMap.surjective x)

/-- Helper for Example 74.6: the square tag descends to the labelled-edge realization. -/
noncomputable def realizationComponent (x : Realization) : Bool :=
  sourceComponent (realizationRepresentative x)

/-- Helper for Example 74.6: the descended tag computes to the source tag on quotient images. -/
lemma realizationComponent_quotientMap (x : regions.Source) :
    realizationComponent (regions.quotientMap x) = sourceComponent x := by
  -- The chosen representative and `x` lie in the same quotient-map fiber.
  apply sourceComponent_eq_of_identified
  apply (regions.quotientMap_realizes.fibers _ _).mp
  exact realizationRepresentative_spec (regions.quotientMap x)

/-- Helper for Example 74.6: the source component restricts to a constant map on each
polygonal-region summand. -/
lemma sourceComponent_comp_sigmaMk (region : LabellingScheme.Occurrence scheme) :
    sourceComponent ∘ Sigma.mk region = fun _ : regions.Point region ↦ regionComponent region := by
  -- On a fixed sigma summand, the first projection is the fixed occurrence `region`.
  funext point
  rfl

/-- Helper for Example 74.6: the tag is continuous on the disjoint-union source. -/
lemma sourceComponent_continuous : Continuous sourceComponent := by
  -- The source topology reduces continuity to continuity on every polygonal-region summand.
  rw [continuous_iSup_dom]
  intro region
  letI : TopologicalSpace (regions.Point region) := regions.topology region
  rw [continuous_coinduced_dom, sourceComponent_comp_sigmaMk]
  -- The component tag is constant on the fixed summand.
  exact continuous_const

/-- Helper for Example 74.6: the descended Boolean component tag is continuous. -/
lemma realizationComponent_continuous : Continuous realizationComponent := by
  -- Continuity descends through the canonical quotient map.
  apply regions.quotientMap_realizes.isQuotientMap.continuous_iff.mpr
  have hcomposition : realizationComponent ∘ regions.quotientMap = sourceComponent := by
    funext x
    exact realizationComponent_quotientMap x
  rw [hcomposition]
  exact sourceComponent_continuous

/-- Helper for Example 74.6: the descended component tag takes both Boolean values. -/
lemma realizationComponent_nonconstant :
    ∃ x y : Realization, realizationComponent x ≠ realizationComponent y := by
  -- The quotient images of the two square origins retain their opposite tags.
  let firstPoint : regions.Source := ⟨firstRegion, (0, 0)⟩
  let secondPoint : regions.Source := ⟨secondRegion, (0, 0)⟩
  refine ⟨regions.quotientMap firstPoint, regions.quotientMap secondPoint, ?_⟩
  simp only [realizationComponent_quotientMap, sourceComponent, firstPoint, secondPoint,
    distinguishedRegionComponentSpecs.1, distinguishedRegionComponentSpecs.2]
  decide

/-- Example 74.6. The quotient specified by Figure 74.7 is not connected. -/
theorem realizationNotConnected : ¬ ConnectedSpace Realization := by
  -- Connectedness would force the continuous discrete-valued tag to be constant.
  intro hconnected
  letI : ConnectedSpace Realization := hconnected
  obtain ⟨x, y, hxy⟩ := realizationComponent_nonconstant
  exact hxy (PreconnectedSpace.constant inferInstance realizationComponent_continuous)


end DisconnectedSquares
