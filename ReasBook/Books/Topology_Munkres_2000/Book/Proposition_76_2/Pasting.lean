module

public import Topology_Munkres_2000.Book.Proposition_76_1.Realization
public import Topology_Munkres_2000.Book.Proposition_76_2.ReassemblyCorrection
public import Mathlib.Topology.Category.TopCat.Basic

public section

universe u v w

namespace LabellingScheme.PolygonalRegions

/-- A homeomorphism from a polygonal-region component to a topological space. -/
abbrev RegionHomeomorph {α : Type u} {scheme : LabellingScheme α}
    (regions : PolygonalRegions.{u, v} scheme) (region : Occurrence scheme)
    (X : Type w) [TopologicalSpace X] :=
  @Homeomorph (regions.Point region) X (regions.topology region) inferInstance

/-- A homeomorphism between components of two polygonal-region families. -/
abbrev RegionHomeomorph.Between {α : Type u}
    {leftScheme rightScheme : LabellingScheme α}
    (leftRegions : PolygonalRegions.{u, v} leftScheme) (leftRegion : Occurrence leftScheme)
    (rightRegions : PolygonalRegions.{u, v} rightScheme) (rightRegion : Occurrence rightScheme) :=
  @Homeomorph (leftRegions.Point leftRegion) (rightRegions.Point rightRegion)
    (leftRegions.topology leftRegion) (rightRegions.topology rightRegion)

/-- A component of `regions` presented by a concrete cyclic polygon, with the
labelling-scheme edge parameter agreeing with the affine polygon-edge parameter. -/
structure CyclicRegion {α : Type u} {scheme : LabellingScheme α}
    (regions : PolygonalRegions.{u, v} scheme) (region : Occurrence scheme) where
  polygon : CyclicPolygon region.1.1.length
  homeomorph : RegionHomeomorph regions region polygon.region
  edgeCompatibility (edge : Fin region.1.1.length) (t : unitInterval) :
    (homeomorph (regions.edge region edge t) : EuclideanSpace ℝ (Fin 2)) =
      AffineMap.lineMap (polygon.toPolygon.vertices edge)
        (polygon.toPolygon.vertices (finRotate region.1.1.length edge)) (t : ℝ)

namespace CyclicRegion

/-- Present a polygonal-region component by a cyclic polygon and an edge-compatible
homeomorphism. -/
def ofHomeomorph {α : Type u} {scheme : LabellingScheme α}
    {regions : PolygonalRegions.{u, v} scheme} {region : Occurrence scheme}
    (polygon : CyclicPolygon region.1.1.length)
    (homeomorph : RegionHomeomorph regions region polygon.region)
    (edgeCompatibility : ∀ (edge : Fin region.1.1.length) (t : unitInterval),
      (homeomorph (regions.edge region edge t) : EuclideanSpace ℝ (Fin 2)) =
        AffineMap.lineMap (polygon.toPolygon.vertices edge)
          (polygon.toPolygon.vertices (finRotate region.1.1.length edge)) (t : ℝ)) :
    CyclicRegion regions region :=
  ⟨polygon, homeomorph, edgeCompatibility⟩

/-- The underlying equivalence of a cyclic-region presentation. -/
def equiv {α : Type u} {scheme : LabellingScheme α}
    {regions : PolygonalRegions.{u, v} scheme} {region : Occurrence scheme}
    (presentation : CyclicRegion regions region) :
    regions.Point region ≃ presentation.polygon.region :=
  @Homeomorph.toEquiv _ _ (regions.topology region) inferInstance presentation.homeomorph

end CyclicRegion

/-- Every component of `regions` is geometrically a polygonal region, with its labelled
boundary parametrization agreeing with the affine parametrization of polygon edges. -/
def IsPolygonal {α : Type u} {scheme : LabellingScheme α}
    (regions : PolygonalRegions.{u, v} scheme) : Prop :=
  ∀ region, Nonempty (CyclicRegion regions region)

/-- A family is polygonal exactly when each component has a cyclic-polygon presentation
compatible with its labelled boundary edges. -/
theorem isPolygonal_iff {α : Type u} {scheme : LabellingScheme α}
    (regions : PolygonalRegions.{u, v} scheme) :
    regions.IsPolygonal ↔ ∀ region, Nonempty (CyclicRegion regions region) :=
  Iff.rfl

/--
Explicit geometric data carrying out one distinguished edge paste. The homeomorphism
identifies the exact quotient produced by `firstPaste` with the source of the merged
polygonal regions.
-/
structure Pasting {α : Type u} [DecidableEq α]
    {splitScheme : LabellingScheme α} (mergedScheme : LabellingScheme α)
    (splitRegions : PolygonalRegions.{u, v} splitScheme) (c : α)
    {Y : Type v} [TopologicalSpace Y] (firstPaste : splitRegions.Source → Y) where
  mergedRegions : PolygonalRegions.{u, v} mergedScheme
  pastesLabel : splitRegions.PastesLabel c firstPaste
  sourceHomeomorph : Y ≃ₜ mergedRegions.Source
  boundaryCompatibility (x y : Y) :
    (splitRegions.RemainingIdentified c firstPaste).r x y ↔
      mergedRegions.Identified.r (sourceHomeomorph x) (sourceHomeomorph y)

/-- The result of an edge paste together with cyclic presentations of the merged
first region and every retained region. -/
structure PasteResult {α : Type u} [DecidableEq α]
    {splitScheme mergedScheme : LabellingScheme α}
    (splitRegions : PolygonalRegions.{u, v} splitScheme) (c : α)
    (mergedFirst : Occurrence mergedScheme)
    {ι : Type u} (splitRest : ι → Occurrence splitScheme)
    (mergedRest : ι → Occurrence mergedScheme) where
  Intermediate : TopCat.{v}
  firstPaste : splitRegions.Source → Intermediate
  pasting : Pasting mergedScheme splitRegions c firstPaste
  mergedFirstRegion : CyclicRegion pasting.mergedRegions mergedFirst
  retained (region : ι) :
    RegionHomeomorph.Between splitRegions (splitRest region)
      pasting.mergedRegions (mergedRest region)
  retainedCyclicRegion (region : ι) :
    CyclicRegion pasting.mergedRegions (mergedRest region)

namespace PasteResult

/-- Extend a completed paste by cyclic data for its merged and retained components. -/
def ofPasting {α : Type u} [DecidableEq α]
    {splitScheme mergedScheme : LabellingScheme α}
    {splitRegions : PolygonalRegions.{u, v} splitScheme} {c : α}
    {mergedFirst : Occurrence mergedScheme}
    {ι : Type u} {splitRest : ι → Occurrence splitScheme}
    {mergedRest : ι → Occurrence mergedScheme}
    {Intermediate : TopCat.{v}} {firstPaste : splitRegions.Source → Intermediate}
    (pasting : Pasting mergedScheme splitRegions c firstPaste)
    (mergedFirstRegion : CyclicRegion pasting.mergedRegions mergedFirst)
    (retained : ∀ region, RegionHomeomorph.Between splitRegions (splitRest region)
      pasting.mergedRegions (mergedRest region))
    (retainedCyclicRegion : ∀ region,
      CyclicRegion pasting.mergedRegions (mergedRest region)) :
    PasteResult splitRegions c mergedFirst splitRest mergedRest :=
  ⟨Intermediate, firstPaste, pasting, mergedFirstRegion, retained, retainedCyclicRegion⟩

end PasteResult

namespace Pasting

/-- Build a completed paste from its merged regions, source homeomorphism, and
compatibility with the remaining boundary identifications. -/
def ofHomeomorph {α : Type u} [DecidableEq α]
    {splitScheme mergedScheme : LabellingScheme α}
    {splitRegions : PolygonalRegions.{u, v} splitScheme} {c : α}
    {Y : Type v} [TopologicalSpace Y] {firstPaste : splitRegions.Source → Y}
    (mergedRegions : PolygonalRegions.{u, v} mergedScheme)
    (pastesLabel : splitRegions.PastesLabel c firstPaste)
    (sourceHomeomorph : Y ≃ₜ mergedRegions.Source)
    (boundaryCompatibility : ∀ x y,
      (splitRegions.RemainingIdentified c firstPaste).r x y ↔
        mergedRegions.Identified.r (sourceHomeomorph x) (sourceHomeomorph y)) :
    Pasting mergedScheme splitRegions c firstPaste :=
  ⟨mergedRegions, pastesLabel, sourceHomeomorph, boundaryCompatibility⟩

/-- The first occurrence in a labelling scheme obtained by adjoining two words. -/
@[expose]
noncomputable def firstOccurrence (word₁ word₂ : PolygonWord α)
    (rest : LabellingScheme α) : Occurrence (word₁ ::ₘ word₂ ::ₘ rest) :=
  (consOccurrenceEquiv word₁ (word₂ ::ₘ rest)).symm none

/-- The second occurrence in a labelling scheme obtained by adjoining two words. -/
@[expose]
noncomputable def secondOccurrence (word₁ word₂ : PolygonWord α)
    (rest : LabellingScheme α) : Occurrence (word₁ ::ₘ word₂ ::ₘ rest) :=
  (consOccurrenceEquiv word₁ (word₂ ::ₘ rest)).symm
    (some ((consOccurrenceEquiv word₂ rest).symm none))

/-- An occurrence in the retained remainder, viewed in the split scheme. -/
@[expose]
noncomputable def splitRestOccurrence (word₁ word₂ : PolygonWord α)
    (rest : LabellingScheme α) (region : Occurrence rest) :
    Occurrence (word₁ ::ₘ word₂ ::ₘ rest) :=
  (consOccurrenceEquiv word₁ (word₂ ::ₘ rest)).symm
    (some ((consOccurrenceEquiv word₂ rest).symm (some region)))

/-- An occurrence in the retained remainder, viewed in the merged scheme. -/
@[expose]
noncomputable def mergedRestOccurrence (word : PolygonWord α)
    (rest : LabellingScheme α) (region : Occurrence rest) :
    Occurrence (word ::ₘ rest) :=
  (consOccurrenceEquiv word rest).symm (some region)

/-- The first occurrence in a labelling scheme obtained by adjoining one word. -/
@[expose]
noncomputable def mergedFirstOccurrence (word : PolygonWord α)
    (rest : LabellingScheme α) : Occurrence (word ::ₘ rest) :=
  (consOccurrenceEquiv word rest).symm none

/-- Helper for Proposition 76.2: the first distinguished occurrence has the first
adjoined polygon word. -/
theorem firstOccurrence_fst (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α) :
    (firstOccurrence word₁ word₂ rest).1 = word₁ := by
  -- Normalize the inverse multiset-cons equivalence at its distinguished point.
  unfold firstOccurrence consOccurrenceEquiv Occurrence
  exact congrArg Sigma.fst
    (@Multiset.consEquiv_symm_none (PolygonWord α) (Classical.decEq _)
      (word₂ ::ₘ rest) word₁)

/-- Helper for Proposition 76.2: the second distinguished occurrence has the second
adjoined polygon word. -/
theorem secondOccurrence_fst (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α) :
    (secondOccurrence word₁ word₂ rest).1 = word₂ := by
  -- Normalize first through the outer cons and then through the inner cons.
  unfold secondOccurrence consOccurrenceEquiv Occurrence
  rw [@Multiset.consEquiv_symm_some (PolygonWord α) (Classical.decEq _)
    (word₂ ::ₘ rest) word₁]
  exact congrArg Sigma.fst
    (@Multiset.consEquiv_symm_none (PolygonWord α) (Classical.decEq _) rest word₂)

/-- Helper for Proposition 76.2: an occurrence retained from the remainder keeps its
original polygon word when embedded in the split scheme. -/
theorem splitRestOccurrence_fst (word₁ word₂ : PolygonWord α)
    (rest : LabellingScheme α) (region : Occurrence rest) :
    (splitRestOccurrence word₁ word₂ rest region).1 = region.1 := by
  -- Normalize successively through the two adjoined-word occurrence equivalences.
  unfold splitRestOccurrence consOccurrenceEquiv Occurrence
  rw [@Multiset.consEquiv_symm_some (PolygonWord α) (Classical.decEq _)
    (word₂ ::ₘ rest) word₁]
  exact congrArg Sigma.fst
    (@Multiset.consEquiv_symm_some (PolygonWord α) (Classical.decEq _) rest word₂ region)

/-- Helper for Proposition 76.2: the distinguished occurrence of the merged scheme
has the newly merged polygon word. -/
theorem mergedFirstOccurrence_fst (word : PolygonWord α) (rest : LabellingScheme α) :
    (mergedFirstOccurrence word rest).1 = word := by
  -- Normalize the inverse multiset-cons equivalence at its distinguished point.
  unfold mergedFirstOccurrence consOccurrenceEquiv Occurrence
  exact congrArg Sigma.fst
    (@Multiset.consEquiv_symm_none (PolygonWord α) (Classical.decEq _) rest word)

/-- Helper for Proposition 76.2: an occurrence retained in the merged scheme keeps
its original polygon word. -/
theorem mergedRestOccurrence_fst (word : PolygonWord α) (rest : LabellingScheme α)
    (region : Occurrence rest) :
    (mergedRestOccurrence word rest region).1 = region.1 := by
  -- Normalize the retained branch of the inverse multiset-cons equivalence.
  unfold mergedRestOccurrence consOccurrenceEquiv Occurrence
  exact congrArg Sigma.fst
    (@Multiset.consEquiv_symm_some (PolygonWord α) (Classical.decEq _) rest word region)

/-- Helper for Proposition 76.2: transporting an index along equality of polygon words
preserves the selected boundary label. -/
theorem get_cast_fst_eq {left right : PolygonWord α} (h : left = right)
    (index : Fin right.1.length) :
    left.1.get (Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length) h).symm index) =
      right.1.get index := by
  -- Once the two words are identified, the transported index is unchanged.
  subst right
  rfl

/-- The global paste sends the distinguished pair through their concrete edge
gluing into the merged first region and sends every retained component through
its declared homeomorphism. -/
def AgreesWithEdgeGluing {α : Type u} [DecidableEq α]
    {splitScheme mergedScheme : LabellingScheme α}
    {splitRegions : PolygonalRegions.{u, v} splitScheme} {c : α}
    {mergedFirst : Occurrence mergedScheme}
    {ι : Type u} {splitRest : ι → Occurrence splitScheme}
    {mergedRest : ι → Occurrence mergedScheme}
    (result : PasteResult splitRegions c mergedFirst splitRest mergedRest)
    {leftOccurrence rightOccurrence : Occurrence splitScheme}
    (leftRegion : CyclicRegion splitRegions leftOccurrence)
    (rightRegion : CyclicRegion splitRegions rightOccurrence)
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon) : Prop :=
  ∃ comparison : gluing.Realization ≃ₜ result.mergedFirstRegion.polygon.region,
    (∀ x : splitRegions.Point leftOccurrence,
      result.pasting.sourceHomeomorph
          (result.firstPaste ⟨leftOccurrence, x⟩) =
        ⟨mergedFirst,
          result.mergedFirstRegion.equiv.symm
              (comparison (gluing.includeLeft (leftRegion.homeomorph x)))⟩) ∧
    (∀ y : splitRegions.Point rightOccurrence,
      result.pasting.sourceHomeomorph
          (result.firstPaste ⟨rightOccurrence, y⟩) =
        ⟨mergedFirst,
          result.mergedFirstRegion.equiv.symm
              (comparison (gluing.includeRight (rightRegion.homeomorph y)))⟩) ∧
    ∀ (region : ι) (x : splitRegions.Point (splitRest region)),
      result.pasting.sourceHomeomorph
          (result.firstPaste ⟨splitRest region, x⟩) =
        ⟨mergedRest region, result.retained region x⟩

/-- Helper for Proposition 76.2: agreement with an edge gluing is exactly the
existence of a comparison homeomorphism satisfying the three component rules. -/
theorem agreesWithEdgeGluing_iff {α : Type u} [DecidableEq α]
    {splitScheme mergedScheme : LabellingScheme α}
    {splitRegions : PolygonalRegions.{u, v} splitScheme} {c : α}
    {mergedFirst : Occurrence mergedScheme}
    {ι : Type u} {splitRest : ι → Occurrence splitScheme}
    {mergedRest : ι → Occurrence mergedScheme}
    (result : PasteResult splitRegions c mergedFirst splitRest mergedRest)
    {leftOccurrence rightOccurrence : Occurrence splitScheme}
    (leftRegion : CyclicRegion splitRegions leftOccurrence)
    (rightRegion : CyclicRegion splitRegions rightOccurrence)
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon) :
    AgreesWithEdgeGluing result leftRegion rightRegion gluing ↔
      ∃ comparison : gluing.Realization ≃ₜ result.mergedFirstRegion.polygon.region,
        (∀ x : splitRegions.Point leftOccurrence,
          result.pasting.sourceHomeomorph
              (result.firstPaste ⟨leftOccurrence, x⟩) =
            ⟨mergedFirst,
              result.mergedFirstRegion.equiv.symm
                (comparison (gluing.includeLeft (leftRegion.homeomorph x)))⟩) ∧
        (∀ y : splitRegions.Point rightOccurrence,
          result.pasting.sourceHomeomorph
              (result.firstPaste ⟨rightOccurrence, y⟩) =
            ⟨mergedFirst,
              result.mergedFirstRegion.equiv.symm
                (comparison (gluing.includeRight (rightRegion.homeomorph y)))⟩) ∧
        ∀ (region : ι) (x : splitRegions.Point (splitRest region)),
          result.pasting.sourceHomeomorph
              (result.firstPaste ⟨splitRest region, x⟩) =
            ⟨mergedRest region, result.retained region x⟩ := by
  rfl

/-- Helper for Proposition 76.2: if a label is fresh in a list, its occurrence in
that list followed by a singleton must be the singleton's final index. -/
theorem appendSingletonIndex_eq_length {α : Type u} (letters : List (α × Bool))
    (c : α) (b : Bool) (index : Fin (letters ++ [(c, b)]).length)
    (havoid : ∀ letter ∈ letters, letter.1 ≠ c)
    (hget : (letters ++ [(c, b)]).get index = (c, b)) :
    index.val = letters.length := by
  -- An earlier index would exhibit the forbidden label inside `letters`.
  by_contra hne
  have hlt : index.val < letters.length := by
    have hbound := index.isLt
    simp only [List.length_append, List.length_singleton] at hbound
    omega
  have hmem : (letters ++ [(c, b)]).get index ∈ letters := by
    rw [List.get_eq_getElem, List.getElem_append_left hlt]
    exact List.getElem_mem _
  exact havoid _ hmem (by simpa only [hget])

/-- Helper for Proposition 76.2: if a label is fresh in a tail, its occurrence in
a list formed by consing that label must have index zero. -/
theorem consIndex_eq_zero {α : Type u} (letters : List (α × Bool))
    (c : α) (b : Bool) (index : Fin ((c, b) :: letters).length)
    (havoid : ∀ letter ∈ letters, letter.1 ≠ c)
    (hget : ((c, b) :: letters).get index = (c, b)) :
    index.val = 0 := by
  -- A successor index lies in the tail and contradicts freshness there.
  rcases index with ⟨i, hi⟩
  cases i with
  | zero => rfl
  | succ i =>
      exfalso
      have hiTail : i < letters.length := by
        simp only [List.length_cons] at hi
        omega
      have hgetTail : letters[i] = (c, b) := by
        simpa only [List.get_eq_getElem, List.getElem_cons_succ] using hget
      exact havoid letters[i] (List.getElem_mem _) (by simpa only [hgetTail])

/-- A completed geometric paste transports a realization of the split regions to
the merged polygonal regions through its comparison homeomorphism. -/
theorem realizes {α : Type u} [DecidableEq α]
    {splitScheme mergedScheme : LabellingScheme α}
    {splitRegions : PolygonalRegions.{u, v} splitScheme} {c : α}
    {Y : Type v} [TopologicalSpace Y] {firstPaste : splitRegions.Source → Y}
    (pasting : splitRegions.Pasting mergedScheme c firstPaste)
    {X : Type w} [TopologicalSpace X] (remainingPastes : Y → X)
    (hsplit : splitRegions.Realizes (remainingPastes ∘ firstPaste)) :
    pasting.mergedRegions.Realizes
      (remainingPastes ∘ pasting.sourceHomeomorph.symm) := by
  constructor
  · -- Cancel the first quotient and then transport quotientness across the homeomorphism.
    exact (pasting.pastesLabel.isQuotientMap.of_comp_isQuotientMap
      hsplit.isQuotientMap).comp
      pasting.sourceHomeomorph.symm.isQuotientMap
  · intro x y
    -- Pull both fiber relations back to the intermediate paste.
    obtain ⟨x', hx'⟩ := pasting.pastesLabel.isQuotientMap.surjective
      (pasting.sourceHomeomorph.symm x)
    obtain ⟨y', hy'⟩ := pasting.pastesLabel.isQuotientMap.surjective
      (pasting.sourceHomeomorph.symm y)
    rw [Function.comp_apply, Function.comp_apply, ← hx', ← hy']
    calc
      remainingPastes (firstPaste x') = remainingPastes (firstPaste y') ↔
          splitRegions.Identified.r x' y' := by
        simpa only [Function.comp_apply] using hsplit.fibers x' y'
      _ ↔ (splitRegions.RemainingIdentified c firstPaste).r
          (firstPaste x') (firstPaste y') :=
        splitRegions.identified_iff_remainingIdentified_pullback c firstPaste
          pasting.pastesLabel x' y'
      _ ↔ (splitRegions.RemainingIdentified c firstPaste).r
          (pasting.sourceHomeomorph.symm x) (pasting.sourceHomeomorph.symm y) := by
        rw [hx', hy']
      _ ↔ pasting.mergedRegions.Identified.r x y := by
        rw [pasting.boundaryCompatibility]
        simp only [Homeomorph.apply_symm_apply]

end Pasting

end LabellingScheme.PolygonalRegions
