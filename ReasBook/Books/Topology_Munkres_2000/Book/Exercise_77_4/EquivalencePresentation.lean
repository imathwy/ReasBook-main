module

public import Topology_Munkres_2000.Book.Exercise_77_4.PresentationTransport
public import Topology_Munkres_2000.Book.Definition_76_6.RelabelRealization
public import Topology_Munkres_2000.Book.Definition_76_10.Equivalence
public import Topology_Munkres_2000.Book.Theorem_77_1.CancelCompression
public import Topology_Munkres_2000.Book.Theorem_77_1.SourceComparison
import all Topology_Munkres_2000.Book.Definition_76_6.RelabelRealization
import all Topology_Munkres_2000.Book.Definition_76_10.Equivalence

public section

universe u v

namespace PolygonWord

/-- Helper for Exercise 77.4: mapping labels by an equivalence agrees with the
canonical relabelling operation. -/
theorem mapLabels_toEmbedding_eq_relabel {α : Type u} {β : Type v}
    (e : α ≃ β) (word : PolygonWord α) :
    word.mapLabels e.toEmbedding = word.relabel e := by
  -- Both operations map the unsigned label and leave the orientation bit fixed.
  apply Subtype.ext
  rw [mapLabels_val, relabel_val]
  rfl

end PolygonWord

namespace LabellingScheme

/-- Helper for Exercise 77.4: mapping an entire scheme by an equivalence agrees
with the canonical scheme relabelling. -/
theorem mapLabels_toEmbedding_eq_relabel {α : Type u} {β : Type v}
    (e : α ≃ β) (scheme : LabellingScheme α) :
    scheme.mapLabels e.toEmbedding = scheme.relabel e := by
  -- Compare the two multiset maps word by word using the polygon-word bridge.
  apply Multiset.map_congr rfl
  intro word _hword
  exact PolygonWord.mapLabels_toEmbedding_eq_relabel e word

namespace PolygonalRegions

/-- Helper for Exercise 77.4: a cyclic presentation of a component transports
through reversal of all signs carrying one fixed label. -/
private theorem cyclicRegion_reverseLabel {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    (a : α) (region : Occurrence (scheme.reverseLabel a))
    (presentation :
      CyclicRegion regions ((reverseLabelRegionEquiv scheme a).symm region)) :
    Nonempty (CyclicRegion (regions.reverseLabel a) region) := by
  let original := (reverseLabelRegionEquiv scheme a).symm region
  letI : TopologicalSpace (regions.Point original) := regions.topology original
  letI : TopologicalSpace ((regions.reverseLabel a).Point region) :=
    (regions.reverseLabel a).topology region
  let hlength := reverseLabelRegion_length scheme a region
  let targetPolygon :=
    CyclicPolygon.transportSides hlength.symm presentation.polygon
  obtain ⟨H, hH⟩ :=
    CyclicPolygon.existsRegionHomeomorphPreservingEdgeParameters_of_eq
      hlength.symm presentation.polygon targetPolygon
  let componentHomeomorph :
      RegionHomeomorph (regions.reverseLabel a) region targetPolygon.region :=
    presentation.homeomorph.trans H
  have hcomponentApply (x : (regions.reverseLabel a).Point region) :
      componentHomeomorph x = H (presentation.homeomorph x) := by
    rfl
  refine ⟨CyclicRegion.ofHomeomorph targetPolygon componentHomeomorph ?_⟩
  intro edge t
  let originalEdge := Fin.cast hlength edge
  have hpresentation :
      presentation.homeomorph (regions.edge original originalEdge t) =
        presentation.polygon.boundaryToRegion
          (presentation.polygon.edgePoint originalEdge t) := by
    -- Upgrade the affine compatibility equation to the filled polygon carrier.
    apply Subtype.ext
    exact (presentation.edgeCompatibility originalEdge t).trans
      ((presentation.polygon.edgePoint_coe_eq_lineMap originalEdge t).symm.trans
        (presentation.polygon.boundaryToRegion_coe
          (presentation.polygon.edgePoint originalEdge t)).symm)
  have hedge : (regions.reverseLabel a).edge region edge t =
      regions.edge original originalEdge t := by
    rfl
  -- Follow the unchanged component edge through the side-count comparison.
  rw [hcomponentApply, hedge, hpresentation, hH]
  exact (targetPolygon.boundaryToRegion_coe
    (targetPolygon.edgePoint edge t)).trans
      (targetPolygon.edgePoint_coe_eq_lineMap edge t)

/-- Helper for Exercise 77.4: reversing one label's signs preserves geometric
polygonality of every component. -/
theorem reverseLabel_isPolygonal {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    (a : α) (hpolygonal : regions.IsPolygonal) :
    (regions.reverseLabel a).IsPolygonal := by
  rw [isPolygonal_iff] at hpolygonal ⊢
  intro region
  obtain ⟨presentation⟩ :=
    hpolygonal ((reverseLabelRegionEquiv scheme a).symm region)
  -- Transport the selected component while retaining every affine edge parameter.
  exact cyclicRegion_reverseLabel regions a region presentation

end PolygonalRegions

namespace Presents

/-- Helper for Exercise 77.4: relabelling by an equivalence preserves the
spaces presented by a labelling scheme. -/
theorem relabel {α : Type u} {β : Type v} {scheme : LabellingScheme α}
    (e : α ≃ β) {X : Type*} [TopologicalSpace X]
    (hpresents : scheme.Presents X) : (scheme.relabel e).Presents X := by
  -- Use the existing injective-map presentation theorem, then identify its scheme.
  rw [← mapLabels_toEmbedding_eq_relabel e scheme]
  exact hpresents.mapLabels e.toEmbedding

/-- Helper for Exercise 77.4: reversing all signs carrying one label preserves
the spaces presented by a labelling scheme. -/
theorem reverseLabel {α : Type u} {scheme : LabellingScheme α} (a : α)
    {X : Type v} [TopologicalSpace X] (hpresents : scheme.Presents X) :
    (scheme.reverseLabel a).Presents X := by
  rw [LabellingScheme.presents_iff] at hpresents ⊢
  obtain ⟨regions, hpolygonal, q, hrealizes⟩ := hpresents
  refine ⟨regions.reverseLabel a,
    regions.reverseLabel_isPolygonal a hpolygonal,
    q ∘ (PolygonalRegions.reverseLabelSourceEquiv regions a).symm, ?_⟩
  -- The realization theorem transports the quotient map and its fibers together.
  exact (regions.realizes_reverseLabel_iff a q).mp hrealizes

/-- Helper for Exercise 77.4: cyclic permutation of one polygon word preserves
the spaces presented by the full labelling scheme. -/
theorem permute {α : Type u} {before after : LabellingScheme α}
    (step : Permute before after) {X : Type v} [TopologicalSpace X]
    (hpresents : before.Presents X) : after.Presents X := by
  rcases step with ⟨word, rotated, rest, hrotation⟩
  obtain ⟨n, hn, hrotate⟩ := List.isRotated_iff_mod.mp hrotation
  let initial := word.val.take n
  let suffix := word.val.drop n
  have hjoin : initial ++ suffix = word.val :=
    List.take_append_drop n word.val
  have hlength : 3 ≤ (initial ++ suffix).length := by
    rw [hjoin]
    exact word.property
  let sourceWord : PolygonWord α := ⟨initial ++ suffix, hlength⟩
  have hsourceWord : sourceWord = word := by
    -- The explicit split reconstructs the original polygon word.
    apply Subtype.ext
    exact hjoin
  have htargetList : suffix ++ initial = rotated.val := by
    calc
      suffix ++ initial = word.val.rotate n := by
        exact (List.rotate_eq_drop_append_take hn).symm
      _ = rotated.val := hrotate
  let targetWord : PolygonWord α :=
    ⟨suffix ++ initial, PolygonWord.appendSwap_length initial suffix hlength⟩
  have htargetWord : targetWord = rotated := by
    -- The append swap is exactly the rotation supplied by the permutation step.
    apply Subtype.ext
    exact htargetList
  have hsourcePresents :
      LabellingScheme.Presents (sourceWord ::ₘ rest) X := by
    rwa [hsourceWord]
  have htargetPresents :
      LabellingScheme.Presents (targetWord ::ₘ rest) X :=
    appendSwap initial suffix rest hlength hsourcePresents
  simpa only [htargetWord] using htargetPresents

end Presents

namespace ElementaryStep

/-- Helper for Exercise 77.4: every elementary scheme operation transports a
presentation in its forward direction. -/
theorem presents {α : Type u} [Infinite α]
    {before after : LabellingScheme α} (step : ElementaryStep before after)
    {X : Type v} [TopologicalSpace X] (hpresents : before.Presents X) :
    after.Presents X := by
  cases step with
  | cut step =>
      -- Cutting is the forward direction of the established presentation equivalence.
      exact (presents_iff_of_cut step).mp hpresents
  | paste step =>
      -- A paste is a cut read backwards.
      exact (presents_iff_of_cut (paste_iff_cut.mp step)).mpr hpresents
  | flip step =>
      -- Formal inversion of the selected polygon uses the extracted flip transport.
      cases step with
      | of word rest => exact Presents.formalInverseCons hpresents
  | permute step =>
      -- Reduce an arbitrary cyclic permutation to one append swap.
      exact Presents.permute step hpresents
  | rename a c h_ac h_fresh =>
      -- Renaming is relabelling by the transposition of the old and fresh labels.
      exact Presents.relabel (PolygonWord.swapLabels a c) hpresents
  | reverse a =>
      -- Sign reversal transports the chosen polygonal model componentwise.
      exact Presents.reverseLabel a hpresents
  | cancel step =>
      -- Cancellation uses the rank-decreasing presentation equivalence.
      exact (presents_iff_of_cancel step).mp hpresents
  | uncancel step =>
      -- Uncancellation is cancellation read in the reverse direction.
      exact (presents_iff_of_cancel (uncancel_iff.mp step)).mpr hpresents

end ElementaryStep

namespace Equivalent

/-- Helper for Exercise 77.4: equivalent labelling schemes present exactly the
same topological spaces. -/
theorem presents_iff {α : Type u} [Infinite α]
    {before after : LabellingScheme α} (equivalent : Equivalent before after)
    {X : Type v} [TopologicalSpace X] :
    before.Presents X ↔ after.Presents X := by
  have forward {first last : LabellingScheme α}
      (chain : LabellingScheme.Equivalent first last)
      (hpresents : first.Presents X) : last.Presents X := by
    unfold LabellingScheme.Equivalent at chain
    induction chain with
    | refl => exact hpresents
    | tail _ step ih => exact step.presents ih
  constructor
  · exact forward equivalent
  · exact forward equivalent.symm

end Equivalent

end LabellingScheme

end
