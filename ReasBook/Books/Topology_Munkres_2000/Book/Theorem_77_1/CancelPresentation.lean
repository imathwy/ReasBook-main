module

public import Topology_Munkres_2000.Book.Theorem_77_1.MapLabels
public import Topology_Munkres_2000.Book.Theorem_76_1.Presentation
public import Topology_Munkres_2000.Book.Definition_76_6.RelabelRealization
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization

public section

universe u v w

namespace CyclicPolygon

/-- Helper for Theorem 77.1: transport a cyclic polygon across an equality of
its numbers of sides. -/
def transportSides {first second : ℕ} (h : first = second)
    (poly : CyclicPolygon first) : CyclicPolygon second :=
  h ▸ poly

/-- Helper for Theorem 77.1: cyclic polygons whose side counts are equal admit
a filled-region homeomorphism preserving every affine edge parameter. -/
theorem existsRegionHomeomorphPreservingEdgeParameters_of_eq
    {first second : ℕ} (h : first = second) (left : CyclicPolygon first)
    (right : CyclicPolygon second) :
    ∃ H : left.region ≃ₜ right.region, ∀ (i : Fin second) (s : unitInterval),
      H (left.boundaryToRegion (left.edgePoint (Fin.cast h.symm i) s)) =
        right.boundaryToRegion (right.edgePoint i s) := by
  -- Eliminate the abstract side-count equality before applying the homogeneous API.
  subst second
  exact left.existsRegionHomeomorphPreservingEdgeParameters right

end CyclicPolygon

namespace LabellingScheme.PolygonalRegions

variable {α : Type u} {β : Type v} {scheme : LabellingScheme α}

/-- Helper for Theorem 77.1: mapping labels gives a canonical equivalence of polygon
occurrences, even though the label map need only be injective. -/
@[expose]
noncomputable def mapLabelsRegionEquiv (f : α → β) (scheme : LabellingScheme α) :
    Occurrence scheme ≃ Occurrence (scheme.mapLabels f) :=
  @Multiset.mapEquiv (PolygonWord α) (PolygonWord β) (Classical.decEq _)
    (Classical.decEq _) scheme (PolygonWord.mapLabels f)

/-- Helper for Theorem 77.1: the occurrence equivalence exposes the pointwise-mapped
polygon word. -/
theorem mapLabelsRegionEquiv_val (f : α → β) (scheme : LabellingScheme α)
    (region : Occurrence scheme) :
    (mapLabelsRegionEquiv f scheme region).1 = region.1.mapLabels f := by
  -- Compute the word carried by the corresponding multiset occurrence.
  exact @Multiset.mapEquiv_apply (PolygonWord α) (PolygonWord β) (Classical.decEq _)
    (Classical.decEq _) scheme (PolygonWord.mapLabels f) region

/-- Helper for Theorem 77.1: corresponding occurrences have the same boundary length. -/
theorem mapLabelsRegionEquiv_length (f : α → β) (scheme : LabellingScheme α)
    (region : Occurrence scheme) :
    (mapLabelsRegionEquiv f scheme region).1.1.length = region.1.1.length := by
  -- Mapping changes labels but preserves the list of boundary positions.
  rw [mapLabelsRegionEquiv_val]
  exact PolygonWord.mapLabels_length f region.1

/-- Helper for Theorem 77.1: a mapped occurrence and its original preimage have equal
boundary lengths. -/
theorem mapLabelsRegion_length (f : α → β) (scheme : LabellingScheme α)
    (region : Occurrence (scheme.mapLabels f)) :
    region.1.1.length =
      ((mapLabelsRegionEquiv f scheme).symm region).1.1.length := by
  -- Apply the forward length formula to the inverse occurrence.
  let original := (mapLabelsRegionEquiv f scheme).symm region
  calc
    region.1.1.length =
        (mapLabelsRegionEquiv f scheme original).1.1.length := by
      rw [(mapLabelsRegionEquiv f scheme).apply_symm_apply]
    _ = original.1.1.length := mapLabelsRegionEquiv_length f scheme original

/-- Helper for Theorem 77.1: pulling a mapped occurrence and its transported
edge index back to the original scheme recovers the original boundary letter. -/
theorem mapLabelsOriginalLetter_eq (f : α → β) (scheme : LabellingScheme α)
    (region : Occurrence scheme) (edge : Fin region.1.1.length) :
    ((mapLabelsRegionEquiv f scheme).symm (mapLabelsRegionEquiv f scheme region)).1.1.get
        (Fin.cast
          (mapLabelsRegion_length f scheme (mapLabelsRegionEquiv f scheme region))
          (Fin.cast (mapLabelsRegionEquiv_length f scheme region).symm edge)) =
      region.1.1.get edge := by
  -- Package the dependent occurrence and edge index before cancelling both casts.
  have hregion := (mapLabelsRegionEquiv f scheme).symm_apply_apply region
  have hboundary :
      (⟨(mapLabelsRegionEquiv f scheme).symm (mapLabelsRegionEquiv f scheme region),
          Fin.cast
            (mapLabelsRegion_length f scheme (mapLabelsRegionEquiv f scheme region))
            (Fin.cast (mapLabelsRegionEquiv_length f scheme region).symm edge)⟩ :
        (r : Occurrence scheme) × Fin r.1.1.length) = ⟨region, edge⟩ := by
    apply Sigma.ext hregion
    rw [Fin.heq_ext_iff
      (congrArg (fun r : Occurrence scheme ↦ r.1.1.length) hregion)]
    rfl
  exact congrArg
    (fun p : (r : Occurrence scheme) × Fin r.1.1.length ↦ p.1.1.1.get p.2)
    hboundary

/-- Helper for Theorem 77.1: retain every polygonal region while injectively mapping its
boundary labels. -/
@[expose]
noncomputable def mapLabelsRegions (regions : PolygonalRegions scheme) (f : α → β) :
    PolygonalRegions (scheme.mapLabels f) where
  Point region := regions.Point ((mapLabelsRegionEquiv f scheme).symm region)
  topology region := regions.topology ((mapLabelsRegionEquiv f scheme).symm region)
  edge region edge t :=
    regions.edge ((mapLabelsRegionEquiv f scheme).symm region)
      (Fin.cast (mapLabelsRegion_length f scheme region) edge) t

/-- Helper for Theorem 77.1: the edge parametrization of a mapped region is the
original parametrization at the boundary-length cast of the same edge index. -/
theorem mapLabelsRegions_edge (regions : PolygonalRegions scheme) (f : α → β)
    (region : Occurrence (scheme.mapLabels f)) (edge : Fin region.1.1.length)
    (t : unitInterval) :
    (regions.mapLabelsRegions f).edge region edge t =
      regions.edge ((mapLabelsRegionEquiv f scheme).symm region)
        (Fin.cast (mapLabelsRegion_length f scheme region) edge) t := by
  -- Expose the single projection formula promised by the mapped-region construction.
  rfl

/-- Helper for Theorem 77.1: a cyclic presentation of an original occurrence
induces one for the corresponding occurrence after mapping boundary labels. -/
theorem cyclicRegion_mapLabels (regions : PolygonalRegions scheme) (f : α → β)
    (region : Occurrence (scheme.mapLabels f))
    (presentation :
      CyclicRegion regions ((mapLabelsRegionEquiv f scheme).symm region)) :
    Nonempty (CyclicRegion (regions.mapLabelsRegions f) region) := by
  -- Route correction: direct equality elimination cannot rewrite the two
  -- non-variable occurrence projections, so transport the polygon and compare regions.
  -- Transport the original polygon once, then compare the two filled regions geometrically.
  let original := (mapLabelsRegionEquiv f scheme).symm region
  letI : TopologicalSpace (regions.Point original) := regions.topology original
  letI : TopologicalSpace ((regions.mapLabelsRegions f).Point region) :=
    (regions.mapLabelsRegions f).topology region
  let hlength := mapLabelsRegion_length f scheme region
  let targetPolygon :=
    CyclicPolygon.transportSides hlength.symm presentation.polygon
  obtain ⟨H, hH⟩ :=
    CyclicPolygon.existsRegionHomeomorphPreservingEdgeParameters_of_eq
      hlength.symm presentation.polygon targetPolygon
  let componentHomeomorph :
      RegionHomeomorph (regions.mapLabelsRegions f) region targetPolygon.region :=
    presentation.homeomorph.trans H
  have hcomponentApply (x : (regions.mapLabelsRegions f).Point region) :
      componentHomeomorph x = H (presentation.homeomorph x) := by
    -- The component comparison is the composite just defined.
    rfl
  refine ⟨CyclicRegion.ofHomeomorph targetPolygon componentHomeomorph ?_⟩
  intro edge t
  let originalEdge := Fin.cast hlength edge
  have hpresentation :
      presentation.homeomorph (regions.edge original originalEdge t) =
        presentation.polygon.boundaryToRegion
          (presentation.polygon.edgePoint originalEdge t) := by
    -- Upgrade the ambient edge formula to equality in the filled polygonal region.
    apply Subtype.ext
    exact (presentation.edgeCompatibility originalEdge t).trans
      ((presentation.polygon.edgePoint_coe_eq_lineMap originalEdge t).symm.trans
        (presentation.polygon.boundaryToRegion_coe
          (presentation.polygon.edgePoint originalEdge t)).symm)
  -- Follow the original compatible edge through the side-count comparison map.
  rw [hcomponentApply, mapLabelsRegions_edge, hpresentation, hH]
  exact (targetPolygon.boundaryToRegion_coe
    (targetPolygon.edgePoint edge t)).trans
      (targetPolygon.edgePoint_coe_eq_lineMap edge t)

/-- Helper for Theorem 77.1: mapping labels preserves the geometric polygonal
certificate for every component of a polygonal-region family. -/
theorem isPolygonal_mapLabels (regions : PolygonalRegions scheme) (f : α → β)
    (hpolygonal : regions.IsPolygonal) :
    (regions.mapLabelsRegions f).IsPolygonal := by
  -- Pull each mapped occurrence back and transport its cyclic presentation forward.
  rw [isPolygonal_iff] at hpolygonal ⊢
  intro region
  obtain ⟨presentation⟩ :=
    hpolygonal ((mapLabelsRegionEquiv f scheme).symm region)
  exact cyclicRegion_mapLabels regions f region presentation

/-- Helper for Theorem 77.1: label mapping induces an equivalence of the disjoint unions
of region points. -/
@[expose]
noncomputable def mapLabelsSourceEquiv (regions : PolygonalRegions scheme) (f : α → β) :
    regions.Source ≃ (regions.mapLabelsRegions f).Source :=
  Equiv.sigmaCongr (mapLabelsRegionEquiv f scheme) fun region ↦
    Equiv.cast (congrArg regions.Point
      ((mapLabelsRegionEquiv f scheme).symm_apply_apply region).symm)

/-- Helper for Theorem 77.1: the source equivalence maps a component point by
transporting it to the corresponding mapped occurrence. -/
theorem mapLabelsSourceEquiv_apply (regions : PolygonalRegions scheme) (f : α → β)
    (region : Occurrence scheme) (point : regions.Point region) :
    mapLabelsSourceEquiv regions f ⟨region, point⟩ =
      ⟨mapLabelsRegionEquiv f scheme region,
        Equiv.cast (congrArg regions.Point
          ((mapLabelsRegionEquiv f scheme).symm_apply_apply region).symm) point⟩ := by
  -- Compute the two layers of the sigma congruence.
  rfl

/-- Helper for Theorem 77.1: transport between two propositionally equal
region fibers is continuous for their stored component topologies. -/
theorem continuous_castRegionPoint (regions : PolygonalRegions scheme)
    {region₁ region₂ : Occurrence scheme} (hregion : region₂ = region₁) :
    @Continuous (regions.Point region₁) (regions.Point region₂)
      (regions.topology region₁) (regions.topology region₂)
      (Equiv.cast (congrArg regions.Point hregion.symm)) := by
  -- Once the region equality is eliminated, the transport is the identity map.
  subst region₂
  exact @continuous_id _ (regions.topology region₁)

/-- Helper for Theorem 77.1: the source equivalence induced by label mapping is
continuous for the disjoint-union topologies. -/
theorem continuous_mapLabelsSourceEquiv (regions : PolygonalRegions scheme) (f : α → β) :
    Continuous (mapLabelsSourceEquiv regions f) := by
  -- Check continuity separately on every original polygonal-region summand.
  rw [continuous_iSup_dom]
  intro region
  rw [continuous_coinduced_dom]
  let target := mapLabelsRegionEquiv f scheme region
  have hregion := (mapLabelsRegionEquiv f scheme).symm_apply_apply region
  have hcast := continuous_castRegionPoint regions hregion
  have hinclusion :
      @Continuous ((regions.mapLabelsRegions f).Point target)
        (regions.mapLabelsRegions f).Source
        ((regions.mapLabelsRegions f).topology target)
        (regions.mapLabelsRegions f).sourceTopology (Sigma.mk target) :=
    continuous_iSup_rng (i := target) (f := Sigma.mk target)
      (continuous_coinduced_rng (f := Sigma.mk target))
  dsimp [mapLabelsSourceEquiv, Equiv.sigmaCongr]
  exact @Continuous.comp
    (regions.Point region) ((regions.mapLabelsRegions f).Point target)
    (regions.mapLabelsRegions f).Source (regions.topology region)
    ((regions.mapLabelsRegions f).topology target)
    (regions.mapLabelsRegions f).sourceTopology _ _ hinclusion hcast

/-- Helper for Theorem 77.1: the inverse source equivalence induced by label
mapping is continuous for the disjoint-union topologies. -/
theorem continuous_mapLabelsSourceEquiv_symm
    (regions : PolygonalRegions scheme) (f : α → β) :
    Continuous (mapLabelsSourceEquiv regions f).symm := by
  -- Check the inverse on each mapped summand, whose topology is copied from its preimage.
  rw [continuous_iSup_dom]
  intro region
  rw [continuous_coinduced_dom]
  let original := (mapLabelsRegionEquiv f scheme).symm region
  letI : TopologicalSpace (regions.Point original) := regions.topology original
  have hinclusion : Continuous
      (Sigma.mk original : regions.Point original → regions.Source) :=
    continuous_iSup_rng (i := original) (f := Sigma.mk original)
      (continuous_coinduced_rng (f := Sigma.mk original))
  have hinverse :
      (mapLabelsSourceEquiv regions f).symm ∘ Sigma.mk region =
        (Sigma.mk original : regions.Point original → regions.Source) := by
    funext point
    dsimp only [Function.comp_apply]
    dsimp [mapLabelsRegions, original] at point
    apply (mapLabelsSourceEquiv regions f).injective
    rw [(mapLabelsSourceEquiv regions f).apply_symm_apply]
    rw [mapLabelsSourceEquiv_apply]
    apply Sigma.ext
    · exact (mapLabelsRegionEquiv f scheme).apply_symm_apply region |>.symm
    · exact (cast_heq _ _).symm
  rw [hinverse]
  exact hinclusion

/-- Helper for Theorem 77.1: injective or noninjective label mapping retains the
underlying topological disjoint union of polygonal regions. -/
noncomputable def mapLabelsSourceHomeomorph
    (regions : PolygonalRegions scheme) (f : α → β) :
    regions.Source ≃ₜ (regions.mapLabelsRegions f).Source :=
  { mapLabelsSourceEquiv regions f with
    continuous_toFun := continuous_mapLabelsSourceEquiv regions f
    continuous_invFun := continuous_mapLabelsSourceEquiv_symm regions f }

/-- Helper for Theorem 77.1: the source homeomorphism has the previously
constructed occurrence-and-point equivalence as its underlying forward map. -/
theorem mapLabelsSourceHomeomorph_apply
    (regions : PolygonalRegions scheme) (f : α → β) (x : regions.Source) :
    mapLabelsSourceHomeomorph regions f x = mapLabelsSourceEquiv regions f x := by
  -- The homeomorphism bundles the source equivalence without changing its map.
  rfl

/-- Helper for Theorem 77.1: the inverse source homeomorphism has the inverse
source equivalence as its underlying map. -/
theorem mapLabelsSourceHomeomorph_symm_apply
    (regions : PolygonalRegions scheme) (f : α → β)
    (x : (regions.mapLabelsRegions f).Source) :
    (mapLabelsSourceHomeomorph regions f).symm x =
      (mapLabelsSourceEquiv regions f).symm x := by
  -- The homeomorphism bundles the source equivalence without changing its inverse.
  rfl

/-- Helper for Theorem 77.1: the source equivalence sends each original boundary point to
the corresponding mapped boundary point. -/
theorem mapLabelsSourceEquiv_edge (regions : PolygonalRegions scheme) (f : α → β)
    (region : Occurrence scheme) (edge : Fin region.1.1.length) (t : unitInterval) :
    mapLabelsSourceEquiv regions f ⟨region, regions.edge region edge t⟩ =
      ⟨mapLabelsRegionEquiv f scheme region,
        (regions.mapLabelsRegions f).edge (mapLabelsRegionEquiv f scheme region)
          (Fin.cast (mapLabelsRegionEquiv_length f scheme region).symm edge) t⟩ := by
  -- Compare the occurrence first, then normalize the two inverse length casts.
  apply Sigma.ext
  · rfl
  · have hregion := (mapLabelsRegionEquiv f scheme).symm_apply_apply region
    have hindex :
        (⟨(mapLabelsRegionEquiv f scheme).symm
              (mapLabelsRegionEquiv f scheme region),
            Fin.cast
              (mapLabelsRegion_length f scheme
                (mapLabelsRegionEquiv f scheme region))
              (Fin.cast (mapLabelsRegionEquiv_length f scheme region).symm edge)⟩ :
          (r : Occurrence scheme) × Fin r.1.1.length) = ⟨region, edge⟩ := by
      apply Sigma.ext hregion
      rw [Fin.heq_ext_iff
        (congrArg (fun r : Occurrence scheme ↦ r.1.1.length) hregion)]
      rfl
    have hedge := congr_arg_heq
      (fun p : (r : Occurrence scheme) × Fin r.1.1.length ↦
        regions.edge p.1 p.2 t) hindex
    dsimp [mapLabelsSourceEquiv, Equiv.sigmaCongr, mapLabelsRegions]
    exact (cast_heq _ _).trans hedge.symm

/-- Helper for Theorem 77.1: pulling a mapped boundary point back through the source
equivalence recovers the corresponding original edge and parameter. -/
theorem mapLabelsSourceEquiv_symm_edge (regions : PolygonalRegions scheme) (f : α → β)
    (region : Occurrence (scheme.mapLabels f)) (edge : Fin region.1.1.length)
    (t : unitInterval) :
    (mapLabelsSourceEquiv regions f).symm
        ⟨region, (regions.mapLabelsRegions f).edge region edge t⟩ =
      ⟨(mapLabelsRegionEquiv f scheme).symm region,
        regions.edge ((mapLabelsRegionEquiv f scheme).symm region)
          (Fin.cast (mapLabelsRegion_length f scheme region) edge) t⟩ := by
  -- Apply the forward equivalence and normalize its occurrence and index inverses.
  apply (mapLabelsSourceEquiv regions f).injective
  rw [(mapLabelsSourceEquiv regions f).apply_symm_apply, mapLabelsSourceEquiv_edge]
  let original := (mapLabelsRegionEquiv f scheme).symm region
  let originalEdge := Fin.cast (mapLabelsRegion_length f scheme region) edge
  have hregion : mapLabelsRegionEquiv f scheme original = region :=
    (mapLabelsRegionEquiv f scheme).apply_symm_apply region
  have hboundary :
      (⟨mapLabelsRegionEquiv f scheme original,
          Fin.cast (mapLabelsRegionEquiv_length f scheme original).symm originalEdge⟩ :
        (r : Occurrence (scheme.mapLabels f)) × Fin r.1.1.length) =
        ⟨region, edge⟩ := by
    apply Sigma.ext hregion
    rw [Fin.heq_ext_iff
      (congrArg (fun r : Occurrence (scheme.mapLabels f) ↦ r.1.1.length) hregion)]
    rfl
  have hedge := congr_arg_heq
    (fun p : (r : Occurrence (scheme.mapLabels f)) × Fin r.1.1.length ↦
      (regions.mapLabelsRegions f).edge p.1 p.2 t) hboundary
  exact Sigma.ext hregion.symm hedge.symm

/-- Helper for Theorem 77.1: each mapped boundary letter is the image of the corresponding
original letter, with its orientation unchanged. -/
theorem mapLabelsLetter_eq (f : α → β) (scheme : LabellingScheme α)
    (region : Occurrence (scheme.mapLabels f)) (edge : Fin region.1.1.length) :
    region.1.1.get edge =
      (f (((mapLabelsRegionEquiv f scheme).symm region).1.1.get
        (Fin.cast (mapLabelsRegion_length f scheme region) edge)).1,
       (((mapLabelsRegionEquiv f scheme).symm region).1.1.get
        (Fin.cast (mapLabelsRegion_length f scheme region) edge)).2) := by
  -- Package the word and dependent index before computing lookup in the mapped list.
  let original := (mapLabelsRegionEquiv f scheme).symm region
  have hword : region.1 = original.1.mapLabels f := by
    calc
      region.1 = (mapLabelsRegionEquiv f scheme original).1 :=
        congrArg (fun r : Occurrence (scheme.mapLabels f) ↦ r.1)
          ((mapLabelsRegionEquiv f scheme).apply_symm_apply region).symm
      _ = original.1.mapLabels f := mapLabelsRegionEquiv_val f scheme original
  have hboundary :
      (⟨region.1, edge⟩ : (word : PolygonWord β) × Fin word.1.length) =
        ⟨original.1.mapLabels f,
          Fin.cast (congrArg (fun word : PolygonWord β ↦ word.1.length) hword) edge⟩ := by
    apply Sigma.ext hword
    rw [Fin.heq_ext_iff
      (congrArg (fun word : PolygonWord β ↦ word.1.length) hword)]
    rfl
  have hget := congrArg
    (fun p : (word : PolygonWord β) × Fin word.1.length ↦ p.1.1.get p.2) hboundary
  simpa only [PolygonWord.mapLabels_val, List.get_eq_getElem, List.getElem_map,
    Fin.val_cast] using hget

/-- Helper for Theorem 77.1: injective label mapping preserves and reflects equality of
the unsigned labels at two mapped boundary positions. -/
theorem mapLabels_fst_eq_iff (f : α ↪ β) (scheme : LabellingScheme α)
    (region₁ region₂ : Occurrence (scheme.mapLabels f))
    (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length) :
    (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1 ↔
      (((mapLabelsRegionEquiv f scheme).symm region₁).1.1.get
          (Fin.cast (mapLabelsRegion_length f scheme region₁) edge₁)).1 =
        (((mapLabelsRegionEquiv f scheme).symm region₂).1.1.get
          (Fin.cast (mapLabelsRegion_length f scheme region₂) edge₂)).1 := by
  -- Normalize both mapped letters, then reflect equality with injectivity.
  rw [mapLabelsLetter_eq, mapLabelsLetter_eq]
  exact f.injective.eq_iff

/-- Helper for Theorem 77.1: mapping labels retains each boundary orientation. -/
theorem mapLabels_snd_eq (f : α → β) (scheme : LabellingScheme α)
    (region : Occurrence (scheme.mapLabels f)) (edge : Fin region.1.1.length) :
    (region.1.1.get edge).2 =
      (((mapLabelsRegionEquiv f scheme).symm region).1.1.get
        (Fin.cast (mapLabelsRegion_length f scheme region) edge)).2 := by
  -- Project the orientation component from the mapped-letter computation.
  exact congrArg Prod.snd (mapLabelsLetter_eq f scheme region edge)

/-- Helper for Theorem 77.1: direct edge relatedness is exposed through its
canonical regions, edge indices, and boundary parameter. -/
theorem edgeRelated_iff_witness (regions : PolygonalRegions scheme)
    (x y : regions.Source) :
    regions.EdgeRelated x y ↔
      ∃ (region₁ region₂ : Occurrence scheme)
        (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
        (t : unitInterval),
          (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1 ∧
          x = ⟨region₁, regions.edge region₁ edge₁ t⟩ ∧
          y = ⟨region₂, regions.edge region₂ edge₂
            (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
              else unitInterval.symm t)⟩ := by
  -- Unfold the owner definition once; downstream transport uses only this interface.
  rfl

/-- Helper for Theorem 77.1: an injective label map preserves and reflects the direct
labelled-edge relation. -/
theorem edgeRelated_mapLabels_iff (regions : PolygonalRegions scheme) (f : α ↪ β)
    (x y : regions.Source) :
    (regions.mapLabelsRegions f).EdgeRelated (mapLabelsSourceEquiv regions f x)
        (mapLabelsSourceEquiv regions f y) ↔
      regions.EdgeRelated x y := by
  rw [edgeRelated_iff_witness, edgeRelated_iff_witness]
  constructor
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabel, hx, hy⟩
    let original₁ := (mapLabelsRegionEquiv f scheme).symm region₁
    let original₂ := (mapLabelsRegionEquiv f scheme).symm region₂
    let originalEdge₁ := Fin.cast (mapLabelsRegion_length f scheme region₁) edge₁
    let originalEdge₂ := Fin.cast (mapLabelsRegion_length f scheme region₂) edge₂
    refine ⟨original₁, original₂, originalEdge₁, originalEdge₂, t,
      (mapLabels_fst_eq_iff f scheme region₁ region₂ edge₁ edge₂).mp hlabel, ?_, ?_⟩
    · -- Pull the first mapped boundary point back to its original occurrence.
      have hx' := congrArg (mapLabelsSourceEquiv regions f).symm hx
      simpa only [Equiv.symm_apply_apply, mapLabelsSourceEquiv_symm_edge] using hx'
    · -- Pull back the second point and normalize the unchanged orientation signs.
      have hy' := congrArg (mapLabelsSourceEquiv regions f).symm hy
      simpa only [Equiv.symm_apply_apply, mapLabelsSourceEquiv_symm_edge,
        mapLabels_snd_eq] using hy'
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabel, hx, hy⟩
    let mapped₁ := mapLabelsRegionEquiv f scheme region₁
    let mapped₂ := mapLabelsRegionEquiv f scheme region₂
    let mappedEdge₁ := Fin.cast (mapLabelsRegionEquiv_length f scheme region₁).symm edge₁
    let mappedEdge₂ := Fin.cast (mapLabelsRegionEquiv_length f scheme region₂).symm edge₂
    refine ⟨mapped₁, mapped₂, mappedEdge₁, mappedEdge₂, t, ?_, ?_, ?_⟩
    · -- Injectivity transports the original label equality to the mapped letters.
      apply (mapLabels_fst_eq_iff f scheme mapped₁ mapped₂ mappedEdge₁ mappedEdge₂).mpr
      dsimp only [mapped₁, mapped₂, mappedEdge₁, mappedEdge₂]
      simpa only [mapLabelsOriginalLetter_eq] using hlabel
    · -- The source equivalence computes directly on the first boundary point.
      rw [hx, mapLabelsSourceEquiv_edge]
    · -- The same computation applies to the second point; mapped signs are unchanged.
      rw [hy, mapLabelsSourceEquiv_edge]
      dsimp only [mapped₁, mapped₂, mappedEdge₁, mappedEdge₂]
      simp only [mapLabels_snd_eq, mapLabelsOriginalLetter_eq]

/-- Helper for Theorem 77.1: the labelled-edge setoid is precisely the
equivalence closure of direct edge relatedness. -/
theorem identified_iff_eqvGen (regions : PolygonalRegions scheme)
    (x y : regions.Source) :
    regions.Identified.r x y ↔ Relation.EqvGen regions.EdgeRelated x y := by
  -- Expose the generated setoid once and retain `EqvGen` as the stable interface.
  rfl

/-- Helper for Theorem 77.1: injective label mapping preserves and reflects
the full generated boundary-identification relation. -/
theorem identified_mapLabels_iff (regions : PolygonalRegions scheme) (f : α ↪ β)
    (x y : regions.Source) :
    (regions.mapLabelsRegions f).Identified.r (mapLabelsSourceEquiv regions f x)
        (mapLabelsSourceEquiv regions f y) ↔
      regions.Identified.r x y := by
  -- Lift the verified direct-relation comparison one generated edge at a time.
  rw [identified_iff_eqvGen, identified_iff_eqvGen]
  exact eqvGen_equiv_iff (mapLabelsSourceEquiv regions f)
    (edgeRelated_mapLabels_iff regions f) x y

/-- Helper for Theorem 77.1: injective label mapping preserves realization by
precomposing the quotient map with the inverse source homeomorphism. -/
theorem realizes_mapLabels_iff (regions : PolygonalRegions scheme) (f : α ↪ β)
    {X : Type w} [TopologicalSpace X] (q : regions.Source → X) :
    regions.Realizes q ↔
      (regions.mapLabelsRegions f).Realizes
        (q ∘ (mapLabelsSourceHomeomorph regions f).symm) := by
  constructor
  · intro hrealizes
    constructor
    · -- Precomposition by a homeomorphism preserves quotientness.
      exact hrealizes.isQuotientMap.comp
        (mapLabelsSourceHomeomorph regions f).symm.isQuotientMap
    · intro x y
      -- Pull both mapped points back, then use the generated-relation comparison.
      simp only [Function.comp_apply]
      rw [hrealizes.fibers]
      simpa only [mapLabelsSourceHomeomorph_symm_apply, Equiv.apply_symm_apply] using
        (identified_mapLabels_iff regions f
          ((mapLabelsSourceHomeomorph regions f).symm x)
          ((mapLabelsSourceHomeomorph regions f).symm y)).symm
  · intro hrealizes
    constructor
    · -- Compose back with the forward homeomorphism and cancel its inverse.
      simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using
        hrealizes.isQuotientMap.comp
          (mapLabelsSourceHomeomorph regions f).isQuotientMap
    · intro x y
      have hfibers := hrealizes.fibers
        (mapLabelsSourceHomeomorph regions f x)
        (mapLabelsSourceHomeomorph regions f y)
      have hfibers' :
          q x = q y ↔
            (regions.mapLabelsRegions f).Identified.r
              (mapLabelsSourceHomeomorph regions f x)
              (mapLabelsSourceHomeomorph regions f y) := by
        simpa only [Function.comp_apply, Homeomorph.symm_apply_apply] using hfibers
      have hmapped :
          q x = q y ↔
            (regions.mapLabelsRegions f).Identified.r
              (mapLabelsSourceEquiv regions f x)
              (mapLabelsSourceEquiv regions f y) := by
        simpa only [mapLabelsSourceHomeomorph_apply] using hfibers'
      exact hmapped.trans (identified_mapLabels_iff regions f x y)

end LabellingScheme.PolygonalRegions

namespace LabellingScheme.Presents

/-- Helper for Theorem 77.1: injectively extending the label type preserves a
chosen geometric presentation of a topological space. -/
theorem mapLabels {scheme : LabellingScheme α} (f : α ↪ β)
    {X : Type w} [TopologicalSpace X] (hpresents : scheme.Presents X) :
    (scheme.mapLabels f).Presents X := by
  -- Transport the chosen regions and their polygonality certificate componentwise.
  rw [LabellingScheme.presents_iff] at hpresents ⊢
  obtain ⟨regions, hpolygonal, q, hrealizes⟩ := hpresents
  refine ⟨regions.mapLabelsRegions f,
    regions.isPolygonal_mapLabels f hpolygonal,
    q ∘ (regions.mapLabelsSourceHomeomorph f).symm, ?_⟩
  -- The generated edge relation and quotient map were already transported together.
  exact (regions.realizes_mapLabels_iff f q).mp hrealizes

end LabellingScheme.Presents

end
