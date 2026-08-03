module

public import Topology_Munkres_2000.Book.Theorem_77_1.CancelPresentation
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization

public section

universe u v w z

namespace LabellingScheme.PolygonalRegions

/-- Helper for Theorem 77.1: two quotient maps realizing the same labelled-edge
relation have homeomorphic targets. -/
theorem Realizes.homeomorphicTargets {α : Type u} {scheme : LabellingScheme α}
    (regions : PolygonalRegions.{u, v} scheme)
    {X : Type w} {Y : Type z} [TopologicalSpace X] [TopologicalSpace Y]
    (qX : regions.Source → X) (qY : regions.Source → Y)
    (hX : regions.Realizes qX) (hY : regions.Realizes qY) :
    Nonempty (X ≃ₜ Y) := by
  -- Compare both targets with the quotients by the kernels of their realizing maps.
  let qXContinuous : C(regions.Source, X) :=
    ⟨qX, hX.isQuotientMap.continuous⟩
  let qYContinuous : C(regions.Source, Y) :=
    ⟨qY, hY.isQuotientMap.continuous⟩
  let kernelHomeomorph : Quotient (Setoid.ker qX) ≃ₜ Quotient (Setoid.ker qY) :=
    Homeomorph.Quotient.congrRight (r := Setoid.ker qX) (r' := Setoid.ker qY)
      (fun x y ↦ (hX.fibers x y).trans (hY.fibers x y).symm)
  -- Compose the two quotient-kernel comparisons through the common kernel relation.
  exact ⟨(Topology.IsQuotientMap.homeomorph
      (f := qXContinuous) hX.isQuotientMap).symm |>.trans
    (kernelHomeomorph.trans
      (Topology.IsQuotientMap.homeomorph
        (f := qYContinuous) hY.isQuotientMap))⟩

/-- Helper for Theorem 77.1: a component homeomorphism between polygonal
families may cross the universes in which their component types live. -/
abbrev ComponentHomeomorphBetween {α : Type u}
    {leftScheme rightScheme : LabellingScheme α}
    (left : PolygonalRegions.{u, v} leftScheme) (leftRegion : Occurrence leftScheme)
    (right : PolygonalRegions.{u, w} rightScheme) (rightRegion : Occurrence rightScheme) :=
  @Homeomorph (left.Point leftRegion) (right.Point rightRegion)
    (left.topology leftRegion) (right.topology rightRegion)

/-- Helper for Theorem 77.1: corresponding polygonal components admit a
homeomorphism preserving every affine edge parameter. -/
noncomputable def presentationComponentHomeomorph {α : Type u}
    {scheme : LabellingScheme α}
    (left : PolygonalRegions.{u, v} scheme)
    (right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    (region : Occurrence scheme) :
    ComponentHomeomorphBetween left region right region :=
  -- Local instance justification (topology): each comparison uses the topologies
  -- stored by the two arbitrary polygonal-region families.
  letI : TopologicalSpace (left.Point region) := left.topology region
  letI : TopologicalSpace (right.Point region) := right.topology region
  let leftPresentation := Classical.choice ((isPolygonal_iff left).mp hleft region)
  let rightPresentation := Classical.choice ((isPolygonal_iff right).mp hright region)
  let polygonComparison := Classical.choose
    (leftPresentation.polygon.existsRegionHomeomorphPreservingEdgeParameters
      rightPresentation.polygon)
  leftPresentation.homeomorph.trans
    (polygonComparison.trans rightPresentation.homeomorph.symm)

/-- Helper for Theorem 77.1: the component comparison sends each boundary point
to the equally indexed boundary point with the same affine parameter. -/
theorem presentationComponentHomeomorph_edge {α : Type u}
    {scheme : LabellingScheme α}
    (left : PolygonalRegions.{u, v} scheme)
    (right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    (region : Occurrence scheme) (edge : Fin region.1.1.length)
    (t : unitInterval) :
    presentationComponentHomeomorph left right hleft hright region
        (left.edge region edge t) = right.edge region edge t := by
  -- Local instance justification (topology): the chosen cyclic presentations
  -- and their comparison use the stored component topologies.
  letI : TopologicalSpace (left.Point region) := left.topology region
  letI : TopologicalSpace (right.Point region) := right.topology region
  let leftPresentation := Classical.choice ((isPolygonal_iff left).mp hleft region)
  let rightPresentation := Classical.choice ((isPolygonal_iff right).mp hright region)
  let polygonComparison := Classical.choose
    (leftPresentation.polygon.existsRegionHomeomorphPreservingEdgeParameters
      rightPresentation.polygon)
  have hpolygonComparison := Classical.choose_spec
    (leftPresentation.polygon.existsRegionHomeomorphPreservingEdgeParameters
      rightPresentation.polygon)
  have hleftEdge :
      leftPresentation.homeomorph (left.edge region edge t) =
        leftPresentation.polygon.boundaryToRegion
          (leftPresentation.polygon.edgePoint edge t) := by
    -- Upgrade the stored ambient edge formula to equality in the filled region.
    apply Subtype.ext
    exact (leftPresentation.edgeCompatibility edge t).trans
      ((leftPresentation.polygon.edgePoint_coe_eq_lineMap edge t).symm.trans
        (leftPresentation.polygon.boundaryToRegion_coe
          (leftPresentation.polygon.edgePoint edge t)).symm)
  have hrightEdge :
      rightPresentation.homeomorph (right.edge region edge t) =
        rightPresentation.polygon.boundaryToRegion
          (rightPresentation.polygon.edgePoint edge t) := by
    -- Record the matching boundary formula in the target component.
    apply Subtype.ext
    exact (rightPresentation.edgeCompatibility edge t).trans
      ((rightPresentation.polygon.edgePoint_coe_eq_lineMap edge t).symm.trans
        (rightPresentation.polygon.boundaryToRegion_coe
          (rightPresentation.polygon.edgePoint edge t)).symm)
  -- Cancel the target chart and apply the polygon comparison formula.
  apply rightPresentation.homeomorph.injective
  rw [presentationComponentHomeomorph]
  simp only [Homeomorph.trans_apply]
  rw [hleftEdge, hrightEdge, rightPresentation.homeomorph.apply_symm_apply]
  exact hpolygonComparison edge t

/-- Helper for Theorem 77.1: component homeomorphisms indexed by an occurrence
equivalence assemble to a homeomorphism of polygonal-region sources. -/
noncomputable def sourceHomeomorphOfComponents {α : Type u}
    {leftScheme rightScheme : LabellingScheme α}
    (left : PolygonalRegions.{u, v} leftScheme)
    (right : PolygonalRegions.{u, w} rightScheme)
    (indexEquiv : Occurrence leftScheme ≃ Occurrence rightScheme)
    (component : ∀ region,
      ComponentHomeomorphBetween left region right (indexEquiv region)) :
    left.Source ≃ₜ right.Source :=
  -- Local instance justification (topology): `sigmaMap` needs the component
  -- topologies stored in the two polygonal-region structures.
  letI : ∀ region, TopologicalSpace (left.Point region) :=
    fun region ↦ left.topology region
  letI : ∀ region, TopologicalSpace (right.Point region) :=
    fun region ↦ right.topology region
  IsHomeomorph.homeomorph
    (Sigma.map indexEquiv fun region point ↦ component region point)
    (IsHomeomorph.sigmaMap indexEquiv.bijective fun region ↦
      (component region).isHomeomorph)

/-- Helper for Theorem 77.1: the assembled source homeomorphism applies the
chosen occurrence equivalence and its corresponding component map. -/
theorem sourceHomeomorphOfComponents_apply {α : Type u}
    {leftScheme rightScheme : LabellingScheme α}
    (left : PolygonalRegions.{u, v} leftScheme)
    (right : PolygonalRegions.{u, w} rightScheme)
    (indexEquiv : Occurrence leftScheme ≃ Occurrence rightScheme)
    (component : ∀ region,
      ComponentHomeomorphBetween left region right (indexEquiv region))
    (region : Occurrence leftScheme) (point : left.Point region) :
    sourceHomeomorphOfComponents left right indexEquiv component ⟨region, point⟩ =
      ⟨indexEquiv region, component region point⟩ := by
  -- Expose the single dependent-sigma computation promised by the constructor.
  simp only [sourceHomeomorphOfComponents, IsHomeomorph.homeomorph_apply]
  rfl

/-- Helper for Theorem 77.1: two polygonal families for the same scheme have a
canonical componentwise source homeomorphism. -/
noncomputable def presentationSourceHomeomorph {α : Type u}
    {scheme : LabellingScheme α}
    (left : PolygonalRegions.{u, v} scheme)
    (right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal) :
    left.Source ≃ₜ right.Source :=
  sourceHomeomorphOfComponents left right (Equiv.refl _)
    (fun region ↦ presentationComponentHomeomorph left right hleft hright region)

/-- Helper for Theorem 77.1: the canonical same-scheme source comparison acts
componentwise. -/
theorem presentationSourceHomeomorph_apply {α : Type u}
    {scheme : LabellingScheme α}
    (left : PolygonalRegions.{u, v} scheme)
    (right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    (region : Occurrence scheme) (point : left.Point region) :
    presentationSourceHomeomorph left right hleft hright ⟨region, point⟩ =
      ⟨region, presentationComponentHomeomorph left right hleft hright region point⟩ := by
  -- Specialize the general sigma computation to the identity occurrence equivalence.
  exact sourceHomeomorphOfComponents_apply left right (Equiv.refl _)
    (fun current ↦ presentationComponentHomeomorph left right hleft hright current)
    region point

/-- Helper for Theorem 77.1: the canonical same-scheme source comparison
preserves every labelled boundary point. -/
theorem presentationSourceHomeomorph_edge {α : Type u}
    {scheme : LabellingScheme α}
    (left : PolygonalRegions.{u, v} scheme)
    (right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    (region : Occurrence scheme) (edge : Fin region.1.1.length)
    (t : unitInterval) :
    presentationSourceHomeomorph left right hleft hright
        ⟨region, left.edge region edge t⟩ =
      ⟨region, right.edge region edge t⟩ := by
  -- Compute on the component, then use its edge-parameter formula.
  rw [presentationSourceHomeomorph_apply,
    presentationComponentHomeomorph_edge]

/-- Helper for Theorem 77.1: the same-scheme source comparison preserves and
reflects direct labelled-edge pairings. -/
theorem edgeRelated_presentationSourceHomeomorph_iff {α : Type u}
    {scheme : LabellingScheme α}
    (left : PolygonalRegions.{u, v} scheme)
    (right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    (x y : left.Source) :
    right.EdgeRelated (presentationSourceHomeomorph left right hleft hright x)
        (presentationSourceHomeomorph left right hleft hright y) ↔
      left.EdgeRelated x y := by
  unfold EdgeRelated
  constructor
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabels, hx, hy⟩
    refine ⟨region₁, region₂, edge₁, edge₂, t, hlabels, ?_, ?_⟩
    · -- Reflect the first boundary equality through injectivity of the source map.
      apply (presentationSourceHomeomorph left right hleft hright).injective
      rw [presentationSourceHomeomorph_edge]
      exact hx
    · -- Reflect the second boundary equality in the same way.
      apply (presentationSourceHomeomorph left right hleft hright).injective
      rw [presentationSourceHomeomorph_edge]
      exact hy
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabels, hx, hy⟩
    refine ⟨region₁, region₂, edge₁, edge₂, t, hlabels, ?_, ?_⟩
    · -- Push the first source point through the edge computation.
      rw [hx, presentationSourceHomeomorph_edge]
    · -- Push the sign-corrected second source point through the same computation.
      rw [hy, presentationSourceHomeomorph_edge]

/-- Helper for Theorem 77.1: the same-scheme source comparison preserves and
reflects the full generated identification relation. -/
theorem identified_presentationSourceHomeomorph_iff {α : Type u}
    {scheme : LabellingScheme α}
    (left : PolygonalRegions.{u, v} scheme)
    (right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    (x y : left.Source) :
    right.Identified.r (presentationSourceHomeomorph left right hleft hright x)
        (presentationSourceHomeomorph left right hleft hright y) ↔
      left.Identified.r x y := by
  -- Lift direct edge preservation through the generated equivalence closure.
  unfold Identified
  exact eqvGen_equiv_iff
    (presentationSourceHomeomorph left right hleft hright).toEquiv
    (edgeRelated_presentationSourceHomeomorph_iff left right hleft hright) x y

/-- Helper for Theorem 77.1: a realization transports between any two
polygonal families carrying the same labelling scheme. -/
theorem realizesOfPresentationComparison {α : Type u}
    {scheme : LabellingScheme α}
    (left : PolygonalRegions.{u, v} scheme)
    (right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    {X : Type z} [TopologicalSpace X] (q : left.Source → X)
    (hrealizes : left.Realizes q) :
    right.Realizes
      (q ∘ (presentationSourceHomeomorph left right hleft hright).symm) := by
  constructor
  · -- Precomposition by the inverse source homeomorphism preserves quotientness.
    exact hrealizes.isQuotientMap.comp
      (presentationSourceHomeomorph left right hleft hright).symm.isQuotientMap
  · intro x y
    -- Cancel the inverse map and rewrite the resulting identification relation.
    simp only [Function.comp_apply]
    rw [hrealizes.fibers]
    simpa only [Homeomorph.apply_symm_apply] using
      (identified_presentationSourceHomeomorph_iff left right hleft hright
        ((presentationSourceHomeomorph left right hleft hright).symm x)
        ((presentationSourceHomeomorph left right hleft hright).symm y)).symm

end LabellingScheme.PolygonalRegions

namespace LabellingScheme.Presents

/-- Helper for Theorem 77.1: any two spaces presented by the same labelling
scheme are homeomorphic. -/
theorem homeomorphic_of_sameScheme {α : Type u} {scheme : LabellingScheme α}
    {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : scheme.Presents X) (hY : scheme.Presents Y) :
    Nonempty (X ≃ₜ Y) := by
  rw [LabellingScheme.presents_iff] at hX hY
  obtain ⟨left, hleft, qX, hrealizesX⟩ := hX
  obtain ⟨right, hright, qY, hrealizesY⟩ := hY
  let transported :=
    qX ∘ (LabellingScheme.PolygonalRegions.presentationSourceHomeomorph
      left right hleft hright).symm
  have htransported : right.Realizes transported := by
    -- Move the first quotient map to the source chosen by the second presentation.
    exact LabellingScheme.PolygonalRegions.realizesOfPresentationComparison
      left right hleft hright qX hrealizesX
  -- Both quotient maps now have the same polygonal source and generated relation.
  exact LabellingScheme.PolygonalRegions.Realizes.homeomorphicTargets
    right transported qY htransported hrealizesY

end LabellingScheme.Presents

end
