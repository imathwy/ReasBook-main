module

public import Topology_Munkres_2000.Book.Algorithm_76_2.Cut
public import Topology_Munkres_2000.Book.Proposition_76_1
public import Topology_Munkres_2000.Book.Proposition_76_2
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization

public section

universe u w

namespace LabellingScheme

namespace PolygonalRegions

/-- Helper for Theorem 76.1: the standard lifted arguments of a regular `n`-gon. -/
private noncomputable def regularAngles (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  2 * Real.pi * i / n

/-- Helper for Theorem 76.1: the lifted arguments of a regular polygon are strictly
increasing when it has at least three sides. -/
private theorem regularAngles_strictMono (n : ℕ) (hn : 3 ≤ n) :
    StrictMono (regularAngles n) := by
  intro i j hij
  rw [regularAngles, regularAngles]
  have hnPositive : (0 : ℝ) < n := by
    positivity
  have hcoefficient : (0 : ℝ) < 2 * Real.pi := by
    positivity
  rw [div_lt_div_iff_of_pos_right hnPositive]
  exact mul_lt_mul_of_pos_left (Nat.cast_lt.2 hij) hcoefficient

/-- Helper for Theorem 76.1: the last lifted argument of the regular polygon closes
one full turn after its first argument. -/
private theorem regularAngles_last (n : ℕ) (hn : 3 ≤ n) :
    regularAngles n (Fin.last n) = regularAngles n 0 + 2 * Real.pi := by
  rw [regularAngles, regularAngles]
  have hnPositive : (0 : ℝ) < n := by
    positivity
  field_simp
  norm_num [Fin.last]

/-- Helper for Theorem 76.1: every admissible number of sides has a standard regular
cyclic polygon. -/
private noncomputable def regularPolygon (n : ℕ) (hn : 3 ≤ n) : CyclicPolygon n where
  three_le := hn
  center := 0
  radius := 1
  radius_pos := zero_lt_one
  angles := regularAngles n
  angles_strictMono := regularAngles_strictMono n hn
  angles_last := regularAngles_last n hn

/-- Helper for Theorem 76.1: the canonical family assigns to every polygon word its
standard regular filled polygon and its affine boundary parametrization. -/
private noncomputable def regularRegions {α : Type u} (scheme : LabellingScheme α) :
    PolygonalRegions.{u, w} scheme where
  Point region := ULift.{w} (regularPolygon region.1.1.length region.1.2).region
  topology _ := inferInstance
  edge region edge t :=
    ULift.up ((regularPolygon region.1.1.length region.1.2).boundaryToRegion
      ((regularPolygon region.1.1.length region.1.2).edgePoint edge t))

/-- Helper for Theorem 76.1: the canonical family has the expected affine edge
parametrization on every boundary component. -/
private theorem regularRegions_edgeCompatibility {α : Type u}
    (scheme : LabellingScheme α) (region : Occurrence scheme)
    (edge : Fin region.1.1.length) (t : unitInterval) :
    ((((regularRegions.{u, w} scheme).edge region edge t).down :
      (regularPolygon region.1.1.length region.1.2).region) :
        EuclideanSpace ℝ (Fin 2)) =
      AffineMap.lineMap
        ((regularPolygon region.1.1.length region.1.2).toPolygon.vertices edge)
        ((regularPolygon region.1.1.length region.1.2).toPolygon.vertices
          (finRotate region.1.1.length edge)) (t : ℝ) := by
  change (((regularPolygon region.1.1.length region.1.2).boundaryToRegion
    ((regularPolygon region.1.1.length region.1.2).edgePoint edge t) :
      (regularPolygon region.1.1.length region.1.2).region) :
        EuclideanSpace ℝ (Fin 2)) = _
  rw [(regularPolygon region.1.1.length region.1.2).boundaryToRegion_coe,
    (regularPolygon region.1.1.length region.1.2).edgePoint_coe_eq_lineMap]

/-- Helper for Theorem 76.1: each component of the canonical family is presented by
its standard regular cyclic polygon. -/
private noncomputable def regularCyclicRegion {α : Type u} (scheme : LabellingScheme α)
    (region : Occurrence scheme) : CyclicRegion (regularRegions.{u, w} scheme) region :=
  CyclicRegion.ofHomeomorph
    (regularPolygon region.1.1.length region.1.2)
    Homeomorph.ulift
    (regularRegions_edgeCompatibility.{u, w} scheme region)

/-- Helper for Theorem 76.1: the canonical family is polygonal. -/
private theorem regularRegions_isPolygonal {α : Type u} (scheme : LabellingScheme α) :
    (regularRegions scheme).IsPolygonal := by
  rw [isPolygonal_iff]
  intro region
  exact ⟨regularCyclicRegion scheme region⟩

/-- Helper for Theorem 76.1: two polygonal presentations of the same component admit
an edge-parameter-preserving homeomorphism. -/
private noncomputable def componentComparison {α : Type u} {scheme : LabellingScheme α}
    (left right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    (region : Occurrence scheme) :
    RegionHomeomorph.Between left region right region :=
  letI : TopologicalSpace (left.Point region) := left.topology region
  letI : TopologicalSpace (right.Point region) := right.topology region
  let leftPresentation := Classical.choice ((isPolygonal_iff left).mp hleft region)
  let rightPresentation := Classical.choice ((isPolygonal_iff right).mp hright region)
  let polygonComparison := Classical.choose
    (leftPresentation.polygon.existsRegionHomeomorphPreservingEdgeParameters
      rightPresentation.polygon)
  leftPresentation.homeomorph.trans
    (polygonComparison.trans rightPresentation.homeomorph.symm)

/-- Helper for Theorem 76.1: the component comparison carries each labelled edge
point to the point with the same edge index and affine parameter. -/
private theorem componentComparison_edge {α : Type u} {scheme : LabellingScheme α}
    (left right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    (region : Occurrence scheme) (edge : Fin region.1.1.length)
    (t : unitInterval) :
    componentComparison left right hleft hright region (left.edge region edge t) =
      right.edge region edge t := by
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
    apply Subtype.ext
    exact (leftPresentation.edgeCompatibility edge t).trans
      ((leftPresentation.polygon.edgePoint_coe_eq_lineMap edge t).symm.trans
        (leftPresentation.polygon.boundaryToRegion_coe
          (leftPresentation.polygon.edgePoint edge t)).symm)
  have hrightEdge :
      rightPresentation.homeomorph (right.edge region edge t) =
        rightPresentation.polygon.boundaryToRegion
          (rightPresentation.polygon.edgePoint edge t) := by
    apply Subtype.ext
    exact (rightPresentation.edgeCompatibility edge t).trans
      ((rightPresentation.polygon.edgePoint_coe_eq_lineMap edge t).symm.trans
        (rightPresentation.polygon.boundaryToRegion_coe
          (rightPresentation.polygon.edgePoint edge t)).symm)
  apply rightPresentation.homeomorph.injective
  rw [componentComparison]
  simp only [Homeomorph.trans_apply]
  rw [hleftEdge, hrightEdge, rightPresentation.homeomorph.apply_symm_apply]
  exact hpolygonComparison edge t

/-- Helper for Theorem 76.1: componentwise edge-preserving comparisons assemble to a
homeomorphism of the disjoint unions of polygonal regions. -/
private noncomputable def sourceComparison {α : Type u} {scheme : LabellingScheme α}
    (left right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal) :
    left.Source ≃ₜ right.Source :=
  letI : ∀ region, TopologicalSpace (left.Point region) :=
    fun region ↦ left.topology region
  letI : ∀ region, TopologicalSpace (right.Point region) :=
    fun region ↦ right.topology region
  IsHomeomorph.homeomorph
    (Sigma.map (fun region ↦ region)
      (fun region point ↦ componentComparison left right hleft hright region point))
    (IsHomeomorph.sigmaMap Function.bijective_id fun region ↦
      (componentComparison left right hleft hright region).isHomeomorph)

/-- Helper for Theorem 76.1: the source comparison has the expected componentwise
value. -/
private theorem sourceComparison_apply {α : Type u} {scheme : LabellingScheme α}
    (left right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    (region : Occurrence scheme) (point : left.Point region) :
    sourceComparison left right hleft hright ⟨region, point⟩ =
      ⟨region, componentComparison left right hleft hright region point⟩ := by
  simp only [sourceComparison, IsHomeomorph.homeomorph_apply]
  rfl

/-- Helper for Theorem 76.1: the source comparison preserves every labelled boundary
point. -/
private theorem sourceComparison_edge {α : Type u} {scheme : LabellingScheme α}
    (left right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    (region : Occurrence scheme) (edge : Fin region.1.1.length)
    (t : unitInterval) :
    sourceComparison left right hleft hright
        ⟨region, left.edge region edge t⟩ =
      ⟨region, right.edge region edge t⟩ := by
  rw [sourceComparison_apply, componentComparison_edge]

/-- Helper for Theorem 76.1: the source comparison preserves and reflects direct
labelled-edge pairings. -/
private theorem edgeRelated_sourceComparison_iff {α : Type u}
    {scheme : LabellingScheme α} (left right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    (x y : left.Source) :
    right.EdgeRelated (sourceComparison left right hleft hright x)
        (sourceComparison left right hleft hright y) ↔
      left.EdgeRelated x y := by
  unfold EdgeRelated
  constructor
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabels, hx, hy⟩
    refine ⟨region₁, region₂, edge₁, edge₂, t, hlabels, ?_, ?_⟩
    · apply (sourceComparison left right hleft hright).injective
      rw [sourceComparison_edge]
      exact hx
    · apply (sourceComparison left right hleft hright).injective
      rw [sourceComparison_edge]
      exact hy
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabels, hx, hy⟩
    refine ⟨region₁, region₂, edge₁, edge₂, t, hlabels, ?_, ?_⟩
    · rw [hx, sourceComparison_edge]
    · rw [hy, sourceComparison_edge]

/-- Helper for Theorem 76.1: an equivalence preserving a relation also preserves the
equivalence relation generated by it. -/
private theorem eqvGen_sourceComparison_iff {A B : Type*} (equiv : A ≃ B)
    {r : A → A → Prop} {s : B → B → Prop}
    (hrel : ∀ x y, s (equiv x) (equiv y) ↔ r x y) (x y : A) :
    Relation.EqvGen s (equiv x) (equiv y) ↔ Relation.EqvGen r x y := by
  constructor
  · intro hxy
    have hpull : ∀ {a b}, Relation.EqvGen s a b →
        Relation.EqvGen r (equiv.symm a) (equiv.symm b) := by
      intro a b hab
      induction hab with
      | rel a b hab =>
          exact Relation.EqvGen.rel _ _
            ((hrel (equiv.symm a) (equiv.symm b)).mp (by simpa using hab))
      | refl a => exact Relation.EqvGen.refl _
      | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans a b c _ _ hab hbc => exact Relation.EqvGen.trans _ _ _ hab hbc
    simpa using hpull hxy
  · intro hxy
    have hpush : ∀ {a b}, Relation.EqvGen r a b →
        Relation.EqvGen s (equiv a) (equiv b) := by
      intro a b hab
      induction hab with
      | rel a b hab => exact Relation.EqvGen.rel _ _ ((hrel a b).mpr hab)
      | refl a => exact Relation.EqvGen.refl _
      | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans a b c _ _ hab hbc => exact Relation.EqvGen.trans _ _ _ hab hbc
    exact hpush hxy

/-- Helper for Theorem 76.1: componentwise edge-preserving comparisons preserve the
full generated labelled-edge relation. -/
private theorem identified_sourceComparison_iff {α : Type u}
    {scheme : LabellingScheme α} (left right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    (x y : left.Source) :
    right.Identified.r (sourceComparison left right hleft hright x)
        (sourceComparison left right hleft hright y) ↔
      left.Identified.r x y := by
  unfold Identified
  exact eqvGen_sourceComparison_iff
    (sourceComparison left right hleft hright).toEquiv
    (edgeRelated_sourceComparison_iff left right hleft hright) x y

/-- Helper for Theorem 76.1: a realization transports between any two polygonal
families carrying the same labelling scheme. -/
private theorem realizes_of_isPolygonal {α : Type u} {scheme : LabellingScheme α}
    (left right : PolygonalRegions.{u, w} scheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    {X : Type w} [TopologicalSpace X] (q : left.Source → X)
    (hrealizes : left.Realizes q) :
    right.Realizes (q ∘ (sourceComparison left right hleft hright).symm) := by
  constructor
  · exact hrealizes.isQuotientMap.comp
      (sourceComparison left right hleft hright).symm.isQuotientMap
  · intro x y
    simp only [Function.comp_apply]
    rw [hrealizes.fibers]
    simpa only [Homeomorph.apply_symm_apply] using
      (identified_sourceComparison_iff left right hleft hright
        ((sourceComparison left right hleft hright).symm x)
        ((sourceComparison left right hleft hright).symm y)).symm

end PolygonalRegions

/-- A labelling scheme presents `X` when a collection of genuine polygonal regions with
that scheme realizes `X` by its labelled-edge quotient. -/
def Presents (scheme : LabellingScheme α) (X : Type w) [TopologicalSpace X] : Prop :=
  ∃ regions : PolygonalRegions.{u, w} scheme, regions.IsPolygonal ∧
    ∃ q : regions.Source → X, regions.Realizes q

/-- A presentation consists exactly of geometrically certified polygonal regions and a
quotient map to the presented space with the prescribed labelled-edge fibers. -/
theorem presents_iff (scheme : LabellingScheme α) (X : Type w) [TopologicalSpace X] :
    scheme.Presents X ↔ ∃ regions : PolygonalRegions.{u, w} scheme, regions.IsPolygonal ∧
      ∃ q : regions.Source → X, regions.Realizes q :=
  Iff.rfl

namespace Presents

/-- Cutting one genuine polygonal region along the diagonal prescribed by a cut step
produces genuine polygonal regions presenting the same space. -/
theorem cut {α : Type u} {before after : LabellingScheme α} (hcut : Cut before after)
    {X : Type w} [TopologicalSpace X] (hbefore : before.Presents X) :
    after.Presents X := by
  classical
  -- Use a standard split family to obtain concrete geometric paste data.
  rcases hcut with ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hy₀, hy₁, hrest⟩
  rw [presents_iff] at hbefore ⊢
  obtain ⟨originalRegions, horiginalPolygonal, q, horiginal⟩ := hbefore
  let splitRegions := PolygonalRegions.regularRegions.{u, w}
    (⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
      ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest)
  have hsplitPolygonal : splitRegions.IsPolygonal := by
    exact PolygonalRegions.regularRegions_isPolygonal _
  obtain ⟨result, hmergedPolygonal, _⟩ :=
    pasteRealizesSameSpace y₀ y₁ c b rest hy₀Length hy₁Length hy₀ hy₁ hrest
      splitRegions hsplitPolygonal splitRegions.quotientMap splitRegions.quotientMap_realizes
  -- Transport the given realization to the merged family supplied by the paste.
  let mergedQuotient :=
    q ∘ (PolygonalRegions.sourceComparison originalRegions result.pasting.mergedRegions
      horiginalPolygonal hmergedPolygonal).symm
  have hmergedRealizes : result.pasting.mergedRegions.Realizes mergedQuotient := by
    exact PolygonalRegions.realizes_of_isPolygonal originalRegions result.pasting.mergedRegions
      horiginalPolygonal hmergedPolygonal q horiginal
  let remainingPastes := mergedQuotient ∘ result.pasting.sourceHomeomorph
  have hremainingComposite :
      remainingPastes ∘ result.pasting.sourceHomeomorph.symm = mergedQuotient := by
    funext point
    exact congrArg mergedQuotient
      (result.pasting.sourceHomeomorph.apply_symm_apply point)
  have hremaining : result.pasting.mergedRegions.Realizes
      (remainingPastes ∘ result.pasting.sourceHomeomorph.symm) := by
    rw [hremainingComposite]
    exact hmergedRealizes
  -- Proposition 76.1 now cuts the merged realization back into the standard split family.
  have hsplitRealizes :=
    cutSchemeRealizesSameSpace y₀ y₁ c b rest hy₀Length hy₁Length
      result.pasting.mergedRegions splitRegions result.firstPaste remainingPastes
      result.pasting.pastesLabel result.pasting.sourceHomeomorph
      result.pasting.boundaryCompatibility hremaining
  exact ⟨splitRegions, hsplitPolygonal, remainingPastes ∘ result.firstPaste, hsplitRealizes⟩

/-- Pasting the two genuine polygonal regions along the fresh pair of edges prescribed
by a cut step produces a genuine polygonal region presenting the same space. -/
theorem paste {α : Type u} {before after : LabellingScheme α} (hcut : Cut before after)
    {X : Type w} [TopologicalSpace X] (hafter : after.Presents X) :
    before.Presents X := by
  classical
  -- Expose the cut data and apply the geometric reassembly theorem to the given presentation.
  rcases hcut with ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hy₀, hy₁, hrest⟩
  rw [presents_iff] at hafter ⊢
  obtain ⟨splitRegions, hsplitPolygonal, q, hsplit⟩ := hafter
  obtain ⟨result, hmergedPolygonal, mergedQuotient, hmerged⟩ :=
    pasteRealizesSameSpace y₀ y₁ c b rest hy₀Length hy₁Length hy₀ hy₁ hrest
      splitRegions hsplitPolygonal q hsplit
  exact ⟨result.pasting.mergedRegions, hmergedPolygonal, mergedQuotient, hmerged⟩

end Presents

/-- Cutting a polygon word along a fresh label preserves the presented space. -/
theorem presents_iff_of_cut {α : Type u} {before after : LabellingScheme α}
    (hcut : Cut before after) {X : Type w} [TopologicalSpace X] :
    before.Presents X ↔ after.Presents X :=
  ⟨Presents.cut hcut, Presents.paste hcut⟩

end LabellingScheme

end
