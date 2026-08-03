module

public import Topology_Munkres_2000.Book.Proposition_76_2.Pasting
public import Topology_Munkres_2000.Book.Proposition_74_1
public import Topology_Munkres_2000.Book.Definition_76_6.Realization
public import Topology_Munkres_2000.Book.Theorem_76_1.Presentation
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

public section

namespace CyclicPolygon

/-- Helper for Theorem 78.2: transport a cyclic polygon across an equality of
its numbers of sides. -/
def castSides {first second : ℕ} (h : first = second)
    (poly : CyclicPolygon first) : CyclicPolygon second :=
  h ▸ poly

/-- Helper for Theorem 78.2: reversing indices conjugates the cyclic successor
to its inverse. -/
theorem rev_finRotate {n : ℕ} (poly : CyclicPolygon n) (i : Fin n) :
    (finRotate n i).rev = (finRotate n).symm i.rev := by
  haveI : NeZero n :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) poly.three_le)⟩
  -- Write cyclic rotation as addition by one and use reversal of finite addition.
  rw [finRotate_apply, Fin.rev_add, finRotate_symm_apply]

/-- Helper for Theorem 78.2: a successor followed by reversal and another
successor is just reversal. -/
theorem finRotate_rev_finRotate {n : ℕ} (poly : CyclicPolygon n) (i : Fin n) :
    finRotate n (finRotate n i).rev = i.rev := by
  -- The preceding conjugacy turns the outer rotation into cancellation.
  rw [poly.rev_finRotate, (finRotate n).apply_symm_apply]

/-- Helper for Theorem 78.2: reversing edge indices and affine parameters sends
equal boundary representatives to equal boundary representatives. -/
theorem edgePoint_eq_reverse {n : ℕ} (left right : CyclicPolygon n)
    (i j : Fin n) (s t : unitInterval) :
    left.edgePoint i s = left.edgePoint j t →
      right.edgePoint i.rev (unitInterval.symm s) =
        right.edgePoint j.rev (unitInterval.symm t) := by
  intro hpoint
  rw [left.edgePoint_eq_iff] at hpoint
  rw [right.edgePoint_eq_iff]
  rcases hpoint with ⟨hij, hst⟩ | ⟨hs, ht, hij⟩ | ⟨hs, ht, hij⟩
  · exact Or.inl ⟨congrArg Fin.rev hij, congrArg unitInterval.symm hst⟩
  · subst s
    subst t
    subst i
    exact Or.inr (Or.inr ⟨unitInterval.symm_zero,
      unitInterval.symm_one, right.finRotate_rev_finRotate j⟩)
  · subst s
    subst t
    subst j
    exact Or.inr (Or.inl ⟨unitInterval.symm_one,
      unitInterval.symm_zero, (right.finRotate_rev_finRotate i).symm⟩)

/-- Helper for Theorem 78.2: simultaneous reversal of edge indices and affine
parameters preserves the complete boundary-point fiber relation. -/
theorem edgePoint_eq_reverse_iff {n : ℕ} (left right : CyclicPolygon n)
    (i j : Fin n) (s t : unitInterval) :
    left.edgePoint i s = left.edgePoint j t ↔
      right.edgePoint i.rev (unitInterval.symm s) =
        right.edgePoint j.rev (unitInterval.symm t) := by
  constructor
  · exact left.edgePoint_eq_reverse right i j s t
  · intro hpoint
    -- Apply the forward lemma to the reversed data; both involutions cancel.
    have hback := right.edgePoint_eq_reverse left i.rev j.rev
      (unitInterval.symm s) (unitInterval.symm t) hpoint
    simpa only [Fin.rev_rev, unitInterval.symm_symm] using hback

/-- Helper for Theorem 78.2: two cyclic polygon boundaries admit a
homeomorphism reversing both edge order and edge parameters. -/
theorem existsBoundaryHomeomorphReversingEdgeParameters {n : ℕ}
    (left right : CyclicPolygon n) :
    ∃ h : left.boundary ≃ₜ right.boundary, ∀ (i : Fin n) (s : unitInterval),
      h (left.edgePoint i s) =
        right.edgePoint i.rev (unitInterval.symm s) := by
  let f : C(Fin n × unitInterval, left.boundary) :=
    ⟨fun z ↦ left.edgePoint z.1 z.2, left.continuous_edgePoint⟩
  let g : C(Fin n × unitInterval, right.boundary) :=
    ⟨fun z ↦ right.edgePoint z.1 z.2, right.continuous_edgePoint⟩
  have hf : Topology.IsQuotientMap f :=
    Topology.IsQuotientMap.of_surjective_continuous left.edgePoint_surjective
      left.continuous_edgePoint
  have hg : Topology.IsQuotientMap g :=
    Topology.IsQuotientMap.of_surjective_continuous right.edgePoint_surjective
      right.continuous_edgePoint
  let sourceHomeomorph :
      (Fin n × unitInterval) ≃ₜ (Fin n × unitInterval) :=
    (Homeomorph.ofDiscrete (Fin.revPerm : Fin n ≃ Fin n)).prodCongr
      unitInterval.symmHomeomorph
  have hsource (z : Fin n × unitInterval) :
      sourceHomeomorph z = (z.1.rev, unitInterval.symm z.2) := rfl
  have hker : ∀ z z', f z = f z' ↔
      g (sourceHomeomorph z) = g (sourceHomeomorph z') := by
    intro z z'
    dsimp only [f, g]
    rw [hsource, hsource]
    exact left.edgePoint_eq_reverse_iff right z.1 z'.1 z.2 z'.2
  obtain ⟨h, hh⟩ := existsHomeomorphOfQuotientPresentations
    f g hf hg sourceHomeomorph hker
  refine ⟨h, ?_⟩
  intro i s
  -- Evaluate the induced quotient homeomorphism on the chosen edge representative.
  have hspec := hh (i, s)
  dsimp only [f, g, sourceHomeomorph] at hspec
  exact hspec

/-- Helper for Theorem 78.2: reversing a cyclic polygon boundary extends to a
filled-region homeomorphism with the expected reversed edge formula. -/
theorem existsRegionHomeomorphReversingEdgeParameters {n : ℕ}
    (left right : CyclicPolygon n) :
    ∃ H : left.region ≃ₜ right.region, ∀ (i : Fin n) (s : unitInterval),
      H (left.boundaryToRegion
          (left.edgePoint (Fin.revPerm i) (unitInterval.symm s))) =
        right.boundaryToRegion (right.edgePoint i s) := by
  classical
  let p : left.interior := Classical.choice left.interior_nonempty.to_subtype
  let q : right.interior := Classical.choice right.interior_nonempty.to_subtype
  obtain ⟨h, hedge⟩ := left.existsBoundaryHomeomorphReversingEdgeParameters right
  obtain ⟨H, hH⟩ := existsRadialExtension left right p q h
  refine ⟨H, ?_⟩
  intro i s
  -- View each boundary point as the endpoint of its radial segment.
  rw [← left.radialPoint_one p
    (left.edgePoint (Fin.revPerm i) (unitInterval.symm s))]
  rw [hH.map_radialPoint, hedge]
  simpa only [Fin.revPerm_apply, Fin.rev_rev, unitInterval.symm_symm] using
    right.radialPoint_one q (right.edgePoint i s)

/-- Helper for Theorem 78.2: the reversing filled-region homeomorphism also
works when the two side counts are propositionally equal. -/
theorem existsRegionHomeomorphReversingEdgeParametersOfEq
    {first second : ℕ} (h : first = second) (left : CyclicPolygon first)
    (right : CyclicPolygon second) :
    ∃ H : left.region ≃ₜ right.region, ∀ (i : Fin second) (s : unitInterval),
      H (left.boundaryToRegion
          (left.edgePoint (Fin.revPerm (Fin.cast h.symm i))
            (unitInterval.symm s))) =
        right.boundaryToRegion (right.edgePoint i s) := by
  -- Eliminate the side-count equality once, then use the homogeneous theorem.
  subst second
  exact left.existsRegionHomeomorphReversingEdgeParameters right

/-- Helper for Theorem 78.2: the parameter-preserving filled-region
homeomorphism also works across a propositional equality of side counts. -/
theorem existsRegionHomeomorphPreservingEdgeParametersOfEq
    {first second : ℕ} (h : first = second) (left : CyclicPolygon first)
    (right : CyclicPolygon second) :
    ∃ H : left.region ≃ₜ right.region, ∀ (i : Fin second) (s : unitInterval),
      H (left.boundaryToRegion
          (left.edgePoint (Fin.cast h.symm i) s)) =
        right.boundaryToRegion (right.edgePoint i s) := by
  -- Eliminate the side-count equality once, then use Proposition 76.2.
  subst second
  exact left.existsRegionHomeomorphPreservingEdgeParameters right

/-- Helper for Theorem 78.2: a cyclic edge equivalence commuting with successor
extends to a filled-region homeomorphism with the corresponding edge formula. -/
theorem existsRegionHomeomorphPreservingEdgeParametersAlongOfEq
    {first second : ℕ} (h : first = second) (left : CyclicPolygon first)
    (right : CyclicPolygon second) (e : Fin first ≃ Fin second)
    (he : ∀ i, e (finRotate first i) = finRotate second (e i)) :
    ∃ H : left.region ≃ₜ right.region, ∀ (i : Fin first) (s : unitInterval),
      H (left.boundaryToRegion (left.edgePoint i s)) =
        right.boundaryToRegion (right.edgePoint (e i) s) := by
  subst second
  classical
  let p : left.interior := Classical.choice left.interior_nonempty.to_subtype
  let q : right.interior := Classical.choice right.interior_nonempty.to_subtype
  obtain ⟨boundaryHomeomorph, hedge, hextension⟩ :=
    existsBoundaryHomeomorphWithRadialExtensionAlong left right e he
  obtain ⟨H, hH⟩ := hextension p q
  refine ⟨H, ?_⟩
  intro i s
  -- Rewrite both boundary points as radial endpoints and use the cyclic map.
  rw [← left.radialPoint_one p (left.edgePoint i s)]
  rw [hH.map_radialPoint, hedge.map_edgePoint]
  exact right.radialPoint_one q (right.edgePoint (e i) s)

end CyclicPolygon

namespace LabellingScheme.PolygonalRegions

universe u v

variable {alpha : Type u} {word : PolygonWord alpha}
  {rest : LabellingScheme alpha}

/-- Helper for Theorem 78.2: flipping one polygon word preserves geometric
polygonality of every presented region. -/
theorem flipped_isPolygonal
    (original : PolygonalRegions.{u, v} (word ::ₘ rest))
    (hpolygonal : original.IsPolygonal) : original.flipped.IsPolygonal := by
  rw [isPolygonal_iff] at hpolygonal ⊢
  intro region
  let targetEquiv := consOccurrenceEquiv word.formalInverse rest
  cases hposition : targetEquiv region with
  | none =>
      have hregion : region = targetEquiv.symm none :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      let selected := targetEquiv.symm none
      let source := flipRegionEquiv.symm selected
      letI : TopologicalSpace (original.Point source) := original.topology source
      letI : TopologicalSpace (original.flipped.Point selected) :=
        original.flipped.topology selected
      obtain ⟨presentation⟩ := hpolygonal source
      let targetPolygon := CyclicPolygon.castSides
        (flipRegion_length selected).symm presentation.polygon
      obtain ⟨H, hH⟩ :=
        CyclicPolygon.existsRegionHomeomorphReversingEdgeParametersOfEq
          (flipRegion_length selected).symm presentation.polygon targetPolygon
      let componentHomeomorph :
          RegionHomeomorph original.flipped selected targetPolygon.region :=
        presentation.homeomorph.trans H
      have hcomponentApply (x : original.flipped.Point selected) :
          componentHomeomorph x = H (presentation.homeomorph x) := by
        rfl
      refine ⟨CyclicRegion.ofHomeomorph targetPolygon componentHomeomorph ?_⟩
      intro edge t
      have hpresentation :
          presentation.homeomorph
              (original.edge source
                (Fin.cast (flipRegion_length selected) edge).rev
                (unitInterval.symm t)) =
            presentation.polygon.boundaryToRegion
              (presentation.polygon.edgePoint
                (Fin.cast (flipRegion_length selected) edge).rev
                (unitInterval.symm t)) := by
        apply Subtype.ext
        exact (presentation.edgeCompatibility
          (Fin.cast (flipRegion_length selected) edge).rev
          (unitInterval.symm t)).trans
            ((presentation.polygon.edgePoint_coe_eq_lineMap
                (Fin.cast (flipRegion_length selected) edge).rev
                (unitInterval.symm t)).symm.trans
              (presentation.polygon.boundaryToRegion_coe
                (presentation.polygon.edgePoint
                  (Fin.cast (flipRegion_length selected) edge).rev
                  (unitInterval.symm t))).symm)
      -- Normalize the selected flip, then apply the reversing region homeomorphism.
      have hHedge := hH edge t
      simp only [Fin.revPerm_apply] at hHedge
      rw [hcomponentApply, original.flipped_edge]
      dsimp only [selected, source, targetEquiv] at hpresentation ⊢
      rw [flipEdgeIndex_selected, flipParameter_selected, hpresentation, hHedge]
      exact (targetPolygon.boundaryToRegion_coe
        (targetPolygon.edgePoint edge t)).trans
          (targetPolygon.edgePoint_coe_eq_lineMap edge t)
  | some remainder =>
      have hregion : region = targetEquiv.symm (some remainder) :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      let retained := targetEquiv.symm (some remainder)
      let source := flipRegionEquiv.symm retained
      letI : TopologicalSpace (original.Point source) := original.topology source
      letI : TopologicalSpace (original.flipped.Point retained) :=
        original.flipped.topology retained
      obtain ⟨presentation⟩ := hpolygonal source
      let targetPolygon := CyclicPolygon.castSides
        (flipRegion_length retained).symm presentation.polygon
      obtain ⟨H, hH⟩ :=
        CyclicPolygon.existsRegionHomeomorphPreservingEdgeParametersOfEq
          (flipRegion_length retained).symm presentation.polygon targetPolygon
      let componentHomeomorph :
          RegionHomeomorph original.flipped retained targetPolygon.region :=
        presentation.homeomorph.trans H
      have hcomponentApply (x : original.flipped.Point retained) :
          componentHomeomorph x = H (presentation.homeomorph x) := by
        rfl
      refine ⟨CyclicRegion.ofHomeomorph targetPolygon componentHomeomorph ?_⟩
      intro edge t
      have hpresentation :
          presentation.homeomorph
              (original.edge source
                (Fin.cast (flipRegion_length retained) edge) t) =
            presentation.polygon.boundaryToRegion
              (presentation.polygon.edgePoint
                (Fin.cast (flipRegion_length retained) edge) t) := by
        apply Subtype.ext
        exact (presentation.edgeCompatibility
          (Fin.cast (flipRegion_length retained) edge) t).trans
            ((presentation.polygon.edgePoint_coe_eq_lineMap
                (Fin.cast (flipRegion_length retained) edge) t).symm.trans
              (presentation.polygon.boundaryToRegion_coe
                (presentation.polygon.edgePoint
                  (Fin.cast (flipRegion_length retained) edge) t)).symm)
      -- Normalize the unchanged branch, then apply the preserving homeomorphism.
      rw [hcomponentApply, original.flipped_edge]
      dsimp only [retained, source, targetEquiv] at hpresentation ⊢
      rw [flipEdgeIndex_remainder, flipParameter_remainder,
        hpresentation, hH]
      exact (targetPolygon.boundaryToRegion_coe
        (targetPolygon.edgePoint edge t)).trans
          (targetPolygon.edgePoint_coe_eq_lineMap edge t)

end LabellingScheme.PolygonalRegions

namespace LabellingScheme.PolygonalRegions.Renumbering

universe u v

/-- Helper for Theorem 78.2: the concrete append-swap renumbering preserves
geometric polygonality. -/
theorem ofAppend_isPolygonal {alpha : Type u}
    (y₀ y₁ : List (alpha × Bool)) (rest : LabellingScheme alpha)
    (hLength : 3 ≤ (y₀ ++ y₁).length)
    (original : PolygonalRegions.{u, v}
      (⟨y₀ ++ y₁, hLength⟩ ::ₘ rest))
    (hpolygonal : original.IsPolygonal) :
    ((ofAppend y₀ y₁ rest hLength).regions original).IsPolygonal := by
  rw [isPolygonal_iff] at hpolygonal ⊢
  intro region
  let renumbering := ofAppend y₀ y₁ rest hLength
  let source := renumbering.regionEquiv.symm region
  letI : TopologicalSpace (original.Point source) := original.topology source
  letI : TopologicalSpace ((renumbering.regions original).Point region) :=
    (renumbering.regions original).topology region
  obtain ⟨presentation⟩ := hpolygonal source
  let targetPolygon := CyclicPolygon.castSides
    (ofAppend_region_length y₀ y₁ rest hLength region)
      presentation.polygon
  obtain ⟨H, hH⟩ :=
    CyclicPolygon.existsRegionHomeomorphPreservingEdgeParametersAlongOfEq
      (ofAppend_region_length y₀ y₁ rest hLength region)
      presentation.polygon targetPolygon (renumbering.edgeEquiv region)
      (ofAppend_edgeEquiv_finRotate y₀ y₁ rest hLength region)
  let componentHomeomorph :
      RegionHomeomorph (renumbering.regions original) region targetPolygon.region :=
    presentation.homeomorph.trans H
  have hcomponentApply (x : (renumbering.regions original).Point region) :
      componentHomeomorph x = H (presentation.homeomorph x) := by
    rfl
  refine ⟨CyclicRegion.ofHomeomorph targetPolygon componentHomeomorph ?_⟩
  intro edge t
  let sourceEdge := (renumbering.edgeEquiv region).symm edge
  have hpresentation :
      presentation.homeomorph (original.edge source sourceEdge t) =
        presentation.polygon.boundaryToRegion
          (presentation.polygon.edgePoint sourceEdge t) := by
    apply Subtype.ext
    exact (presentation.edgeCompatibility sourceEdge t).trans
      ((presentation.polygon.edgePoint_coe_eq_lineMap sourceEdge t).symm.trans
        (presentation.polygon.boundaryToRegion_coe
          (presentation.polygon.edgePoint sourceEdge t)).symm)
  have hHedge := hH sourceEdge t
  rw [hcomponentApply, renumbering.regions_edge]
  rw [hpresentation, hHedge,
    (renumbering.edgeEquiv region).apply_symm_apply]
  exact (targetPolygon.boundaryToRegion_coe
    (targetPolygon.edgePoint edge t)).trans
      (targetPolygon.edgePoint_coe_eq_lineMap edge t)

end LabellingScheme.PolygonalRegions.Renumbering

namespace LabellingScheme.Presents

universe u v

/-- Helper for Theorem 78.2: cyclically moving an initial list segment to the
end preserves a polygonal presentation of the same space. -/
theorem appendSwap {alpha : Type u} (y₀ y₁ : List (alpha × Bool))
    (rest : LabellingScheme alpha) (hLength : 3 ≤ (y₀ ++ y₁).length)
    {X : Type v} [TopologicalSpace X]
    (hpresents : Presents (⟨y₀ ++ y₁, hLength⟩ ::ₘ rest) X) :
    Presents
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest) X := by
  rw [LabellingScheme.presents_iff] at hpresents ⊢
  obtain ⟨regions, hpolygonal, q, hrealizes⟩ := hpresents
  let renumbering :=
    PolygonalRegions.Renumbering.ofAppend y₀ y₁ rest hLength
  let qRenumbered : (renumbering.regions regions).Source → X :=
    q ∘ (renumbering.sourceHomeomorph regions).symm
  refine ⟨renumbering.regions regions,
    PolygonalRegions.Renumbering.ofAppend_isPolygonal
      y₀ y₁ rest hLength regions hpolygonal,
    qRenumbered, ?_⟩
  constructor
  · -- Precompose the original quotient map with the renumbering homeomorphism.
    exact hrealizes.isQuotientMap.comp
      (renumbering.sourceHomeomorph regions).symm.isQuotientMap
  · intro x y
    dsimp only [qRenumbered, Function.comp_apply]
    rw [renumbering.sourceHomeomorph_symm_apply,
      renumbering.sourceHomeomorph_symm_apply, hrealizes.fibers]
    have hidentified := renumbering.identified_iff regions
      ((renumbering.sourceEquiv regions).symm x)
      ((renumbering.sourceEquiv regions).symm y)
    simpa only [Equiv.apply_symm_apply] using hidentified

/-- Helper for Theorem 78.2: formally inverting one polygon word preserves a
polygonal presentation of the same space. -/
theorem formalInverseCons {alpha : Type u} {word : PolygonWord alpha}
    {rest : LabellingScheme alpha} {X : Type v} [TopologicalSpace X]
    (hpresents : Presents (word ::ₘ rest) X) :
    Presents (word.formalInverse ::ₘ rest) X := by
  rw [LabellingScheme.presents_iff] at hpresents ⊢
  obtain ⟨regions, hpolygonal, q, hrealizes⟩ := hpresents
  let qFlipped : regions.flipped.Source → X :=
    q ∘ regions.flipSourceHomeomorph.symm
  refine ⟨regions.flipped, regions.flipped_isPolygonal hpolygonal,
    qFlipped, ?_⟩
  constructor
  · -- Precomposing a quotient map with a homeomorphism remains quotient.
    exact hrealizes.isQuotientMap.comp
      regions.flipSourceHomeomorph.symm.isQuotientMap
  · intro x y
    dsimp only [qFlipped, Function.comp_apply]
    rw [regions.flipSourceHomeomorph_symm_apply,
      regions.flipSourceHomeomorph_symm_apply]
    rw [hrealizes.fibers]
    have hidentified := regions.identified_flip_iff
      (regions.flipSourceEquiv.symm x) (regions.flipSourceEquiv.symm y)
    simpa only [Equiv.apply_symm_apply] using hidentified

end LabellingScheme.Presents

end
