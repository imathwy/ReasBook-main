module

public import Topology_Munkres_2000.Book.Exercise_60_2
public import Topology_Munkres_2000.Book.Exercise_60_2.Quotient
public import Topology_Munkres_2000.Book.Example_74_2.UnitSquare
public import Topology_Munkres_2000.Book.Notation_74_1.SignedLetter
public import Topology_Munkres_2000.Book.Proposition_76_1.Realization
import all Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
import all Topology_Munkres_2000.Book.Example_74_2.UnitSquare
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Tactic.FinCases
public import Mathlib.Topology.Homeomorph.Quotient

public section

open scoped SignedLetter
open scoped Topology

/- Example 74.4 (1): The quotient of `B²` identifying each boundary point with its
antipode is homeomorphic to the real projective plane `P²`. -/
#check diskAntipodalQuotientHomeomorphicProjectivePlane

namespace ProjectivePlaneSquare

/-- The signed boundary letters `a b a b`, with labels `0 = a` and `1 = b`. -/
def boundaryLetters : List (Fin 2 × Bool) :=
  [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)]

/-- The polygon word encoding the projective-plane square scheme `a b a b`. -/
def boundaryWord : PolygonWord (Fin 2) :=
  ⟨boundaryLetters, by decide⟩

/-- The singleton labelling scheme whose boundary word is `a b a b`. -/
def scheme : LabellingScheme (Fin 2) :=
  boundaryWord ::ₘ 0

/-- The unit square with its ordered boundary edges prescribed by the word `a b a b`. -/
@[expose]
def regions : LabellingScheme.PolygonalRegions scheme where
  Point _ := unitInterval × unitInterval
  topology _ := inferInstance
  edge _ edge t := UnitSquare.edge edge t

/-- The labelled-edge realization of the square carrying `a b a b`. -/
abbrev Realization := regions.Realization

/-- Helper for Example 74.4: the unique polygonal-region occurrence in the square presentation. -/
noncomputable def region : LabellingScheme.Occurrence scheme :=
  (LabellingScheme.consOccurrenceEquiv boundaryWord 0).symm none

/-- Helper for Example 74.4: every occurrence in the singleton scheme is `region`. -/
lemma occurrence_eq_region (r : LabellingScheme.Occurrence scheme) : r = region := by
  -- The cons-occurrence equivalence sends the only possible occurrence to `none`.
  unfold region
  apply (LabellingScheme.consOccurrenceEquiv boundaryWord 0).injective
  rw [Equiv.apply_symm_apply]
  cases h : LabellingScheme.consOccurrenceEquiv boundaryWord 0 r with
  | none => rfl
  | some remaining =>
      exact (Nat.not_lt_zero remaining.2 remaining.2.isLt).elim

/-- Helper for Example 74.4: projection from the singleton region source to its square is a
homeomorphism. -/
lemma sourceProjectionIsHomeomorph :
    IsHomeomorph (fun x : regions.Source ↦ x.2) := by
  -- Route correction: implementation imports expose the coproduct topology directly.
  rw [isHomeomorph_iff_exists_inverse]
  constructor
  · -- Check projection continuity separately on every region summand.
    rw [continuous_iSup_dom]
    intro r
    rw [continuous_coinduced_dom]
    letI : TopologicalSpace (regions.Point r) := regions.topology r
    exact continuous_id
  · -- Insert into the unique summand and verify the two inverse equations.
    have hinclusion : Continuous[regions.topology region, regions.sourceTopology]
        (Sigma.mk region : regions.Point region → regions.Source) :=
      continuous_iSup_rng (i := region) (f := Sigma.mk region)
        (continuous_coinduced_rng (f := Sigma.mk region))
    refine ⟨fun p ↦ (⟨region, p⟩ : regions.Source), ?_, ?_, ?_⟩
    · rintro ⟨r, p⟩
      rw [occurrence_eq_region r]
    · intro p
      rfl
    · unfold regions at hinclusion ⊢
      exact hinclusion

/-- Helper for Example 74.4: the Euclidean plane used for the centered square and disk. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Helper for Example 74.4: the endpoints `-1` and `1` form a nondegenerate real interval. -/
lemma negOne_lt_one : (-1 : ℝ) < 1 := by
  -- This is the numerical side condition for the affine interval homeomorphism.
  norm_num

/-- Helper for Example 74.4: the closed product interval `[-1, 1] × [-1, 1]`. -/
def coordinateSquare : Set (ℝ × ℝ) :=
  Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1

/-- Helper for Example 74.4: pairs of real coordinates linearly identify with the Euclidean
plane. -/
noncomputable def pairToPlaneLinear : (ℝ × ℝ) ≃L[ℝ] Plane :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (Fin 2) ℝ).symm

/-- Helper for Example 74.4: the topological form of the standard coordinate equivalence. -/
noncomputable def pairToPlane : (ℝ × ℝ) ≃ₜ Plane :=
  pairToPlaneLinear.toHomeomorph

/-- Helper for Example 74.4: the coordinate square `[-1, 1]²` in the Euclidean plane. -/
def centeredSquare : Set Plane := pairToPlane '' coordinateSquare

/-- Helper for Example 74.4: affine centering identifies the unit square with `centeredSquare`. -/
noncomputable def unitSquareHomeomorphCenteredSquare :
    (unitInterval × unitInterval) ≃ₜ centeredSquare :=
  ((iccHomeoI (-1 : ℝ) 1 negOne_lt_one).symm.prodCongr
      (iccHomeoI (-1 : ℝ) 1 negOne_lt_one).symm).trans
    ((Homeomorph.Set.prod (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1)).symm.trans
      (Homeomorph.image pairToPlane coordinateSquare))

/-- Helper for Example 74.4: the centered square is convex. -/
lemma centeredSquare_convex : Convex ℝ centeredSquare := by
  -- Convexity is preserved by the standard linear coordinate equivalence.
  unfold centeredSquare pairToPlane coordinateSquare
  exact ((convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1)).linear_image
    pairToPlaneLinear.toLinearMap

/-- Helper for Example 74.4: the centered square is a neighborhood of the origin. -/
lemma centeredSquare_mem_nhds : centeredSquare ∈ 𝓝 (0 : Plane) := by
  -- The product interval is a neighborhood of zero, and a homeomorphism is open.
  have hcoordinate : coordinateSquare ∈ 𝓝 ((0 : ℝ), (0 : ℝ)) := by
    unfold coordinateSquare
    exact prod_mem_nhds (Icc_mem_nhds (by norm_num) (by norm_num))
      (Icc_mem_nhds (by norm_num) (by norm_num))
  have himage := pairToPlane.isOpenMap.image_mem_nhds hcoordinate
  have hzero : pairToPlane ((0 : ℝ), (0 : ℝ)) = (0 : Plane) := by
    exact map_zero pairToPlaneLinear
  rw [hzero] at himage
  exact himage

/-- Helper for Example 74.4: the centered square is von Neumann bounded. -/
lemma centeredSquare_isVonNBounded : Bornology.IsVonNBounded ℝ centeredSquare := by
  -- Bounded product intervals remain bounded under a continuous linear map.
  have hcoordinate : Bornology.IsVonNBounded ℝ coordinateSquare := by
    apply NormedSpace.isVonNBounded_of_isBounded
    unfold coordinateSquare
    exact (Metric.isBounded_Icc (-1 : ℝ) 1).prod (Metric.isBounded_Icc (-1 : ℝ) 1)
  simpa [centeredSquare, pairToPlane] using
    hcoordinate.image pairToPlaneLinear.toContinuousLinearMap

/-- Helper for Example 74.4: the centered square is invariant under negation. -/
lemma centeredSquare_neg_mem {x : Plane} (hx : x ∈ centeredSquare) : -x ∈ centeredSquare := by
  -- Negate the two interval coordinates before applying the linear equivalence.
  rcases hx with ⟨p, hp, rfl⟩
  refine ⟨-p, ?_, ?_⟩
  · rcases p with ⟨a, b⟩
    rcases hp with ⟨⟨haLower, haUpper⟩, ⟨hbLower, hbUpper⟩⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> dsimp <;> linarith
  · change pairToPlaneLinear (-p) = -pairToPlaneLinear p
    exact map_neg pairToPlaneLinear p

/-- Helper for Example 74.4: radial gauge rescaling carries the centered square to the unit disk. -/
noncomputable def centeredSquareRescale : Plane ≃ₜ Plane :=
  gaugeRescaleHomeomorph centeredSquare (Metric.closedBall 0 1)
    centeredSquare_convex centeredSquare_mem_nhds centeredSquare_isVonNBounded
    (convex_closedBall 0 1) (Metric.closedBall_mem_nhds 0 one_pos)
    (NormedSpace.isVonNBounded_closedBall ℝ Plane 1)

/-- Helper for Example 74.4: the centered square is closed. -/
lemma centeredSquare_isClosed : IsClosed centeredSquare := by
  -- A homeomorphism maps the closed product interval to a closed set.
  unfold centeredSquare coordinateSquare
  exact pairToPlane.isClosedMap _ (isClosed_Icc.prod isClosed_Icc)

/-- Helper for Example 74.4: gauge rescaling maps the centered square onto the closed unit disk. -/
lemma centeredSquareRescale_image :
    centeredSquareRescale '' centeredSquare = Metric.closedBall (0 : Plane) 1 := by
  -- The gauge theorem maps closures, and both sets are already closed.
  simpa only [centeredSquare_isClosed.closure_eq, Metric.isClosed_closedBall.closure_eq,
    centeredSquareRescale] using
      (image_gaugeRescaleHomeomorph_closure centeredSquare_convex centeredSquare_mem_nhds
        centeredSquare_isVonNBounded (convex_closedBall (0 : Plane) 1)
        (Metric.closedBall_mem_nhds (0 : Plane) one_pos)
        (NormedSpace.isVonNBounded_closedBall ℝ Plane 1))

/-- Helper for Example 74.4: membership in the square is equivalent to membership of its
rescaled image in the disk. -/
lemma centeredSquareRescale_mem_iff (x : Plane) :
    x ∈ centeredSquare ↔ centeredSquareRescale x ∈ Metric.closedBall (0 : Plane) 1 := by
  -- Use the exact image computation and injectivity of the ambient homeomorphism.
  constructor
  · intro hx
    rw [← centeredSquareRescale_image]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← centeredSquareRescale_image] at hx
    rcases hx with ⟨y, hy, hxy⟩
    exact centeredSquareRescale.injective hxy ▸ hy

/-- Helper for Example 74.4: gauge rescaling restricted to the centered square is a
homeomorphism onto the closed unit disk. -/
noncomputable def centeredSquareDiskHomeomorph : centeredSquare ≃ₜ B² :=
  centeredSquareRescale.subtype centeredSquareRescale_mem_iff

/-- Helper for Example 74.4: negation as a self-map of the centered square. -/
def centeredSquareNeg (x : centeredSquare) : centeredSquare :=
  ⟨-x.1, centeredSquare_neg_mem x.2⟩

/-- Helper for Example 74.4: the closed unit ball is invariant under negation. -/
lemma closedUnitBall_neg_mem {x : Plane} (hx : x ∈ Metric.closedBall (0 : Plane) 1) :
    -x ∈ Metric.closedBall (0 : Plane) 1 := by
  -- Negation preserves the norm defining the closed ball.
  simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using hx

/-- Helper for Example 74.4: centered gauge rescaling is an odd map. -/
lemma centeredSquareRescale_neg (x : Plane) :
    centeredSquareRescale (-x) = -centeredSquareRescale x := by
  -- Both gauges are even, so only the radial vector changes sign.
  change gaugeRescale centeredSquare (Metric.closedBall (0 : Plane) 1) (-x) =
    -gaugeRescale centeredSquare (Metric.closedBall (0 : Plane) 1) x
  rw [gaugeRescale_def, gaugeRescale_def, gauge_neg (fun _ hx ↦ centeredSquare_neg_mem hx),
    gauge_neg (fun _ hx ↦ closedUnitBall_neg_mem hx)]
  simp

/-- Helper for Example 74.4: the restricted square-to-disk rescaling commutes with negation. -/
lemma centeredSquareDiskHomeomorph_neg (x : centeredSquare) :
    centeredSquareDiskHomeomorph (centeredSquareNeg x) = -centeredSquareDiskHomeomorph x := by
  -- Equality of disk points follows from oddness in the ambient plane.
  apply Subtype.ext
  exact centeredSquareRescale_neg x.1

/-- Helper for Example 74.4: the frontier of the product interval consists of its four sides. -/
lemma mem_frontier_coordinateSquare_iff (p : ℝ × ℝ) (hp : p ∈ coordinateSquare) :
    p ∈ frontier coordinateSquare ↔
      p.1 = -1 ∨ p.1 = 1 ∨ p.2 = -1 ∨ p.2 = 1 := by
  -- Expand the frontier of a product and use the two endpoint frontiers.
  rw [coordinateSquare, frontier_prod_eq]
  simp only [isClosed_Icc.closure_eq, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1),
    Set.mem_union, Set.mem_prod, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hp with ⟨hpFirst, hpSecond⟩
  tauto

/-- Helper for Example 74.4: the coordinate homeomorphism preserves square frontiers. -/
lemma pairToPlane_mem_frontier_iff (p : ℝ × ℝ) :
    pairToPlane p ∈ frontier centeredSquare ↔ p ∈ frontier coordinateSquare := by
  -- Rewrite the target frontier as the homeomorphic image of the coordinate frontier.
  rw [centeredSquare, ← pairToPlane.image_frontier coordinateSquare]
  constructor
  · rintro ⟨q, hq, hqp⟩
    exact pairToPlane.injective hqp ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- Helper for Example 74.4: the standard coordinate equivalence commutes with negation. -/
lemma pairToPlane_neg (p : ℝ × ℝ) : pairToPlane (-p) = -pairToPlane p := by
  -- This is the additive computation rule of the underlying continuous linear equivalence.
  change pairToPlaneLinear (-p) = -pairToPlaneLinear p
  exact map_neg pairToPlaneLinear p

/-- Helper for Example 74.4: the affine square homeomorphism has the expected centered
coordinates. -/
lemma unitSquareHomeomorphCenteredSquare_coe (p : unitInterval × unitInterval) :
    ((unitSquareHomeomorphCenteredSquare p : centeredSquare) : Plane) =
      pairToPlane (2 * (p.1 : ℝ) - 1, 2 * (p.2 : ℝ) - 1) := by
  -- Unfold only the interval and product interfaces, then normalize the affine coordinates.
  have hprod :
      ((iccHomeoI (-1 : ℝ) 1 negOne_lt_one).symm.prodCongr
        (iccHomeoI (-1 : ℝ) 1 negOne_lt_one).symm) p =
      ((iccHomeoI (-1 : ℝ) 1 negOne_lt_one).symm p.1,
        (iccHomeoI (-1 : ℝ) 1 negOne_lt_one).symm p.2) := rfl
  calc
    ((unitSquareHomeomorphCenteredSquare p : centeredSquare) : Plane) =
        pairToPlane ↑((Homeomorph.Set.prod (Set.Icc (-1 : ℝ) 1)
          (Set.Icc (-1 : ℝ) 1)).symm
            ((iccHomeoI (-1 : ℝ) 1 negOne_lt_one).symm p.1,
              (iccHomeoI (-1 : ℝ) 1 negOne_lt_one).symm p.2)) := by
      simp only [unitSquareHomeomorphCenteredSquare, Homeomorph.trans_apply]
      rw [hprod]
      exact Homeomorph.image_apply_coe pairToPlane coordinateSquare
        ((Homeomorph.Set.prod (Set.Icc (-1 : ℝ) 1)
          (Set.Icc (-1 : ℝ) 1)).symm
            ((iccHomeoI (-1 : ℝ) 1 negOne_lt_one).symm p.1,
              (iccHomeoI (-1 : ℝ) 1 negOne_lt_one).symm p.2))
    _ = pairToPlane (2 * (p.1 : ℝ) - 1, 2 * (p.2 : ℝ) - 1) := by
      rw [Homeomorph.Set.prod_symm_apply_coe]
      apply congrArg pairToPlane
      ext <;> simp [iccHomeoI_symm_apply_coe] <;> ring

/-- Helper for Example 74.4: centering turns the square involution into vector negation. -/
lemma unitSquareHomeomorphCenteredSquare_symm (p : unitInterval × unitInterval) :
    unitSquareHomeomorphCenteredSquare (unitInterval.symm p.1, unitInterval.symm p.2) =
      centeredSquareNeg (unitSquareHomeomorphCenteredSquare p) := by
  -- Compare ambient vectors and use linearity of the coordinate equivalence.
  apply Subtype.ext
  change ((unitSquareHomeomorphCenteredSquare
      (unitInterval.symm p.1, unitInterval.symm p.2) : centeredSquare) : Plane) =
    -((unitSquareHomeomorphCenteredSquare p : centeredSquare) : Plane)
  rw [unitSquareHomeomorphCenteredSquare_coe, unitSquareHomeomorphCenteredSquare_coe]
  change pairToPlane
      (2 * (unitInterval.symm p.1 : ℝ) - 1,
        2 * (unitInterval.symm p.2 : ℝ) - 1) =
    -pairToPlane (2 * (p.1 : ℝ) - 1, 2 * (p.2 : ℝ) - 1)
  rw [← pairToPlane_neg]
  have hcoordinates :
      (2 * (unitInterval.symm p.1 : ℝ) - 1,
        2 * (unitInterval.symm p.2 : ℝ) - 1) =
      -(2 * (p.1 : ℝ) - 1, 2 * (p.2 : ℝ) - 1) := by
    ext <;> simp [unitInterval.symm] <;> ring
  exact congrArg pairToPlane hcoordinates

/-- Helper for Example 74.4: gauge rescaling identifies the square frontier with the unit
circle. -/
lemma centeredSquareRescale_frontier :
    centeredSquareRescale '' frontier centeredSquare = Metric.sphere (0 : Plane) 1 := by
  -- Homeomorphisms preserve frontiers, and the disk frontier is its unit sphere.
  rw [centeredSquareRescale.image_frontier, centeredSquareRescale_image,
    frontier_closedBall (0 : Plane) one_ne_zero]

/-- Helper for Example 74.4: a rescaled square point lies on the disk boundary exactly when its
source lies on the square frontier. -/
lemma centeredSquareDiskHomeomorph_isBoundary_iff (x : centeredSquare) :
    ClosedUnitDisk.IsBoundary (centeredSquareDiskHomeomorph x) ↔
      x.1 ∈ frontier centeredSquare := by
  -- Normalize disk boundary membership to the exact image of the square frontier.
  change ‖centeredSquareRescale x.1‖ = 1 ↔ x.1 ∈ frontier centeredSquare
  rw [← mem_sphere_zero_iff_norm, ← centeredSquareRescale_frontier]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact centeredSquareRescale.injective hxy ▸ hy
  · intro hx
    exact ⟨x.1, hx, rfl⟩

/-- Helper for Example 74.4: the centered affine coordinate is `-1` exactly at the left
endpoint. -/
lemma centeredCoordinate_eq_negOne_iff (u : unitInterval) :
    2 * (u : ℝ) - 1 = -1 ↔ u = 0 := by
  -- Coercion to `ℝ` is injective, so the claim is elementary affine arithmetic.
  constructor
  · intro h
    apply Subtype.ext
    dsimp
    linarith
  · rintro rfl
    norm_num

/-- Helper for Example 74.4: the centered affine coordinate is `1` exactly at the right
endpoint. -/
lemma centeredCoordinate_eq_one_iff (u : unitInterval) :
    2 * (u : ℝ) - 1 = 1 ↔ u = 1 := by
  -- Coercion to `ℝ` is injective, so the claim is elementary affine arithmetic.
  constructor
  · intro h
    apply Subtype.ext
    dsimp
    linarith
  · rintro rfl
    norm_num

/-- Helper for Example 74.4: the equivariant homeomorphism from the unit square to the closed
unit disk. -/
noncomputable def unitSquareDiskHomeomorph :
    (unitInterval × unitInterval) ≃ₜ B² :=
  unitSquareHomeomorphCenteredSquare.trans centeredSquareDiskHomeomorph

/-- Helper for Example 74.4: the square-to-disk homeomorphism maps precisely the four sides to
the boundary circle. -/
lemma unitSquareDiskHomeomorph_isBoundary_iff (p : unitInterval × unitInterval) :
    ClosedUnitDisk.IsBoundary (unitSquareDiskHomeomorph p) ↔
      p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1 := by
  -- Pass through the centered frontier and then read off its four affine endpoints.
  change ClosedUnitDisk.IsBoundary
      (centeredSquareDiskHomeomorph (unitSquareHomeomorphCenteredSquare p)) ↔ _
  rw [centeredSquareDiskHomeomorph_isBoundary_iff,
    unitSquareHomeomorphCenteredSquare_coe, pairToPlane_mem_frontier_iff]
  have hp : (2 * (p.1 : ℝ) - 1, 2 * (p.2 : ℝ) - 1) ∈ coordinateSquare := by
    rcases p.1.2 with ⟨hpLower, hpUpper⟩
    rcases p.2.2 with ⟨hqLower, hqUpper⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> dsimp <;> linarith
  rw [mem_frontier_coordinateSquare_iff _ hp]
  exact or_congr (centeredCoordinate_eq_negOne_iff p.1)
    (or_congr (centeredCoordinate_eq_one_iff p.1)
      (or_congr (centeredCoordinate_eq_negOne_iff p.2)
        (centeredCoordinate_eq_one_iff p.2)))

/-- Helper for Example 74.4: the square-to-disk homeomorphism intertwines the square involution
and disk antipodes. -/
lemma unitSquareDiskHomeomorph_symm (p : unitInterval × unitInterval) :
    unitSquareDiskHomeomorph (unitInterval.symm p.1, unitInterval.symm p.2) =
      -unitSquareDiskHomeomorph p := by
  -- The affine centering and radial rescaling are both odd.
  change centeredSquareDiskHomeomorph
      (unitSquareHomeomorphCenteredSquare (unitInterval.symm p.1, unitInterval.symm p.2)) =
    -centeredSquareDiskHomeomorph (unitSquareHomeomorphCenteredSquare p)
  rw [unitSquareHomeomorphCenteredSquare_symm, centeredSquareDiskHomeomorph_neg]

/-- Helper for Example 74.4: there is an equivariant square-to-disk homeomorphism with the
required boundary specification. -/
theorem existsUnitSquareHomeomorphClosedUnitDisk :
    ∃ e : (unitInterval × unitInterval) ≃ₜ B²,
      (∀ p, ClosedUnitDisk.IsBoundary (e p) ↔
        p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) ∧
      ∀ p, e (unitInterval.symm p.1, unitInterval.symm p.2) = -e p := by
  -- Package the two proved computation rules as the geometric interface.
  exact ⟨unitSquareDiskHomeomorph, unitSquareDiskHomeomorph_isBoundary_iff,
    unitSquareDiskHomeomorph_symm⟩

/-- Helper for Example 74.4: the unique occurrence carries the displayed boundary word. -/
lemma region_word : region.1 = boundaryWord := by
  -- The inverse occurrence equivalence selects the head of the singleton scheme.
  rfl

/-- Helper for Example 74.4: every occurrence of the square scheme has four edges. -/
lemma occurrence_length (r : LabellingScheme.Occurrence scheme) : r.1.1.length = 4 := by
  -- Normalize to the unique occurrence and compute the concrete word length.
  rw [occurrence_eq_region r, region_word]
  decide

/-- Helper for Example 74.4: the explicit counterclockwise parametrization of the four square
edges. -/
def explicitUnitSquareEdge (index : ℕ) (t : unitInterval) : unitInterval × unitInterval :=
  match index with
  | 0 => (t, 0)
  | 1 => (1, t)
  | 2 => (unitInterval.symm t, 1)
  | _ => (0, unitInterval.symm t)

/-- Helper for Example 74.4: `UnitSquare.edge` agrees with its four explicit formulas. -/
lemma unitSquare_edge_eq_explicit (index : ℕ) (t : unitInterval) :
    UnitSquare.edge index t = explicitUnitSquareEdge index t := by
  -- Both edge parametrizations reduce to the same four cases.
  rfl

/-- Helper for Example 74.4: direct labelled-edge relatedness has its defining witness form. -/
lemma edgeRelated_iff_witness (x y : regions.Source) :
    regions.EdgeRelated x y ↔
      ∃ (region₁ region₂ : LabellingScheme.Occurrence scheme)
        (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
        (t : unitInterval),
          (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1 ∧
          x = ⟨region₁, regions.edge region₁ edge₁ t⟩ ∧
          y = ⟨region₂, regions.edge region₂ edge₂
            (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
              else unitInterval.symm t)⟩ := by
  -- Expose the generating relation as its canonical edge-and-parameter witnesses.
  rfl

/-- Helper for Example 74.4: the labelled-edge setoid is the equivalence closure of direct
edge relatedness. -/
lemma identified_iff_eqvGen (x y : regions.Source) :
    regions.Identified.r x y ↔ Relation.EqvGen regions.EdgeRelated x y := by
  -- The realization setoid is definitionally the equivalence closure of edge pairings.
  rfl

/-- Helper for Example 74.4: a direct `a b a b` edge pairing is either equality or the square
antipode of a boundary point. -/
lemma edgeRelated_eq_or_boundary_symm {x y : regions.Source}
    (hxy : regions.EdgeRelated x y) :
    y.2 = x.2 ∨
      ((x.2.1 = 0 ∨ x.2.1 = 1 ∨ x.2.2 = 0 ∨ x.2.2 = 1) ∧
        y.2 = (unitInterval.symm x.2.1, unitInterval.symm x.2.2)) := by
  -- Normalize both occurrence indices, then enumerate the sixteen pairs of square edges.
  rw [edgeRelated_iff_witness] at hxy
  rcases hxy with ⟨region₁, region₂, edge₁, edge₂, t, hlabel, rfl, rfl⟩
  have hregion₁ := occurrence_eq_region region₁
  have hregion₂ := occurrence_eq_region region₂
  subst region₁
  subst region₂
  fin_cases edge₁ <;> fin_cases edge₂ <;>
    simp [regions, region_word, boundaryWord, boundaryLetters,
      unitSquare_edge_eq_explicit, explicitUnitSquareEdge] at hlabel ⊢

/-- Helper for Example 74.4: every boundary point is directly paired with its square antipode. -/
lemma edgeRelated_antipode_of_boundary (p : unitInterval × unitInterval)
    (hp : p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) :
    regions.EdgeRelated ⟨region, p⟩
      ⟨region, (unitInterval.symm p.1, unitInterval.symm p.2)⟩ := by
  -- Select the opposite edge corresponding to each of the four possible sides.
  rw [edgeRelated_iff_witness]
  rcases hp with hpLeft | hpRight | hpBottom | hpTop
  · have hpPair : p = (0, p.2) := Prod.ext hpLeft rfl
    rw [hpPair]
    refine ⟨region, region, Fin.cast (occurrence_length region).symm (3 : Fin 4),
      Fin.cast (occurrence_length region).symm (1 : Fin 4), unitInterval.symm p.2, ?_⟩
    simp [regions, region_word, boundaryWord, boundaryLetters,
      unitSquare_edge_eq_explicit, explicitUnitSquareEdge]
  · have hpPair : p = (1, p.2) := Prod.ext hpRight rfl
    rw [hpPair]
    refine ⟨region, region, Fin.cast (occurrence_length region).symm (1 : Fin 4),
      Fin.cast (occurrence_length region).symm (3 : Fin 4), p.2, ?_⟩
    simp [regions, region_word, boundaryWord, boundaryLetters,
      unitSquare_edge_eq_explicit, explicitUnitSquareEdge]
  · have hpPair : p = (p.1, 0) := Prod.ext rfl hpBottom
    rw [hpPair]
    refine ⟨region, region, Fin.cast (occurrence_length region).symm (0 : Fin 4),
      Fin.cast (occurrence_length region).symm (2 : Fin 4), p.1, ?_⟩
    simp [regions, region_word, boundaryWord, boundaryLetters,
      unitSquare_edge_eq_explicit, explicitUnitSquareEdge]
  · have hpPair : p = (p.1, 1) := Prod.ext rfl hpTop
    rw [hpPair]
    refine ⟨region, region, Fin.cast (occurrence_length region).symm (2 : Fin 4),
      Fin.cast (occurrence_length region).symm (0 : Fin 4), unitInterval.symm p.1, ?_⟩
    simp [regions, region_word, boundaryWord, boundaryLetters,
      unitSquare_edge_eq_explicit, explicitUnitSquareEdge]

/-- Helper for Example 74.4: every source point has the unique region as its first component. -/
lemma source_eq_region_mk (x : regions.Source) : x = ⟨region, x.2⟩ := by
  -- Replace the sigma index by the unique occurrence.
  rcases x with ⟨i, p⟩
  have hi := occurrence_eq_region i
  subst i
  rfl

/-- Helper for Example 74.4: a direct square edge pairing maps to the disk-antipodal setoid. -/
lemma edgeRelated_diskAntipodalSetoid
    (e : (unitInterval × unitInterval) ≃ₜ B²)
    (hboundary : ∀ p, ClosedUnitDisk.IsBoundary (e p) ↔
      p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1)
    (hsymm : ∀ p, e (unitInterval.symm p.1, unitInterval.symm p.2) = -e p)
    {x y : regions.Source} (hxy : regions.EdgeRelated x y) :
    DiskAntipodalQuotient.setoid (e x.2) (e y.2) := by
  -- A direct pairing is equality or a boundary antipode, exactly the two disk cases.
  rw [DiskAntipodalQuotient.setoid_rel_iff]
  rcases edgeRelated_eq_or_boundary_symm hxy with hEq | ⟨hBoundary, hSymm⟩
  · exact Or.inl (congrArg e hEq)
  · refine Or.inr ⟨(hboundary x.2).2 hBoundary, ?_⟩
    rw [hSymm, hsymm]

/-- Helper for Example 74.4: the generated square relation is exactly the transported
disk-antipodal setoid. -/
lemma identified_iff_diskAntipodalSetoid
    (e : (unitInterval × unitInterval) ≃ₜ B²)
    (hboundary : ∀ p, ClosedUnitDisk.IsBoundary (e p) ↔
      p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1)
    (hsymm : ∀ p, e (unitInterval.symm p.1, unitInterval.symm p.2) = -e p)
    (x y : regions.Source) :
    regions.Identified.r x y ↔ DiskAntipodalQuotient.setoid (e x.2) (e y.2) := by
  -- Forward, the disk setoid is an equivalence relation containing every generating edge pair.
  rw [identified_iff_eqvGen]
  constructor
  · intro hxy
    induction hxy with
    | rel a b hab => exact edgeRelated_diskAntipodalSetoid e hboundary hsymm hab
    | refl a => exact DiskAntipodalQuotient.setoid.refl (e a.2)
    | symm a b _ hab => exact DiskAntipodalQuotient.setoid.symm hab
    | trans a b c _ _ hab hbc => exact DiskAntipodalQuotient.setoid.trans hab hbc
  · intro hxy
    rw [DiskAntipodalQuotient.setoid_rel_iff] at hxy
    rcases hxy with hEq | ⟨hBoundary, hAntipode⟩
    · have hSecond : y.2 = x.2 := e.injective hEq
      have hSource : y = x := by
        calc
          y = ⟨region, y.2⟩ := source_eq_region_mk y
          _ = ⟨region, x.2⟩ := congrArg (fun p ↦ Sigma.mk region p) hSecond
          _ = x := (source_eq_region_mk x).symm
      rw [hSource]
      exact Relation.EqvGen.refl x
    · have hBoundarySquare := (hboundary x.2).1 hBoundary
      have hSecond : y.2 = (unitInterval.symm x.2.1, unitInterval.symm x.2.2) := by
        apply e.injective
        exact hAntipode.trans (hsymm x.2).symm
      have hSourceY :
          y = ⟨region, (unitInterval.symm x.2.1, unitInterval.symm x.2.2)⟩ := by
        calc
          y = ⟨region, y.2⟩ := source_eq_region_mk y
          _ = ⟨region, (unitInterval.symm x.2.1,
              unitInterval.symm x.2.2)⟩ := congrArg (fun p ↦ Sigma.mk region p) hSecond
      rw [source_eq_region_mk x, hSourceY]
      exact Relation.EqvGen.rel _ _ (edgeRelated_antipode_of_boundary x.2 hBoundarySquare)

/-- Helper for Example 74.4: project the unique region source and apply the equivariant
square-to-disk homeomorphism. -/
noncomputable def sourceDiskHomeomorph : regions.Source ≃ₜ B² :=
  (IsHomeomorph.homeomorph (fun x : regions.Source ↦ x.2)
    sourceProjectionIsHomeomorph).trans unitSquareDiskHomeomorph

/-- Helper for Example 74.4: `sourceDiskHomeomorph` transports the labelled-edge setoid to the
disk-antipodal setoid. -/
lemma sourceDiskHomeomorph_relation (x y : regions.Source) :
    regions.Identified.r x y ↔
      DiskAntipodalQuotient.setoid (sourceDiskHomeomorph x) (sourceDiskHomeomorph y) := by
  -- The source projection contributes no coordinate change, so use the normalized relation.
  simpa only [sourceDiskHomeomorph, Homeomorph.trans_apply, IsHomeomorph.homeomorph_apply] using
    (identified_iff_diskAntipodalSetoid unitSquareDiskHomeomorph
      unitSquareDiskHomeomorph_isBoundary_iff unitSquareDiskHomeomorph_symm x y)

/-- Example 74.4 (2): The square realization specified by the scheme `a b a b` is
homeomorphic to the quotient of `B²` identifying antipodal boundary points. -/
theorem homeomorphicDiskAntipodalQuotient :
    Nonempty (Realization ≃ₜ DiskAntipodalQuotient.Space) := by
  -- Quotient congruence transports the now-identical source relations.
  exact ⟨Homeomorph.Quotient.congr sourceDiskHomeomorph sourceDiskHomeomorph_relation⟩

/-- The square realization specified by `a b a b` is homeomorphic to the real projective
plane `P²`. -/
theorem homeomorphicProjectivePlane :
    Nonempty (Realization ≃ₜ RealProjectivePlane) := by
  -- Compose the square-disk quotient identification with the earlier projective-plane model.
  exact Nonempty.map2 Homeomorph.trans homeomorphicDiskAntipodalQuotient
    diskAntipodalQuotientHomeomorphicProjectivePlane


end ProjectivePlaneSquare
