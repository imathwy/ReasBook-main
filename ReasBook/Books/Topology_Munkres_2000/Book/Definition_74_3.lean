module

public import Topology_Munkres_2000.Book.Definition_74_1.CyclicPolygon
public import Topology_Munkres_2000.Book.Definition_74_2.OrientedSegment
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Topology.Constructions

public section


namespace CyclicPolygon

open Set

universe v

variable {n : ℕ} (poly : CyclicPolygon n)

/-- Helper for Definition 74.3: a cyclic vertex has its defining polar-coordinate formula. -/
lemma vertex_apply (poly : CyclicPolygon n) (i : Fin (n + 1)) :
    poly.vertex i =
      poly.center + poly.radius •
        WithLp.toLp 2 ![Real.cos (poly.angles i), Real.sin (poly.angles i)] := by
  -- Expose the owner definition once so later coordinate arguments use a stable normal form.
  unfold CyclicPolygon.vertex
  rfl

/-- Helper for Definition 74.3: a cyclic rotation has no fixed point
when there are at least two indices. -/
lemma ne_finRotate (hn : 2 ≤ n) (i : Fin n) : i ≠ finRotate n i := by
  -- Reduce rotation to addition by one and compare the underlying finite indices.
  cases n with
  | zero => exact i.elim0
  | succ m =>
      intro h
      rw [finRotate_apply] at h
      have hv := congrArg Fin.val h
      rw [Fin.val_add_one] at hv
      split at hv
      · rename_i hi
        have hi_val := congrArg Fin.val hi
        simp only [Fin.val_last] at hi_val
        omega
      · omega

/-- Helper for Definition 74.3: consecutive vertices of a cyclic polygon are distinct. -/
theorem cyclicEdgeEndpoints_ne (poly : CyclicPolygon n) (i : Fin n) :
    poly.toPolygon.vertices i ≠ poly.toPolygon.vertices (finRotate n i) := by
  -- Equality of vertices forces equality of their cosine and sine coordinates.
  intro hvertices
  rw [poly.toPolygon_vertices, poly.toPolygon_vertices, poly.vertex_apply,
    poly.vertex_apply] at hvertices
  have hcosScaled : poly.radius * Real.cos (poly.angles i.castSucc) =
      poly.radius * Real.cos (poly.angles (finRotate n i).castSucc) := by
    have hcoordinate := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hvertices
    simpa [PiLp.toLp_apply] using hcoordinate
  have hsinScaled : poly.radius * Real.sin (poly.angles i.castSucc) =
      poly.radius * Real.sin (poly.angles (finRotate n i).castSucc) := by
    have hcoordinate := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hvertices
    simpa [PiLp.toLp_apply] using hcoordinate
  -- Package the coordinate equalities as equality on the common circle.
  have hcircle : circleMap 0 poly.radius (poly.angles i.castSucc) =
      circleMap 0 poly.radius (poly.angles (finRotate n i).castSucc) := by
    apply Complex.ext
    · simpa [circleMap_zero_re] using hcosScaled
    · simpa [circleMap_zero_im] using hsinScaled
  -- Both lifted angles lie in the same interval of length strictly less than one full turn.
  have hi_upper := poly.angles_strictMono (Fin.castSucc_lt_last i)
  have hj_upper := poly.angles_strictMono (Fin.castSucc_lt_last (finRotate n i))
  have hi_lower : poly.angles 0 ≤ poly.angles i.castSucc :=
    poly.angles_strictMono.monotone (Fin.zero_le _)
  have hj_lower : poly.angles 0 ≤ poly.angles (finRotate n i).castSucc :=
    poly.angles_strictMono.monotone (Fin.zero_le _)
  have hdist : |poly.angles i.castSucc - poly.angles (finRotate n i).castSucc| <
      2 * Real.pi := by
    rw [abs_lt]
    rw [poly.angles_last] at hi_upper hj_upper
    constructor <;> linarith
  -- Circle-map injectivity on this interval contradicts the nontrivial cyclic rotation.
  have hangles : poly.angles i.castSucc = poly.angles (finRotate n i).castSucc :=
    eq_of_circleMap_eq poly.radius_pos.ne' hdist hcircle
  have hindices : i.castSucc = (finRotate n i).castSucc :=
    poly.angles_strictMono.injective hangles
  have hrotate : i = finRotate n i := Fin.castSucc_inj.mp hindices
  exact ne_finRotate (le_trans (by omega : 2 ≤ 3) poly.three_le) i hrotate

/-- The `i`th polygon edge oriented in the cyclic direction. -/
noncomputable def cyclicOrientation (poly : CyclicPolygon n) (i : Fin n) :
    OrientedSegment (EuclideanSpace ℝ (Fin 2)) where
  initial := poly.toPolygon.vertices i
  final := poly.toPolygon.vertices (finRotate n i)
  ne := poly.cyclicEdgeEndpoints_ne i

/-- The `i`th polygon edge with the orientation selected by a sign. -/
noncomputable def signedOrientation (poly : CyclicPolygon n) (i : Fin n) (sign : Bool) :
    OrientedSegment (EuclideanSpace ℝ (Fin 2)) :=
  if sign then poly.cyclicOrientation i else (poly.cyclicOrientation i).reverse

/-- Helper for Definition 74.3: an oriented segment carrier is its closed segment. -/
lemma OrientedSegment.carrier_def {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : OrientedSegment E) : L.carrier = segment ℝ L.initial L.final := by
  -- Expose the owner definition in the same normal form used by polygon edges.
  unfold OrientedSegment.carrier
  rfl

/-- Helper for Definition 74.3: cyclic orientation has the corresponding polygon edge as carrier. -/
theorem cyclicOrientation_carrier (poly : CyclicPolygon n) (i : Fin n) :
    (poly.cyclicOrientation i).carrier = poly.edgeSet i := by
  -- Rewrite both constructions to the same segment between consecutive vertices.
  rw [OrientedSegment.carrier_def, cyclicOrientation, edgeSet_def, Polygon.edgeSet,
    affineSegment_eq_segment]

/-- A signed orientation has the corresponding polygon edge as its carrier. -/
theorem signedOrientation_carrier (poly : CyclicPolygon n) (i : Fin n) (sign : Bool) :
    (poly.signedOrientation i sign).carrier = poly.edgeSet i := by
  -- The sign changes only the ordering of endpoints, not the underlying segment.
  cases sign
  · simp only [signedOrientation, Bool.false_eq_true, if_false,
      OrientedSegment.carrier_reverse, poly.cyclicOrientation_carrier]
  · simp only [signedOrientation, if_true, poly.cyclicOrientation_carrier]

/-- Definition 74.3: A choice of label and orientation for every polygon edge,
together with the quotient generated by positive identifications of equally labelled edges. -/
structure EdgePasting (poly : CyclicPolygon n) (S : Type v) where
  /-- The label assigned to each edge. -/
  label : Fin n → S
  /-- Each polygon edge with its chosen ordering of endpoints. -/
  orientation : Fin n → OrientedSegment (EuclideanSpace ℝ (Fin 2))
  /-- Whether each orientation agrees with the cyclic direction. -/
  sign : Fin n → Bool
  /-- The sign records the chosen orientation relative to the cyclic direction. -/
  orientation_eq (i : Fin n) : orientation i = poly.signedOrientation i (sign i)

namespace EdgePasting

noncomputable section

variable {poly : CyclicPolygon n} {S : Type v}

/-- Build an edge pasting from labels and signs relative to the cyclic orientation. -/
def ofSigns (poly : CyclicPolygon n) (label : Fin n → S) (sign : Fin n → Bool) :
    poly.EdgePasting S where
  label := label
  orientation i := poly.signedOrientation i (sign i)
  sign := sign
  orientation_eq _ := rfl

/-- The carrier of every oriented edge lies in the polygonal region. -/
theorem carrier_subset_region (pasting : poly.EdgePasting S) (i : Fin n) :
    (pasting.orientation i).carrier ⊆ poly.region := by
  -- Normalize the chosen orientation to the canonical cyclic edge carrier.
  rw [pasting.orientation_eq, poly.signedOrientation_carrier]
  exact poly.edgeSet_subset_region i

/-- A point of an oriented edge, regarded as a point of the polygonal region. -/
def includePoint (pasting : poly.EdgePasting S) (i : Fin n)
    (x : (pasting.orientation i).carrier) : poly.region :=
  ⟨x, pasting.carrier_subset_region i x.property⟩

/-- Including an oriented-edge point in the region preserves its underlying point. -/
theorem includePoint_coe (pasting : poly.EdgePasting S) (i : Fin n)
    (x : (pasting.orientation i).carrier) :
    (pasting.includePoint i x : EuclideanSpace ℝ (Fin 2)) = x := by
  -- `includePoint` only changes the membership proof of the underlying point.
  rfl

/-- The point on edge `i` with its chosen positive affine parameter. -/
def orientedPoint (pasting : poly.EdgePasting S) (i : Fin n) (t : unitInterval) :
    poly.region :=
  pasting.includePoint i ((pasting.orientation i).point t)

/-- Oriented edge parameterization is the canonical parameterization from Definition 74.2. -/
theorem orientedPoint_apply (pasting : poly.EdgePasting S) (i : Fin n)
    (t : unitInterval) :
    pasting.orientedPoint i t =
      pasting.includePoint i ((pasting.orientation i).point t) := by
  -- This is the defining computation rule for the region-valued parameterization.
  rfl

/-- The positive linear identification of two chosen oriented edges. -/
noncomputable def positiveIdentification (pasting : poly.EdgePasting S) (i j : Fin n) :
    (pasting.orientation i).carrier ≃ₜ (pasting.orientation j).carrier :=
  (pasting.orientation i).positiveHomeomorph (pasting.orientation j)

/-- Positive edge identification preserves the common affine parameter. -/
theorem positiveIdentification_point (pasting : poly.EdgePasting S) (i j : Fin n)
    (t : unitInterval) :
    pasting.positiveIdentification i j ((pasting.orientation i).point t) =
      (pasting.orientation j).point t := by
  -- The positive identification is defined by the common affine parameter.
  have hsource :
      (pasting.orientation i).paramHomeomorph t = (pasting.orientation i).point t := by
    apply Subtype.ext
    rw [OrientedSegment.paramHomeomorph_apply, OrientedSegment.point_coe]
  have htarget :
      (pasting.orientation j).paramHomeomorph t = (pasting.orientation j).point t := by
    apply Subtype.ext
    rw [OrientedSegment.paramHomeomorph_apply, OrientedSegment.point_coe]
  rw [← hsource, ← htarget]
  exact (pasting.orientation i).positiveHomeomorph_apply (pasting.orientation j) t

/-- Two region points are directly paired when equally labelled oriented edges give them
the positive linear identification. -/
def Related (pasting : poly.EdgePasting S) (x y : poly.region) : Prop :=
  ∃ i j : Fin n, pasting.label i = pasting.label j ∧
    ∃ z : (pasting.orientation i).carrier,
      x = pasting.includePoint i z ∧
        y = pasting.includePoint j (pasting.positiveIdentification i j z)

/-- Direct edge pairing is characterized by equal labels and the positive edge identification. -/
theorem related_iff (pasting : poly.EdgePasting S) (x y : poly.region) :
    pasting.Related x y ↔
      ∃ i j : Fin n, pasting.label i = pasting.label j ∧
        ∃ z : (pasting.orientation i).carrier,
          x = pasting.includePoint i z ∧
            y = pasting.includePoint j (pasting.positiveIdentification i j z) := Iff.rfl

/-- The equivalence relation generated by the direct equally labelled edge pairings. -/
abbrev Identified (pasting : poly.EdgePasting S) : Setoid poly.region :=
  Relation.EqvGen.setoid pasting.Related

/-- Helper for Definition 74.3: an interior point cannot be an endpoint of a direct edge
identification, in either direction. -/
theorem not_related_of_mem_interior (pasting : poly.EdgePasting S) (x y : poly.region)
    (hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ poly.interior) :
    ¬ pasting.Related x y ∧ ¬ pasting.Related y x := by
  -- Interior membership records precisely that the point is not on the polygon boundary.
  rw [poly.interior_def] at hx
  constructor
  · intro hrelated
    obtain ⟨i, j, _, z, rfl, _⟩ := hrelated
    apply hx.2
    rw [poly.boundary_def]
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [pasting.includePoint_coe]
    rw [← poly.signedOrientation_carrier, ← pasting.orientation_eq]
    exact z.property
  · intro hrelated
    obtain ⟨i, j, _, z, _, rfl⟩ := hrelated
    apply hx.2
    rw [poly.boundary_def]
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    rw [pasting.includePoint_coe]
    rw [← poly.signedOrientation_carrier, ← pasting.orientation_eq]
    exact (pasting.positiveIdentification i j z).property

/-- Interior points of the polygonal region are identified only with themselves. -/
theorem identified_interior_iff (pasting : poly.EdgePasting S) (x y : poly.region)
    (hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ poly.interior) :
    pasting.Identified x y ↔ x = y := by
  -- Propagate the boundary-exclusion invariant through the generated equivalence relation.
  constructor
  · intro hidentified
    have hrigid : ∀ {a b : poly.region}, Relation.EqvGen pasting.Related a b →
        (((a : EuclideanSpace ℝ (Fin 2)) ∈ poly.interior → a = b) ∧
          ((b : EuclideanSpace ℝ (Fin 2)) ∈ poly.interior → a = b)) := by
      intro a b hab
      induction hab with
      | rel a b hab =>
          constructor
          · intro ha
            exact False.elim ((pasting.not_related_of_mem_interior a b ha).1 hab)
          · intro hb
            exact False.elim ((pasting.not_related_of_mem_interior b a hb).2 hab)
      | refl a =>
          exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
      | symm a b hab ih =>
          exact ⟨fun hb ↦ (ih.2 hb).symm, fun ha ↦ (ih.1 ha).symm⟩
      | trans a b c hab hbc ihab ihbc =>
          constructor
          · intro ha
            have hab_eq := ihab.1 ha
            subst b
            exact ihbc.1 ha
          · intro hc
            have hbc_eq := ihbc.2 hc
            have hb : (b : EuclideanSpace ℝ (Fin 2)) ∈ poly.interior := by
              rwa [hbc_eq]
            exact (ihab.2 hb).trans hbc_eq
    exact (hrigid hidentified).1 hx
  · intro hxy
    subst y
    exact Relation.EqvGen.refl x

/-- The topological space obtained by pasting equally labelled oriented edges. -/
abbrev Realization (pasting : poly.EdgePasting S) :=
  Quotient pasting.Identified

/-- The canonical map from the polygonal region to its pasted realization. -/
def quotientMap (pasting : poly.EdgePasting S) : poly.region → pasting.Realization :=
  Quotient.mk pasting.Identified

/-- The canonical map to the pasted realization is a quotient map. -/
theorem isQuotientMap_quotientMap (pasting : poly.EdgePasting S) :
    Topology.IsQuotientMap pasting.quotientMap := by
  -- The realization carries the canonical quotient topology.
  exact isQuotientMap_quotient_mk'


end

end EdgePasting

end CyclicPolygon

end
