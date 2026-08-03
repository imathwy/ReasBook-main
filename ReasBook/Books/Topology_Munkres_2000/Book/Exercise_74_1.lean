module

public import Topology_Munkres_2000.Book.Example_74_8.Surface
public import Topology_Munkres_2000.Book.Theorem_74_2
import all Topology_Munkres_2000.Book.Definition_74_1.CyclicPolygon
import all Topology_Munkres_2000.Book.Definition_74_3
import all Topology_Munkres_2000.Book.Theorem_74_2.Presentation
import all Topology_Munkres_2000.Book.Example_74_8.Surface

public section

namespace ProjectivePlaneTorus

/-- The group presented by the edge labels and boundary relator of the hexagonal pasting. -/
abbrev Presentation : Type :=
  PresentedGroup ({pasting.relator} : Set (FreeGroup pasting.UsedLabel))

/-- The generator `a` represented by the first edge label of the hexagonal pasting. -/
def a : Presentation :=
  PresentedGroup.of ⟨0, ⟨0, pasting_label_zero⟩⟩

/-- The generator `b` represented by the third edge label of the hexagonal pasting. -/
def b : Presentation :=
  PresentedGroup.of ⟨1, ⟨2, pasting_label_two⟩⟩

/-- The generator `c` represented by the fourth edge label of the hexagonal pasting. -/
def c : Presentation :=
  PresentedGroup.of ⟨2, ⟨3, pasting_label_three⟩⟩

/-- Helper for Exercise 74.1: the hexagonal boundary relator is the word
`a² * b * c * b⁻¹ * c⁻¹` on the underlying free generators. -/
private lemma relator_eq_generatorWord :
    pasting.relator =
      FreeGroup.of ⟨0, ⟨0, pasting_label_zero⟩⟩ ^ 2 *
        FreeGroup.of ⟨1, ⟨2, pasting_label_two⟩⟩ *
        FreeGroup.of ⟨2, ⟨3, pasting_label_three⟩⟩ *
        (FreeGroup.of ⟨1, ⟨2, pasting_label_two⟩⟩)⁻¹ *
        (FreeGroup.of ⟨2, ⟨3, pasting_label_three⟩⟩)⁻¹ := by
  have mk_generatorWord (x y z : pasting.UsedLabel) :
      FreeGroup.mk [(x, true), (x, true), (y, true), (z, true), (y, false), (z, false)] =
        FreeGroup.of x ^ 2 * FreeGroup.of y * FreeGroup.of z *
          (FreeGroup.of y)⁻¹ * (FreeGroup.of z)⁻¹ := by
    rw [pow_two]
    rfl
  -- Expand the signed six-edge boundary once and normalize the resulting free word.
  simpa [CyclicPolygon.EdgePasting.relator, CyclicPolygon.EdgePasting.boundaryWord,
    pasting, CyclicPolygon.EdgePasting.ofSigns] using
    mk_generatorWord ⟨0, ⟨0, pasting_label_zero⟩⟩ ⟨1, ⟨2, pasting_label_two⟩⟩
      ⟨2, ⟨3, pasting_label_three⟩⟩

/-- Helper for Exercise 74.1: equally labelled oriented edges pair points with the same
affine parameter. -/
private lemma related_orientedPoint_of_label_eq {n : ℕ} {poly : CyclicPolygon n}
    {S : Type*}
    (q : poly.EdgePasting S) (i j : Fin n) (t : Set.Icc (0 : ℝ) 1)
    (hlabel : q.label i = q.label j) :
    q.Related (q.orientedPoint i t) (q.orientedPoint j t) := by
  -- Use the common affine parameter as the witness in the direct edge pairing.
  rw [q.related_iff]
  refine ⟨i, j, hlabel, (q.orientation i).point t, q.orientedPoint_apply i t, ?_⟩
  rw [q.positiveIdentification_point]
  exact q.orientedPoint_apply j t

/-- Helper for Exercise 74.1: quotienting identifies equally labelled oriented-edge
points with a common affine parameter. -/
private lemma quotientMap_orientedPoint_eq_of_label_eq {n : ℕ} {poly : CyclicPolygon n}
    {S : Type*} (q : poly.EdgePasting S) (i j : Fin n) (t : Set.Icc (0 : ℝ) 1)
    (hlabel : q.label i = q.label j) :
    q.quotientMap (q.orientedPoint i t) = q.quotientMap (q.orientedPoint j t) := by
  -- Lift the direct pairing to the equivalence relation defining the quotient.
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ (related_orientedPoint_of_label_eq q i j t hlabel))

/-- Helper for Exercise 74.1: parameter zero on an oriented pasted edge is its signed
initial vertex. -/
private lemma orientedPoint_zero {n : ℕ} {poly : CyclicPolygon n} {S : Type*}
    (q : poly.EdgePasting S) (i : Fin n) :
    q.orientedPoint i 0 = poly.vertexPoint (if q.sign i then i else finRotate n i) := by
  -- Reduce the affine parameter to the initial endpoint, then inspect its sign.
  apply Subtype.ext
  have hzero : ((0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 := rfl
  rw [q.orientedPoint_apply, q.includePoint_coe, OrientedSegment.point_coe, hzero,
    AffineMap.lineMap_apply_zero, q.orientation_eq]
  cases hsign : q.sign i
  · simp only [Bool.false_eq_true, if_false, CyclicPolygon.signedOrientation,
      OrientedSegment.reverse_initial, CyclicPolygon.cyclicOrientation,
      CyclicPolygon.vertexPoint]
  · simp only [if_true, CyclicPolygon.signedOrientation,
      CyclicPolygon.cyclicOrientation, CyclicPolygon.vertexPoint]

/-- Helper for Exercise 74.1: parameter one on an oriented pasted edge is its signed
final vertex. -/
private lemma orientedPoint_one {n : ℕ} {poly : CyclicPolygon n} {S : Type*}
    (q : poly.EdgePasting S) (i : Fin n) :
    q.orientedPoint i 1 = poly.vertexPoint (if q.sign i then finRotate n i else i) := by
  -- Reduce the affine parameter to the final endpoint, then inspect its sign.
  apply Subtype.ext
  have hone : ((1 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 := rfl
  rw [q.orientedPoint_apply, q.includePoint_coe, OrientedSegment.point_coe, hone,
    AffineMap.lineMap_apply_one, q.orientation_eq]
  cases hsign : q.sign i
  · simp only [Bool.false_eq_true, if_false, CyclicPolygon.signedOrientation,
      OrientedSegment.reverse_final, CyclicPolygon.cyclicOrientation,
      CyclicPolygon.vertexPoint]
  · simp only [if_true, CyclicPolygon.signedOrientation,
      CyclicPolygon.cyclicOrientation, CyclicPolygon.vertexPoint]

/-- The canonical generators satisfy the defining relation of the presentation. -/
theorem relation : a ^ 2 * b * c * b⁻¹ * c⁻¹ = 1 := by
  -- The singleton defining set kills the canonical boundary relator.
  have hrelator :
      PresentedGroup.mk ({pasting.relator} : Set (FreeGroup pasting.UsedLabel))
        pasting.relator = 1 :=
    PresentedGroup.one_of_mem (Set.mem_singleton pasting.relator)
  -- Rewrite through the boundary-word interface and map its factors to the named generators.
  simpa [a, b, c, PresentedGroup.of, relator_eq_generatorWord] using hrelator

/-- Every vertex of the hexagon has image `basepoint` in the edge-pasting realization. -/
theorem quotientMap_vertexPoint (i : Fin 6) :
    quotientMap (hexagon.vertexPoint i) = basepoint := by
  -- Record the three concrete equal-label edge pairs.
  have hlabel01 : pasting.label 0 = pasting.label 1 := by
    rfl
  have hlabel24 : pasting.label 2 = pasting.label 4 := by
    rfl
  have hlabel35 : pasting.label 3 = pasting.label 5 := by
    rfl
  -- Their endpoints give a connected graph on all six quotient vertices.
  have h01raw := quotientMap_orientedPoint_eq_of_label_eq pasting 0 1 0 hlabel01
  have h12raw := quotientMap_orientedPoint_eq_of_label_eq pasting 0 1 1 hlabel01
  have h25raw := quotientMap_orientedPoint_eq_of_label_eq pasting 2 4 0 hlabel24
  have h34raw := quotientMap_orientedPoint_eq_of_label_eq pasting 2 4 1 hlabel24
  have h30raw := quotientMap_orientedPoint_eq_of_label_eq pasting 3 5 0 hlabel35
  have h01 : quotientMap (hexagon.vertexPoint 0) =
      quotientMap (hexagon.vertexPoint 1) := by
    simpa [orientedPoint_zero, Surface, quotientMap, pasting,
      CyclicPolygon.EdgePasting.ofSigns, finRotate_apply] using h01raw
  have h12 : quotientMap (hexagon.vertexPoint 1) =
      quotientMap (hexagon.vertexPoint 2) := by
    simpa [orientedPoint_one, Surface, quotientMap, pasting,
      CyclicPolygon.EdgePasting.ofSigns, finRotate_apply] using h12raw
  have h25 : quotientMap (hexagon.vertexPoint 2) =
      quotientMap (hexagon.vertexPoint 5) := by
    simpa [orientedPoint_zero, Surface, quotientMap, pasting,
      CyclicPolygon.EdgePasting.ofSigns, finRotate_apply] using h25raw
  have h34 : quotientMap (hexagon.vertexPoint 3) =
      quotientMap (hexagon.vertexPoint 4) := by
    simpa [orientedPoint_one, Surface, quotientMap, pasting,
      CyclicPolygon.EdgePasting.ofSigns, finRotate_apply] using h34raw
  have h30 : quotientMap (hexagon.vertexPoint 3) =
      quotientMap (hexagon.vertexPoint 0) := by
    simpa [orientedPoint_zero, Surface, quotientMap, pasting,
      CyclicPolygon.EdgePasting.ofSigns, finRotate_apply] using h30raw
  -- Enumerate the vertices and follow the corresponding path back to vertex zero.
  fin_cases i
  · rfl
  · exact h01.symm
  · exact h12.symm.trans h01.symm
  · exact h30
  · exact h34.symm.trans h30
  · exact h25.symm.trans (h12.symm.trans h01.symm)

/-- Exercise 74.1. The fundamental group of `P² # T` has presentation
`⟨a, b, c | a² * b * c * b⁻¹ * c⁻¹ = 1⟩`. -/
theorem fundamentalGroupMulEquiv :
    Nonempty (FundamentalGroup Surface basepoint ≃* Presentation) :=
  CyclicPolygon.EdgePasting.fundamentalGroupMulEquiv pasting basepoint quotientMap_vertexPoint


end ProjectivePlaneTorus
