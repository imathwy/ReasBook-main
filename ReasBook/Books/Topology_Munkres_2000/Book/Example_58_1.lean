module

public import Topology_Munkres_2000.Book.Definition_58_1.DeformationRetraction
public import Topology_Munkres_2000.Book.Definition_9_0_2
public import Topology_Munkres_2000.Book.Example_24_4
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
public import Topology_Munkres_2000.Book.Theorem_58_2
public import Topology_Munkres_2000.Book.Theorem_58_3
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

public section
noncomputable section

open unitInterval

namespace ZAxisComplement

/-- The `z`-axis in Euclidean three-space. -/
def zAxis : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | x 0 = 0 ∧ x 1 = 0}

/-- Euclidean three-space with the `z`-axis removed. -/
def carrier : Set (EuclideanSpace ℝ (Fin 3)) :=
  zAxisᶜ

end ZAxisComplement

/-- Euclidean three-space with the `z`-axis removed. -/
abbrev ZAxisComplement := ZAxisComplement.carrier

namespace ZAxisComplement

/-- The punctured `xy`-plane embedded in the complement of the `z`-axis. -/
def xyPlane : Set ZAxisComplement :=
  {x | (x : EuclideanSpace ℝ (Fin 3)) 2 = 0}

/-- The ambient value of the collapse that multiplies the `z`-coordinate by `1 - t`. -/
def collapseValue (p : unitInterval × ZAxisComplement) : EuclideanSpace ℝ (Fin 3) :=
  (p.2 : EuclideanSpace ℝ (Fin 3)) -
    (p.1 : ℝ) • EuclideanSpace.single 2 ((p.2 : EuclideanSpace ℝ (Fin 3)) 2)

/-- The collapse value remains outside the `z`-axis. -/
theorem collapseValue_mem (p : unitInterval × ZAxisComplement) :
    collapseValue p ∈ carrier := by
  -- A point on the collapsed axis would force the original planar coordinates to vanish.
  rw [carrier, Set.mem_compl_iff]
  intro hp
  apply p.2.property
  simpa [zAxis, collapseValue] using hp

/-- The point-valued collapse of the `z`-axis complement toward its punctured `xy`-plane. -/
def collapsePoint (p : unitInterval × ZAxisComplement) : ZAxisComplement :=
  ⟨collapseValue p, collapseValue_mem p⟩

/-- The point-valued collapse is continuous. -/
theorem continuous_collapsePoint : Continuous collapsePoint := by
  -- Continuity is inherited from subtraction, scalar multiplication, and coordinate evaluation.
  apply Continuous.subtype_mk
  unfold collapseValue
  have hbase : Continuous fun p : unitInterval × ZAxisComplement ↦
      (p.2 : EuclideanSpace ℝ (Fin 3)) :=
    continuous_subtype_val.comp continuous_snd
  have htime : Continuous fun p : unitInterval × ZAxisComplement ↦ (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hcoordinate : Continuous fun p : unitInterval × ZAxisComplement ↦
      (p.2 : EuclideanSpace ℝ (Fin 3)) 2 :=
    (EuclideanSpace.proj 2).continuous.comp hbase
  have hsingle : Continuous fun a : ℝ ↦
      (EuclideanSpace.single 2 a : EuclideanSpace ℝ (Fin 3)) := by
    apply Isometry.continuous
    intro a b
    exact PiLp.edist_single_same 2 (fun _ : Fin 3 ↦ ℝ) 2 a b
  exact hbase.sub (htime.smul (hsingle.comp hcoordinate))

/-- The continuous collapse of the `z`-axis complement toward its punctured `xy`-plane. -/
def collapse : C(unitInterval × ZAxisComplement, ZAxisComplement) :=
  ⟨collapsePoint, continuous_collapsePoint⟩

/-- The collapse has the textbook formula `H(x, y, z, t) = (x, y, (1 - t)z)`. -/
@[simp]
theorem collapse_apply (t : unitInterval) (x : ZAxisComplement) :
    ((collapse (t, x) : ZAxisComplement) : EuclideanSpace ℝ (Fin 3)) =
      (x : EuclideanSpace ℝ (Fin 3)) -
        (t : ℝ) • EuclideanSpace.single 2 ((x : EuclideanSpace ℝ (Fin 3)) 2) := by
  -- The bundled continuous map evaluates to the ambient collapse formula by construction.
  rfl

/-- The endpoint of the collapse lies in the punctured `xy`-plane. -/
theorem collapse_one_mem_xyPlane (x : ZAxisComplement) :
    collapse (1, x) ∈ xyPlane := by
  -- At time one the final coordinate is subtracted from itself.
  rw [xyPlane, Set.mem_setOf_eq, collapse_apply]
  simp

/-- The endpoint projection onto the punctured `xy`-plane. -/
def projection (x : ZAxisComplement) : xyPlane :=
  ⟨collapse (1, x), collapse_one_mem_xyPlane x⟩

/-- The endpoint projection is continuous. -/
theorem continuous_projection : Continuous projection := by
  -- Restrict the continuous collapse to the constant time-one slice.
  apply Continuous.subtype_mk
  exact continuous_collapsePoint.comp (continuous_const.prodMk continuous_id)

/-- The endpoint projection fixes the punctured `xy`-plane. -/
theorem projection_leftInverse : Function.LeftInverse projection Subtype.val := by
  -- The only changed coordinate is already zero on the `xy`-plane.
  intro x
  have hx : ((x : ZAxisComplement) : EuclideanSpace ℝ (Fin 3)) 2 = 0 := x.property
  apply Subtype.ext
  apply Subtype.ext
  simp [projection, collapse_apply, hx]

/-- The endpoint projection as a retraction onto the punctured `xy`-plane. -/
def retraction : Set.Retraction xyPlane where
  toContinuousMap := ⟨projection, continuous_projection⟩
  leftInverse := projection_leftInverse

/-- At time zero, the collapse is the identity. -/
theorem collapse_zero (x : ZAxisComplement) :
    collapse (0, x) = x := by
  -- At time zero the subtracted scalar multiple vanishes.
  apply Subtype.ext
  simp

/-- At time one, the collapse is the ambient endpoint retraction. -/
theorem collapse_one (x : ZAxisComplement) :
    collapse (1, x) = retraction.toAmbient x := by
  -- The stored retraction is precisely the time-one projection.
  rfl

/-- The collapse fixes every point of the punctured `xy`-plane. -/
theorem collapse_fixed (t : unitInterval) {x : ZAxisComplement} (hx : x ∈ xyPlane) :
    collapse (t, x) = x := by
  -- On the target plane the final coordinate is zero, so the correction term vanishes.
  apply Subtype.ext
  rw [collapse_apply]
  apply sub_eq_self.mpr
  rw [show (x : EuclideanSpace ℝ (Fin 3)) 2 = 0 from hx]
  simp

/-- The collapse as a homotopy relative to the punctured `xy`-plane. -/
def homotopyRel : ContinuousMap.HomotopyRel
    (ContinuousMap.id ZAxisComplement) retraction.toAmbient xyPlane where
  toHomotopy :=
    { toContinuousMap := collapse
      map_zero_left := collapse_zero
      map_one_left := collapse_one }
  prop' := collapse_fixed

/-- The punctured `xy`-plane is a deformation retract of Euclidean three-space with the
`z`-axis removed, via the explicit `z`-coordinate collapse. -/
def deformationRetraction : Set.DeformationRetraction xyPlane where
  toRetraction := retraction
  toHomotopyRel := homotopyRel

/-- The retraction underlying the explicit deformation retraction is the endpoint projection. -/
@[simp]
theorem deformationRetraction_toRetraction :
    deformationRetraction.toRetraction = retraction := by
  -- This is the first stored field of the explicit deformation retraction.
  rfl

/-- Helper for Example 58.1: the relative homotopy stored in the explicit deformation
retraction is the coordinate collapse homotopy. -/
private theorem deformationRetraction_toHomotopyRel :
    deformationRetraction.toHomotopyRel = homotopyRel := by
  -- This is the second stored field of the explicit deformation retraction.
  rfl

/-- Helper for Example 58.1: evaluating the relative homotopy evaluates the bundled
coordinate collapse. -/
private theorem homotopyRel_apply (t : unitInterval) (x : ZAxisComplement) :
    homotopyRel (t, x) = collapse (t, x) := by
  -- The underlying continuous map of the relative homotopy is `collapse`.
  rfl

/-- Helper for Example 58.1: evaluating the relative homotopy stored in the explicit
deformation retraction gives the coordinate collapse. -/
private theorem deformationRetraction_toHomotopyRel_apply
    (t : unitInterval) (x : ZAxisComplement) :
    deformationRetraction.toHomotopyRel (t, x) = collapse (t, x) := by
  -- Evaluate the locally defined structure directly, avoiding transport between endpoint maps.
  rfl

/-- Example 58.1 (1): the explicit deformation retraction has the textbook formula
`H(x, y, z, t) = (x, y, (1 - t)z)`. -/
@[simp]
theorem deformationRetraction_apply (t : unitInterval) (x : ZAxisComplement) :
    ((deformationRetraction.apply t x : ZAxisComplement) : EuclideanSpace ℝ (Fin 3)) =
      (x : EuclideanSpace ℝ (Fin 3)) -
        (t : ℝ) • EuclideanSpace.single 2 ((x : EuclideanSpace ℝ (Fin 3)) 2) := by
  -- Route correction: the owner now exposes its thin evaluation wrapper, so reduction records
  -- the bridge to the stored relative homotopy without duplicating a computation theorem.
  have happly :
      deformationRetraction.apply t x = deformationRetraction.toHomotopyRel (t, x) := rfl
  -- Normalize the stored homotopy to the concrete coordinate collapse and its ambient formula.
  rw [happly, deformationRetraction_toHomotopyRel_apply, collapse_apply]

/-- The punctured `xy`-plane is a deformation retract of the `z`-axis complement. -/
theorem xyPlane_isDeformationRetract : Set.IsDeformationRetract xyPlane :=
  (Set.isDeformationRetract_iff xyPlane).2 ⟨retraction, ⟨homotopyRel⟩⟩

/-- Helper for Example 58.1: split three Euclidean coordinates into the planar pair and
the final coordinate. -/
private noncomputable def splitCoordinates :
    EuclideanSpace ℝ (Fin 3) ≃ₜ
      EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).toHomeomorph

/-- Helper for Example 58.1: the planar part of the coordinate splitting retains the first
two coordinates. -/
private theorem splitCoordinates_fst_apply (x : EuclideanSpace ℝ (Fin 3))
    (i : Fin 2) :
    (splitCoordinates x).1 i = x (Fin.castAdd 1 i) := by
  -- The first summand in `finSumFinEquiv` is embedded by `Fin.castAdd`.
  calc
    (splitCoordinates x).1 i = x ((@finSumFinEquiv 2 1) (Sum.inl i)) := by
      simp [splitCoordinates, EuclideanSpace.finAddEquivProd,
        EuclideanSpace.sumEquivProd]
    _ = x (Fin.castAdd 1 i) := by rw [finSumFinEquiv_apply_left]

/-- Helper for Example 58.1: the last part of the coordinate splitting is the third
coordinate. -/
private theorem splitCoordinates_snd_zero (x : EuclideanSpace ℝ (Fin 3)) :
    (splitCoordinates x).2 0 = x 2 := by
  -- The sole coordinate of the second summand is the final coordinate.
  have hlast : Fin.natAdd 2 (0 : Fin 1) = (2 : Fin 3) := rfl
  calc
    (splitCoordinates x).2 0 = x ((@finSumFinEquiv 2 1) (Sum.inr (0 : Fin 1))) := by
      simp [splitCoordinates, EuclideanSpace.finAddEquivProd,
        EuclideanSpace.sumEquivProd]
    _ = x (Fin.natAdd 2 (0 : Fin 1)) := by rw [finSumFinEquiv_apply_right]
    _ = x 2 := by rw [hlast]

/-- Helper for Example 58.1: extract the first two coordinates from a point of the
punctured `xy`-plane. -/
private def planarCoordinate (x : xyPlane) : EuclideanSpace ℝ (Fin 2) :=
  (splitCoordinates (x : EuclideanSpace ℝ (Fin 3))).1

/-- Helper for Example 58.1: the planar coordinates of a point outside the `z`-axis
cannot both vanish. -/
private theorem planarCoordinate_ne_zero (x : xyPlane) : planarCoordinate x ≠ 0 := by
  -- Vanishing planar coordinates are exactly the two equations defining the deleted axis.
  intro hplanar
  apply x.1.property
  refine ⟨?_, ?_⟩
  · have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hplanar
    simpa [planarCoordinate, splitCoordinates_fst_apply] using hzero
  · have hone := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hplanar
    simpa [planarCoordinate, splitCoordinates_fst_apply] using hone

/-- Helper for Example 58.1: planar coordinates define a point of the punctured
Euclidean plane. -/
private def puncturedPlanarCoordinate (x : xyPlane) : PuncturedEuclideanSpace 1 :=
  ⟨planarCoordinate x, planarCoordinate_ne_zero x⟩

/-- Helper for Example 58.1: insert a punctured planar point with zero final coordinate. -/
private noncomputable def puncturedAmbient (y : PuncturedEuclideanSpace 1) :
    EuclideanSpace ℝ (Fin 3) :=
  splitCoordinates.symm (y.1, 0)

/-- Helper for Example 58.1: the inserted planar point has zero final coordinate. -/
private theorem puncturedAmbient_last_zero (y : PuncturedEuclideanSpace 1) :
    puncturedAmbient y 2 = 0 := by
  -- Apply the coordinate splitting to the inserted pair and read its final component.
  rw [← splitCoordinates_snd_zero]
  simp [puncturedAmbient]

/-- Helper for Example 58.1: inserting a nonzero planar point remains outside the
`z`-axis. -/
private theorem puncturedAmbient_mem_carrier (y : PuncturedEuclideanSpace 1) :
    puncturedAmbient y ∈ carrier := by
  -- Axis membership plus the already-zero final coordinate would make the whole point zero.
  rw [carrier, Set.mem_compl_iff]
  intro haxis
  apply y.property
  have hambient : puncturedAmbient y = 0 := by
    ext i
    fin_cases i
    · exact haxis.1
    · exact haxis.2
    · exact puncturedAmbient_last_zero y
  calc
    y.1 = (splitCoordinates (puncturedAmbient y)).1 := by
      simp [puncturedAmbient]
    _ = 0 := by rw [hambient]; simp [splitCoordinates]

/-- Helper for Example 58.1: insertion of a punctured planar point lands in the
punctured `xy`-plane. -/
private theorem puncturedAmbient_mem_xyPlane (y : PuncturedEuclideanSpace 1) :
    (⟨puncturedAmbient y, puncturedAmbient_mem_carrier y⟩ : ZAxisComplement) ∈ xyPlane := by
  -- Membership is precisely the vanishing of the final coordinate.
  exact puncturedAmbient_last_zero y

/-- Helper for Example 58.1: package planar insertion as a point of the punctured
`xy`-plane. -/
private noncomputable def puncturedEmbedding (y : PuncturedEuclideanSpace 1) : xyPlane :=
  ⟨⟨puncturedAmbient y, puncturedAmbient_mem_carrier y⟩,
    puncturedAmbient_mem_xyPlane y⟩

/-- Helper for Example 58.1: extracting coordinates after planar insertion is the
identity. -/
private theorem planarCoordinate_rightInverse :
    Function.RightInverse puncturedEmbedding puncturedPlanarCoordinate := by
  -- The ambient splitting cancels its inverse before taking the first component.
  intro y
  apply Subtype.ext
  exact congrArg Prod.fst (splitCoordinates.apply_symm_apply (y.1, 0))

/-- Helper for Example 58.1: inserting the extracted coordinates of an `xy`-plane point
recovers that point. -/
private theorem planarCoordinate_leftInverse :
    Function.LeftInverse puncturedEmbedding puncturedPlanarCoordinate := by
  -- Compare split coordinates; the planar parts agree and both final parts vanish.
  intro x
  apply Subtype.ext
  apply Subtype.ext
  apply splitCoordinates.injective
  unfold puncturedEmbedding puncturedAmbient puncturedPlanarCoordinate planarCoordinate
  rw [splitCoordinates.apply_symm_apply]
  apply Prod.ext
  · rfl
  · ext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    rw [PiLp.zero_apply, splitCoordinates_snd_zero]
    exact x.property.symm

/-- Helper for Example 58.1: planar coordinate extraction is continuous. -/
private theorem continuous_puncturedPlanarCoordinate :
    Continuous puncturedPlanarCoordinate := by
  -- Compose the ambient coordinate homeomorphism with both subtype inclusions.
  apply Continuous.subtype_mk
  exact continuous_fst.comp
    (splitCoordinates.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val))

/-- Helper for Example 58.1: inserting a punctured planar point is continuous. -/
private theorem continuous_puncturedEmbedding : Continuous puncturedEmbedding := by
  -- Insert a constant zero final coordinate, apply the inverse splitting, and package subtypes.
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact splitCoordinates.symm.continuous.comp
    (continuous_subtype_val.prodMk continuous_const)

/-- Helper for Example 58.1: the punctured `xy`-plane is canonically homeomorphic to the
punctured Euclidean plane. -/
private noncomputable def xyPlaneHomeomorphPuncturedEuclideanPlane :
    xyPlane ≃ₜ PuncturedEuclideanSpace 1 :=
  { toFun := puncturedPlanarCoordinate
    invFun := puncturedEmbedding
    left_inv := planarCoordinate_leftInverse
    right_inv := planarCoordinate_rightInverse
    continuous_toFun := continuous_puncturedPlanarCoordinate
    continuous_invFun := continuous_puncturedEmbedding }

/-- Helper for Example 58.1: the canonical Euclidean-plane coordinates preserve the
unit-sphere predicate. -/
private theorem euclideanPlaneComplex_mem_unitSphere_iff
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ Metric.sphere (0 : ℂ) 1 := by
  -- Both sphere predicates reduce to the norm-one equation preserved by the isometry.
  simp only [Metric.mem_sphere, dist_zero_right]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm ▸ Iff.rfl

/-- Helper for Example 58.1: the standard one-sphere is canonically homeomorphic to the
complex unit circle. -/
private noncomputable def standardSphereOneHomeomorphCircle :
    StandardSphere 1 ≃ₜ Circle :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    euclideanPlaneComplex_mem_unitSphere_iff

/-- Helper for Example 58.1: the punctured Euclidean plane is path connected. -/
private theorem isPathConnected_puncturedEuclideanPlane :
    IsPathConnected {x : EuclideanSpace ℝ (Fin 2) | x ≠ 0} := by
  -- Rewrite the nonzero predicate as the complement of the origin and apply Example 24.4.
  have hset : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) =
      {x : EuclideanSpace ℝ (Fin 2) | x ≠ 0} := by
    ext x
    simp
  rw [← hset]
  exact isPathConnected_puncturedEuclideanSpace 2 (by omega)

/-- Helper for Example 58.1: the punctured Euclidean plane has infinite-cyclic
fundamental group at every basepoint. -/
private theorem fundamentalGroup_puncturedEuclideanPlane_equiv_int
    (q : PuncturedEuclideanSpace 1) :
    Nonempty (FundamentalGroup (PuncturedEuclideanSpace 1) q ≃*
      Multiplicative ℤ) := by
  -- Path connectedness permits arbitrary basepoints in the punctured plane.
  letI : PathConnectedSpace (PuncturedEuclideanSpace 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      isPathConnected_puncturedEuclideanPlane
  -- Choose one sphere point to invoke the radial deformation computation of Theorem 58.2.
  obtain ⟨b : StandardSphere 1⟩ :=
    NormedSpace.sphere_nonempty_rclike ℝ (E := EuclideanSpace ℝ (Fin 2)) zero_le_one
  let sphereToPuncturedOpposite := MulEquiv.ofBijective
    (((StandardSphere.toPunctured 1)₍b₎)₊)
    (StandardSphere.fundamentalGroupMap_bijective 1 b)
  let sphereToPunctured := MulEquiv.unop sphereToPuncturedOpposite
  -- Compose basepoint change, radial retraction, sphere-circle coordinates, and winding number.
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected q
      (StandardSphere.toPunctured 1 b)).trans
    (sphereToPunctured.symm.trans
      ((standardSphereOneHomeomorphCircle.fundamentalGroupMulEquiv b).trans
        ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
          (standardSphereOneHomeomorphCircle b) 1).trans
            Circle.fundamentalGroupEquivInt)))⟩

/-- Example 58.1 (2): the complement of the `z`-axis in Euclidean three-space has infinite
cyclic fundamental group. -/
theorem fundamentalGroup_equiv_int (p : ZAxisComplement) :
    Nonempty (FundamentalGroup ZAxisComplement p ≃* Multiplicative ℤ) := by
  -- Move the arbitrary ambient basepoint along the collapse to its endpoint in the plane.
  let q : xyPlane := projection p
  have collapsePath : Path p (q : ZAxisComplement) := by
    exact homotopyRel.toHomotopy.evalAt p
  -- Theorem 58.3 identifies the retract and ambient groups in the left-to-right convention.
  let inclusionOpposite := MulEquiv.ofBijective
    (((⟨Subtype.val, continuous_subtype_val⟩ :
      C(xyPlane, ZAxisComplement))₍q₎)₊)
    (xyPlane_isDeformationRetract.fundamentalGroupMap_bijective q)
  let inclusion := MulEquiv.unop inclusionOpposite
  -- Reverse inclusion, pass to standard planar coordinates, and use the punctured-plane result.
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPath collapsePath).trans
    (inclusion.symm.trans
      ((xyPlaneHomeomorphPuncturedEuclideanPlane.fundamentalGroupMulEquiv q).trans
        (fundamentalGroup_puncturedEuclideanPlane_equiv_int
          (xyPlaneHomeomorphPuncturedEuclideanPlane q)).some))⟩

end ZAxisComplement
