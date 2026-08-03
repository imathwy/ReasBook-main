module

public import Topology_Munkres_2000.Book.Exercise_35_4.RadialRetraction
public import Topology_Munkres_2000.Book.Theorem_55_6
public import Mathlib.Topology.Separation.Connected

public section

/- Exercise 35.4 (1): A subspace is a retract when its inclusion admits a continuous
left inverse. -/
#check Set.Retraction
#check Set.IsRetract
#check Set.isRetract_iff

namespace Set

universe u

/-- A retract of a Hausdorff space is closed, as shown in Exercise 35.4 (2). -/
theorem isClosed_of_isRetract {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    {Y : Set Z} (hY : IsRetract Y) : IsClosed Y := by
  -- Present the retract by a continuous left inverse to its inclusion.
  rw [isRetract_iff] at hY
  obtain ⟨r, hr⟩ := hY
  -- The retract is exactly the equalizer of the ambient retraction and the identity.
  have hEq : Y = {z | ((r z : Y) : Z) = z} := by
    ext z
    constructor
    · intro hz
      exact congrArg Subtype.val (hr ⟨z, hz⟩)
    · intro hz
      rw [← hz]
      exact (r z).property
  rw [hEq]
  exact isClosed_eq (continuous_subtype_val.comp r.continuous) continuous_id

end Set

namespace EuclideanPlane

/-- A two-point subset of the Euclidean plane is not a retract, as shown in Exercise 35.4 (3). -/
theorem twoPoint_not_isRetract (a b : EuclideanSpace ℝ (Fin 2)) (hab : a ≠ b) :
    ¬ Set.IsRetract ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro h
  -- A retraction makes the two-point subtype a continuous image of the connected plane.
  rw [Set.isRetract_iff] at h
  obtain ⟨r, hr⟩ := h
  letI : Finite ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) :=
    Set.Finite.fintype (Set.Finite.insert a (Set.finite_singleton b)) |>.finite
  haveI : DiscreteTopology ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) := inferInstance
  have hsurj : Function.Surjective r := hr.surjective
  haveI : ConnectedSpace ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) :=
    hsurj.connectedSpace r.continuous
  -- A connected discrete space is a singleton, contradicting the two distinct points.
  have hsub : Subsingleton ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) :=
    PreconnectedSpace.trivial_of_discrete
  have hae : a ∈ ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) := by
    simp
  have hbe : b ∈ ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) := by
    simp
  exact hab (congrArg Subtype.val (hsub.elim ⟨a, hae⟩ ⟨b, hbe⟩))

/- Exercise 35.4 (4): The unit circle is a retract of the punctured Euclidean plane,
via radial projection. -/
#check radialRetraction
#check unitCircle_isRetract

private abbrev unitSphere :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

private abbrev closedUnitDisk :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- Helper for Exercise 35.4: the antipode of a circle-valued map lies in the closed unit disk. -/
private lemma antipodalRetractionMap_mem_closedUnitDisk
    (r : C(EuclideanSpace ℝ (Fin 2), unitSphere)) (x : closedUnitDisk) :
    -(r x : EuclideanSpace ℝ (Fin 2)) ∈ closedUnitDisk := by
  -- Sphere membership gives norm one, hence closed-ball membership after negation.
  rw [Metric.mem_closedBall, dist_zero_right, norm_neg]
  have hsphere := (r x).property
  rw [Metric.mem_sphere, dist_zero_right] at hsphere
  exact hsphere.le

/-- Helper for Exercise 35.4: the underlying antipodal disk self-map. -/
private def antipodalRetractionToFun
    (r : C(EuclideanSpace ℝ (Fin 2), unitSphere)) (x : closedUnitDisk) :
    closedUnitDisk :=
  ⟨-(r x : EuclideanSpace ℝ (Fin 2)), antipodalRetractionMap_mem_closedUnitDisk r x⟩

/-- Helper for Exercise 35.4: the antipodal disk self-map is continuous. -/
private lemma continuous_antipodalRetractionToFun
    (r : C(EuclideanSpace ℝ (Fin 2), unitSphere)) :
    Continuous (antipodalRetractionToFun r) := by
  -- Continuity follows by composing both subtype inclusions with the retraction and negation.
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp (r.continuous.comp continuous_subtype_val)).neg

/-- Helper for Exercise 35.4: the disk self-map obtained by negating a circle retraction. -/
private def antipodalRetractionMap
    (r : C(EuclideanSpace ℝ (Fin 2), unitSphere)) :
    C(closedUnitDisk, closedUnitDisk) :=
  ⟨antipodalRetractionToFun r, continuous_antipodalRetractionToFun r⟩

/-- Helper for Exercise 35.4: the antipodal disk map associated to a retraction
has no fixed point. -/
private lemma antipodalRetractionMap_hasNoFixedPoint
    (r : C(EuclideanSpace ℝ (Fin 2), unitSphere))
    (hr : Function.LeftInverse r Subtype.val) (x : closedUnitDisk) :
    ¬ Function.IsFixedPt (antipodalRetractionMap r) x := by
  intro hfix
  -- A fixed point identifies the disk point with the antipode of its retraction value.
  have hfixAmbient :
      -(r x : EuclideanSpace ℝ (Fin 2)) = (x : EuclideanSpace ℝ (Fin 2)) := by
    exact congrArg Subtype.val hfix
  have hxSphere : (x : EuclideanSpace ℝ (Fin 2)) ∈ unitSphere := by
    rw [Metric.mem_sphere, dist_zero_right]
    calc
      ‖(x : EuclideanSpace ℝ (Fin 2))‖ =
          ‖-(r x : EuclideanSpace ℝ (Fin 2))‖ := congrArg norm hfixAmbient.symm
      _ = ‖(r x : EuclideanSpace ℝ (Fin 2))‖ := norm_neg _
      _ = 1 := by
        have hsphere := (r x).property
        rwa [Metric.mem_sphere, dist_zero_right] at hsphere
  let y : unitSphere := ⟨x, hxSphere⟩
  -- On this boundary point the retraction is the identity, so the point equals its antipode.
  have hrAmbient :
      (r x : EuclideanSpace ℝ (Fin 2)) = (x : EuclideanSpace ℝ (Fin 2)) := by
    exact congrArg Subtype.val (hr y)
  have hneg :
      -(x : EuclideanSpace ℝ (Fin 2)) = (x : EuclideanSpace ℝ (Fin 2)) := by
    calc
      -(x : EuclideanSpace ℝ (Fin 2)) =
          -(r x : EuclideanSpace ℝ (Fin 2)) := congrArg Neg.neg hrAmbient |>.symm
      _ = (x : EuclideanSpace ℝ (Fin 2)) := hfixAmbient
  have htwo : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 2)) = 0 := by
    calc
      (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 2)) =
          (x : EuclideanSpace ℝ (Fin 2)) + x := two_smul ℝ _
      _ = (x : EuclideanSpace ℝ (Fin 2)) + -x :=
        congrArg ((x : EuclideanSpace ℝ (Fin 2)) + ·) hneg.symm
      _ = 0 := add_neg_cancel _
  have htwoNe : (2 : ℝ) ≠ 0 := by
    norm_num
  have hxzero : (x : EuclideanSpace ℝ (Fin 2)) = 0 := by
    exact (smul_eq_zero.mp htwo).resolve_left htwoNe
  have hnorm : ‖(x : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hxSphere
  rw [hxzero, norm_zero] at hnorm
  norm_num at hnorm

/-- Helper for Exercise 35.4: the closed-disk fixed-point property forbids a circle retraction. -/
private lemma unitCircle_not_isRetract_of_closedUnitDisk_fixedPoint
    (hfp : ∀ f : C(closedUnitDisk, closedUnitDisk), ∃ x, Function.IsFixedPt f x) :
    ¬ Set.IsRetract unitSphere := by
  intro h
  -- Apply the fixed-point property to the antipodal map built from the hypothetical retraction.
  rw [Set.isRetract_iff] at h
  obtain ⟨r, hr⟩ := h
  obtain ⟨x, hx⟩ := hfp (antipodalRetractionMap r)
  exact antipodalRetractionMap_hasNoFixedPoint r hr x hx

/-- Exercise 35.4 (5): The unit circle is not a retract of the whole Euclidean plane. -/
theorem unitCircle_not_isRetract :
    ¬ Set.IsRetract (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  -- Route correction: the strengthened target needs the later Brouwer fixed-point theorem.
  apply unitCircle_not_isRetract_of_closedUnitDisk_fixedPoint
  -- The canonical closed-disk theorem supplies the fixed point for every bundled self-map.
  exact ClosedUnitDisk.exists_fixedPoint

end EuclideanPlane
