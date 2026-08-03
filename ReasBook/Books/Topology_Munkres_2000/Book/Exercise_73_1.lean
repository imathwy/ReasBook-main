module

public import Topology_Munkres_2000.Book.Definition_73_1.DunceCap
public import Topology_Munkres_2000.Book.Definition_58_1.DeformationRetraction
public import Topology_Munkres_2000.Book.Exercise_71_2
public import Topology_Munkres_2000.Book.Lemma_71_4
public import Topology_Munkres_2000.Book.Theorem_22_1
public import Topology_Munkres_2000.Book.Theorem_68_4
public import Topology_Munkres_2000.Book.Theorem_73_4
public import Topology_Munkres_2000.Book.Exercise_73_1.Wedge
public import Topology_Munkres_2000.Book.Exercise_54_7.Product
public import Topology_Munkres_2000.Book.Corollary_52_5
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.CoprodI
import all Topology_Munkres_2000.Book.Definition_73_1.DunceCap
import all Topology_Munkres_2000.Book.Exercise_59_1.PointedWedge
import all Topology_Munkres_2000.Book.Lemma_71_4
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
import all Topology_Munkres_2000.Book.Proposition_58_2.HomotopyEquiv

public section

universe u

/-- Helper for Exercise 73.1: the constant map to a chosen point is the endpoint
map of the singleton retraction. -/
private def exercise731SingletonRetractionMap
    {X : Type u} [TopologicalSpace X] (x : X) : C(X, ({x} : Set X)) :=
  ContinuousMap.const X ⟨x, Set.mem_singleton x⟩

/-- Helper for Exercise 73.1: the constant singleton map is a left inverse to
the singleton inclusion. -/
private lemma exercise731SingletonRetractionMap_leftInverse
    {X : Type u} [TopologicalSpace X] (x : X) :
    Function.LeftInverse (exercise731SingletonRetractionMap x) Subtype.val := by
  -- Every point of the singleton has underlying value `x`.
  intro y
  apply Subtype.ext
  exact (Set.mem_singleton_iff.mp y.property).symm

/-- Helper for Exercise 73.1: the canonical retraction onto a singleton. -/
private def exercise731SingletonRetraction
    {X : Type u} [TopologicalSpace X] (x : X) : Set.Retraction ({x} : Set X) :=
  Set.Retraction.ofContinuousMap (exercise731SingletonRetractionMap x)
    (exercise731SingletonRetractionMap_leftInverse x)

/-- Helper for Exercise 73.1: affine interpolation in homeomorphic normed-space
coordinates contracts a space to a chosen point. -/
private def exercise731NormedSpaceContraction
    {X : Type u} {E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x : X) : unitInterval × X → X :=
  fun z ↦ e.symm (((1 - (z.1 : ℝ)) • e z.2) + ((z.1 : ℝ) • e x))

/-- Helper for Exercise 73.1: affine contraction in normed-space coordinates is
continuous. -/
private lemma continuous_exercise731NormedSpaceContraction
    {X : Type u} {E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x : X) : Continuous (exercise731NormedSpaceContraction e x) := by
  -- Continuity follows from the coordinate homeomorphism and continuous affine operations.
  unfold exercise731NormedSpaceContraction
  fun_prop

/-- Helper for Exercise 73.1: affine contraction starts at the identity. -/
private lemma exercise731NormedSpaceContraction_zero
    {X : Type u} {E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x y : X) :
    exercise731NormedSpaceContraction e x (0, y) = ContinuousMap.id X y := by
  -- At time zero the affine expression is the original point.
  simp [exercise731NormedSpaceContraction]

/-- Helper for Exercise 73.1: affine contraction ends at the singleton
retraction. -/
private lemma exercise731NormedSpaceContraction_one
    {X : Type u} {E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x y : X) :
    exercise731NormedSpaceContraction e x (1, y) =
      (exercise731SingletonRetraction x).toAmbient y := by
  -- At time one the affine expression is the chosen center.
  unfold exercise731NormedSpaceContraction exercise731SingletonRetraction
    Set.Retraction.toAmbient exercise731SingletonRetractionMap
    Set.Retraction.ofContinuousMap
  simp

/-- Helper for Exercise 73.1: affine contraction fixes its center throughout. -/
private lemma exercise731NormedSpaceContraction_fixed
    {X : Type u} {E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x : X) (t : unitInterval) {y : X}
    (hy : y ∈ ({x} : Set X)) :
    exercise731NormedSpaceContraction e x (t, y) = ContinuousMap.id X y := by
  -- Substitute the center and combine the complementary scalar coefficients.
  rw [Set.mem_singleton_iff.mp hy]
  simp only [exercise731NormedSpaceContraction, ContinuousMap.id_apply]
  rw [← add_smul]
  simp

/-- Helper for Exercise 73.1: affine contraction supplies the relative homotopy
from the identity to the singleton retraction. -/
private def exercise731NormedSpaceSingletonHomotopy
    {X : Type u} {E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x : X) :
    ContinuousMap.HomotopyRel (ContinuousMap.id X)
      (exercise731SingletonRetraction x).toAmbient {x} where
  toFun := exercise731NormedSpaceContraction e x
  continuous_toFun := continuous_exercise731NormedSpaceContraction e x
  map_zero_left := exercise731NormedSpaceContraction_zero e x
  map_one_left := exercise731NormedSpaceContraction_one e x
  prop' := exercise731NormedSpaceContraction_fixed e x

/-- Helper for Exercise 73.1: a point in a space homeomorphic to a real normed
space is a deformation retract. -/
private lemma exercise731IsDeformationRetract_singleton_of_homeomorph_normedSpace
    {X : Type u} {E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x : X) : Set.IsDeformationRetract ({x} : Set X) := by
  -- Package the singleton retraction with the affine relative homotopy.
  rw [Set.isDeformationRetract_iff]
  refine ⟨exercise731SingletonRetraction x, ?_⟩
  exact ⟨exercise731NormedSpaceSingletonHomotopy e x⟩

namespace DunceCap

/-- Helper for Exercise 73.1: the fundamental group of a dunce cap at its center is
the corresponding finite cyclic group. -/
lemma fundamentalGroupMulEquivZModAtBasepoint (n : ℕ) (hn : 1 < n) :
    Nonempty
      (FundamentalGroup (Space n) (basepoint n) ≃*
        Multiplicative (ZMod n)) := by
  -- Transport the cyclic computation from its boundary basepoint through path connectedness.
  letI : PathConnectedSpace Disk :=
    isPathConnected_iff_pathConnectedSpace.mp
      (Metric.isPathConnected_closedBall (zero_le_one : (0 : ℝ) ≤ 1))
  letI : PathConnectedSpace (Space n) :=
    (quotientMap_isQuotientMap n).surjective.pathConnectedSpace
      (quotientMap_isQuotientMap n).continuous
  obtain ⟨equiv⟩ := fundamentalGroupMulEquivZMod n hn
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
    (basepoint n) (quotientMap n (boundary (1 : Circle)))).trans equiv⟩

/-- Helper for Exercise 73.1: a family of dunce caps has a simultaneous family
of cyclic fundamental-group coordinates at the canonical basepoints. -/
lemma piFundamentalGroupMulEquivZModAtBasepoint {I : Type*} (n : I → ℕ)
    (hn : ∀ i, 1 < n i) :
    Nonempty
      (∀ i, FundamentalGroup (Space (n i)) (basepoint (n i)) ≃*
        Multiplicative (ZMod (n i))) := by
  -- Choose the already established cyclic coordinate independently in each factor.
  classical
  exact Classical.nonempty_pi.mpr
    (fun i ↦ fundamentalGroupMulEquivZModAtBasepoint (n i) (hn i))

/-- Helper for Exercise 73.1: two dunce-cap fundamental groups have the product
of their cyclic coordinates. -/
lemma prodFundamentalGroupMulEquivZModAtBasepoint (n m : ℕ)
    (hn : 1 < n) (hm : 1 < m) :
    Nonempty
      ((FundamentalGroup (Space n) (basepoint n) ×
          FundamentalGroup (Space m) (basepoint m)) ≃*
        Multiplicative (ZMod n × ZMod m)) := by
  -- Identify the two factors, then combine their multiplicative wrappers.
  obtain ⟨equivN⟩ := fundamentalGroupMulEquivZModAtBasepoint n hn
  obtain ⟨equivM⟩ := fundamentalGroupMulEquivZModAtBasepoint m hm
  exact ⟨(equivN.prodCongr equivM).trans
    (MulEquiv.prodMultiplicative _ _).symm⟩

/-- Helper for Exercise 73.1: the fundamental group of an ULifted dunce cap at
its lifted center is the corresponding finite cyclic group. -/
lemma uliftFundamentalGroupMulEquivZModAtBasepoint (n : ℕ) (hn : 1 < n) :
    Nonempty
      (FundamentalGroup (ULift (Space n)) (ULift.up (basepoint n)) ≃*
        Multiplicative (ZMod n)) := by
  -- Transport the source group through the canonical ULift homeomorphism.
  obtain ⟨equiv⟩ := fundamentalGroupMulEquivZModAtBasepoint n hn
  exact ⟨(Homeomorph.ulift.fundamentalGroupMulEquiv
    (ULift.up (basepoint n))).trans equiv⟩

/-- Helper for Exercise 73.1: the two lifted factors of a pointed wedge admit
their corresponding cyclic fundamental-group coordinates simultaneously. -/
lemma pointedWedgeFactorPairMulEquivZModAtBasepoint (n m : ℕ)
    (hn : 1 < n) (hm : 1 < m) :
    Nonempty
      ((FundamentalGroup
          (Topology.PointedWedge.Family (Space n) (Space m) false)
          (Topology.PointedWedge.points (basepoint n) (basepoint m) false) ≃*
        Multiplicative (ZMod n)) ×
      (FundamentalGroup
          (Topology.PointedWedge.Family (Space n) (Space m) true)
          (Topology.PointedWedge.points (basepoint n) (basepoint m) true) ≃*
        Multiplicative (ZMod m))) := by
  -- Route correction: package the existing ULift coordinate route as a
  -- concrete pair, avoiding typeclass search on an abstract Boolean match.
  obtain ⟨leftEquiv⟩ := uliftFundamentalGroupMulEquivZModAtBasepoint n hn
  obtain ⟨rightEquiv⟩ := uliftFundamentalGroupMulEquivZModAtBasepoint m hm
  exact ⟨(leftEquiv, rightEquiv)⟩

/-- Helper for Exercise 73.1: the open part of the closed disk consists of the
points of norm strictly less than one. -/
def interiorDisk : Set Disk :=
  {z | ‖(z : ℂ)‖ < 1}

/-- Helper for Exercise 73.1: the center belongs to the open part of the disk. -/
lemma zero_mem_interiorDisk : (0 : Disk) ∈ interiorDisk := by
  -- The center has norm zero.
  simp [interiorDisk]

/-- Helper for Exercise 73.1: disk-interior membership is membership in the
ambient complex open unit ball. -/
lemma mem_interiorDisk_iff_mem_ball (z : Disk) :
    z ∈ interiorDisk ↔ (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
  -- Both predicates say that the ambient complex norm is strictly below one.
  rw [interiorDisk, Metric.mem_ball, dist_zero_right]
  simp only [Set.mem_setOf_eq]

/-- Helper for Exercise 73.1: the open part of the closed disk is open in the
subspace topology. -/
lemma isOpen_interiorDisk : IsOpen interiorDisk := by
  -- Pull the complex open unit ball back along the disk inclusion.
  have hpreimage :
      ((↑) : Disk → ℂ) ⁻¹' Metric.ball (0 : ℂ) 1 = interiorDisk := by
    ext z
    exact (mem_interiorDisk_iff_mem_ball z).symm
  rw [← hpreimage]
  exact Metric.isOpen_ball.preimage
    (continuous_subtype_val : Continuous ((↑) : Disk → ℂ))

/-- Helper for Exercise 73.1: an identified interior disk point has no distinct
representative. -/
lemma identified_eq_of_mem_interiorDisk (n : ℕ) {x y : Disk}
    (hxy : Identified n x y) (hx : x ∈ interiorDisk) : x = y := by
  -- Bound the generated relation by the setoid that only collapses boundary points.
  have boundaryEquivalence :
      Equivalence (fun u v : Disk ↦
        u = v ∨ (‖(u : ℂ)‖ = 1 ∧ ‖(v : ℂ)‖ = 1)) := by
    constructor
    · intro u
      exact Or.inl rfl
    · intro u v huv
      rcases huv with huv | ⟨hu, hv⟩
      · exact Or.inl huv.symm
      · exact Or.inr ⟨hv, hu⟩
    · intro u v w huv hvw
      rcases huv with huv | ⟨hu, hv⟩
      · simpa [huv] using hvw
      · rcases hvw with hvw | ⟨_, hw⟩
        · exact Or.inr ⟨hu, hvw ▸ hv⟩
        · exact Or.inr ⟨hu, hw⟩
  let boundarySetoid : Setoid Disk :=
    { r := fun u v ↦ u = v ∨ (‖(u : ℂ)‖ = 1 ∧ ‖(v : ℂ)‖ = 1)
      iseqv := boundaryEquivalence }
  have identifiedLe : Identified n ≤ boundarySetoid := by
    apply (identified_le_iff_boundary_rotations n boundarySetoid).2
    intro z k
    exact Or.inr ⟨Circle.norm_coe z, Circle.norm_coe ((rotation n ^ (k : ℕ)) z)⟩
  rcases identifiedLe hxy with hxy | ⟨hxBoundary, _⟩
  · exact hxy
  · rw [interiorDisk] at hx
    exact (ne_of_lt hx hxBoundary).elim

/-- Helper for Exercise 73.1: the open disk is saturated under the dunce-cap
quotient map. -/
lemma interiorDisk_isSaturated (n : ℕ) :
    Set.IsSaturated (quotientMap n) interiorDisk := by
  -- Equality of quotient images forces equality when one representative is interior.
  rw [Set.isSaturated_iff_mem_of_eq]
  intro x y hx hy
  have hxy : x = y := identified_eq_of_mem_interiorDisk n
    ((quotientMap_eq_iff n x y).1 hy.symm) hx
  exact hxy ▸ hx

/-- Helper for Exercise 73.1: the canonical open neighborhood of the dunce-cap
basepoint is the image of the open disk. -/
def basepointNeighborhood (n : ℕ) : Set (Space n) :=
  Set.range (interiorDisk.restrict (quotientMap n))

/-- Helper for Exercise 73.1: the inverse image of the canonical basepoint
neighborhood is exactly the open disk. -/
lemma preimage_basepointNeighborhood (n : ℕ) :
    quotientMap n ⁻¹' basepointNeighborhood n = interiorDisk := by
  -- The range of the restricted map is the image of the saturated open disk.
  rw [basepointNeighborhood, Set.range_restrict]
  exact Set.isSaturated_iff_preimage_image.mp (interiorDisk_isSaturated n)

/-- Helper for Exercise 73.1: the canonical basepoint neighborhood is open. -/
lemma isOpen_basepointNeighborhood (n : ℕ) :
    IsOpen (basepointNeighborhood n) := by
  -- Reflect openness through the quotient map using the saturated preimage formula.
  rw [← (quotientMap_isQuotientMap n).isOpen_preimage,
    preimage_basepointNeighborhood]
  exact isOpen_interiorDisk

/-- Helper for Exercise 73.1: the dunce-cap center belongs to its canonical open
neighborhood. -/
lemma basepoint_mem_basepointNeighborhood (n : ℕ) :
    basepoint n ∈ basepointNeighborhood n := by
  -- The zero representative supplies the required restricted-map witness.
  exact ⟨⟨0, zero_mem_interiorDisk⟩, rfl⟩

/-- Helper for Exercise 73.1: forgetting the closed-disk membership sends the
open disk into the complex open unit ball. -/
def interiorDiskToBall : interiorDisk → Metric.ball (0 : ℂ) 1 :=
  fun z ↦ ⟨z.1.1, (mem_interiorDisk_iff_mem_ball z.1).mp z.2⟩

/-- Helper for Exercise 73.1: a complex point in the open unit ball determines
a point of the open part of the closed disk. -/
def ballToInteriorDisk : Metric.ball (0 : ℂ) 1 → interiorDisk :=
  fun z ↦
    ⟨⟨z.1, Metric.ball_subset_closedBall z.2⟩,
      (mem_interiorDisk_iff_mem_ball
        ⟨z.1, Metric.ball_subset_closedBall z.2⟩).mpr z.2⟩

/-- Helper for Exercise 73.1: passing from the open disk to the complex ball and
back is the identity. -/
lemma ballToInteriorDisk_leftInverse :
    Function.LeftInverse ballToInteriorDisk interiorDiskToBall := by
  -- Both maps preserve the underlying complex number.
  intro z
  exact Subtype.ext (Subtype.ext rfl)

/-- Helper for Exercise 73.1: passing from the complex ball to the open disk and
back is the identity. -/
lemma ballToInteriorDisk_rightInverse :
    Function.RightInverse ballToInteriorDisk interiorDiskToBall := by
  -- Both maps preserve the underlying complex number.
  intro z
  exact Subtype.ext rfl

/-- Helper for Exercise 73.1: the map from the open disk to the complex ball is
continuous. -/
lemma continuous_interiorDiskToBall : Continuous interiorDiskToBall := by
  -- Continuity is inherited from the two subtype inclusions.
  exact Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val)
    (fun z ↦ (mem_interiorDisk_iff_mem_ball z.1).mp z.2)

/-- Helper for Exercise 73.1: the map from the complex ball to the open disk is
continuous. -/
lemma continuous_ballToInteriorDisk : Continuous ballToInteriorDisk := by
  -- Continuity is inherited from the nested subtype inclusions.
  exact Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val
      (fun z ↦ Metric.ball_subset_closedBall z.2))
    (fun z ↦
      (mem_interiorDisk_iff_mem_ball
        ⟨z.1, Metric.ball_subset_closedBall z.2⟩).mpr z.2)

/-- Helper for Exercise 73.1: the open part of the closed disk is homeomorphic
to the complex open unit ball. -/
def interiorDiskHomeomorphBall : interiorDisk ≃ₜ Metric.ball (0 : ℂ) 1 where
  toFun := interiorDiskToBall
  invFun := ballToInteriorDisk
  left_inv := ballToInteriorDisk_leftInverse
  right_inv := ballToInteriorDisk_rightInverse
  continuous_toFun := continuous_interiorDiskToBall
  continuous_invFun := continuous_ballToInteriorDisk

/-- Helper for Exercise 73.1: the open part of the closed disk is homeomorphic
to the complex plane. -/
noncomputable def interiorDiskHomeomorphComplex : interiorDisk ≃ₜ ℂ :=
  interiorDiskHomeomorphBall.trans Homeomorph.unitBall.symm

/-- Helper for Exercise 73.1: the restricted quotient map is injective on the
open disk after corestriction to its image. -/
lemma basepointNeighborhoodRangeFactorization_injective (n : ℕ) :
    Function.Injective
      (Set.rangeFactorization (interiorDisk.restrict (quotientMap n))) := by
  -- Equality in the quotient reduces to equality of the interior representatives.
  intro x y hxy
  apply Subtype.ext
  apply identified_eq_of_mem_interiorDisk n
  · apply (quotientMap_eq_iff n x y).1
    exact congrArg Subtype.val hxy
  · exact x.2

/-- Helper for Exercise 73.1: the restricted quotient identifies the open disk
homeomorphically with the canonical basepoint neighborhood. -/
lemma basepointNeighborhoodRangeFactorization_isHomeomorph (n : ℕ) :
    IsHomeomorph
      (Set.rangeFactorization (interiorDisk.restrict (quotientMap n))) := by
  -- Saturated open restriction makes the range factorization a quotient map;
  -- interior uniqueness supplies injectivity.
  rw [isHomeomorph_iff_isQuotientMap_injective]
  exact ⟨(quotientMap_isQuotientMap n).restrictImage_of_isOpen_or_isClosed
      (interiorDisk_isSaturated n) (Or.inl isOpen_interiorDisk),
    basepointNeighborhoodRangeFactorization_injective n⟩

/-- Helper for Exercise 73.1: the canonical basepoint neighborhood is
homeomorphic to the complex plane. -/
noncomputable def basepointNeighborhoodHomeomorphComplex (n : ℕ) :
    basepointNeighborhood n ≃ₜ ℂ :=
  (basepointNeighborhoodRangeFactorization_isHomeomorph n).homeomorph
      (Set.rangeFactorization (interiorDisk.restrict (quotientMap n))) |>.symm.trans
    interiorDiskHomeomorphComplex

/-- Helper for Exercise 73.1: the lifted preimage of the canonical basepoint
neighborhood is homeomorphic to the complex plane. -/
noncomputable def uliftBasepointNeighborhoodHomeomorphComplex (n : ℕ) :
    (Homeomorph.ulift ⁻¹' basepointNeighborhood n : Set (ULift (Space n))) ≃ₜ ℂ :=
  -- Restrict the canonical ULift homeomorphism, then use the original coordinates.
  (Homeomorph.ulift.sets rfl).trans (basepointNeighborhoodHomeomorphComplex n)

/-- Helper for Exercise 73.1: every dunce-cap center has an open neighborhood
that deformation retracts onto it. -/
lemma existsBasepointDeformationNeighborhood (n : ℕ) :
    ∃ (W : Set (Space n)) (hbase : basepoint n ∈ W),
      IsOpen W ∧
        Set.IsDeformationRetract
          ({(⟨basepoint n, hbase⟩ : W)} : Set W) := by
  -- Use the quotient image of the open disk and contract it in complex coordinates.
  refine ⟨basepointNeighborhood n, basepoint_mem_basepointNeighborhood n,
    isOpen_basepointNeighborhood n, ?_⟩
  exact exercise731IsDeformationRetract_singleton_of_homeomorph_normedSpace
    (basepointNeighborhoodHomeomorphComplex n)
    ⟨basepoint n, basepoint_mem_basepointNeighborhood n⟩

end DunceCap

namespace FundamentalGroup

/-- Helper for Exercise 73.1: rebuilding a loop from all its coordinate projections
recovers the original loop. -/
lemma piProjections_reconstruct {I : Type*} {X : I → Type*}
    [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i)
    (p : FundamentalGroup (∀ i, X i) x) :
    Path.Homotopic.pi
      (fun i ↦ FundamentalGroup.map ⟨fun y ↦ y i, continuous_apply i⟩ x p) = p := by
  -- This is the path-class product/projection inverse law.
  exact Path.Homotopic.pi_proj p

/-- Helper for Exercise 73.1: projecting a product of loops is the pointwise product
of their projections. -/
lemma piProjections_map_mul {I : Type*} {X : I → Type*}
    [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i)
    (p q : FundamentalGroup (∀ i, X i) x) :
    (fun i ↦ FundamentalGroup.map ⟨fun y ↦ y i, continuous_apply i⟩ x (p * q)) =
      (fun i ↦ FundamentalGroup.map ⟨fun y ↦ y i, continuous_apply i⟩ x p *
        FundamentalGroup.map ⟨fun y ↦ y i, continuous_apply i⟩ x q) := by
  -- Each coordinate is induced by a continuous projection and hence preserves products.
  funext i
  exact (FundamentalGroup.map ⟨fun y ↦ y i, continuous_apply i⟩ x).map_mul p q

/-- Helper for Exercise 73.1: projecting the loop assembled from a family of loops
recovers that family. -/
lemma piProjections_of_pi {I : Type*} {X : I → Type*}
    [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i)
    (p : ∀ i, FundamentalGroup (X i) (x i)) :
    (fun i ↦ FundamentalGroup.map ⟨fun y ↦ y i, continuous_apply i⟩ x
      (Path.Homotopic.pi p)) = p := by
  -- Extensionality reduces the family equality to projection of a path-class product.
  funext i
  exact Path.Homotopic.proj_pi i p

/-- Helper for Exercise 73.1: the fundamental group of an indexed product is the
indexed product of the fundamental groups. -/
noncomputable def piMulEquiv {I : Type*} {X : I → Type*} [∀ i, TopologicalSpace (X i)]
    (x : ∀ i, X i) :
    FundamentalGroup (∀ i, X i) x ≃* ∀ i, FundamentalGroup (X i) (x i) where
  toFun := fun p i ↦ FundamentalGroup.map ⟨fun y ↦ y i, continuous_apply i⟩ x p
  invFun := fun p ↦ Path.Homotopic.pi p
  left_inv := piProjections_reconstruct x
  right_inv := piProjections_of_pi x
  map_mul' := piProjections_map_mul x

end FundamentalGroup

namespace DunceCap

/-- Helper for Exercise 73.1: an indexed product of dunce caps realizes the
pointwise product of the corresponding finite cyclic groups. -/
lemma fundamentalGroupPiMulEquivZModAtBasepoint {I : Type*} (n : I → ℕ)
    (hn : ∀ i, 1 < n i) :
    Nonempty
      (FundamentalGroup ((i : I) → Space (n i))
          (fun i ↦ basepoint (n i)) ≃*
        Multiplicative ((i : I) → ZMod (n i))) := by
  -- Decompose loops coordinatewise and choose the cyclic coordinate in each factor.
  obtain ⟨equiv⟩ := piFundamentalGroupMulEquivZModAtBasepoint n hn
  exact ⟨(FundamentalGroup.piMulEquiv (fun i ↦ basepoint (n i))).trans
    ((MulEquiv.piCongrRight equiv).trans
      (MulEquiv.piMultiplicative (fun i ↦ ZMod (n i))).symm)⟩

end DunceCap

/-- Helper for Exercise 73.1: a homeomorphism pulls the image of a set back to
the original set. -/
private lemma exercise731Homeomorph_preimage_image
    {X : Type u} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (s : Set X) : s = e ⁻¹' (e '' s) := by
  -- Injectivity of the homeomorphism gives the exact preimage-image identity.
  exact (Set.preimage_image_eq s e.injective).symm

/-- Helper for Exercise 73.1: a homeomorphism restricts to a homeomorphism from
a set onto its image. -/
private def exercise731HomeomorphImage
    {X : Type u} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (s : Set X) : s ≃ₜ e '' s :=
  e.sets (exercise731Homeomorph_preimage_image e s)

namespace MonoidHom.IsExternalFreeProduct

/-- Helper for Exercise 73.1: precomposing every factor inclusion by a
multiplicative equivalence preserves an external free-product decomposition. -/
lemma compDomainMulEquiv
    {I : Type u} {G G' : I → Type u} {H : Type u}
    [∀ i, Group (G i)] [∀ i, Group (G' i)] [Group H]
    {j : ∀ i, G i →* H} (hfree : MonoidHom.IsExternalFreeProduct j)
    (e : ∀ i, G' i ≃* G i) :
    MonoidHom.IsExternalFreeProduct
      (fun i ↦ (j i).comp (e i).toMonoidHom) := by
  -- Each transported inclusion is injective because both of its factors are.
  refine ⟨fun i ↦ (hfree.injective i).comp (e i).injective, ?_⟩
  have rangeComp (i : I) :
      ((j i).comp (e i).toMonoidHom).range = (j i).range := by
    -- Surjectivity of the equivalence leaves the subgroup range unchanged.
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Set.mem_range_self (e i y)
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := (e i).surjective y
      exact Set.mem_range_self x
  simpa only [rangeComp] using hfree.isFreeProduct

end MonoidHom.IsExternalFreeProduct

namespace Topology.IndexedPointedWedge

variable {I : Type u} (X : I → Type u) [∀ i, TopologicalSpace (X i)]
  (p : ∀ i, X i)

omit [∀ i, TopologicalSpace (X i)] in
/-- Helper for Exercise 73.1: the generated pointed-wedge relation is exactly
equality or simultaneous membership at the designated points. -/
lemma eqvGen_iff_designated (x y : Σ i, X i) :
    Relation.EqvGen (Related X p) x y ↔
      Topology.Lemma714Wedge.designatedRel X p x y := by
  -- The normalized relation is already reflexive, symmetric, and transitive.
  constructor
  · intro hxy
    induction hxy with
    | rel x y h =>
        obtain ⟨i, j, rfl, rfl⟩ := h
        exact Or.inr ⟨rfl, rfl⟩
    | refl x => exact Or.inl rfl
    | symm x y _ ih =>
        exact Topology.Lemma714Wedge.designatedRel_symm X p ih
    | trans x y z _ _ hxy hyz =>
        exact Topology.Lemma714Wedge.designatedRel_trans X p hxy hyz
  · intro hxy
    rcases hxy with hxy | ⟨hx, hy⟩
    · subst y
      exact Relation.EqvGen.refl x
    · apply Relation.EqvGen.rel
      exact ⟨x.1, y.1, Sigma.ext rfl (heq_of_eq hx),
        Sigma.ext rfl (heq_of_eq hy)⟩

/-- Helper for Exercise 73.1: the canonical indexed pointed wedge is
homeomorphic to the normalized quotient model used in Lemma 71.4. -/
noncomputable def normalizedHomeomorph :
    Space X p ≃ₜ Topology.Lemma714Wedge.Space X p :=
  Homeomorph.Quotient.congrRight (eqvGen_iff_designated X p)

/-- Helper for Exercise 73.1: the normalization homeomorphism preserves every
factor inclusion. -/
lemma normalizedHomeomorph_inclusion (i : I) (x : X i) :
    normalizedHomeomorph X p (inclusion X p i x) =
      Topology.Lemma714Wedge.inclusion X p i x := by
  -- Both quotient maps use the same sigma representative.
  rfl

/-- Helper for Exercise 73.1: the inverse normalization homeomorphism sends a
normalized factor inclusion back to the canonical one. -/
lemma normalizedHomeomorph_symm_inclusion (i : I) (x : X i) :
    (normalizedHomeomorph X p).symm
        (Topology.Lemma714Wedge.inclusion X p i x) = inclusion X p i x := by
  -- Apply the forward normalization and cancel the homeomorphism.
  apply (normalizedHomeomorph X p).injective
  rw [(normalizedHomeomorph X p).apply_symm_apply,
    normalizedHomeomorph_inclusion]

/-- Helper for Exercise 73.1: each canonical factor inclusion in an indexed
pointed wedge is a closed embedding when all factors are `T1Space`s. -/
lemma isClosedEmbedding_inclusion [∀ i, T1Space (X i)] (i : I) :
    IsClosedEmbedding (inclusion X p i) := by
  -- Transport the established normalized-model embedding through the quotient homeomorphism.
  have hnormalized := Topology.Lemma714Wedge.isClosedEmbedding_inclusion X p i
  have htransported := (normalizedHomeomorph X p).symm.isClosedEmbedding.comp hnormalized
  have hmap :
      (normalizedHomeomorph X p).symm ∘
          Topology.Lemma714Wedge.inclusion X p i = inclusion X p i := by
    -- Normalize the composite pointwise before transporting the embedding property.
    funext x
    exact normalizedHomeomorph_symm_inclusion X p i x
  rw [hmap] at htransported
  exact htransported

omit [∀ i, TopologicalSpace (X i)] in
/-- Helper for Exercise 73.1: the canonical factor images cover an indexed
pointed wedge. -/
lemma iUnion_range_inclusion :
    ⋃ i, Set.range (inclusion X p i) = Set.univ := by
  -- Choose a sigma representative of each quotient point.
  ext q
  constructor
  · intro _
    exact Set.mem_univ q
  · intro _
    induction q using Quotient.inductionOn with
    | _ x => exact Set.mem_iUnion.mpr ⟨x.1, x.2, rfl⟩

omit [∀ i, TopologicalSpace (X i)] in
/-- Helper for Exercise 73.1: distinct canonical factor images meet only at the
common wedge point. -/
lemma range_inclusion_inter (i j : I) (hij : i ≠ j) :
    Set.range (inclusion X p i) ∩ Set.range (inclusion X p j) =
      {point X p i} := by
  -- Normalize equality of quotient representatives and inspect its two alternatives.
  ext q
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hxy⟩⟩
    have hnormalized :=
      (eqvGen_iff_designated X p _ _).mp (Quotient.exact hxy)
    rcases hnormalized with h | h
    · exact (hij (Sigma.mk.inj_iff.mp h.symm).1).elim
    · rw [Set.mem_singleton_iff, point]
      exact congrArg (inclusion X p i) h.2
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    exact ⟨⟨p i, rfl⟩, ⟨p j, point_eq X p j i⟩⟩

/-- Helper for Exercise 73.1: the canonical factor images form a finite wedge at
any chosen representation of the common point. -/
lemma factorImagesFormFiniteWedge [Fintype I] [∀ i, T1Space (X i)] (i₀ : I) :
    Topology.IsFiniteWedge (fun i ↦ Set.range (inclusion X p i))
      (point X p i₀) := by
  -- Assemble coverage, closedness, common-point membership, and pairwise intersections.
  apply Topology.IsFiniteWedge.of
  · exact iUnion_range_inclusion X p
  · intro i
    exact (isClosedEmbedding_inclusion X p i).isClosed_range
  · intro i
    exact ⟨p i, point_eq X p i i₀⟩
  · intro i j hij
    have hinter := range_inclusion_inter X p i j hij
    rwa [point_eq X p i i₀] at hinter

/-- Helper for Exercise 73.1: open contractible factor neighborhoods and factor
group coordinates identify a finite indexed pointed wedge with the indexed free
product of those groups. -/
lemma fundamentalGroupMulEquivCoprodI
    [Finite I] [∀ i, T1Space (X i)] (i₀ : I)
    (U : ∀ i, Set (X i)) (hpU : ∀ i, p i ∈ U i)
    (hU_open : ∀ i, IsOpen (U i))
    (neighborhoodCoordinates : ∀ i, U i ≃ₜ ℂ)
    (G : I → Type u) [∀ i, Group (G i)]
    (factorCoordinates : ∀ i, FundamentalGroup (X i) (p i) ≃* G i) :
    Nonempty
      (FundamentalGroup (Space X p) (point X p i₀) ≃*
        Monoid.CoprodI G) := by
  -- Local instance justification (finite indexing): the finite-wedge API uses `Fintype`.
  letI : Fintype I := Fintype.ofFinite I
  -- Expose the canonical factor images as the finite-wedge cover used by van Kampen.
  let S : I → Set (Space X p) := fun i ↦ Set.range (inclusion X p i)
  let wedgePoint : Space X p := point X p i₀
  letI : Topology.IsFiniteWedge S wedgePoint :=
    factorImagesFormFiniteWedge X p i₀
  let factorHomeomorph (i : I) : X i ≃ₜ S i :=
    (isClosedEmbedding_inclusion X p i).isEmbedding.toHomeomorph
  let W : ∀ i, Set (S i) := fun i ↦ factorHomeomorph i '' U i
  have hW_open : ∀ i, IsOpen (W i) := by
    -- Each factor neighborhood is carried to an open set by its factor homeomorphism.
    intro i
    exact (factorHomeomorph i).isOpen_image.mpr (hU_open i)
  have hpW : ∀ i, (⟨wedgePoint,
      Topology.IsFiniteWedge.point_mem i⟩ : S i) ∈ W i := by
    -- The selected point maps to the common wedge point in every factor image.
    intro i
    have hfactorPoint :
        factorHomeomorph i (p i) =
          (⟨wedgePoint, Topology.IsFiniteWedge.point_mem i⟩ : S i) := by
      apply Subtype.ext
      exact point_eq X p i i₀
    exact ⟨p i, hpU i, hfactorPoint⟩
  have hW_retract : ∀ i,
      Set.IsDeformationRetract
        ({(⟨⟨wedgePoint, Topology.IsFiniteWedge.point_mem i⟩, hpW i⟩ : W i)} :
          Set (W i)) := by
    -- Pull each image neighborhood back to its normed-space coordinates and contract it.
    intro i
    let imageCoordinates : W i ≃ₜ ℂ :=
      (exercise731HomeomorphImage (factorHomeomorph i) (U i)).symm.trans
        (neighborhoodCoordinates i)
    exact exercise731IsDeformationRetract_singleton_of_homeomorph_normedSpace
      imageCoordinates
      ⟨⟨wedgePoint, Topology.IsFiniteWedge.point_mem i⟩, hpW i⟩
  -- Van Kampen now exhibits the ambient group as the external free product of
  -- the fundamental groups of the factor-image subtypes.
  let F : I → Type u := fun i ↦
    FundamentalGroup (S i) ⟨wedgePoint, Topology.IsFiniteWedge.point_mem i⟩
  let j : ∀ i, F i →* FundamentalGroup (Space X p) wedgePoint := fun i ↦
    FundamentalGroup.mapOfEq
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S i, Space X p)) rfl
  have hfree : MonoidHom.IsExternalFreeProduct j := by
    -- Apply the finite-wedge van Kampen theorem to the named factor images.
    exact fundamentalGroup_isExternalFreeProduct_of_finiteWedge
      S wedgePoint W hW_open hpW hW_retract
  have imageFactorCoordinatesPoint (i : I) :
      (factorHomeomorph i).symm
          ⟨wedgePoint, Topology.IsFiniteWedge.point_mem i⟩ = p i := by
    -- Inverting the factor homeomorphism sends the common point back to `p i`.
    have hfactorPoint :
        factorHomeomorph i (p i) =
          (⟨wedgePoint, Topology.IsFiniteWedge.point_mem i⟩ : S i) := by
      apply Subtype.ext
      exact point_eq X p i i₀
    simpa only [(factorHomeomorph i).symm_apply_apply] using
      (congrArg (factorHomeomorph i).symm hfactorPoint).symm
  let imageFactorCoordinates : ∀ i, F i ≃* G i := fun i ↦
    ((factorHomeomorph i).symm.fundamentalGroupMulEquiv
      ⟨wedgePoint, Topology.IsFiniteWedge.point_mem i⟩).trans
      ((MulEquiv.cast (imageFactorCoordinatesPoint i) :
        FundamentalGroup (X i)
            ((factorHomeomorph i).symm
              ⟨wedgePoint, Topology.IsFiniteWedge.point_mem i⟩) ≃*
          FundamentalGroup (X i) (p i)).trans
        (factorCoordinates i))
  have hcanonical : MonoidHom.IsExternalFreeProduct
      (fun i ↦ (Monoid.CoprodI.of : G i →* Monoid.CoprodI G).comp
        (imageFactorCoordinates i).toMonoidHom) := by
    -- Precompose the canonical coproduct inclusions by the factor coordinates.
    exact (Monoid.CoprodI.canonicalIsExternalFreeProduct G).compDomainMulEquiv
      imageFactorCoordinates
  obtain ⟨equiv, _, _⟩ := MonoidHom.HasFreeProductExtension.uniqueMulEquiv
    F j
      (fun i ↦ (Monoid.CoprodI.of : G i →* Monoid.CoprodI G).comp
        (imageFactorCoordinates i).toMonoidHom)
      hfree.hasExtension hcanonical.hasExtension
  exact ⟨equiv⟩

end Topology.IndexedPointedWedge

namespace Monoid.CoprodI

/-- Helper for Exercise 73.1: a Boolean-indexed free product is multiplicatively
equivalent to the binary free product of its two factors. -/
lemma nonemptyBoolEquivCoprod (G : Bool → Type u) [∀ b, Group (G b)] :
    Nonempty (Monoid.CoprodI G ≃* Monoid.Coprod (G false) (G true)) := by
  -- Define the comparison maps by the universal properties of both coproducts.
  let toCoprod : Monoid.CoprodI G →* Monoid.Coprod (G false) (G true) :=
    Monoid.CoprodI.lift fun
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr
  let fromCoprod : Monoid.Coprod (G false) (G true) →* Monoid.CoprodI G :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (i := false))
      (Monoid.CoprodI.of (i := true))
  have leftInverse : Function.LeftInverse fromCoprod toCoprod := by
    -- Extensionality on the indexed generators shows the first composite is identity.
    have composite : fromCoprod.comp toCoprod = MonoidHom.id _ := by
      apply Monoid.CoprodI.ext_hom
      intro b
      cases b <;> rfl
    exact DFunLike.congr_fun composite
  have rightInverse : Function.RightInverse fromCoprod toCoprod := by
    -- Extensionality on the two binary generators proves the converse composite.
    have composite : toCoprod.comp fromCoprod = MonoidHom.id _ := by
      apply Monoid.Coprod.hom_ext <;> rfl
    exact DFunLike.congr_fun composite
  -- The mutually inverse comparison maps package as the desired equivalence.
  exact ⟨MulEquiv.ofBijective toCoprod
    ⟨leftInverse.injective, rightInverse.surjective⟩⟩

end Monoid.CoprodI

/-- Exercise 73.1 (1): The product of the `n`-fold and `m`-fold dunce caps realizes
the direct product of the corresponding finite cyclic groups. -/
theorem fundamentalGroup_productDunceCaps (n m : ℕ) (hn : 1 < n) (hm : 1 < m) :
    Nonempty
      (FundamentalGroup (DunceCap.Space n × DunceCap.Space m)
          (DunceCap.basepoint n, DunceCap.basepoint m) ≃*
        Multiplicative (ZMod n × ZMod m)) := by
  -- Decompose the topological product, then apply the paired cyclic coordinates.
  obtain ⟨factorEquiv⟩ :=
    DunceCap.prodFundamentalGroupMulEquivZModAtBasepoint n m hn hm
  exact ⟨(FundamentalGroup.prodMulEquiv
    (DunceCap.basepoint n) (DunceCap.basepoint m)).trans factorEquiv⟩

/-- Exercise 73.1 (2): A finite product of dunce caps realizes the direct product of
the corresponding finite cyclic groups. -/
theorem fundamentalGroup_finiteProductDunceCaps (k : ℕ) (n : Fin k → ℕ)
    (hn : ∀ i, 1 < n i) :
    Nonempty
      (FundamentalGroup ((i : Fin k) → DunceCap.Space (n i))
          (fun i ↦ DunceCap.basepoint (n i)) ≃*
        Multiplicative ((i : Fin k) → ZMod (n i))) := by
  -- Specialize the indexed dunce-cap product computation to the finite family.
  exact DunceCap.fundamentalGroupPiMulEquivZModAtBasepoint n hn

/-- Exercise 73.1 (3): The pointed wedge of two dunce caps realizes the free product
of the corresponding finite cyclic groups. -/
theorem fundamentalGroup_wedgeDunceCaps (n m : ℕ) (hn : 1 < n) (hm : 1 < m) :
    Nonempty
      (FundamentalGroup
          (Topology.PointedWedge (DunceCap.Space n) (DunceCap.basepoint n)
            (DunceCap.Space m) (DunceCap.basepoint m))
          (Topology.PointedWedge.basepoint (DunceCap.basepoint n) (DunceCap.basepoint m)) ≃*
        Monoid.Coprod (Multiplicative (ZMod n)) (Multiplicative (ZMod m))) := by
  classical
  -- Pull the canonical dunce-cap neighborhoods back to the two ULifted factors.
  let U : ∀ b, Set (Topology.PointedWedge.Family (DunceCap.Space n)
      (DunceCap.Space m) b) := fun
    | false => Homeomorph.ulift ⁻¹' DunceCap.basepointNeighborhood n
    | true => Homeomorph.ulift ⁻¹' DunceCap.basepointNeighborhood m
  have hpU : ∀ b, Topology.PointedWedge.points (DunceCap.basepoint n)
      (DunceCap.basepoint m) b ∈ U b := by
    -- In each branch, the lifted center maps to the original center.
    intro b
    cases b
    · exact DunceCap.basepoint_mem_basepointNeighborhood n
    · exact DunceCap.basepoint_mem_basepointNeighborhood m
  have hU_open : ∀ b, IsOpen (U b) := by
    -- A homeomorphism pulls each canonical open neighborhood back to an open set.
    intro b
    cases b
    · exact Homeomorph.ulift.isOpen_preimage.mpr
        (DunceCap.isOpen_basepointNeighborhood n)
    · exact Homeomorph.ulift.isOpen_preimage.mpr
        (DunceCap.isOpen_basepointNeighborhood m)
  let neighborhoodCoordinates : ∀ b, U b ≃ₜ ℂ := fun
    | false => DunceCap.uliftBasepointNeighborhoodHomeomorphComplex n
    | true => DunceCap.uliftBasepointNeighborhoodHomeomorphComplex m
  let G : Bool → Type := fun
    | false => Multiplicative (ZMod n)
    | true => Multiplicative (ZMod m)
  -- The dependent Bool families require explicit branchwise instances.
  letI (b : Bool) : T1Space (Topology.PointedWedge.Family (DunceCap.Space n)
      (DunceCap.Space m) b) := match b with
    | false => inferInstance
    | true => inferInstance
  letI (b : Bool) : Group (G b) := match b with
    | false => inferInstance
    | true => inferInstance
  -- Select both transported cyclic computations, then assemble the Boolean family.
  obtain ⟨factorPair⟩ :=
    DunceCap.pointedWedgeFactorPairMulEquivZModAtBasepoint n m hn hm
  let factorCoordinates : ∀ b, FundamentalGroup
      (Topology.PointedWedge.Family (DunceCap.Space n) (DunceCap.Space m) b)
      (Topology.PointedWedge.points (DunceCap.basepoint n)
        (DunceCap.basepoint m) b) ≃* G b := fun
    | false => factorPair.1
    | true => factorPair.2
  have indexedResult :
      Nonempty
        (FundamentalGroup
            (Topology.PointedWedge (DunceCap.Space n) (DunceCap.basepoint n)
              (DunceCap.Space m) (DunceCap.basepoint m))
            (Topology.PointedWedge.basepoint (DunceCap.basepoint n)
              (DunceCap.basepoint m)) ≃* Monoid.CoprodI G) := by
    -- Specialize the indexed wedge computation to the two Boolean factors.
    exact Topology.IndexedPointedWedge.fundamentalGroupMulEquivCoprodI
      (Topology.PointedWedge.Family (DunceCap.Space n) (DunceCap.Space m))
      (Topology.PointedWedge.points (DunceCap.basepoint n) (DunceCap.basepoint m))
      false U hpU hU_open neighborhoodCoordinates G factorCoordinates
  obtain ⟨indexedEquiv⟩ := indexedResult
  obtain ⟨binaryEquiv⟩ := Monoid.CoprodI.nonemptyBoolEquivCoprod G
  -- Convert the Bool-indexed free product to the requested binary free product.
  exact ⟨indexedEquiv.trans binaryEquiv⟩

/-- Exercise 73.1 (4): A finite pointed wedge of dunce caps realizes the indexed free
product of the corresponding finite cyclic groups. -/
theorem fundamentalGroup_finiteWedgeDunceCaps (k : ℕ) (hk : 0 < k)
    (n : Fin k → ℕ) (hn : ∀ i, 1 < n i) :
    Nonempty
      (FundamentalGroup
          (Topology.IndexedPointedWedge.Space (fun i : Fin k ↦ DunceCap.Space (n i))
            (fun i ↦ DunceCap.basepoint (n i)))
          (Topology.IndexedPointedWedge.point (fun i : Fin k ↦ DunceCap.Space (n i))
            (fun i ↦ DunceCap.basepoint (n i)) ⟨0, hk⟩) ≃*
        Monoid.CoprodI (fun i : Fin k ↦ Multiplicative (ZMod (n i)))) := by
    -- Choose the cyclic coordinate equivalence for every dunce-cap factor.
    obtain ⟨factorCoordinates⟩ :=
      DunceCap.piFundamentalGroupMulEquivZModAtBasepoint n hn
    -- The canonical open-disk neighborhoods satisfy the indexed van Kampen bridge.
    exact Topology.IndexedPointedWedge.fundamentalGroupMulEquivCoprodI
      (fun i : Fin k ↦ DunceCap.Space (n i))
      (fun i ↦ DunceCap.basepoint (n i)) ⟨0, hk⟩
      (fun i ↦ DunceCap.basepointNeighborhood (n i))
      (fun i ↦ DunceCap.basepoint_mem_basepointNeighborhood (n i))
      (fun i ↦ DunceCap.isOpen_basepointNeighborhood (n i))
      (fun i ↦ DunceCap.basepointNeighborhoodHomeomorphComplex (n i))
      (fun i : Fin k ↦ Multiplicative (ZMod (n i))) factorCoordinates
