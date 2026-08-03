module

public import Topology_Munkres_2000.Book.Definition_71_4.WedgeOfCircles
public import Topology_Munkres_2000.Book.Example_71_1
public import Topology_Munkres_2000.Book.Exercise_13_99_5.Instances
public import Topology_Munkres_2000.Book.Exercise_71_4
public import Topology_Munkres_2000.Book.Exercise_71_5.ExpandingCircles
public import Topology_Munkres_2000.Book.Lemma_71_4
public import Topology_Munkres_2000.Book.Theorem_58_7
import all Topology_Munkres_2000.Book.Theorem_71_1.LoopClass
public import Topology_Munkres_2000.Book.Theorem_71_3
public import Mathlib.Analysis.Complex.Angle
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.CompactOpen

public section

universe u v

open Path.Homotopic.Quotient

namespace ExpandingCircles

/-- Helper for Exercise 71.5: the ambient included loop class computes as the
fundamental-group map of the component's subtype inclusion. -/
private lemma includedLoopClass_eq_mapOfEq
    {ι : Type v} {X : Type u} [TopologicalSpace X]
    (S : ι → Set X) (p : X) (i : ι) {hp : p ∈ S i}
    (f : Path (⟨p, hp⟩ : S i) ⟨p, hp⟩) :
    CircleWedge.includedLoopClass S p i f =
      FundamentalGroup.mapOfEq
        (⟨Subtype.val, continuous_subtype_val⟩ : C(S i, X)) rfl
        (FundamentalGroup.fromPath (mk f)) := by
  -- Route correction: cache the imported definition's reducible computation
  -- equation instead of repeatedly unfolding it under induced maps.
  unfold CircleWedge.includedLoopClass
  congr

/-- Helper for Exercise 71.5: the point opposite the origin on the `n`th circle
belongs to the expanding-circle union. -/
lemma outerPoint_mem_carrier (n : ℕ+) :
    WithLp.toLp 2 ![2 * (n : ℝ), 0] ∈ carrier := by
  -- Select the `n`th component and verify its defining sphere equation.
  rw [mem_carrier_iff]
  refine ⟨n, ?_⟩
  rw [mem_circle_iff, EuclideanSpace.dist_eq]
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast n.property
  have hsub : 2 * (n : ℝ) - (n : ℝ) = (n : ℝ) := by
    ring
  simp only [Fin.sum_univ_two, Real.dist_eq, center_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, sub_zero, sq_abs]
  rw [hsub]
  norm_num only [zero_pow, add_zero, Real.sqrt_sq_eq_abs, abs_of_pos hnpos]

/-- Helper for Exercise 71.5: the outer point of the `n`th expanding circle. -/
noncomputable def outerPoint (n : ℕ+) : Space :=
  ⟨WithLp.toLp 2 ![2 * (n : ℝ), 0], outerPoint_mem_carrier n⟩

/-- Helper for Exercise 71.5: the ambient coordinates of an outer point. -/
lemma outerPoint_coe (n : ℕ+) :
    (outerPoint n : Plane) = WithLp.toLp 2 ![2 * (n : ℝ), 0] := by
  -- Coercing the subtype point forgets only its carrier-membership proof.
  rfl

/-- Helper for Exercise 71.5: outer points escape linearly from the common origin. -/
lemma dist_origin_outerPoint (n : ℕ+) :
    dist origin (outerPoint n) = 2 * (n : ℝ) := by
  -- Compute first in the ambient Euclidean space, avoiding subtype unfolding.
  have hnnonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast n.property.le
  have hambient :
      dist (0 : Plane) (WithLp.toLp 2 ![2 * (n : ℝ), 0]) = 2 * (n : ℝ) := by
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two, Real.dist_eq, sq_abs, hnnonneg]
  rw [Subtype.dist_eq, origin_coe, outerPoint_coe]
  exact hambient

/-- Helper for Exercise 71.5: the planar expanding-circle union is noncompact. -/
instance instNoncompactSpace : NoncompactSpace Space := by
  refine ⟨?_⟩
  intro hcompact
  -- Compactness would impose one bound on all pairwise distances in the subtype.
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hcompact.isBounded
  obtain ⟨k, hk⟩ := exists_nat_gt (C / 2)
  let n : ℕ+ := ⟨k + 1, Nat.succ_pos k⟩
  have hdist : dist origin (outerPoint n) ≤ C :=
    hC (Set.mem_univ origin) (Set.mem_univ (outerPoint n))
  -- The selected outer point has distance greater than the proposed bound.
  rw [dist_origin_outerPoint] at hdist
  have hkn : (k : ℝ) < (n : ℝ) := by
    norm_num [n]
  nlinarith

/-- Helper for Exercise 71.5: only finitely many positive integers lie below a
fixed real bound. -/
lemma finite_setOf_pnatCast_le (C : ℝ) : {n : ℕ+ | (n : ℝ) ≤ C}.Finite := by
  -- Place every such positive integer in one finite natural-number interval.
  obtain ⟨k, hk⟩ := exists_nat_gt C
  let N : ℕ+ := ⟨k + 1, Nat.succ_pos k⟩
  have hfinite :
      ((fun n : ℕ+ ↦ (n : ℕ)) ⁻¹' Set.Iic (N : ℕ)).Finite :=
    (Set.finite_Iic (N : ℕ)).preimage PNat.coe_injective.injOn
  apply hfinite.subset
  intro n hn
  have hnkReal : (n : ℝ) < (k : ℝ) := hn.trans_lt hk
  have hnk : (n : ℕ) < k := by
    exact_mod_cast hnkReal
  change (n : ℕ) ≤ k + 1
  omega

/-- Helper for Exercise 71.5: distinct ambient expanding circles meet only at
the common origin. -/
lemma circle_inter_circle (m n : ℕ+) (hmn : m ≠ n) :
    circle m ∩ circle n = {(0 : Plane)} := by
  -- Expand the two sphere equations and subtract them to force the first
  -- coordinate to vanish; either circle equation then forces the second.
  ext x
  constructor
  · intro hx
    have hm := hx.1
    have hn := hx.2
    rw [mem_circle_iff] at hm hn
    have hm_sq := congrArg (fun z : ℝ ↦ z ^ 2) hm
    have hn_sq := congrArg (fun z : ℝ ↦ z ^ 2) hn
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two] at hm_sq hn_sq
    have hm_quad :
        (x 0 - (m : ℝ)) ^ 2 + (x 1) ^ 2 = (m : ℝ) ^ 2 := by
      simpa [center_apply, Real.dist_eq] using hm_sq
    have hn_quad :
        (x 0 - (n : ℝ)) ^ 2 + (x 1) ^ 2 = (n : ℝ) ^ 2 := by
      simpa [center_apply, Real.dist_eq] using hn_sq
    have hradius_ne : (m : ℝ) ≠ (n : ℝ) := by
      intro h
      apply hmn
      apply PNat.eq
      exact_mod_cast h
    have hfactor : ((m : ℝ) - (n : ℝ)) * x 0 = 0 := by
      nlinarith [hm_quad, hn_quad]
    have hx0 : x 0 = 0 := by
      rcases mul_eq_zero.mp hfactor with hradius | hxzero
      · exact False.elim (hradius_ne (sub_eq_zero.mp hradius))
      · exact hxzero
    have hm_zero := hm_quad
    rw [hx0] at hm_zero
    have hx1_sq : (x 1) ^ 2 = 0 := by
      nlinarith [hm_zero]
    have hx1 : x 1 = 0 := sq_eq_zero_iff.mp hx1_sq
    rw [Set.mem_singleton_iff]
    ext i
    fin_cases i
    · simp [hx0]
    · simp [hx1]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨zero_mem_circle m, zero_mem_circle n⟩

/-- Helper for Exercise 71.5: distinct component subspaces of the expanding
circle union meet only at `origin`. -/
lemma component_inter_component (m n : ℕ+) (hmn : m ≠ n) :
    component m ∩ component n = {origin} := by
  -- Pull the ambient intersection formula back along the subtype inclusion.
  ext x
  rw [Set.mem_inter_iff, mem_component_iff, mem_component_iff,
    ← Set.mem_inter_iff, circle_inter_circle m n hmn]
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hx
    apply Subtype.ext
    exact hx.trans origin_coe.symm
  · intro hx
    have hcoe := congrArg (fun y : Space ↦ (y : Plane)) hx
    rwa [origin_coe] at hcoe

/-- Helper for Exercise 71.5: every expanding circle lies in the planar union. -/
lemma circle_subset_carrier (n : ℕ+) : circle n ⊆ carrier := by
  -- Insert the selected circle into the indexed union defining the carrier.
  intro x hx
  rw [mem_carrier_iff]
  exact ⟨n, hx⟩

/-- Helper for Exercise 71.5: the component predicate is the pullback of its
ambient circle along the carrier inclusion. -/
lemma component_eq_preimage (n : ℕ+) :
    component n = (Subtype.val : Space → Plane) ⁻¹' circle n := by
  -- Compare membership using the public component-membership equation.
  ext x
  exact mem_component_iff x n

/-- Helper for Exercise 71.5: every point of one ambient circle has a canonical
representative in the union subtype. -/
lemma circle_subset_range_subtypeVal (n : ℕ+) :
    circle n ⊆ Set.range (Subtype.val : Space → Plane) := by
  -- Package circle membership first as membership in the union carrier.
  intro x hx
  exact ⟨⟨x, circle_subset_carrier n hx⟩, rfl⟩

/-- Helper for Exercise 71.5: forgetting the outer carrier subtype identifies
an expanding component with its ambient planar circle. -/
noncomputable def componentAmbientHomeomorph (n : ℕ+) : component n ≃ₜ circle n :=
  (Homeomorph.setCongr (component_eq_preimage n)).trans
    (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (circle_subset_range_subtypeVal n))

/-- Helper for Exercise 71.5: the canonical Euclidean unit sphere is
homeomorphic to the complex unit circle. -/
noncomputable def unitSphereHomeomorphCircle :
    Metric.sphere (0 : Plane) 1 ≃ₜ Circle :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    InfiniteEarring.unitPlane_mem_iff

/-- Helper for Exercise 71.5: the positive horizontal unit vector belongs to
the Euclidean unit sphere. -/
lemma unitEast_mem_sphere :
    WithLp.toLp 2 ![(1 : ℝ), 0] ∈ Metric.sphere (0 : Plane) 1 := by
  -- Its Euclidean norm is one by direct coordinate calculation.
  rw [Metric.mem_sphere, EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two]

/-- Helper for Exercise 71.5: the positive horizontal point of the Euclidean
unit sphere. -/
noncomputable def unitEast : Metric.sphere (0 : Plane) 1 :=
  ⟨WithLp.toLp 2 ![(1 : ℝ), 0], unitEast_mem_sphere⟩

/-- Helper for Exercise 71.5: the canonical unit-sphere coordinate sends the
positive horizontal point to `1 : Circle`. -/
lemma unitSphereHomeomorphCircle_unitEast :
    unitSphereHomeomorphCircle unitEast = (1 : Circle) := by
  -- The orthonormal coordinate equivalence sends `(1,0)` to `1 + 0 * I`.
  apply Subtype.ext
  change Complex.orthonormalBasisOneI.repr.symm (unitEast : Plane) = 1
  rw [Complex.orthonormalBasisOneI_repr_symm_apply]
  simp [unitEast]

/-- Helper for Exercise 71.5: the real cast of a positive natural is nonzero. -/
lemma pnatCast_ne_zero (n : ℕ+) : (n : ℝ) ≠ 0 := by
  -- Positivity of the positive natural survives the real cast.
  exact_mod_cast n.ne_zero

/-- Helper for Exercise 71.5: the affine dilation sending the Euclidean unit
sphere to the `n`th expanding circle and the point `(1,0)` to the origin. -/
noncomputable def circleDilation (n : ℕ+) : Plane ≃ₜ Plane :=
  (DilationEquiv.smulTorsor (center n) (neg_ne_zero.mpr (pnatCast_ne_zero n))).toHomeomorph

/-- Helper for Exercise 71.5: the affine dilation sends the Euclidean unit
sphere exactly onto the `n`th expanding circle. -/
lemma circleDilation_mem_circle (n : ℕ+) (x : Plane) :
    x ∈ Metric.sphere 0 1 ↔ circleDilation n x ∈ circle n := by
  -- The dilation has metric ratio `n`, so the unit-radius equation scales to
  -- the defining radius of the component.
  rw [Metric.mem_sphere, mem_circle_iff]
  simp only [circleDilation, DilationEquiv.coe_toHomeomorph,
    DilationEquiv.smulTorsor_apply, vadd_eq_add]
  rw [dist_add_self_left, norm_smul, dist_zero_right]
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast n.property
  rw [norm_neg, Real.norm_eq_abs, abs_of_pos hnpos]
  constructor
  · intro hx
    rw [hx, mul_one]
  · intro hx
    exact mul_left_cancel₀ (pnatCast_ne_zero n) (by simpa using hx)

/-- Helper for Exercise 71.5: the affine component dilation sends the positive
horizontal unit point to the ambient origin. -/
lemma circleDilation_unitEast (n : ℕ+) :
    (circleDilation n).subtype (circleDilation_mem_circle n) unitEast =
      (⟨0, zero_mem_circle n⟩ : circle n) := by
  -- Coerce to the plane and compute the two coordinates of `-n • (1,0) + (n,0)`.
  apply Subtype.ext
  ext i
  fin_cases i
  · simp [circleDilation, unitEast, center_apply]
  · simp [circleDilation, unitEast, center_apply]

/-- Helper for Exercise 71.5: a pointed coordinate identifies the `n`th
expanding component with the standard complex circle. -/
noncomputable def componentCoordinate (n : ℕ+) : component n ≃ₜ Circle :=
  (componentAmbientHomeomorph n).trans
    (((circleDilation n).subtype (circleDilation_mem_circle n)).symm.trans
      unitSphereHomeomorphCircle)

/-- Helper for Exercise 71.5: the ambient component identification preserves
the underlying planar coordinate. -/
lemma componentAmbientHomeomorph_coe (n : ℕ+) (x : component n) :
    ((componentAmbientHomeomorph n x : circle n) : Plane) = ((x : Space) : Plane) := by
  -- Both stages of the homeomorphism merely repackage the same point with a
  -- different membership proof.
  rw [componentAmbientHomeomorph, Homeomorph.trans_apply,
    Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe]
  rfl

/-- Helper for Exercise 71.5: the ambient component identification carries the
common component point to the planar origin. -/
lemma componentAmbientHomeomorph_origin (n : ℕ+) :
    componentAmbientHomeomorph n (componentOrigin n) =
      (⟨0, zero_mem_circle n⟩ : circle n) := by
  -- Both nested subtype points have the same ambient planar coordinate.
  apply Subtype.ext
  rw [componentAmbientHomeomorph_coe, origin_coe]

/-- Helper for Exercise 71.5: the component coordinate is pointed at
`origin` and `1 : Circle`. -/
lemma componentCoordinate_origin (n : ℕ+) :
    componentCoordinate n (componentOrigin n) = (1 : Circle) := by
  -- Move the origin through the ambient identification, invert the dilation
  -- using its explicit unit-point computation, and finish in complex coordinates.
  rw [componentCoordinate, Homeomorph.trans_apply, Homeomorph.trans_apply,
    componentAmbientHomeomorph_origin]
  have hinverse :
      ((circleDilation n).subtype (circleDilation_mem_circle n)).symm
          (⟨0, zero_mem_circle n⟩ : circle n) = unitEast := by
    apply ((circleDilation n).subtype (circleDilation_mem_circle n)).injective
    rw [Homeomorph.apply_symm_apply, circleDilation_unitEast]
  rw [hinverse, unitSphereHomeomorphCircle_unitEast]

/-- Helper for Exercise 71.5: the canonical Euclidean-sphere coordinate
preserves distances. -/
lemma dist_unitSphereHomeomorphCircle
    (x y : Metric.sphere (0 : Plane) 1) :
    dist (unitSphereHomeomorphCircle x) (unitSphereHomeomorphCircle y) =
      dist x y := by
  -- Pass to ambient norms and use the linear isometry's preservation of
  -- subtraction and norm.
  change dist (Complex.orthonormalBasisOneI.repr.symm (x : Plane))
      (Complex.orthonormalBasisOneI.repr.symm (y : Plane)) =
    dist (x : Plane) (y : Plane)
  rw [dist_eq_norm, dist_eq_norm, ← map_sub,
    Complex.orthonormalBasisOneI.repr.symm.norm_map]

/-- Helper for Exercise 71.5: the component dilation scales distances by the
positive radius `n`. -/
lemma dist_circleDilation (n : ℕ+)
    (x y : Metric.sphere (0 : Plane) 1) :
    dist ((circleDilation n).subtype (circleDilation_mem_circle n) x)
        ((circleDilation n).subtype (circleDilation_mem_circle n) y) =
      (n : ℝ) * dist x y := by
  -- Compute in the ambient plane; translation cancels and scalar
  -- multiplication contributes the norm of `-n`.
  change dist (-(n : ℝ) • (x : Plane) + center n)
      (-(n : ℝ) • (y : Plane) + center n) =
    (n : ℝ) * dist (x : Plane) (y : Plane)
  rw [dist_add_right, dist_eq_norm, ← smul_sub, norm_smul, dist_eq_norm]
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast n.property
  rw [norm_neg, Real.norm_eq_abs, abs_of_pos hnpos]

/-- Helper for Exercise 71.5: the ambient component identification preserves
the inherited metric. -/
lemma dist_componentAmbientHomeomorph (n : ℕ+) (x y : component n) :
    dist (componentAmbientHomeomorph n x) (componentAmbientHomeomorph n y) =
      dist (x : Space) (y : Space) := by
  -- Both sides are the ambient planar distance after forgetting subtype proofs.
  simp only [Subtype.dist_eq, componentAmbientHomeomorph_coe]

/-- Helper for Exercise 71.5: component coordinates scale distances by the
reciprocal of the component radius. -/
lemma dist_componentCoordinate (n : ℕ+) (x y : component n) :
    dist (componentCoordinate n x) (componentCoordinate n y) =
      dist (x : Space) (y : Space) / (n : ℝ) := by
  -- Normalize both points to the unit sphere, use its isometric complex
  -- coordinate, and solve the dilation scaling equation.
  let d := (circleDilation n).subtype (circleDilation_mem_circle n)
  let x' := d.symm (componentAmbientHomeomorph n x)
  let y' := d.symm (componentAmbientHomeomorph n y)
  have hscale := dist_circleDilation n x' y'
  rw [d.apply_symm_apply, d.apply_symm_apply,
    dist_componentAmbientHomeomorph] at hscale
  change dist (unitSphereHomeomorphCircle x')
      (unitSphereHomeomorphCircle y') = dist (x : Space) (y : Space) / (n : ℝ)
  rw [dist_unitSphereHomeomorphCircle]
  rw [eq_div_iff (pnatCast_ne_zero n), mul_comm]
  exact hscale.symm

/-- Helper for Exercise 71.5: distance from the pointed component coordinate
to `1` is planar distance from `origin`, divided by the radius. -/
lemma dist_componentCoordinate_origin (n : ℕ+) (x : component n) :
    dist (componentCoordinate n x) 1 =
      dist (x : Space) origin / (n : ℝ) := by
  -- Specialize the two-point scaling formula at the common component point.
  rw [← componentCoordinate_origin n]
  exact dist_componentCoordinate n x (componentOrigin n)

/-- Helper for Exercise 71.5: every expanding component is homeomorphic to a circle. -/
lemma component_homeomorphic_circle (n : ℕ+) : Nonempty (component n ≃ₜ Circle) := by
  -- Use the explicit pointed component coordinate.
  exact ⟨componentCoordinate n⟩

/-- Helper for Exercise 71.5: each expanding component is closed in the planar
union. -/
lemma isClosed_component (n : ℕ+) : IsClosed (component n) := by
  -- A component is the preimage of a closed metric sphere under the subtype
  -- inclusion into the Euclidean plane.
  have hcircle : circle n = Metric.sphere (center n) (n : ℝ) := by
    ext x
    rw [mem_circle_iff, Metric.mem_sphere]
  rw [component_eq_preimage, hcircle]
  exact (Metric.isClosed_sphere :
    IsClosed (Metric.sphere (center n) (n : ℝ))).preimage continuous_subtype_val

/-- Helper for Exercise 71.5: a non-origin point belongs to at most one
expanding component. -/
lemma component_index_unique_of_ne_origin {x : Space} (hx : x ≠ origin)
    {m n : ℕ+} (hm : x ∈ component m) (hn : x ∈ component n) : m = n := by
  -- Distinct components intersect only in the origin, contradicting `hx`.
  by_contra hmn
  have hinter : x ∈ component m ∩ component n := ⟨hm, hn⟩
  rw [component_inter_component m n hmn] at hinter
  exact hx (Set.mem_singleton_iff.mp hinter)

/-- Helper for Exercise 71.5: a point on the `n`th expanding circle satisfies
the quadratic rank identity defining that circle. -/
lemma component_radius_identity (n : ℕ+) (x : Space) (hx : x ∈ component n) :
    (x : Plane) 0 ^ 2 + (x : Plane) 1 ^ 2 =
      2 * (n : ℝ) * (x : Plane) 0 := by
  -- Square the sphere equation and expand the two Euclidean coordinates.
  have hsphere : dist (x : Plane) (center n) = (n : ℝ) :=
    (mem_circle_iff (x : Plane) n).mp ((mem_component_iff x n).mp hx)
  have hsquare := congrArg (fun z : ℝ ↦ z ^ 2) hsphere
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two] at hsquare
  have hquad :
      ((x : Plane) 0 - (n : ℝ)) ^ 2 + (x : Plane) 1 ^ 2 =
        (n : ℝ) ^ 2 := by
    simpa only [center_apply, Real.dist_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, sub_zero, sq_abs] using hsquare
  nlinarith [hquad]

/-- Helper for Exercise 71.5: every non-origin point of the expanding-circle
union has positive first coordinate. -/
lemma firstCoordinate_pos_of_ne_origin {x : Space} (hx : x ≠ origin) :
    0 < (x : Plane) 0 := by
  -- Choose a containing circle.  Its rank identity makes the first coordinate
  -- nonnegative, while equality would force both coordinates to vanish.
  obtain ⟨n, hxnCircle⟩ := (mem_carrier_iff (x : Plane)).mp x.property
  have hxn : x ∈ component n := (mem_component_iff x n).mpr hxnCircle
  have hrank := component_radius_identity n x hxn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast n.property
  have hx0nonneg : 0 ≤ (x : Plane) 0 := by
    nlinarith [sq_nonneg ((x : Plane) 0), sq_nonneg ((x : Plane) 1)]
  refine lt_of_le_of_ne hx0nonneg ?_
  intro hx0
  have hx0zero : (x : Plane) 0 = 0 := hx0.symm
  have hx1zero : (x : Plane) 1 = 0 := by
    rw [hx0zero] at hrank
    exact sq_eq_zero_iff.mp (by nlinarith [hrank])
  apply hx
  apply Subtype.ext
  rw [origin_coe]
  ext i
  fin_cases i
  · simpa using hx0zero
  · simpa using hx1zero

-- Route correction: replace the opaque designated-point quotient by the
-- kernel quotient of the actual component-representative map.
/-- Helper for Exercise 71.5: forget the component index of a representative. -/
def componentRepresentative : (Σ n : ℕ+, component n) → Space :=
  fun x ↦ x.2

/-- Helper for Exercise 71.5: the coherent model is the kernel quotient of
the component-representative map. -/
abbrev CoherentModel := Quotient (Setoid.ker componentRepresentative)

/-- Helper for Exercise 71.5: include one component in the kernel quotient. -/
def coherentInclusion (n : ℕ+) : component n → CoherentModel :=
  fun x ↦ Quotient.mk'' ⟨n, x⟩

/-- Helper for Exercise 71.5: the image of one component in the coherent
kernel-quotient model. -/
abbrev coherentComponent (n : ℕ+) : Set CoherentModel :=
  Set.range (coherentInclusion n)

/-- Helper for Exercise 71.5: the common point of the coherent component model. -/
def coherentOrigin : CoherentModel :=
  coherentInclusion 1 (componentOrigin 1)

/-- Helper for Exercise 71.5: the coherent component model is inhabited by
its common origin. -/
instance instNonemptyCoherentModel : Nonempty CoherentModel :=
  -- Use the distinguished quotient class shared by all component origins.
  ⟨coherentOrigin⟩

/-- Helper for Exercise 71.5: all component origins have the same kernel class. -/
lemma coherentInclusion_componentOrigin (n : ℕ+) :
    coherentInclusion n (componentOrigin n) = coherentOrigin := by
  -- Both representatives forget to the ambient origin.
  apply Quotient.sound
  rfl

/-- Helper for Exercise 71.5: every kernel-quotient class lies in a component image. -/
lemma iUnion_coherentComponent : ⋃ n, coherentComponent n = Set.univ := by
  -- Choose the component index carried by a sigma representative.
  ext q
  constructor
  · intro _
    exact Set.mem_univ q
  · intro _
    induction q using Quotient.inductionOn with
    | _ x => exact Set.mem_iUnion.mpr ⟨x.1, x.2, rfl⟩

/-- Helper for Exercise 71.5: a component inclusion into the kernel quotient is injective. -/
lemma coherentInclusion_injective (n : ℕ+) :
    Function.Injective (coherentInclusion n) := by
  -- Quotient equality says that the two underlying points of the same
  -- component agree, which is equality in the component subtype.
  intro x y hxy
  apply Subtype.ext
  exact Quotient.exact hxy

/-- Helper for Exercise 71.5: the saturation of a component subset consists
exactly of representatives with the same underlying point as one of its members. -/
lemma componentKernelSaturation (n : ℕ+) (C : Set (component n)) :
    Quotient.mk'' ⁻¹' (coherentInclusion n '' C) =
      {x : Σ k : ℕ+, component k | ∃ c ∈ C, (x.2 : Space) = (c : Space)} := by
  -- Normalize quotient equality with the defining kernel relation.
  ext x
  constructor
  · rintro ⟨c, hc, hcx⟩
    exact ⟨c, hc, (Quotient.exact hcx).symm⟩
  · rintro ⟨c, hc, hxc⟩
    exact ⟨c, hc, Quotient.sound hxc.symm⟩

/-- Helper for Exercise 71.5: each component inclusion is a closed embedding. -/
lemma coherentInclusion_isClosedEmbedding (n : ℕ+) :
    Topology.IsClosedEmbedding (coherentInclusion n) := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
  · -- The inclusion is the quotient map after the continuous sigma injection.
    exact continuous_quotient_mk'.comp continuous_sigmaMk
  · exact coherentInclusion_injective n
  · intro C hC
    -- Test closedness after pulling the image back to the sigma coproduct.
    rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
    change IsClosed (Quotient.mk'' ⁻¹' (coherentInclusion n '' C))
    rw [componentKernelSaturation, isClosed_sigma_iff]
    intro k
    by_cases hkn : k = n
    · subst k
      have hsame :
          Sigma.mk n ⁻¹' {x : Σ k : ℕ+, component k |
              ∃ c ∈ C, (x.2 : Space) = (c : Space)} = C := by
        ext x
        constructor
        · rintro ⟨c, hc, hxc⟩
          have hxc' : x = c := Subtype.ext hxc
          rwa [hxc']
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [hsame]
      exact hC
    · have hsubsingleton :
          (Sigma.mk k ⁻¹' {x : Σ j : ℕ+, component j |
              ∃ c ∈ C, (x.2 : Space) = (c : Space)}).Subsingleton := by
        rintro x ⟨cx, _, hxc⟩ y ⟨cy, _, hyc⟩
        have hxIntersection : (x : Space) ∈ component k ∩ component n :=
          ⟨x.property, hxc.symm ▸ cx.property⟩
        have hyIntersection : (y : Space) ∈ component k ∩ component n :=
          ⟨y.property, hyc.symm ▸ cy.property⟩
        rw [component_inter_component k n hkn] at hxIntersection hyIntersection
        apply Subtype.ext
        exact (Set.mem_singleton_iff.mp hxIntersection).trans
          (Set.mem_singleton_iff.mp hyIntersection).symm
      exact hsubsingleton.finite.isClosed

/-- Helper for Exercise 71.5: distinct kernel-quotient component images meet
only in the common origin class. -/
lemma coherentComponent_inter (m n : ℕ+) (hmn : m ≠ n) :
    coherentComponent m ∩ coherentComponent n = {coherentOrigin} := by
  ext q
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hyx⟩⟩
    have hxy : (x : Space) = (y : Space) := (Quotient.exact hyx).symm
    have hxIntersection : (x : Space) ∈ component m ∩ component n :=
      ⟨x.property, hxy.symm ▸ y.property⟩
    have hxOrigin : (x : Space) = origin := by
      rw [component_inter_component m n hmn] at hxIntersection
      exact Set.mem_singleton_iff.mp hxIntersection
    rw [Set.mem_singleton_iff, ← coherentInclusion_componentOrigin m]
    exact congrArg (coherentInclusion m) (Subtype.ext hxOrigin)
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    exact ⟨⟨componentOrigin m, coherentInclusion_componentOrigin m⟩,
      ⟨componentOrigin n, coherentInclusion_componentOrigin n⟩⟩

/-- Helper for Exercise 71.5: the quotient topology is coherent with its
component images. -/
lemma coherentModel_isCoherentWith :
    Topology.IsCoherentWith (Set.range coherentComponent) := by
  apply Topology.IsCoherentWith.of_isClosed
  intro D hD
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage, isClosed_sigma_iff]
  intro n
  have himage : coherentComponent n ∈ Set.range coherentComponent := ⟨n, rfl⟩
  have hrestricted := hD (coherentComponent n) himage
  have hemb := coherentInclusion_isClosedEmbedding n
  have hpreimage : IsClosed (coherentInclusion n ⁻¹' D) := by
    simpa only [coherentComponent, Topology.IsEmbedding.toHomeomorph_apply_coe,
      Set.preimage_preimage, Function.comp_def] using
      hemb.isEmbedding.toHomeomorph.isClosed_preimage.mpr hrestricted
  exact hpreimage

/-- Helper for Exercise 71.5: the component images make the kernel quotient a
wedge of circles. -/
lemma coherentModel_isWedgeOfCircles :
    Topology.IsWedgeOfCircles coherentComponent coherentOrigin := by
  -- Assemble the cover, circle coordinates, intersection law, and coherence.
  apply Topology.IsWedgeOfCircles.of
  · exact iUnion_coherentComponent
  · intro n
    exact ⟨(coherentInclusion_isClosedEmbedding n).isEmbedding.toHomeomorph.symm.trans
      (componentCoordinate n)⟩
  · exact fun m n hmn ↦ coherentComponent_inter m n hmn
  · exact coherentModel_isCoherentWith

/-- Helper for Exercise 71.5: the coherent model carries its canonical wedge
of circles instance. -/
instance instCoherentModelIsWedgeOfCircles :
    Topology.IsWedgeOfCircles coherentComponent coherentOrigin :=
  coherentModel_isWedgeOfCircles

/-- Helper for Exercise 71.5: forgetting the component index is continuous on
the sigma coproduct of expanding components. -/
lemma continuous_coherentRepresentative :
    Continuous (fun x : Σ n : ℕ+, component n ↦ (x.2 : Space)) := by
  -- Continuity on a sigma coproduct is checked independently on each factor.
  apply continuous_sigma
  intro n
  exact continuous_subtype_val

/-- Helper for Exercise 71.5: the canonical comparison from the coherent
quotient to the planar union. -/
def coherentComparison : C(CoherentModel, Space) :=
  ⟨Setoid.kerLift componentRepresentative,
    continuous_coherentRepresentative.quotient_lift (fun _ _ hxy ↦ hxy)⟩

/-- Helper for Exercise 71.5: the canonical comparison restricts to the
ordinary inclusion on every expanding component. -/
lemma coherentComparison_inclusion (n : ℕ+) (x : component n) :
    coherentComparison (coherentInclusion n x) = (x : Space) := by
  -- Compute the kernel lift on the chosen representative.
  exact Setoid.kerLift_mk componentRepresentative ⟨n, x⟩

/-- Helper for Exercise 71.5: the canonical coherent comparison preserves the
common basepoint. -/
lemma coherentComparison_origin : coherentComparison coherentOrigin = origin := by
  -- Represent the coherent origin in the first component and apply the
  -- comparison's factor computation.
  rw [← coherentInclusion_componentOrigin 1,
    coherentComparison_inclusion]

/-- Helper for Exercise 71.5: the canonical coherent comparison is bijective. -/
lemma coherentComparison_bijective : Function.Bijective coherentComparison := by
  constructor
  · -- A lift through its own kernel is injective.
    exact Setoid.kerLift_injective componentRepresentative
  · intro y
    -- Choose any component containing the planar point and use its quotient class.
    obtain ⟨n, hyn⟩ := (mem_carrier_iff (y : Plane)).mp y.property
    let x : component n := ⟨y, (mem_component_iff y n).mpr hyn⟩
    refine ⟨coherentInclusion n x, ?_⟩
    exact coherentComparison_inclusion n x

/-- Helper for Exercise 71.5: there is a continuous bijective comparison from
the coherent component quotient to the planar union, computing as the ordinary
inclusion on every factor. -/
lemma exists_coherentComparison :
    ∃ comparison : C(CoherentModel, Space),
      Function.Bijective comparison ∧
        ∀ (n : ℕ+) (x : component n),
          comparison (coherentInclusion n x) = (x : Space) := by
  -- Package the canonical quotient lift with its bijectivity and factor formula.
  exact ⟨coherentComparison, coherentComparison_bijective,
    coherentComparison_inclusion⟩

/-- Helper for Exercise 71.5: one component is homeomorphic to its image in
the coherent quotient model. -/
noncomputable def coherentComponentHomeomorph (n : ℕ+) :
    component n ≃ₜ coherentComponent n :=
  (coherentInclusion_isClosedEmbedding n).isEmbedding.toHomeomorph

/-- Helper for Exercise 71.5: the common point as an element of one coherent
component image. -/
abbrev coherentComponentOrigin (n : ℕ+) : coherentComponent n :=
  ⟨coherentOrigin, Topology.IsWedgeOfCircles.mem_basepoint n⟩

/-- Helper for Exercise 71.5: the component homeomorphism preserves the
chosen common point. -/
lemma coherentComponentHomeomorph_origin (n : ℕ+) :
    coherentComponentHomeomorph n (componentOrigin n) =
      coherentComponentOrigin n := by
  -- Equality in the range subtype follows from the factor-inclusion formula.
  apply Subtype.ext
  rw [coherentComponentHomeomorph,
    Topology.IsEmbedding.toHomeomorph_apply_coe,
    coherentInclusion_componentOrigin]

/-- Helper for Exercise 71.5: a component generator transported to the
corresponding circle in the coherent quotient model. -/
noncomputable def coherentGeneratorLoop
    (f : ∀ n : ℕ+, Path (componentOrigin n) (componentOrigin n))
    (n : ℕ+) :
    Path (coherentComponentOrigin n) (coherentComponentOrigin n) :=
  ((f n).map (coherentComponentHomeomorph n).continuous).cast
    (coherentComponentHomeomorph_origin n).symm
    (coherentComponentHomeomorph_origin n).symm

/-- Helper for Exercise 71.5: transporting a component loop through its image
homeomorphism commutes with the induced fundamental-group map. -/
lemma coherentGeneratorLoop_fromPath
    (f : ∀ n : ℕ+, Path (componentOrigin n) (componentOrigin n))
    (n : ℕ+) :
    FundamentalGroup.mapOfEq ⟨coherentComponentHomeomorph n,
        (coherentComponentHomeomorph n).continuous⟩
        (coherentComponentHomeomorph_origin n)
        (FundamentalGroup.fromPath (mk (f n))) =
      FundamentalGroup.fromPath (mk (coherentGeneratorLoop f n)) := by
  -- Expand the induced map, then identify its mapped-and-cast representative.
  rw [FundamentalGroup.mapOfEq_apply, ← mk_map, ← mk_cast]
  rfl

/-- Helper for Exercise 71.5: a cyclic component generator remains a
generator after transport to the coherent component image. -/
lemma coherentGeneratorLoop_zpowers_eq_top
    (f : ∀ n : ℕ+, Path (componentOrigin n) (componentOrigin n))
    (hf : ∀ n : ℕ+,
      Subgroup.zpowers (FundamentalGroup.fromPath (mk (f n))) = ⊤)
    (n : ℕ+) :
    Subgroup.zpowers
        (FundamentalGroup.fromPath (mk (coherentGeneratorLoop f n))) = ⊤ := by
  let φ := FundamentalGroup.mapOfEq
    ⟨coherentComponentHomeomorph n, (coherentComponentHomeomorph n).continuous⟩
    (coherentComponentHomeomorph_origin n)
  have hφSurjective : Function.Surjective φ := by
    -- A homeomorphism is a homotopy equivalence, so its fundamental-group map is onto.
    exact (ContinuousMap.HomotopyEquiv.fundamentalGroupMapOfEq_bijective
      (coherentComponentHomeomorph n).toHomotopyEquiv
      (componentOrigin n) (coherentComponentOrigin n)
      (coherentComponentHomeomorph_origin n)).2
  have hmap :
      (Subgroup.zpowers (FundamentalGroup.fromPath (mk (f n)))).map φ = ⊤ := by
    -- Surjectivity sends the top subgroup to the top subgroup.
    rw [hf n]
    exact Subgroup.map_top_of_surjective φ hφSurjective
  -- Rewrite the image of a cyclic subgroup and compute the transported generator.
  rw [MonoidHom.map_zpowers, coherentGeneratorLoop_fromPath] at hmap
  exact hmap

/-- Helper for Exercise 71.5: the real pinch coordinate collapses the first
quarter to `0`, expands the middle half linearly, and collapses the last
quarter to `1`. -/
private noncomputable def circlePinchCoordinate (x : ℝ) : ℝ :=
  (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * x - 1 / 2) : ℝ)

/-- Helper for Exercise 71.5: the real pinch coordinate is continuous. -/
private lemma continuous_circlePinchCoordinate :
    Continuous circlePinchCoordinate := by
  -- Compose the affine middle-coordinate function with projection onto `[0,1]`.
  exact continuous_subtype_val.comp
    (continuous_projIcc.comp
      ((continuous_const.mul continuous_id).sub continuous_const))

/-- Helper for Exercise 71.5: the first quarter of the parameter interval is
sent to its left endpoint by the pinch coordinate. -/
private lemma circlePinchCoordinate_eq_zero_of_le {x : ℝ} (hx : x ≤ 1 / 4) :
    circlePinchCoordinate x = 0 := by
  -- The affine argument lies to the left of the projected interval.
  have hlinear : 2 * x - 1 / 2 ≤ 0 := by
    linarith
  rw [circlePinchCoordinate, Set.projIcc_of_le_left zero_le_one hlinear]

/-- Helper for Exercise 71.5: the last quarter of the parameter interval is
sent to its right endpoint by the pinch coordinate. -/
private lemma circlePinchCoordinate_eq_one_of_le {x : ℝ} (hx : 3 / 4 ≤ x) :
    circlePinchCoordinate x = 1 := by
  -- The affine argument lies to the right of the projected interval.
  have hlinear : 1 ≤ 2 * x - 1 / 2 := by
    linarith
  rw [circlePinchCoordinate, Set.projIcc_of_right_le zero_le_one hlinear]

/-- Helper for Exercise 71.5: the pinch coordinate fixes the left endpoint. -/
private lemma circlePinchCoordinate_zero : circlePinchCoordinate 0 = 0 := by
  -- Zero lies in the collapsed first quarter.
  have hquarter : (0 : ℝ) ≤ 1 / 4 := by
    norm_num
  exact circlePinchCoordinate_eq_zero_of_le hquarter

/-- Helper for Exercise 71.5: the pinch coordinate fixes the right endpoint. -/
private lemma circlePinchCoordinate_one : circlePinchCoordinate 1 = 1 := by
  -- One lies in the collapsed last quarter.
  have hquarter : (3 / 4 : ℝ) ≤ 1 := by
    norm_num
  exact circlePinchCoordinate_eq_one_of_le hquarter

/-- Helper for Exercise 71.5: the pinched coordinate stays in the closed unit
interval and grows by at most a factor of two from the left endpoint. -/
private lemma circlePinchCoordinate_bounds_left {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ circlePinchCoordinate x ∧ circlePinchCoordinate x ≤ 1 ∧
      circlePinchCoordinate x ≤ 2 * x := by
  -- The first two bounds are the range of `projIcc`; split at the two clamp
  -- thresholds for the quantitative third bound.
  have hrange : circlePinchCoordinate x ∈ Set.Icc (0 : ℝ) 1 := by
    exact (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * x - 1 / 2)).property
  refine ⟨hrange.1, hrange.2, ?_⟩
  by_cases hleft : x ≤ 1 / 4
  · rw [circlePinchCoordinate_eq_zero_of_le hleft]
    linarith
  by_cases hright : 3 / 4 ≤ x
  · rw [circlePinchCoordinate_eq_one_of_le hright]
    linarith
  · have hmiddle : 2 * x - 1 / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith
    rw [circlePinchCoordinate, Set.projIcc_of_mem zero_le_one hmiddle]
    linarith

/-- Helper for Exercise 71.5: measured from the right endpoint, the pinched
coordinate also grows by at most a factor of two. -/
private lemma circlePinchCoordinate_bounds_right {x : ℝ} (hx : x ≤ 1) :
    2 * x - 1 ≤ circlePinchCoordinate x := by
  -- Again split at the clamp thresholds; in the middle the projection is the
  -- affine expression itself.
  by_cases hleft : x ≤ 1 / 4
  · rw [circlePinchCoordinate_eq_zero_of_le hleft]
    linarith
  by_cases hright : 3 / 4 ≤ x
  · rw [circlePinchCoordinate_eq_one_of_le hright]
    linarith
  · have hmiddle : 2 * x - 1 / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith
    rw [circlePinchCoordinate, Set.projIcc_of_mem zero_le_one hmiddle]
    linarith

/-- Helper for Exercise 71.5: linear interpolation from the identity coordinate
to the pinched coordinate. -/
private noncomputable def circlePinchCoordinateHomotopy (p : unitInterval × ℝ) : ℝ :=
  (1 - (p.1 : ℝ)) * p.2 + (p.1 : ℝ) * circlePinchCoordinate p.2

/-- Helper for Exercise 71.5: the coordinate interpolation is jointly continuous. -/
private lemma continuous_circlePinchCoordinateHomotopy :
    Continuous circlePinchCoordinateHomotopy := by
  -- Continuity follows from the time coordinate, the spatial coordinate, and
  -- the already continuous clamp.
  have ht : Continuous (fun p : unitInterval × ℝ ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  exact ((continuous_const.sub ht).mul continuous_snd).add
    (ht.mul (continuous_circlePinchCoordinate.comp continuous_snd))

/-- Helper for Exercise 71.5: the coordinate interpolation starts at the identity. -/
private lemma circlePinchCoordinateHomotopy_zero (x : ℝ) :
    circlePinchCoordinateHomotopy (0, x) = x := by
  -- At time zero only the identity summand remains.
  simp [circlePinchCoordinateHomotopy]

/-- Helper for Exercise 71.5: the coordinate interpolation ends at the pinch. -/
private lemma circlePinchCoordinateHomotopy_one (x : ℝ) :
    circlePinchCoordinateHomotopy (1, x) = circlePinchCoordinate x := by
  -- At time one only the pinched-coordinate summand remains.
  simp [circlePinchCoordinateHomotopy]

/-- Helper for Exercise 71.5: every interpolation slice fixes the left endpoint. -/
private lemma circlePinchCoordinateHomotopy_left (t : unitInterval) :
    circlePinchCoordinateHomotopy (t, 0) = 0 := by
  -- Both the identity coordinate and the pinched coordinate vanish at zero.
  simp [circlePinchCoordinateHomotopy, circlePinchCoordinate_zero]

/-- Helper for Exercise 71.5: every interpolation slice fixes the right endpoint. -/
private lemma circlePinchCoordinateHomotopy_right (t : unitInterval) :
    circlePinchCoordinateHomotopy (t, 1) = 1 := by
  -- Both endpoint coordinates equal one, so their affine interpolation is one.
  rw [circlePinchCoordinateHomotopy, circlePinchCoordinate_one]
  simp only [mul_one]
  have ht : (t : ℝ) ∈ Set.Icc 0 1 := t.property
  linarith

/-- Helper for Exercise 71.5: every interpolation slice is uniformly
controlled from both endpoints of the parameter interval. -/
private lemma circlePinchCoordinateHomotopy_bounds (t : unitInterval)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ circlePinchCoordinateHomotopy (t, x) ∧
      circlePinchCoordinateHomotopy (t, x) ≤ 1 ∧
      circlePinchCoordinateHomotopy (t, x) ≤ 2 * x ∧
      2 * x - 1 ≤ circlePinchCoordinateHomotopy (t, x) := by
  -- Both the identity and pinch coordinates satisfy the endpoint bounds, and
  -- the homotopy is their convex interpolation.
  obtain ⟨hc0, hc1, hc2⟩ := circlePinchCoordinate_bounds_left hx.1
  have hc3 := circlePinchCoordinate_bounds_right hx.2
  have ht0 : 0 ≤ (t : ℝ) := t.property.1
  have ht1 : (t : ℝ) ≤ 1 := t.property.2
  have hweight : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr ht1
  rw [circlePinchCoordinateHomotopy]
  constructor
  · exact add_nonneg (mul_nonneg hweight hx.1) (mul_nonneg ht0 hc0)
  constructor
  · calc
      (1 - (t : ℝ)) * x + (t : ℝ) * circlePinchCoordinate x ≤
          (1 - (t : ℝ)) * 1 + (t : ℝ) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 hweight)
          (mul_le_mul_of_nonneg_left hc1 ht0)
      _ = 1 := by ring
  constructor
  · calc
      (1 - (t : ℝ)) * x + (t : ℝ) * circlePinchCoordinate x ≤
          (1 - (t : ℝ)) * (2 * x) + (t : ℝ) * (2 * x) :=
        add_le_add (mul_le_mul_of_nonneg_left (by linarith) hweight)
          (mul_le_mul_of_nonneg_left hc2 ht0)
      _ = 2 * x := by ring
  · calc
      2 * x - 1 =
          (1 - (t : ℝ)) * (2 * x - 1) + (t : ℝ) * (2 * x - 1) := by
        ring
      _ ≤ (1 - (t : ℝ)) * x + (t : ℝ) * circlePinchCoordinate x :=
        add_le_add (mul_le_mul_of_nonneg_left (by linarith) hweight)
          (mul_le_mul_of_nonneg_left hc3 ht0)

/-- Helper for Exercise 71.5: the closed unit interval covers the additive
circle by identifying its endpoints. -/
private def unitIntervalToAddCircle (x : unitInterval) : UnitAddCircle :=
  ((x : ℝ) : UnitAddCircle)

/-- Helper for Exercise 71.5: the closed-interval map to the additive circle
is continuous. -/
private lemma continuous_unitIntervalToAddCircle :
    Continuous unitIntervalToAddCircle := by
  -- Compose the interval inclusion with the additive quotient map.
  exact (AddCircle.continuous_mk' 1).comp continuous_subtype_val

/-- Helper for Exercise 71.5: every additive-circle point has a representative
in the closed unit interval. -/
private lemma unitIntervalToAddCircle_surjective :
    Function.Surjective unitIntervalToAddCircle := by
  intro z
  -- Use the standard closed-interval image formula for `AddCircle 1`.
  have hz : z ∈ ((fun x : ℝ ↦ (x : UnitAddCircle)) '' Set.Icc 0 (0 + 1)) := by
    rw [AddCircle.coe_image_Icc_eq 1 0]
    exact Set.mem_univ z
  obtain ⟨x, hx, rfl⟩ := hz
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [zero_add] using hx
  exact ⟨⟨x, hx'⟩, rfl⟩

/-- Helper for Exercise 71.5: the closed-interval parametrization of the
additive circle is a quotient map. -/
private lemma unitIntervalToAddCircle_isQuotientMap :
    Topology.IsQuotientMap unitIntervalToAddCircle := by
  -- Compact-to-Hausdorff continuous surjections are quotient maps.
  exact Topology.IsQuotientMap.of_surjective_continuous
    unitIntervalToAddCircle_surjective continuous_unitIntervalToAddCircle

/-- Helper for Exercise 71.5: the interpolated coordinate, descended through
the half-open representative of `UnitAddCircle`. -/
private noncomputable def addCirclePinchHomotopyValue
    (p : unitInterval × UnitAddCircle) : UnitAddCircle :=
  AddCircle.liftIco 1 0
    (fun x : ℝ ↦ (circlePinchCoordinateHomotopy (p.1, x) : UnitAddCircle)) p.2

/-- Helper for Exercise 71.5: evaluating the descended interpolation on a
closed-interval representative recovers the coordinate formula. -/
private lemma addCirclePinchHomotopyValue_unitInterval
    (t x : unitInterval) :
    addCirclePinchHomotopyValue (t, unitIntervalToAddCircle x) =
      (circlePinchCoordinateHomotopy (t, (x : ℝ)) : UnitAddCircle) := by
  by_cases hx : x = 1
  · subst x
    -- The two interval endpoints agree in the quotient, and the interpolation
    -- fixes both of them.
    have hzeroIco : (0 : ℝ) ∈ Set.Ico 0 1 := by
      norm_num
    unfold addCirclePinchHomotopyValue
    simp only [unitIntervalToAddCircle]
    rw [AddCircle.coe_period]
    calc
      AddCircle.liftIco 1 0
          (fun x : ℝ ↦ (circlePinchCoordinateHomotopy (t, x) : UnitAddCircle)) 0 =
          (circlePinchCoordinateHomotopy (t, 0) : UnitAddCircle) :=
        by
          simpa only [AddCircle.coe_zero] using
            (AddCircle.liftIco_zero_coe_apply hzeroIco)
      _ = (circlePinchCoordinateHomotopy (t, 1) : UnitAddCircle) := by
        rw [circlePinchCoordinateHomotopy_left,
          circlePinchCoordinateHomotopy_right, AddCircle.coe_period,
          AddCircle.coe_zero]
  · have hxlt : (x : ℝ) < 1 := by
      exact lt_of_le_of_ne x.property.2 (fun h ↦ hx (Subtype.ext h))
    have hxIco : (x : ℝ) ∈ Set.Ico 0 1 := ⟨x.property.1, hxlt⟩
    -- Away from the upper endpoint, `liftIco` uses the displayed representative.
    unfold addCirclePinchHomotopyValue
    simp only [unitIntervalToAddCircle]
    rw [AddCircle.liftIco_zero_coe_apply hxIco]

/-- Helper for Exercise 71.5: the additive-circle pinch interpolation is
jointly continuous in time and space. -/
private lemma continuous_addCirclePinchHomotopyValue :
    Continuous addCirclePinchHomotopyValue := by
  -- Test continuity after the quotient map from the closed interval on the
  -- spatial factor; there the map is the explicit coordinate interpolation.
  apply unitIntervalToAddCircle_isQuotientMap.continuous_lift_prod_right
  have hparameters : Continuous (fun p : unitInterval × unitInterval ↦
      (p.1, (p.2 : ℝ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hcoordinate : Continuous (fun p : unitInterval × unitInterval ↦
      (circlePinchCoordinateHomotopy (p.1, (p.2 : ℝ)) : UnitAddCircle)) :=
    (AddCircle.continuous_mk' 1).comp
      (continuous_circlePinchCoordinateHomotopy.comp hparameters)
  exact hcoordinate.congr fun p ↦
    (addCirclePinchHomotopyValue_unitInterval p.1 p.2).symm

/-- Helper for Exercise 71.5: the terminal additive-circle pinch is continuous. -/
private lemma continuous_addCirclePinch :
    Continuous (fun z : UnitAddCircle ↦ addCirclePinchHomotopyValue (1, z)) := by
  -- Restrict the jointly continuous interpolation to its time-one slice.
  exact continuous_addCirclePinchHomotopyValue.comp
    (continuous_const.prodMk continuous_id)

/-- Helper for Exercise 71.5: the terminal self-map of the additive circle. -/
private noncomputable def addCirclePinch : C(UnitAddCircle, UnitAddCircle) :=
  ⟨fun z ↦ addCirclePinchHomotopyValue (1, z), continuous_addCirclePinch⟩

/-- Helper for Exercise 71.5: the descended interpolation starts at the
identity on the additive circle. -/
private lemma addCirclePinchHomotopyValue_zero (z : UnitAddCircle) :
    addCirclePinchHomotopyValue (0, z) = z := by
  -- Choose a closed-interval representative and use the coordinate zero-time law.
  obtain ⟨x, rfl⟩ := unitIntervalToAddCircle_surjective z
  rw [addCirclePinchHomotopyValue_unitInterval,
    circlePinchCoordinateHomotopy_zero]
  rfl

/-- Helper for Exercise 71.5: the descended interpolation ends at the
additive-circle pinch. -/
private lemma addCirclePinchHomotopyValue_one (z : UnitAddCircle) :
    addCirclePinchHomotopyValue (1, z) = addCirclePinch z := by
  -- The terminal map was defined by this time-one slice.
  rfl

/-- Helper for Exercise 71.5: every descended interpolation slice fixes the
additive-circle basepoint. -/
private lemma addCirclePinchHomotopyValue_basepoint (t : unitInterval) :
    addCirclePinchHomotopyValue (t, 0) = 0 := by
  -- Represent the basepoint by the left endpoint, which every coordinate
  -- interpolation slice fixes.
  have hparam : unitIntervalToAddCircle 0 = (0 : UnitAddCircle) := by
    rfl
  calc
    addCirclePinchHomotopyValue (t, 0) =
        addCirclePinchHomotopyValue (t, unitIntervalToAddCircle 0) :=
      congrArg (fun z ↦ addCirclePinchHomotopyValue (t, z)) hparam.symm
    _ = (circlePinchCoordinateHomotopy (t, ((0 : unitInterval) : ℝ)) :
        UnitAddCircle) := addCirclePinchHomotopyValue_unitInterval t 0
    _ = 0 := by
      rw [Set.Icc.coe_zero, circlePinchCoordinateHomotopy_left,
        AddCircle.coe_zero]

/-- Helper for Exercise 71.5: the additive-circle pinch homotopy moves points
at most twice as far from the basepoint in the quotient norm. -/
private lemma addCirclePinchHomotopyValue_norm_le (t : unitInterval)
    (z : UnitAddCircle) :
    ‖addCirclePinchHomotopyValue (t, z)‖ ≤ 2 * ‖z‖ := by
  -- Use the standard representative and estimate from its nearer endpoint.
  obtain ⟨x, rfl⟩ := unitIntervalToAddCircle_surjective z
  rw [addCirclePinchHomotopyValue_unitInterval]
  simp only [unitIntervalToAddCircle]
  let y := circlePinchCoordinateHomotopy (t, (x : ℝ))
  have hy := circlePinchCoordinateHomotopy_bounds t x.property
  change ‖(y : UnitAddCircle)‖ ≤ 2 * ‖((x : ℝ) : UnitAddCircle)‖
  by_cases hx : (x : ℝ) ≤ 1 / 2
  · have hxabs : |(x : ℝ)| ≤ |(1 : ℝ)| / 2 := by
      rw [abs_of_nonneg x.property.1, abs_one]
      exact hx
    have hnorm : ‖((x : ℝ) : UnitAddCircle)‖ = |(x : ℝ)| :=
      (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr hxabs
    rw [hnorm, abs_of_nonneg x.property.1]
    calc
      ‖(y : UnitAddCircle)‖ ≤ ‖y‖ := QuotientAddGroup.norm_mk_le_norm
      _ = y := by rw [Real.norm_eq_abs, abs_of_nonneg hy.1]
      _ ≤ 2 * (x : ℝ) := hy.2.2.1
  · have hxhalf : 1 / 2 < (x : ℝ) := lt_of_not_ge hx
    have hxshift : |(x : ℝ) - 1| ≤ |(1 : ℝ)| / 2 := by
      rw [abs_one, abs_of_nonpos (sub_nonpos.mpr x.property.2)]
      linarith
    have hnormShift : ‖(((x : ℝ) - 1 : ℝ) : UnitAddCircle)‖ =
        |(x : ℝ) - 1| :=
      (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr hxshift
    have hxperiod : ((x : ℝ) : UnitAddCircle) =
        (((x : ℝ) - 1 : ℝ) : UnitAddCircle) := by
      simpa only [sub_add_cancel] using
        AddCircle.coe_add_period (1 : ℝ) ((x : ℝ) - 1)
    have hyperiod : (y : UnitAddCircle) = ((y - 1 : ℝ) : UnitAddCircle) := by
      simpa only [sub_add_cancel] using AddCircle.coe_add_period (1 : ℝ) (y - 1)
    rw [hxperiod, hnormShift,
      abs_of_nonpos (sub_nonpos.mpr x.property.2), hyperiod]
    calc
      ‖((y - 1 : ℝ) : UnitAddCircle)‖ ≤ ‖y - 1‖ :=
        QuotientAddGroup.norm_mk_le_norm
      _ = 1 - y := by
        rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hy.2.1)]
        ring
      _ ≤ 2 * (1 - (x : ℝ)) := by linarith [hy.2.2.2]
      _ = 2 * (-(x - 1)) := by ring

/-- Helper for Exercise 71.5: the terminal additive-circle pinch collapses
the open quarter-ball about the basepoint. -/
private lemma addCirclePinch_eq_zero_of_norm_lt (z : UnitAddCircle)
    (hz : ‖z‖ < 1 / 4) : addCirclePinch z = 0 := by
  -- Choose the standard representative and split according to which endpoint
  -- realizes its quotient norm.
  obtain ⟨x, rfl⟩ := unitIntervalToAddCircle_surjective z
  have hz' : ‖(((x : ℝ) : UnitAddCircle))‖ < 1 / 4 := by
    simpa only [unitIntervalToAddCircle] using hz
  rw [← addCirclePinchHomotopyValue_one,
    addCirclePinchHomotopyValue_unitInterval,
    circlePinchCoordinateHomotopy_one]
  by_cases hx : (x : ℝ) ≤ 1 / 2
  · have hxabs : |(x : ℝ)| ≤ |(1 : ℝ)| / 2 := by
      rw [abs_of_nonneg x.property.1, abs_one]
      exact hx
    have hnorm : ‖((x : ℝ) : UnitAddCircle)‖ = |(x : ℝ)| :=
      (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr hxabs
    have hxquarter : (x : ℝ) ≤ 1 / 4 := by
      rw [hnorm, abs_of_nonneg x.property.1] at hz'
      exact hz'.le
    rw [circlePinchCoordinate_eq_zero_of_le hxquarter, AddCircle.coe_zero]
  · have hxhalf : 1 / 2 < (x : ℝ) := lt_of_not_ge hx
    have hxshift : |(x : ℝ) - 1| ≤ |(1 : ℝ)| / 2 := by
      rw [abs_one, abs_of_nonpos (sub_nonpos.mpr x.property.2)]
      linarith
    have hnormShift : ‖(((x : ℝ) - 1 : ℝ) : UnitAddCircle)‖ =
        |(x : ℝ) - 1| :=
      (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr hxshift
    have hperiod : ((x : ℝ) : UnitAddCircle) =
        (((x : ℝ) - 1 : ℝ) : UnitAddCircle) := by
      simpa only [sub_add_cancel] using
        AddCircle.coe_add_period (1 : ℝ) ((x : ℝ) - 1)
    have hxquarter : 3 / 4 ≤ (x : ℝ) := by
      rw [hperiod, hnormShift,
        abs_of_nonpos (sub_nonpos.mpr x.property.2)] at hz'
      linarith
    rw [circlePinchCoordinate_eq_one_of_le hxquarter, AddCircle.coe_period]

/-- Helper for Exercise 71.5: the descended interpolation is a homotopy from
the identity to the additive-circle pinch. -/
private noncomputable def addCirclePinchHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id UnitAddCircle) addCirclePinch :=
  { toFun := addCirclePinchHomotopyValue
    continuous_toFun := continuous_addCirclePinchHomotopyValue
    map_zero_left := addCirclePinchHomotopyValue_zero
    map_one_left := addCirclePinchHomotopyValue_one }

/-- Helper for Exercise 71.5: the additive-circle pinch homotopy is fixed at
the additive basepoint. -/
private lemma addCirclePinchHomotopy_fixed (t : unitInterval)
    (z : UnitAddCircle) (hz : z ∈ ({0} : Set UnitAddCircle)) :
    addCirclePinchHomotopy (t, z) = (ContinuousMap.id UnitAddCircle) z := by
  -- Membership in the singleton reduces the claim to the fixed-basepoint law.
  rw [Set.mem_singleton_iff] at hz
  subst z
  exact addCirclePinchHomotopyValue_basepoint t

/-- Helper for Exercise 71.5: a based homotopy from the additive-circle
identity to the controlled pinch. -/
private noncomputable def addCirclePinchHomotopyRel :
    ContinuousMap.HomotopyRel (ContinuousMap.id UnitAddCircle)
      addCirclePinch {0} :=
  { toHomotopy := addCirclePinchHomotopy
    prop' := addCirclePinchHomotopy_fixed }

/-- Helper for Exercise 71.5: the canonical homeomorphism from the additive
unit circle to the complex unit circle. -/
private noncomputable def unitAddCircleHomeomorphCircle :
    UnitAddCircle ≃ₜ Circle :=
  AddCircle.homeomorphCircle one_ne_zero

/-- Helper for Exercise 71.5: the canonical additive-circle homeomorphism
sends its zero class to `1 : Circle`. -/
private lemma unitAddCircleHomeomorphCircle_zero :
    unitAddCircleHomeomorphCircle 0 = (1 : Circle) := by
  -- Evaluate the standard exponential coordinate at the additive zero class.
  rw [unitAddCircleHomeomorphCircle, AddCircle.homeomorphCircle_apply]
  exact AddCircle.toCircle_zero

/-- Helper for Exercise 71.5: angular distance after the standard
additive-to-complex circle coordinate is `2π` times the quotient norm. -/
private lemma angle_unitAddCircleHomeomorphCircle (z : UnitAddCircle) :
    InnerProductGeometry.angle (unitAddCircleHomeomorphCircle z : ℂ) 1 =
      2 * Real.pi * ‖z‖ := by
  -- Choose the representative in `(-1/2, 1/2]`, where both the quotient norm
  -- and the principal complex angle have their unreduced formulas.
  let x := AddCircle.equivIoc (1 : ℝ) (-1 / 2) z
  have hxcoe : ((x : ℝ) : UnitAddCircle) = z := AddCircle.coe_equivIoc
  have hxinterval : (x : ℝ) ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2) := by
    have hx := x.property
    norm_num at hx ⊢
    exact hx
  have hxabs : |(x : ℝ)| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_one, abs_le]
    constructor <;> linarith [hxinterval.1, hxinterval.2]
  have hnorm : ‖((x : ℝ) : UnitAddCircle)‖ = |(x : ℝ)| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr hxabs
  have hangleInterval : 2 * Real.pi * (x : ℝ) ∈
      Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    constructor
    · nlinarith [Real.pi_pos, hxinterval.1]
    · nlinarith [Real.pi_pos, hxinterval.2]
  have hmod : toIocMod Real.two_pi_pos (-Real.pi)
      (2 * Real.pi * (x : ℝ)) = 2 * Real.pi * (x : ℝ) :=
    (toIocMod_eq_self Real.two_pi_pos).mpr hangleInterval
  rw [← hxcoe, unitAddCircleHomeomorphCircle,
    AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
    div_one, Circle.coe_exp, Complex.angle_exp_one, hmod, hnorm]
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]

/-- Helper for Exercise 71.5: the forward additive-to-complex circle
homeomorphism as a bundled continuous map. -/
private noncomputable def unitAddCircleToCircle : C(UnitAddCircle, Circle) :=
  ⟨unitAddCircleHomeomorphCircle, unitAddCircleHomeomorphCircle.continuous⟩

/-- Helper for Exercise 71.5: the inverse complex-to-additive circle
homeomorphism as a bundled continuous map. -/
private noncomputable def circleToUnitAddCircle : C(Circle, UnitAddCircle) :=
  ⟨unitAddCircleHomeomorphCircle.symm,
    unitAddCircleHomeomorphCircle.symm.continuous⟩

/-- Helper for Exercise 71.5: the controlled pinch transported to the complex
unit circle. -/
private noncomputable def circlePinch : C(Circle, Circle) :=
  unitAddCircleToCircle.comp (addCirclePinch.comp circleToUnitAddCircle)

/-- Helper for Exercise 71.5: the additive pinch interpolation conjugated to
the complex unit circle. -/
private noncomputable def circlePinchHomotopyValue
    (p : unitInterval × Circle) : Circle :=
  unitAddCircleHomeomorphCircle
    (addCirclePinchHomotopyValue
      (p.1, unitAddCircleHomeomorphCircle.symm p.2))

/-- Helper for Exercise 71.5: the complex-circle pinch interpolation is
jointly continuous. -/
private lemma continuous_circlePinchHomotopyValue :
    Continuous circlePinchHomotopyValue := by
  -- Precompose spatially with the inverse homeomorphism, apply the additive
  -- homotopy, and postcompose with the forward homeomorphism.
  have hparameters : Continuous (fun p : unitInterval × Circle ↦
      (p.1, unitAddCircleHomeomorphCircle.symm p.2)) :=
    continuous_fst.prodMk
      (unitAddCircleHomeomorphCircle.symm.continuous.comp continuous_snd)
  exact unitAddCircleHomeomorphCircle.continuous.comp
    (continuous_addCirclePinchHomotopyValue.comp hparameters)

/-- Helper for Exercise 71.5: the complex-circle interpolation starts at the
identity. -/
private lemma circlePinchHomotopyValue_zero (z : Circle) :
    circlePinchHomotopyValue (0, z) = z := by
  -- Apply the additive zero-time law and cancel the homeomorphism pair.
  rw [circlePinchHomotopyValue, addCirclePinchHomotopyValue_zero,
    unitAddCircleHomeomorphCircle.apply_symm_apply]

/-- Helper for Exercise 71.5: the complex-circle interpolation ends at the
transported pinch. -/
private lemma circlePinchHomotopyValue_one (z : Circle) :
    circlePinchHomotopyValue (1, z) = circlePinch z := by
  -- Both sides are the conjugated time-one additive pinch.
  rw [circlePinchHomotopyValue, addCirclePinchHomotopyValue_one]
  rfl

/-- Helper for Exercise 71.5: every complex-circle interpolation slice fixes
the basepoint `1`. -/
private lemma circlePinchHomotopyValue_basepoint (t : unitInterval) :
    circlePinchHomotopyValue (t, 1) = (1 : Circle) := by
  -- Pull `1` back to the additive zero class, use its fixed-point law, and
  -- transport zero forward again.
  have hinverse : unitAddCircleHomeomorphCircle.symm (1 : Circle) = 0 := by
    rw [← unitAddCircleHomeomorphCircle_zero,
      unitAddCircleHomeomorphCircle.symm_apply_apply]
  rw [circlePinchHomotopyValue, hinverse,
    addCirclePinchHomotopyValue_basepoint,
    unitAddCircleHomeomorphCircle_zero]

/-- Helper for Exercise 71.5: the inherited circle distance is the ambient
complex norm of the difference. -/
private lemma circle_dist_eq_norm_sub (z w : Circle) :
    dist z w = ‖(z : ℂ) - (w : ℂ)‖ := by
  -- Cross the `Circle` metric-instance spelling once, then use the ambient
  -- normed-group distance formula.
  change dist (z : ℂ) (w : ℂ) = ‖(z : ℂ) - (w : ℂ)‖
  rw [dist_eq_norm]

/-- Helper for Exercise 71.5: the complex-circle pinch homotopy has a uniform
linear distance bound at its fixed basepoint. -/
private lemma circlePinchHomotopyValue_dist_le (t : unitInterval) (z : Circle) :
    dist (circlePinchHomotopyValue (t, z)) 1 ≤
      Real.pi * dist z 1 := by
  -- Convert chord length to angular distance, apply the additive norm bound,
  -- and convert the input angular distance back to chord length.
  let a := unitAddCircleHomeomorphCircle.symm z
  let b := addCirclePinchHomotopyValue (t, a)
  have haImage : unitAddCircleHomeomorphCircle a = z :=
    unitAddCircleHomeomorphCircle.apply_symm_apply z
  have hbNorm : ‖b‖ ≤ 2 * ‖a‖ :=
    addCirclePinchHomotopyValue_norm_le t a
  have haAngle := angle_unitAddCircleHomeomorphCircle a
  have hbAngle := angle_unitAddCircleHomeomorphCircle b
  have hinputAngle := Complex.angle_le_mul_norm_sub
    (unitAddCircleHomeomorphCircle a).norm_coe (norm_one : ‖(1 : ℂ)‖ = 1)
  change dist (unitAddCircleHomeomorphCircle b) 1 ≤ Real.pi * dist z 1
  calc
    dist (unitAddCircleHomeomorphCircle b) 1 =
        ‖(unitAddCircleHomeomorphCircle b : ℂ) - 1‖ := by
      rw [circle_dist_eq_norm_sub, Circle.coe_one]
    _ ≤ InnerProductGeometry.angle
        (unitAddCircleHomeomorphCircle b : ℂ) 1 :=
      Complex.norm_sub_le_angle
        (unitAddCircleHomeomorphCircle b).norm_coe
        (norm_one : ‖(1 : ℂ)‖ = 1)
    _ = 2 * Real.pi * ‖b‖ := hbAngle
    _ ≤ 2 * Real.pi * (2 * ‖a‖) :=
      mul_le_mul_of_nonneg_left hbNorm (by positivity)
    _ = 2 * (2 * Real.pi * ‖a‖) := by ring
    _ = 2 * InnerProductGeometry.angle
        (unitAddCircleHomeomorphCircle a : ℂ) 1 := by rw [haAngle]
    _ ≤ 2 * (Real.pi / 2 *
        ‖(unitAddCircleHomeomorphCircle a : ℂ) - 1‖) :=
      mul_le_mul_of_nonneg_left hinputAngle (by norm_num)
    _ = Real.pi * dist z 1 := by
      rw [← haImage, circle_dist_eq_norm_sub, Circle.coe_one]
      ring

/-- Helper for Exercise 71.5: the terminal complex-circle pinch collapses the
open unit chord-ball about its basepoint. -/
private lemma circlePinch_eq_one_of_dist_lt (z : Circle)
    (hz : dist z 1 < 1) : circlePinch z = 1 := by
  -- Chord distance controls angular distance, hence the additive quotient
  -- norm lies in the quarter-ball collapsed by the terminal pinch.
  let a := unitAddCircleHomeomorphCircle.symm z
  have haImage : unitAddCircleHomeomorphCircle a = z :=
    unitAddCircleHomeomorphCircle.apply_symm_apply z
  have hchord : ‖(unitAddCircleHomeomorphCircle a : ℂ) - 1‖ < 1 := by
    rw [← Circle.coe_one, ← circle_dist_eq_norm_sub, haImage]
    exact hz
  have hangleLe := Complex.angle_le_mul_norm_sub
    (unitAddCircleHomeomorphCircle a).norm_coe (norm_one : ‖(1 : ℂ)‖ = 1)
  have hscaled : Real.pi / 2 *
      ‖(unitAddCircleHomeomorphCircle a : ℂ) - 1‖ < Real.pi / 2 := by
    simpa only [mul_one] using
      mul_lt_mul_of_pos_left hchord (by positivity : 0 < Real.pi / 2)
  have hangleLt : InnerProductGeometry.angle
      (unitAddCircleHomeomorphCircle a : ℂ) 1 < Real.pi / 2 :=
    hangleLe.trans_lt hscaled
  have hnorm : ‖a‖ < 1 / 4 := by
    have hmul : (2 * Real.pi) * ‖a‖ < (2 * Real.pi) * (1 / 4) := by
      calc
        (2 * Real.pi) * ‖a‖ =
            InnerProductGeometry.angle
              (unitAddCircleHomeomorphCircle a : ℂ) 1 := by
          rw [angle_unitAddCircleHomeomorphCircle]
        _ < Real.pi / 2 := hangleLt
        _ = (2 * Real.pi) * (1 / 4) := by ring
    nlinarith [hmul, Real.pi_pos]
  have hcollapse : addCirclePinch a = 0 :=
    addCirclePinch_eq_zero_of_norm_lt a hnorm
  change unitAddCircleHomeomorphCircle (addCirclePinch a) = 1
  rw [hcollapse, unitAddCircleHomeomorphCircle_zero]

/-- Helper for Exercise 71.5: the controlled complex-circle pinch homotopy. -/
private noncomputable def circlePinchHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id Circle) circlePinch :=
  { toFun := circlePinchHomotopyValue
    continuous_toFun := continuous_circlePinchHomotopyValue
    map_zero_left := circlePinchHomotopyValue_zero
    map_one_left := circlePinchHomotopyValue_one }

/-- Helper for Exercise 71.5: the complex-circle pinch homotopy is relative
to its basepoint. -/
private lemma circlePinchHomotopy_fixed (t : unitInterval) (z : Circle)
    (hz : z ∈ ({1} : Set Circle)) :
    circlePinchHomotopy (t, z) = (ContinuousMap.id Circle) z := by
  -- Singleton membership identifies the spatial input with the fixed basepoint.
  rw [Set.mem_singleton_iff] at hz
  subst z
  exact circlePinchHomotopyValue_basepoint t

/-- Helper for Exercise 71.5: a based homotopy from the identity of `Circle`
to the controlled pinch. -/
private noncomputable def circlePinchHomotopyRel :
    ContinuousMap.HomotopyRel (ContinuousMap.id Circle) circlePinch {1} :=
  { toHomotopy := circlePinchHomotopy
    prop' := circlePinchHomotopy_fixed }

/-- Helper for Exercise 71.5: the controlled circle homotopy transported to
one expanding component. -/
private noncomputable def componentPinchHomotopyValue (n : ℕ+)
    (p : unitInterval × component n) : component n :=
  (componentCoordinate n).symm
    (circlePinchHomotopyValue (p.1, componentCoordinate n p.2))

/-- Helper for Exercise 71.5: the transported component pinch homotopy is
jointly continuous. -/
private lemma continuous_componentPinchHomotopyValue (n : ℕ+) :
    Continuous (componentPinchHomotopyValue n) := by
  -- Conjugate the continuous circle homotopy by the component coordinate.
  have hparameters : Continuous (fun p : unitInterval × component n ↦
      (p.1, componentCoordinate n p.2)) :=
    continuous_fst.prodMk ((componentCoordinate n).continuous.comp continuous_snd)
  exact (componentCoordinate n).symm.continuous.comp
    (continuous_circlePinchHomotopyValue.comp hparameters)

/-- Helper for Exercise 71.5: every transported component homotopy slice
fixes the common origin. -/
private lemma componentPinchHomotopyValue_origin (n : ℕ+) (t : unitInterval) :
    componentPinchHomotopyValue n (t, componentOrigin n) = componentOrigin n := by
  -- Compute in the pointed circle coordinate, where the homotopy fixes `1`.
  apply (componentCoordinate n).injective
  rw [componentPinchHomotopyValue, Homeomorph.apply_symm_apply,
    componentCoordinate_origin, circlePinchHomotopyValue_basepoint]

/-- Helper for Exercise 71.5: the transported component homotopy starts at
the identity. -/
private lemma componentPinchHomotopyValue_zero (n : ℕ+) (x : component n) :
    componentPinchHomotopyValue n (0, x) = x := by
  -- At time zero the conjugated circle homotopy is the identity.
  apply (componentCoordinate n).injective
  rw [componentPinchHomotopyValue, Homeomorph.apply_symm_apply,
    circlePinchHomotopyValue_zero]

/-- Helper for Exercise 71.5: the terminal controlled pinch on one expanding
component. -/
private noncomputable def componentPinch (n : ℕ+) : C(component n, component n) :=
  ⟨fun x ↦ componentPinchHomotopyValue n (1, x),
    continuous_componentPinchHomotopyValue n |>.comp
      (continuous_const.prodMk continuous_id)⟩

/-- Helper for Exercise 71.5: evaluation of the terminal component pinch is
the time-one component homotopy value. -/
private lemma componentPinch_apply (n : ℕ+) (x : component n) :
    componentPinch n x = componentPinchHomotopyValue n (1, x) := by
  -- This is the public computation rule for the bundled terminal map.
  rfl

/-- Helper for Exercise 71.5: the component homotopy ends at its terminal
pinch map. -/
private lemma componentPinchHomotopyValue_one (n : ℕ+) (x : component n) :
    componentPinchHomotopyValue n (1, x) = componentPinch n x := by
  -- The terminal component map is defined by the time-one slice.
  rfl

/-- Helper for Exercise 71.5: the terminal component pinch fixes the common
origin. -/
private lemma componentPinch_origin (n : ℕ+) :
    componentPinch n (componentOrigin n) = componentOrigin n := by
  -- Specialize the fixed-origin homotopy law at the terminal time.
  rw [componentPinch_apply, componentPinchHomotopyValue_origin]

/-- Helper for Exercise 71.5: the componentwise homotopy has a radius-uniform
linear distance bound at the common origin. -/
private lemma componentPinchHomotopyValue_dist_le (n : ℕ+)
    (t : unitInterval) (x : component n) :
    dist (componentPinchHomotopyValue n (t, x) : Space) origin ≤
      Real.pi * dist (x : Space) origin := by
  -- Divide by the component radius, apply the circle estimate, then cancel
  -- the same positive radius from both sides.
  have hcircle := circlePinchHomotopyValue_dist_le t (componentCoordinate n x)
  have hcoordinate : componentCoordinate n
      (componentPinchHomotopyValue n (t, x)) =
        circlePinchHomotopyValue (t, componentCoordinate n x) := by
    rw [componentPinchHomotopyValue, Homeomorph.apply_symm_apply]
  rw [← hcoordinate, dist_componentCoordinate_origin,
    dist_componentCoordinate_origin] at hcircle
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast n.property
  rw [← div_le_div_iff_of_pos_right hnpos]
  simpa only [mul_div_assoc] using hcircle

/-- Helper for Exercise 71.5: the terminal component pinch collapses points
whose distance from the common origin is smaller than the component radius. -/
private lemma componentPinch_eq_origin_of_dist_lt (n : ℕ+) (x : component n)
    (hx : dist origin (x : Space) < (n : ℝ)) :
    componentPinch n x = componentOrigin n := by
  -- Scale the hypothesis to the unit circle and use the terminal collapse
  -- there, then return through the pointed component coordinate.
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast n.property
  have hscaled : dist (componentCoordinate n x) 1 < 1 := by
    rw [dist_componentCoordinate_origin, dist_comm]
    exact (div_lt_one hnpos).mpr hx
  have hcollapse := circlePinch_eq_one_of_dist_lt (componentCoordinate n x) hscaled
  apply (componentCoordinate n).injective
  rw [componentPinch_apply, componentPinchHomotopyValue,
    Homeomorph.apply_symm_apply, circlePinchHomotopyValue_one,
    hcollapse, componentCoordinate_origin]

/-- Helper for Exercise 71.5: componentwise pinch values represented by the
same planar point determine the same coherent quotient class. -/
private lemma coherentInclusion_componentPinchHomotopyValue_eq
    (t : unitInterval) {m n : ℕ+} (x : component m) (y : component n)
    (hxy : (x : Space) = (y : Space)) :
    coherentInclusion m (componentPinchHomotopyValue m (t, x)) =
      coherentInclusion n (componentPinchHomotopyValue n (t, y)) := by
  -- At the common origin both values are the common quotient point; away
  -- from it, uniqueness of the component index reduces to one representative.
  by_cases hxOrigin : (x : Space) = origin
  · have hyOrigin : (y : Space) = origin := hxy.symm.trans hxOrigin
    have hx : x = componentOrigin m := Subtype.ext hxOrigin
    have hy : y = componentOrigin n := Subtype.ext hyOrigin
    rw [hx, hy, componentPinchHomotopyValue_origin,
      componentPinchHomotopyValue_origin,
      coherentInclusion_componentOrigin, coherentInclusion_componentOrigin]
  · have hmn : m = n := component_index_unique_of_ne_origin hxOrigin
      x.property (hxy ▸ y.property)
    subst n
    have hxy' : x = y := Subtype.ext hxy
    subst y
    rfl

/-- Helper for Exercise 71.5: the componentwise pinch homotopy descended to
the coherent kernel quotient. -/
private noncomputable def coherentPinchHomotopyValue
    (p : unitInterval × CoherentModel) : CoherentModel :=
  Quotient.lift
    (fun x : Σ n : ℕ+, component n ↦
      coherentInclusion x.1 (componentPinchHomotopyValue x.1 (p.1, x.2)))
    (fun a b hab ↦
      coherentInclusion_componentPinchHomotopyValue_eq p.1 a.2 b.2 hab)
    p.2

/-- Helper for Exercise 71.5: the descended coherent homotopy computes
componentwise on each canonical inclusion. -/
private lemma coherentPinchHomotopyValue_inclusion
    (t : unitInterval) (n : ℕ+) (x : component n) :
    coherentPinchHomotopyValue (t, coherentInclusion n x) =
      coherentInclusion n (componentPinchHomotopyValue n (t, x)) := by
  -- Quotient evaluation uses the selected component representative.
  rfl

/-- Helper for Exercise 71.5: the descended coherent pinch homotopy is
jointly continuous. -/
private lemma continuous_coherentPinchHomotopyValue :
    Continuous coherentPinchHomotopyValue := by
  -- Pull back along the quotient map and distribute the time product over
  -- the sigma coproduct; continuity is then componentwise.
  apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
  have hcore : Continuous (fun q : Σ n : ℕ+, component n × unitInterval ↦
      coherentInclusion q.1
        (componentPinchHomotopyValue q.1 (q.2.2, q.2.1))) := by
    apply continuous_sigma
    intro n
    have hinclusion : Continuous (coherentInclusion n) :=
      continuous_quotient_mk'.comp continuous_sigmaMk
    exact hinclusion.comp (continuous_componentPinchHomotopyValue n |>.comp
      (continuous_snd.prodMk continuous_fst))
  have hdistribute : Continuous
      (fun p : unitInterval × (Σ n : ℕ+, component n) ↦
        Homeomorph.sigmaProdDistrib (Homeomorph.prodComm _ _ p)) :=
    Homeomorph.sigmaProdDistrib.continuous.comp
      (Homeomorph.prodComm _ _).continuous
  have hexplicit : Continuous
      (fun p : unitInterval × (Σ n : ℕ+, component n) ↦
        coherentInclusion p.2.1
          (componentPinchHomotopyValue p.2.1 (p.1, p.2.2))) := by
    exact hcore.comp hdistribute
  apply hexplicit.congr
  intro p
  rfl

/-- Helper for Exercise 71.5: the coherent quotient homotopy starts at the
identity. -/
private lemma coherentPinchHomotopyValue_zero (q : CoherentModel) :
    coherentPinchHomotopyValue (0, q) = q := by
  -- Check the endpoint on an arbitrary quotient representative.
  induction q using Quotient.inductionOn with
  | _ x =>
      calc
        coherentPinchHomotopyValue (0, Quotient.mk'' x) =
            coherentInclusion x.1
              (componentPinchHomotopyValue x.1 (0, x.2)) := by
          rfl
        _ = coherentInclusion x.1 x.2 := by
          rw [componentPinchHomotopyValue_zero]
        _ = Quotient.mk'' x := rfl

/-- Helper for Exercise 71.5: the terminal self-map of the coherent model
obtained from the controlled componentwise pinch. -/
private noncomputable def coherentPinch : C(CoherentModel, CoherentModel) :=
  ⟨fun q ↦ coherentPinchHomotopyValue (1, q),
    continuous_coherentPinchHomotopyValue.comp
      (continuous_const.prodMk continuous_id)⟩

/-- Helper for Exercise 71.5: the terminal coherent pinch evaluates by the
time-one slice of the coherent homotopy. -/
private lemma coherentPinch_apply (q : CoherentModel) :
    coherentPinch q = coherentPinchHomotopyValue (1, q) := by
  -- The bundled terminal map was defined by this slice.
  rfl

/-- Helper for Exercise 71.5: the coherent homotopy ends at its terminal
pinch map. -/
private lemma coherentPinchHomotopyValue_one (q : CoherentModel) :
    coherentPinchHomotopyValue (1, q) = coherentPinch q := by
  -- The endpoint is definitionally the terminal coherent pinch.
  rfl

/-- Helper for Exercise 71.5: every coherent pinch slice fixes the common
origin class. -/
private lemma coherentPinchHomotopyValue_origin (t : unitInterval) :
    coherentPinchHomotopyValue (t, coherentOrigin) = coherentOrigin := by
  -- Represent the common class in the first component and use the
  -- componentwise fixed-origin law.
  rw [← coherentInclusion_componentOrigin 1,
    coherentPinchHomotopyValue_inclusion,
    componentPinchHomotopyValue_origin,
    coherentInclusion_componentOrigin]

/-- Helper for Exercise 71.5: the terminal coherent pinch fixes the common
origin class. -/
private lemma coherentPinch_origin : coherentPinch coherentOrigin = coherentOrigin := by
  -- Specialize the fixed-origin homotopy computation at time one.
  rw [coherentPinch_apply, coherentPinchHomotopyValue_origin]

/-- Helper for Exercise 71.5: the descended coherent homotopy runs from the
identity to the terminal coherent pinch. -/
private noncomputable def coherentPinchHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id CoherentModel) coherentPinch :=
  { toFun := coherentPinchHomotopyValue
    continuous_toFun := continuous_coherentPinchHomotopyValue
    map_zero_left := coherentPinchHomotopyValue_zero
    map_one_left := coherentPinchHomotopyValue_one }

/-- Helper for Exercise 71.5: the coherent pinch homotopy is relative to its
common origin class. -/
private lemma coherentPinchHomotopy_fixed (t : unitInterval)
    (q : CoherentModel) (hq : q ∈ ({coherentOrigin} : Set CoherentModel)) :
    coherentPinchHomotopy (t, q) = (ContinuousMap.id CoherentModel) q := by
  -- Singleton membership reduces the claim to the fixed-origin computation.
  rw [Set.mem_singleton_iff] at hq
  subst q
  exact coherentPinchHomotopyValue_origin t

/-- Helper for Exercise 71.5: a based coherent homotopy from the identity to
the controlled terminal pinch. -/
private noncomputable def coherentPinchHomotopyRel :
    ContinuousMap.HomotopyRel (ContinuousMap.id CoherentModel)
      coherentPinch {coherentOrigin} :=
  { toHomotopy := coherentPinchHomotopy
    prop' := coherentPinchHomotopy_fixed }

/-- Helper for Exercise 71.5: the terminal coherent pinch transported
set-theoretically across the bijective comparison. -/
noncomputable def scaledPinch (x : Space) : Space :=
  coherentComparison
    (coherentPinch (Function.invFun coherentComparison x))

/-- Helper for Exercise 71.5: on a chosen expanding component, the transported
pinch is exactly the component pinch. -/
private lemma scaledPinch_on_component (n : ℕ+) (x : component n) :
    scaledPinch (x : Space) = (componentPinch n x : Space) := by
  -- Replace the point by its coherent representative, cancel the set-theoretic
  -- inverse, and compute both the coherent and planar component inclusions.
  rw [scaledPinch, ← coherentComparison_inclusion n x,
    Function.leftInverse_invFun coherentComparison_bijective.1,
    coherentPinch_apply, coherentPinchHomotopyValue_inclusion,
    coherentComparison_inclusion]
  exact congrArg Subtype.val (componentPinchHomotopyValue_one n x)

/-- Helper for Exercise 71.5: pinching after comparison agrees with comparing
after the coherent pinch. -/
private lemma scaledPinch_comparison (q : CoherentModel) :
    scaledPinch (coherentComparison q) = coherentComparison (coherentPinch q) := by
  -- The set-theoretic inverse cancels on every coherent input.
  rw [scaledPinch,
    Function.leftInverse_invFun coherentComparison_bijective.1]

/-- Helper for Exercise 71.5: the transported terminal pinch preserves every
expanding component. -/
lemma scaledPinch_preserves_component (n : ℕ+) (x : Space)
    (hx : x ∈ component n) : scaledPinch x ∈ component n := by
  -- Repackage the input in the selected component and use its terminal pinch.
  let x' : component n := ⟨x, hx⟩
  have hvalue : scaledPinch x = (componentPinch n x' : Space) := by
    exact scaledPinch_on_component n x'
  rw [hvalue]
  exact (componentPinch n x').property

/-- Helper for Exercise 71.5: on the `n`th component, the transported terminal
pinch collapses the open radius-`n` ball to the common origin. -/
lemma scaledPinch_eq_origin_of_dist_lt (n : ℕ+) (x : Space)
    (hx : x ∈ component n) (hdist : dist origin x < (n : ℝ)) :
    scaledPinch x = origin := by
  -- Apply the component collapse theorem after selecting the component
  -- representative, then forget its membership proof.
  let x' : component n := ⟨x, hx⟩
  rw [scaledPinch_on_component n x',
    componentPinch_eq_origin_of_dist_lt n x' hdist]

/-- Helper for Exercise 71.5: away from the common origin, the quadratic
coordinate ratio recovers the index of an expanding component. -/
private noncomputable def componentRank (x : Space) : ℝ :=
  ((x : Plane) 0 ^ 2 + (x : Plane) 1 ^ 2) / (2 * (x : Plane) 0)

/-- Helper for Exercise 71.5: the component rank equals the positive-natural
index on every non-origin point of that component. -/
private lemma componentRank_eq (n : ℕ+) (x : Space)
    (hx : x ∈ component n) (hxOrigin : x ≠ origin) :
    componentRank x = (n : ℝ) := by
  -- Substitute the component's quadratic identity and cancel the positive
  -- first coordinate.
  have hx0 : (x : Plane) 0 ≠ 0 := ne_of_gt (firstCoordinate_pos_of_ne_origin hxOrigin)
  rw [componentRank, component_radius_identity n x hx]
  field_simp

/-- Helper for Exercise 71.5: the component-rank function is continuous on
the open positive-first-coordinate region. -/
private lemma continuousOn_componentRank :
    ContinuousOn componentRank {x : Space | 0 < (x : Plane) 0} := by
  -- The denominator is nonzero throughout this region, so the coordinate
  -- quotient is continuous there.
  unfold componentRank
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    have htwo : (2 : ℝ) ≠ 0 := two_ne_zero
    exact mul_ne_zero htwo (ne_of_gt hx)

/-- Helper for Exercise 71.5: a real cast lying within one half of a
positive-natural cast determines the same positive natural. -/
private lemma pnat_eq_of_cast_mem_halfInterval (m n : ℕ+)
    (hm : (m : ℝ) ∈ Set.Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2)) :
    m = n := by
  -- Distinct natural numbers are separated by at least one, contradicting
  -- membership in the open half-unit interval.
  rcases lt_trichotomy m n with hlt | heq | hgt
  · have hsucc : (m : ℕ) + 1 ≤ (n : ℕ) := by
      exact hlt
    have hsuccReal : (m : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast hsucc
    linarith [hm.1]
  · exact heq
  · have hsucc : (n : ℕ) + 1 ≤ (m : ℕ) := by
      exact hgt
    have hsuccReal : (n : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast hsucc
    linarith [hm.2]

/-- Helper for Exercise 71.5: deleting the common origin makes each expanding
component open in the planar union. -/
private lemma isOpen_component_diff_origin (n : ℕ+) :
    IsOpen (component n \ {origin}) := by
  let positiveRegion : Set Space := {x | 0 < (x : Plane) 0}
  let rankWindow : Set ℝ :=
    Set.Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2)
  have hpositive : IsOpen positiveRegion := by
    -- The first ambient coordinate is continuous on the carrier subtype.
    have hcoordinate : Continuous (fun x : Space ↦ (x : Plane) 0) := by
      fun_prop
    exact isOpen_lt continuous_const hcoordinate
  have hrankWindow : IsOpen rankWindow := isOpen_Ioo
  have hdescription :
      component n \ {origin} =
        positiveRegion ∩ componentRank ⁻¹' rankWindow := by
    ext x
    constructor
    · intro hx
      have hxOrigin : x ≠ origin := by
        simpa only [Set.mem_singleton_iff] using hx.2
      have hpositiveX : x ∈ positiveRegion :=
        firstCoordinate_pos_of_ne_origin hxOrigin
      have hrank := componentRank_eq n x hx.1 hxOrigin
      refine ⟨hpositiveX, ?_⟩
      rw [Set.mem_preimage, hrank]
      constructor <;> norm_num
    · rintro ⟨hxPositive, hxRank⟩
      have hxOrigin : x ≠ origin := by
        intro hxo
        subst x
        have hzero : (origin : Plane) 0 = 0 := by
          rw [origin_coe]
          rfl
        have hfalse : (0 : ℝ) < 0 := by
          simpa only [positiveRegion, Set.mem_setOf_eq, hzero] using hxPositive
        exact (lt_irrefl 0) hfalse
      obtain ⟨m, hxmCircle⟩ := (mem_carrier_iff (x : Plane)).mp x.property
      have hxm : x ∈ component m := (mem_component_iff x m).mpr hxmCircle
      have hrank := componentRank_eq m x hxm hxOrigin
      have hmWindow : (m : ℝ) ∈ rankWindow := by
        simpa only [Set.mem_preimage, hrank] using hxRank
      have hmn : m = n := pnat_eq_of_cast_mem_halfInterval m n hmWindow
      subst m
      have hxNotOrigin : x ∉ ({origin} : Set Space) := by
        simpa only [Set.mem_singleton_iff] using hxOrigin
      exact ⟨hxm, hxNotOrigin⟩
  rw [hdescription]
  exact continuousOn_componentRank.isOpen_inter_preimage
    hpositive hrankWindow

/-- Helper for Exercise 71.5: a component containing a non-origin point is a
neighborhood of that point in the expanding-circle union. -/
private lemma component_mem_nhds_of_ne_origin (n : ℕ+) (x : Space)
    (hx : x ∈ component n) (hxOrigin : x ≠ origin) :
    component n ∈ nhds x := by
  -- Use the open component with its common origin deleted.
  have hxNotOrigin : x ∉ ({origin} : Set Space) := by
    simpa only [Set.mem_singleton_iff] using hxOrigin
  apply Filter.mem_of_superset
    ((isOpen_component_diff_origin n).mem_nhds ⟨hx, hxNotOrigin⟩)
  exact Set.sdiff_subset

/-- Helper for Exercise 71.5: the transported terminal pinch is continuous
when restricted to any one expanding component. -/
private lemma continuousOn_scaledPinch_component (n : ℕ+) :
    ContinuousOn scaledPinch (component n) := by
  rw [continuousOn_iff_continuous_restrict]
  have hcomponent : Continuous
      (fun x : component n ↦ (componentPinch n x : Space)) :=
    continuous_subtype_val.comp (componentPinch n).continuous
  apply hcomponent.congr
  intro x
  exact (scaledPinch_on_component n x).symm

/-- Helper for Exercise 71.5: the transported terminal pinch moves points by
at most the uniform factor `Real.pi` away from the common origin. -/
lemma scaledPinch_dist_le (x : Space) :
    dist (scaledPinch x) origin ≤ Real.pi * dist x origin := by
  -- Select a component representative and apply the componentwise estimate
  -- at the terminal homotopy time.
  obtain ⟨n, hxnCircle⟩ := (mem_carrier_iff (x : Plane)).mp x.property
  let x' : component n := ⟨x, (mem_component_iff x n).mpr hxnCircle⟩
  rw [scaledPinch_on_component n x']
  exact componentPinchHomotopyValue_dist_le n 1 x'

/-- Helper for Exercise 71.5: the transported terminal pinch fixes the common
origin. -/
lemma scaledPinch_origin : scaledPinch origin = origin := by
  -- The origin lies in the first component and has distance zero from itself.
  apply scaledPinch_eq_origin_of_dist_lt 1 origin (origin_mem_component 1)
  simp

/-- Helper for Exercise 71.5: the terminal componentwise pinch is continuous
on the planar expanding-circle union. -/
lemma continuous_scaledPinch : Continuous scaledPinch := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxOrigin : x = origin
  · subst x
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hdenom : 0 < Real.pi + 1 := by positivity
    refine ⟨ε / (Real.pi + 1), div_pos hε hdenom, ?_⟩
    intro y hy
    have hratio : Real.pi * (ε / (Real.pi + 1)) < ε := by
      have hdivision : (Real.pi * ε) / (Real.pi + 1) < ε := by
        apply (div_lt_iff₀ hdenom).mpr
        nlinarith [Real.pi_pos]
      calc
        Real.pi * (ε / (Real.pi + 1)) =
            (Real.pi * ε) / (Real.pi + 1) := by ring
        _ < ε := hdivision
    calc
      dist (scaledPinch y) (scaledPinch origin) =
          dist (scaledPinch y) origin := by rw [scaledPinch_origin]
      _ ≤ Real.pi * dist y origin := scaledPinch_dist_le y
      _ < Real.pi * (ε / (Real.pi + 1)) :=
        mul_lt_mul_of_pos_left hy Real.pi_pos
      _ < ε := hratio
  · obtain ⟨n, hxnCircle⟩ := (mem_carrier_iff (x : Plane)).mp x.property
    have hxn : x ∈ component n := (mem_component_iff x n).mpr hxnCircle
    exact (continuousOn_scaledPinch_component n).continuousAt
      (component_mem_nhds_of_ne_origin n x hxn hxOrigin)

/-- Helper for Exercise 71.5: the full coherent pinch homotopy transported
set-theoretically across the comparison. -/
private noncomputable def scaledPinchHomotopyValue
    (p : unitInterval × Space) : Space :=
  coherentComparison
    (coherentPinchHomotopyValue
      (p.1, Function.invFun coherentComparison p.2))

/-- Helper for Exercise 71.5: the transported homotopy computes by the chosen
component homotopy on every expanding component. -/
private lemma scaledPinchHomotopyValue_on_component (t : unitInterval)
    (n : ℕ+) (x : component n) :
    scaledPinchHomotopyValue (t, (x : Space)) =
      (componentPinchHomotopyValue n (t, x) : Space) := by
  -- Replace the point by its coherent representative and cancel the
  -- set-theoretic inverse before evaluating both component inclusions.
  rw [scaledPinchHomotopyValue, ← coherentComparison_inclusion n x,
    Function.leftInverse_invFun coherentComparison_bijective.1,
    coherentPinchHomotopyValue_inclusion,
    coherentComparison_inclusion]

/-- Helper for Exercise 71.5: the set-theoretic comparison inverse sends the
planar origin to the coherent origin. -/
private lemma coherentComparison_invFun_origin :
    Function.invFun coherentComparison origin = coherentOrigin := by
  -- Rewrite the origin as the image of the coherent basepoint and cancel the
  -- comparison with its set-theoretic inverse.
  calc
    Function.invFun coherentComparison origin =
        Function.invFun coherentComparison
          (coherentComparison coherentOrigin) := by
      rw [coherentComparison_origin]
    _ = coherentOrigin :=
      Function.leftInverse_invFun coherentComparison_bijective.1 coherentOrigin

/-- Helper for Exercise 71.5: the transported homotopy starts at the identity
of the planar expanding-circle union. -/
private lemma scaledPinchHomotopyValue_zero (x : Space) :
    scaledPinchHomotopyValue (0, x) = x := by
  -- Use the coherent zero-time law and the right-inverse law of the bijective
  -- comparison.
  rw [scaledPinchHomotopyValue, coherentPinchHomotopyValue_zero]
  exact Function.rightInverse_invFun coherentComparison_bijective.2 x

/-- Helper for Exercise 71.5: the transported homotopy ends at the planar
terminal pinch. -/
private lemma scaledPinchHomotopyValue_one (x : Space) :
    scaledPinchHomotopyValue (1, x) = scaledPinch x := by
  -- Both sides use the same time-one coherent pinch value.
  rw [scaledPinchHomotopyValue, scaledPinch, coherentPinch_apply]

/-- Helper for Exercise 71.5: every transported homotopy slice fixes the
planar origin. -/
private lemma scaledPinchHomotopyValue_origin (t : unitInterval) :
    scaledPinchHomotopyValue (t, origin) = origin := by
  -- Pull the origin back to the coherent basepoint, use its fixed-point law,
  -- and compare forward again.
  rw [scaledPinchHomotopyValue, coherentComparison_invFun_origin,
    coherentPinchHomotopyValue_origin, coherentComparison_origin]

/-- Helper for Exercise 71.5: every transported homotopy slice satisfies the
same uniform distance bound at the planar origin. -/
private lemma scaledPinchHomotopyValue_dist_le (t : unitInterval) (x : Space) :
    dist (scaledPinchHomotopyValue (t, x)) origin ≤
      Real.pi * dist x origin := by
  -- Select a component and apply the componentwise uniform estimate.
  obtain ⟨n, hxnCircle⟩ := (mem_carrier_iff (x : Plane)).mp x.property
  let x' : component n := ⟨x, (mem_component_iff x n).mpr hxnCircle⟩
  rw [scaledPinchHomotopyValue_on_component t n x']
  exact componentPinchHomotopyValue_dist_le n t x'

/-- Helper for Exercise 71.5: the transported homotopy is continuous on the
product of the parameter interval with any one component. -/
private lemma continuousOn_scaledPinchHomotopyValue_component (n : ℕ+) :
    ContinuousOn scaledPinchHomotopyValue
      ((Set.univ : Set unitInterval) ×ˢ component n) := by
  rw [continuousOn_iff_continuous_restrict]
  have hparameters : Continuous
      (fun p : ↑((Set.univ : Set unitInterval) ×ˢ component n) ↦
        (p.1.1, (⟨p.1.2, p.2.2⟩ : component n))) := by
    fun_prop
  have hcomponent : Continuous
      (fun p : ↑((Set.univ : Set unitInterval) ×ˢ component n) ↦
        (componentPinchHomotopyValue n
          (p.1.1, ⟨p.1.2, p.2.2⟩) : Space)) :=
    continuous_subtype_val.comp
      (continuous_componentPinchHomotopyValue n |>.comp hparameters)
  apply hcomponent.congr
  intro p
  exact (scaledPinchHomotopyValue_on_component p.1.1 n
    ⟨p.1.2, p.2.2⟩).symm

/-- Helper for Exercise 71.5: the transported componentwise pinch is jointly
continuous in its time and planar variables. -/
private lemma continuous_scaledPinchHomotopyValue :
    Continuous scaledPinchHomotopyValue := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, x⟩
  by_cases hxOrigin : x = origin
  · subst x
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hdenom : 0 < Real.pi + 1 := by positivity
    refine ⟨ε / (Real.pi + 1), div_pos hε hdenom, ?_⟩
    rintro ⟨s, y⟩ hy
    have hySpatial : dist y origin < ε / (Real.pi + 1) := by
      rw [Prod.dist_eq] at hy
      exact (le_max_right (dist s t) (dist y origin)).trans_lt hy
    have hratio : Real.pi * (ε / (Real.pi + 1)) < ε := by
      have hdivision : (Real.pi * ε) / (Real.pi + 1) < ε := by
        apply (div_lt_iff₀ hdenom).mpr
        nlinarith [Real.pi_pos]
      calc
        Real.pi * (ε / (Real.pi + 1)) =
            (Real.pi * ε) / (Real.pi + 1) := by ring
        _ < ε := hdivision
    calc
      dist (scaledPinchHomotopyValue (s, y))
          (scaledPinchHomotopyValue (t, origin)) =
          dist (scaledPinchHomotopyValue (s, y)) origin := by
        rw [scaledPinchHomotopyValue_origin]
      _ ≤ Real.pi * dist y origin :=
        scaledPinchHomotopyValue_dist_le s y
      _ < Real.pi * (ε / (Real.pi + 1)) :=
        mul_lt_mul_of_pos_left hySpatial Real.pi_pos
      _ < ε := hratio
  · obtain ⟨n, hxnCircle⟩ := (mem_carrier_iff (x : Plane)).mp x.property
    have hxn : x ∈ component n := (mem_component_iff x n).mpr hxnCircle
    have hneighborhood :
        (Set.univ : Set unitInterval) ×ˢ component n ∈ nhds (t, x) :=
      prod_mem_nhds Filter.univ_mem
        (component_mem_nhds_of_ne_origin n x hxn hxOrigin)
    exact (continuousOn_scaledPinchHomotopyValue_component n).continuousAt
      hneighborhood

/-- Helper for Exercise 71.5: the terminal planar pinch as a bundled
continuous map. -/
private noncomputable def scaledPinchMap : C(Space, Space) :=
  ⟨scaledPinch, continuous_scaledPinch⟩

/-- Helper for Exercise 71.5: the transported planar homotopy runs from the
identity to the terminal scaled pinch. -/
private noncomputable def scaledPinchHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id Space) scaledPinchMap :=
  { toFun := scaledPinchHomotopyValue
    continuous_toFun := continuous_scaledPinchHomotopyValue
    map_zero_left := scaledPinchHomotopyValue_zero
    map_one_left := scaledPinchHomotopyValue_one }

/-- Helper for Exercise 71.5: the transported planar homotopy is relative to
the common origin. -/
private lemma scaledPinchHomotopy_fixed (t : unitInterval) (x : Space)
    (hx : x ∈ ({origin} : Set Space)) :
    scaledPinchHomotopy (t, x) = (ContinuousMap.id Space) x := by
  -- Singleton membership reduces the claim to the fixed-origin law.
  rw [Set.mem_singleton_iff] at hx
  subst x
  exact scaledPinchHomotopyValue_origin t

/-- Helper for Exercise 71.5: a based planar homotopy from the identity to the
controlled scaled pinch. -/
private noncomputable def scaledPinchHomotopyRel :
    ContinuousMap.HomotopyRel (ContinuousMap.id Space)
      scaledPinchMap {origin} :=
  { toHomotopy := scaledPinchHomotopy
    prop' := scaledPinchHomotopy_fixed }

/-- Helper for Exercise 71.5: a scaled input collapse sends every compact set
into a finite union of expanding components. -/
lemma compactImage_finiteSupport_of_scaledCollapse
    (r : Space → Space) {ε : ℝ} (hε : 0 < ε)
    (hpreserves : ∀ n x, x ∈ component n → r x ∈ component n)
    (hcollapse : ∀ n x, x ∈ component n →
      dist origin x < ε * (n : ℝ) → r x = origin)
    {K : Set Space} (hK : IsCompact K) :
    ∃ F : Finset ℕ+, r '' K ⊆ ⋃ n ∈ F, component n := by
  classical
  -- Bound the compact input uniformly by a closed ball centered at the
  -- common point, and retain only indices below the resulting scaled bound.
  obtain ⟨C, hKC⟩ := hK.isBounded.subset_closedBall origin
  let boundedIndices : Set ℕ+ := {n | (n : ℝ) ≤ C / ε}
  have hfinite : boundedIndices.Finite := by
    exact finite_setOf_pnatCast_le (C / ε)
  let F : Finset ℕ+ := insert 1 hfinite.toFinset
  refine ⟨F, ?_⟩
  rintro y ⟨x, hxK, rfl⟩
  -- The collapsed point is supported on the first component.  Otherwise,
  -- choose an input component and use the collapse implication
  -- contrapositively to bound its index.
  by_cases horigin : r x = origin
  · rw [horigin]
    rw [Set.mem_iUnion]
    refine ⟨1, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨Finset.mem_insert_self 1 hfinite.toFinset, origin_mem_component 1⟩
  · have hxCarrier : (x : Plane) ∈ carrier := x.property
    obtain ⟨n, hxnCircle⟩ := (mem_carrier_iff (x : Plane)).mp hxCarrier
    have hxn : x ∈ component n := (mem_component_iff x n).mpr hxnCircle
    have hthreshold : ε * (n : ℝ) ≤ dist origin x := by
      exact le_of_not_gt (fun hlt ↦ horigin (hcollapse n x hxn hlt))
    have hxbound : dist origin x ≤ C := by
      have hxball := hKC hxK
      rw [Metric.mem_closedBall, dist_comm] at hxball
      exact hxball
    have hnBound : (n : ℝ) ≤ C / ε := by
      rw [le_div_iff₀ hε]
      rw [mul_comm]
      exact hthreshold.trans hxbound
    have hnFinite : n ∈ hfinite.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hnBound
    rw [Set.mem_iUnion]
    refine ⟨n, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨Finset.mem_insert_of_mem hnFinite, hpreserves n x hxn⟩

/-- Helper for Exercise 71.5: the controlled terminal pinch sends every
compact set into a finite union of expanding components. -/
lemma scaledPinch_compactImage_finiteSupport {K : Set Space}
    (hK : IsCompact K) :
    ∃ F : Finset ℕ+, scaledPinch '' K ⊆ ⋃ n ∈ F, component n := by
  -- Apply the abstract compact-support criterion with scale one, using the
  -- component-preservation and radius-collapse laws proved above.
  apply compactImage_finiteSupport_of_scaledCollapse scaledPinch zero_lt_one
    scaledPinch_preserves_component
  · intro n x hx hdist
    have hdist' : dist origin x < (n : ℝ) := by
      simpa only [one_mul] using hdist
    exact scaledPinch_eq_origin_of_dist_lt n x hx hdist'
  · exact hK

/-- Helper for Exercise 71.5: the set-theoretic inverse of the coherent
comparison is continuous after a map whose image meets only finitely many
expanding components. -/
lemma continuous_coherentLift_of_finiteComponentRange
    {Z : Type*} [TopologicalSpace Z] (g : C(Z, Space)) (F : Finset ℕ+)
    (hg : Set.range g ⊆ ⋃ n ∈ F, component n) :
    Continuous (fun z ↦ Function.invFun coherentComparison (g z)) := by
  classical
  let A : {n // n ∈ F} → Set Z := fun n ↦ g ⁻¹' component n
  -- Paste the canonical component lifts over the finite closed preimage cover.
  refine (locallyFinite_of_finite A).continuous ?_ ?_ ?_
  · ext z
    constructor
    · intro _
      exact Set.mem_univ z
    · intro _
      have hz := hg (Set.mem_range_self z)
      simp only [Set.mem_iUnion] at hz ⊢
      obtain ⟨n, hnF, hgn⟩ := hz
      exact ⟨⟨n, hnF⟩, hgn⟩
  · intro n
    exact (isClosed_component n).preimage g.continuous
  · intro n
    rw [continuousOn_iff_continuous_restrict]
    let localLift : A n → CoherentModel := fun z ↦
      coherentInclusion n ⟨g z, z.property⟩
    have hcomponent : Continuous (fun z : A n ↦
        (⟨g z, z.property⟩ : component n)) :=
      (g.continuous.comp continuous_subtype_val).subtype_mk _
    have hinclusion : Continuous (coherentInclusion (n : ℕ+)) :=
      continuous_quotient_mk'.comp continuous_sigmaMk
    have hlocalLift : Continuous localLift := hinclusion.comp hcomponent
    apply hlocalLift.congr
    intro z
    symm
    calc
      Function.invFun coherentComparison (g z) =
          Function.invFun coherentComparison
            (coherentComparison (coherentInclusion n ⟨g z, z.property⟩)) := by
        rw [coherentComparison_inclusion]
      _ = coherentInclusion n ⟨g z, z.property⟩ :=
        Function.leftInverse_invFun coherentComparison_bijective.1 _

/-- Helper for Exercise 71.5: every based coherent loop is path-homotopic to
its image under the terminal coherent pinch. -/
private lemma homotopic_coherentPinchPath
    (p : Path coherentOrigin coherentOrigin) :
    Path.Homotopic p
      ((p.map coherentPinch.continuous).cast
        coherentPinch_origin.symm coherentPinch_origin.symm) := by
  let pinchedPath : Path coherentOrigin coherentOrigin :=
    (p.map coherentPinch.continuous).cast
      coherentPinch_origin.symm coherentPinch_origin.symm
  have hcontinuous : Continuous
      (fun z : unitInterval × unitInterval ↦
        coherentPinchHomotopyValue (z.1, p z.2)) :=
    continuous_coherentPinchHomotopyValue.comp
      (continuous_fst.prodMk (p.continuous.comp continuous_snd))
  have hzero : ∀ s : unitInterval,
      coherentPinchHomotopyValue (0, p s) = p s :=
    fun s ↦ coherentPinchHomotopyValue_zero (p s)
  have hone : ∀ s : unitInterval,
      coherentPinchHomotopyValue (1, p s) = pinchedPath s := by
    intro s
    rw [coherentPinchHomotopyValue_one]
    rfl
  have hboundary : ∀ (t s : unitInterval),
      s ∈ ({0, 1} : Set unitInterval) →
        coherentPinchHomotopyValue (t, p s) = p s := by
    intro t s hs
    rcases hs with hs | hs
    · subst s
      rw [p.source, coherentPinchHomotopyValue_origin]
    · rw [Set.mem_singleton_iff] at hs
      subst s
      rw [p.target, coherentPinchHomotopyValue_origin]
  let H : Path.Homotopy p pinchedPath :=
    { toFun := fun z ↦ coherentPinchHomotopyValue (z.1, p z.2)
      continuous_toFun := hcontinuous
      map_zero_left := hzero
      map_one_left := hone
      prop' := hboundary }
  -- The coherent pinch square is the required path homotopy.
  exact ⟨H⟩

/-- Helper for Exercise 71.5: every based loop is path-homotopic to its image
under the controlled terminal pinch. -/
private lemma homotopic_scaledPinchPath
    (p : Path origin origin) :
    Path.Homotopic p
      ((p.map continuous_scaledPinch).cast
        scaledPinch_origin.symm scaledPinch_origin.symm) := by
  let pinchedPath : Path origin origin :=
    (p.map continuous_scaledPinch).cast
      scaledPinch_origin.symm scaledPinch_origin.symm
  have hcontinuous : Continuous
      (fun z : unitInterval × unitInterval ↦
        scaledPinchHomotopyValue (z.1, p z.2)) :=
    continuous_scaledPinchHomotopyValue.comp
      (continuous_fst.prodMk (p.continuous.comp continuous_snd))
  have hzero : ∀ s : unitInterval,
      scaledPinchHomotopyValue (0, p s) = p s :=
    fun s ↦ scaledPinchHomotopyValue_zero (p s)
  have hone : ∀ s : unitInterval,
      scaledPinchHomotopyValue (1, p s) = pinchedPath s := by
    intro s
    rw [scaledPinchHomotopyValue_one]
    rfl
  have hboundary : ∀ (t s : unitInterval),
      s ∈ ({0, 1} : Set unitInterval) →
        scaledPinchHomotopyValue (t, p s) = p s := by
    intro t s hs
    rcases hs with hs | hs
    · subst s
      rw [p.source, scaledPinchHomotopyValue_origin]
    · rw [Set.mem_singleton_iff] at hs
      subst s
      rw [p.target, scaledPinchHomotopyValue_origin]
  let H : Path.Homotopy p pinchedPath :=
    { toFun := fun z ↦ scaledPinchHomotopyValue (z.1, p z.2)
      continuous_toFun := hcontinuous
      map_zero_left := hzero
      map_one_left := hone
      prop' := hboundary }
  -- The explicit square supplies the path-homotopy witness.
  exact ⟨H⟩

/-- Helper for Exercise 71.5: the controlled pinch of every based planar loop
admits a continuous based lift to the coherent model. -/
private lemma exists_coherentLift_scaledPinchPath
    (p : Path origin origin) :
    ∃ q : Path coherentOrigin coherentOrigin,
      ∀ t : unitInterval,
        coherentComparison (q t) = scaledPinch (p t) := by
  let pinchedPath : Path origin origin :=
    (p.map continuous_scaledPinch).cast
      scaledPinch_origin.symm scaledPinch_origin.symm
  let g : C(unitInterval, Space) :=
    ⟨pinchedPath, pinchedPath.continuous⟩
  have hcompact : IsCompact (Set.range p) := isCompact_range p.continuous
  obtain ⟨F, hF⟩ := scaledPinch_compactImage_finiteSupport hcompact
  have hg : Set.range g ⊆ ⋃ n ∈ F, component n := by
    rintro y ⟨t, rfl⟩
    apply hF
    refine ⟨p t, Set.mem_range_self t, ?_⟩
    rfl
  have hlift : Continuous
      (fun t ↦ Function.invFun coherentComparison (g t)) :=
    continuous_coherentLift_of_finiteComponentRange g F hg
  let liftMap : C(unitInterval, CoherentModel) :=
    ⟨fun t ↦ Function.invFun coherentComparison (g t), hlift⟩
  have hgSource : g 0 = origin := by
    exact pinchedPath.source
  have hgTarget : g 1 = origin := by
    exact pinchedPath.target
  have hliftSource : liftMap 0 = coherentOrigin := by
    calc
      liftMap 0 = Function.invFun coherentComparison (g 0) := rfl
      _ = Function.invFun coherentComparison origin :=
        congrArg (Function.invFun coherentComparison) hgSource
      _ = coherentOrigin := coherentComparison_invFun_origin
  have hliftTarget : liftMap 1 = coherentOrigin := by
    calc
      liftMap 1 = Function.invFun coherentComparison (g 1) := rfl
      _ = Function.invFun coherentComparison origin :=
        congrArg (Function.invFun coherentComparison) hgTarget
      _ = coherentOrigin := coherentComparison_invFun_origin
  let q : Path coherentOrigin coherentOrigin :=
    { toContinuousMap := liftMap
      source' := hliftSource
      target' := hliftTarget }
  refine ⟨q, ?_⟩
  intro t
  have hqApply : q t = Function.invFun coherentComparison (g t) := rfl
  have hright :=
    Function.rightInverse_invFun coherentComparison_bijective.2 (g t)
  calc
    coherentComparison (q t) =
        coherentComparison (Function.invFun coherentComparison (g t)) :=
      congrArg coherentComparison hqApply
    _ = g t := hright
    _ = scaledPinch (p t) := rfl

/-- Helper for Exercise 71.5: an ambient path homotopy between compared
coherent loops lifts after pinching and therefore already identifies the
original coherent loops. -/
private lemma homotopic_of_comparison_homotopic
    (p q : Path coherentOrigin coherentOrigin)
    (h : Path.Homotopic
      ((p.map coherentComparison.continuous).cast
        coherentComparison_origin.symm coherentComparison_origin.symm)
      ((q.map coherentComparison.continuous).cast
        coherentComparison_origin.symm coherentComparison_origin.symm)) :
    Path.Homotopic p q := by
  let mappedP : Path origin origin :=
    (p.map coherentComparison.continuous).cast
      coherentComparison_origin.symm coherentComparison_origin.symm
  let mappedQ : Path origin origin :=
    (q.map coherentComparison.continuous).cast
      coherentComparison_origin.symm coherentComparison_origin.symm
  let pinchedP : Path coherentOrigin coherentOrigin :=
    (p.map coherentPinch.continuous).cast
      coherentPinch_origin.symm coherentPinch_origin.symm
  let pinchedQ : Path coherentOrigin coherentOrigin :=
    (q.map coherentPinch.continuous).cast
      coherentPinch_origin.symm coherentPinch_origin.symm
  obtain ⟨F⟩ := h
  let g : C(unitInterval × unitInterval, Space) :=
    ⟨fun z ↦ scaledPinch (F z),
      continuous_scaledPinch.comp F.continuous⟩
  have hcompact : IsCompact (Set.range F) := isCompact_range F.continuous
  obtain ⟨indices, hindices⟩ :=
    scaledPinch_compactImage_finiteSupport hcompact
  have hg : Set.range g ⊆ ⋃ n ∈ indices, component n := by
    rintro y ⟨z, rfl⟩
    apply hindices
    exact ⟨F z, Set.mem_range_self z, rfl⟩
  have hlift : Continuous
      (fun z ↦ Function.invFun coherentComparison (g z)) :=
    continuous_coherentLift_of_finiteComponentRange g indices hg
  have hzero : ∀ s : unitInterval,
      Function.invFun coherentComparison (g (0, s)) = pinchedP s := by
    intro s
    calc
      Function.invFun coherentComparison (g (0, s)) =
          Function.invFun coherentComparison
            (scaledPinch (F (0, s))) := rfl
      _ = Function.invFun coherentComparison
          (scaledPinch (mappedP s)) :=
        congrArg (fun x ↦ Function.invFun coherentComparison (scaledPinch x))
          (F.map_zero_left s)
      _ = Function.invFun coherentComparison
          (scaledPinch (coherentComparison (p s))) := rfl
      _ = Function.invFun coherentComparison
          (coherentComparison (coherentPinch (p s))) :=
        congrArg (Function.invFun coherentComparison)
          (scaledPinch_comparison (p s))
      _ = coherentPinch (p s) :=
        Function.leftInverse_invFun coherentComparison_bijective.1 _
      _ = pinchedP s := rfl
  have hone : ∀ s : unitInterval,
      Function.invFun coherentComparison (g (1, s)) = pinchedQ s := by
    intro s
    calc
      Function.invFun coherentComparison (g (1, s)) =
          Function.invFun coherentComparison
            (scaledPinch (F (1, s))) := rfl
      _ = Function.invFun coherentComparison
          (scaledPinch (mappedQ s)) :=
        congrArg (fun x ↦ Function.invFun coherentComparison (scaledPinch x))
          (F.map_one_left s)
      _ = Function.invFun coherentComparison
          (scaledPinch (coherentComparison (q s))) := rfl
      _ = Function.invFun coherentComparison
          (coherentComparison (coherentPinch (q s))) :=
        congrArg (Function.invFun coherentComparison)
          (scaledPinch_comparison (q s))
      _ = coherentPinch (q s) :=
        Function.leftInverse_invFun coherentComparison_bijective.1 _
      _ = pinchedQ s := rfl
  have hboundary : ∀ (t s : unitInterval),
      s ∈ ({0, 1} : Set unitInterval) →
        Function.invFun coherentComparison (g (t, s)) = pinchedP s := by
    intro t s hs
    rcases hs with hs | hs
    · subst s
      calc
        Function.invFun coherentComparison (g (t, 0)) =
            Function.invFun coherentComparison
              (scaledPinch (F (t, 0))) := rfl
        _ = Function.invFun coherentComparison (scaledPinch origin) :=
          congrArg (fun x ↦ Function.invFun coherentComparison (scaledPinch x))
            (F.source t)
        _ = Function.invFun coherentComparison origin :=
          congrArg (Function.invFun coherentComparison) scaledPinch_origin
        _ = coherentOrigin := coherentComparison_invFun_origin
        _ = pinchedP 0 := pinchedP.source.symm
    · rw [Set.mem_singleton_iff] at hs
      subst s
      calc
        Function.invFun coherentComparison (g (t, 1)) =
            Function.invFun coherentComparison
              (scaledPinch (F (t, 1))) := rfl
        _ = Function.invFun coherentComparison (scaledPinch origin) :=
          congrArg (fun x ↦ Function.invFun coherentComparison (scaledPinch x))
            (F.target t)
        _ = Function.invFun coherentComparison origin :=
          congrArg (Function.invFun coherentComparison) scaledPinch_origin
        _ = coherentOrigin := coherentComparison_invFun_origin
        _ = pinchedP 1 := pinchedP.target.symm
  let liftedHomotopy : Path.Homotopy pinchedP pinchedQ :=
    { toFun := fun z ↦ Function.invFun coherentComparison (g z)
      continuous_toFun := hlift
      map_zero_left := hzero
      map_one_left := hone
      prop' := hboundary }
  have hpPinched : Path.Homotopic p pinchedP :=
    homotopic_coherentPinchPath p
  have hqPinched : Path.Homotopic q pinchedQ :=
    homotopic_coherentPinchPath q
  -- Join the endpoint coherent pinch homotopies to the lifted middle square.
  exact hpPinched.trans ⟨liftedHomotopy⟩ |>.trans hqPinched.symm

/-- Helper for Exercise 71.5: the canonical comparison induces a surjection
on based fundamental groups. -/
private lemma coherentComparison_fundamentalGroupMap_surjective :
    Function.Surjective
      (FundamentalGroup.mapOfEq coherentComparison coherentComparison_origin) := by
  intro P
  induction P using Path.Homotopic.Quotient.ind with
  | mk p =>
      obtain ⟨q, hq⟩ := exists_coherentLift_scaledPinchPath p
      let mappedQ : Path origin origin :=
        (q.map coherentComparison.continuous).cast
          coherentComparison_origin.symm coherentComparison_origin.symm
      let pinchedP : Path origin origin :=
        (p.map continuous_scaledPinch).cast
          scaledPinch_origin.symm scaledPinch_origin.symm
      have hmapped : mappedQ = pinchedP := by
        -- Both paths compute pointwise as the scaled pinch of `p`.
        apply Path.ext
        funext t
        exact hq t
      have hpinched :
          Path.Homotopic.Quotient.mk pinchedP =
            Path.Homotopic.Quotient.mk p := by
        exact (Path.Homotopic.Quotient.eq.mpr
          (homotopic_scaledPinchPath p)).symm
      refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q), ?_⟩
      rw [FundamentalGroup.mapOfEq_apply,
        ← Path.Homotopic.Quotient.mk_map,
        ← Path.Homotopic.Quotient.mk_cast]
      exact congrArg FundamentalGroup.fromPath
        ((congrArg Path.Homotopic.Quotient.mk hmapped).trans hpinched)

/-- Helper for Exercise 71.5: the canonical coherent comparison induces a
bijection on based fundamental groups. -/
lemma coherentComparison_fundamentalGroupMap_bijective :
    Function.Bijective
      (FundamentalGroup.mapOfEq coherentComparison coherentComparison_origin) := by
  constructor
  · -- Route correction: a global homotopy inverse is stronger than needed.
    -- Pinch a representative equality homotopy, lift its finite-component
    -- image, and recover the original coherent endpoint classes.
    intro P Q hPQ
    induction P using Path.Homotopic.Quotient.ind with
    | mk p =>
        induction Q using Path.Homotopic.Quotient.ind with
        | mk q =>
            rw [FundamentalGroup.mapOfEq_apply,
              FundamentalGroup.mapOfEq_apply,
              ← Path.Homotopic.Quotient.mk_map,
              ← Path.Homotopic.Quotient.mk_cast,
              ← Path.Homotopic.Quotient.mk_map,
              ← Path.Homotopic.Quotient.mk_cast] at hPQ
            have hambient := Path.Homotopic.Quotient.eq.mp hPQ
            have hcoherent :=
              homotopic_of_comparison_homotopic p q hambient
            exact congrArg FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.eq.mpr hcoherent)
  · exact coherentComparison_fundamentalGroupMap_surjective

/-- Helper for Exercise 71.5: equal continuous maps induce the same based
fundamental-group homomorphism, independently of the endpoint proofs. -/
lemma fundamentalGroupMapOfEq_congr
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (g h : C(X, Y)) {x : X} {y : Y} (hgh : g = h)
    (hg : g x = y) (hh : h x = y) :
    FundamentalGroup.mapOfEq g hg = FundamentalGroup.mapOfEq h hh := by
  -- Substitute the map equality; proof irrelevance identifies the endpoint witnesses.
  subst h
  rfl

/-- Helper for Exercise 71.5: based fundamental-group maps preserve composition,
independently of the endpoint proofs used to align the basepoints. -/
lemma fundamentalGroupMapOfEq_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) (hgf : (g.comp f) x = z) :
    (FundamentalGroup.mapOfEq g hg).comp (FundamentalGroup.mapOfEq f hf) =
      FundamentalGroup.mapOfEq (g.comp f) hgf := by
  -- Normalize the intermediate and target points, then use functoriality of
  -- the map on path-homotopy classes.
  subst y
  subst z
  have hg_rfl : hg = rfl := Subsingleton.elim _ _
  cases hg_rfl
  ext a
  simp only [MonoidHom.coe_comp, Function.comp_apply,
    FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl,
    Path.Homotopic.Quotient.map_comp]
  apply eq_of_heq
  exact Path.Homotopic.Quotient.cast_heq _ _

/-- Helper for Exercise 71.5: comparison after the coherent component
homeomorphism is the ordinary inclusion of that planar component. -/
private lemma coherentComparison_comp_componentHomeomorph (n : ℕ+) :
    coherentComparison.comp
        ((⟨Subtype.val, continuous_subtype_val⟩ :
            C(coherentComponent n, CoherentModel)).comp
          ⟨coherentComponentHomeomorph n,
            (coherentComponentHomeomorph n).continuous⟩) =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(component n, Space)) := by
  -- Evaluate on a component point, expose the embedding homeomorphism, and
  -- apply the comparison's component computation rule.
  apply ContinuousMap.ext
  intro x
  have hcomponent :
      ((coherentComponentHomeomorph n x : coherentComponent n) : CoherentModel) =
        coherentInclusion n x := by
    exact Topology.IsEmbedding.toHomeomorph_apply_coe
      (coherentInclusion_isClosedEmbedding n).isEmbedding x
  calc
    (coherentComparison.comp
        ((⟨Subtype.val, continuous_subtype_val⟩ :
            C(coherentComponent n, CoherentModel)).comp
          ⟨coherentComponentHomeomorph n,
            (coherentComponentHomeomorph n).continuous⟩)) x =
      coherentComparison
        ((coherentComponentHomeomorph n x : coherentComponent n) :
          CoherentModel) := rfl
    _ = coherentComparison (coherentInclusion n x) :=
      congrArg (fun q ↦ coherentComparison q) hcomponent
    _ = (x : Space) := coherentComparison_inclusion n x

/-- Helper for Exercise 71.5: the comparison-induced fundamental-group map
sends each coherent component generator to its planar included loop class. -/
lemma coherentComparison_map_coherentGenerator
    (f : ∀ n : ℕ+, Path (componentOrigin n) (componentOrigin n))
    (n : ℕ+) :
    FundamentalGroup.mapOfEq coherentComparison coherentComparison_origin
        (CircleWedge.includedLoopClass coherentComponent coherentOrigin n
          (coherentGeneratorLoop f n)) =
      CircleWedge.includedLoopClass component origin n (f n) := by
  let componentMap : C(component n, coherentComponent n) :=
    ⟨coherentComponentHomeomorph n,
      (coherentComponentHomeomorph n).continuous⟩
  let coherentInclusionMap : C(coherentComponent n, CoherentModel) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let planarInclusionMap : C(component n, Space) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let generatorClass := FundamentalGroup.fromPath (mk (f n))
  -- Record the three basepoint equations used by functoriality.
  have hcomponentBase :
      componentMap (componentOrigin n) = coherentComponentOrigin n :=
    coherentComponentHomeomorph_origin n
  have hcoherentBase :
      coherentInclusionMap (coherentComponentOrigin n) = coherentOrigin := rfl
  have hcomponentCompositeBase :
      (coherentInclusionMap.comp componentMap) (componentOrigin n) =
        coherentOrigin := by
    exact congrArg Subtype.val hcomponentBase
  have hfullCompositeBase :
      (coherentComparison.comp (coherentInclusionMap.comp componentMap))
          (componentOrigin n) = origin := by
    rw [ContinuousMap.comp_apply, hcomponentCompositeBase,
      coherentComparison_origin]
  have hplanarBase : planarInclusionMap (componentOrigin n) = origin := rfl
  -- Cache functoriality for the two successive compositions and identify the
  -- resulting continuous map with the planar subtype inclusion.
  have hcomponentComposition := fundamentalGroupMapOfEq_comp
    componentMap coherentInclusionMap hcomponentBase hcoherentBase
      hcomponentCompositeBase
  have hcomparisonComposition := fundamentalGroupMapOfEq_comp
    (coherentInclusionMap.comp componentMap) coherentComparison
      hcomponentCompositeBase coherentComparison_origin hfullCompositeBase
  have hunderlyingMap :
      coherentComparison.comp (coherentInclusionMap.comp componentMap) =
        planarInclusionMap := by
    exact coherentComparison_comp_componentHomeomorph n
  have hinducedMap := fundamentalGroupMapOfEq_congr
    (coherentComparison.comp (coherentInclusionMap.comp componentMap))
    planarInclusionMap hunderlyingMap hfullCompositeBase hplanarBase
  -- Expand the two included classes, transport the chosen component loop,
  -- and compose the three induced maps in order.
  rw [includedLoopClass_eq_mapOfEq, includedLoopClass_eq_mapOfEq,
    ← coherentGeneratorLoop_fromPath]
  calc
    FundamentalGroup.mapOfEq coherentComparison coherentComparison_origin
        (FundamentalGroup.mapOfEq coherentInclusionMap hcoherentBase
          (FundamentalGroup.mapOfEq componentMap hcomponentBase generatorClass)) =
      FundamentalGroup.mapOfEq coherentComparison coherentComparison_origin
        (FundamentalGroup.mapOfEq (coherentInclusionMap.comp componentMap)
          hcomponentCompositeBase generatorClass) := by
            exact congrArg
              (FundamentalGroup.mapOfEq coherentComparison
                coherentComparison_origin)
              (DFunLike.congr_fun hcomponentComposition generatorClass)
    _ = FundamentalGroup.mapOfEq
        (coherentComparison.comp (coherentInclusionMap.comp componentMap))
          hfullCompositeBase generatorClass := by
            exact DFunLike.congr_fun hcomparisonComposition generatorClass
    _ = FundamentalGroup.mapOfEq planarInclusionMap hplanarBase
        generatorClass := by
            exact DFunLike.congr_fun hinducedMap generatorClass

end ExpandingCircles

/-- Helper for Exercise 71.5: the planar union of expanding circles is not homeomorphic to
an `ℕ+`-indexed wedge of circles. -/
theorem expandingCircles_not_homeomorphic_wedge {X : Type u} [TopologicalSpace X]
    (S : ℕ+ → Set X) (p : X) [Topology.IsWedgeOfCircles S p] :
    ¬ Nonempty (ExpandingCircles.Space ≃ₜ X) := by
  -- A homeomorphism would transfer first countability from the metrizable
  -- planar subspace to the infinite coherent wedge.
  rintro ⟨e⟩
  letI : FirstCountableTopology X := e.symm.isInducing.firstCountableTopology
  exact Topology.IsWedgeOfCircles.not_firstCountable_of_infinite S p inferInstance

/-- Helper for Exercise 71.5: the planar union of expanding circles is not homeomorphic to
the infinite earring of `Example 71.1`. -/
theorem expandingCircles_not_homeomorphic_infiniteEarring :
    ¬ Nonempty (ExpandingCircles.Space ≃ₜ InfiniteEarring.Space) := by
  -- Compactness of the earring would transfer backward, contradicting the
  -- escaping outer points of the expanding circles.
  rintro ⟨e⟩
  letI : CompactSpace ExpandingCircles.Space := e.symm.compactSpace
  exact noncompact_univ ExpandingCircles.Space isCompact_univ

/-- Exercise 71.5: component loops generating their circle fundamental groups
map to a free basis of the fundamental group of the expanding-circle union. -/
theorem expandingCircles_fundamentalGroup_freeBasis
    (f : ∀ n : ℕ+, Path (ExpandingCircles.componentOrigin n)
      (ExpandingCircles.componentOrigin n))
    (hf : ∀ n : ℕ+,
      Subgroup.zpowers
          (FundamentalGroup.fromPath (mk (f n))) = ⊤) :
    ∃ b : FreeGroupBasis ℕ+
        (FundamentalGroup ExpandingCircles.Space ExpandingCircles.origin),
      ∀ n : ℕ+, b n = CircleWedge.includedLoopClass ExpandingCircles.component
        ExpandingCircles.origin n (f n) := by
  -- Transfer the coherent wedge basis through the comparison-induced group
  -- isomorphism; no global homotopy inverse of spaces is required.
  obtain ⟨b, hb⟩ := fundamentalGroup_freeBasis_of_circleWedge
    ExpandingCircles.coherentComponent ExpandingCircles.coherentOrigin
    (ExpandingCircles.coherentGeneratorLoop f)
    (ExpandingCircles.coherentGeneratorLoop_zpowers_eq_top f hf)
  let φ := FundamentalGroup.mapOfEq ExpandingCircles.coherentComparison
    ExpandingCircles.coherentComparison_origin
  have hφBijective : Function.Bijective φ := by
    -- The compact-image pinch argument supplies bijectivity directly.
    exact ExpandingCircles.coherentComparison_fundamentalGroupMap_bijective
  let E := MulEquiv.ofBijective φ hφBijective
  refine ⟨b.map E, ?_⟩
  intro n
  -- Compute the transported basis generator and apply comparison naturality.
  rw [FreeGroupBasis.map_apply, hb n]
  exact ExpandingCircles.coherentComparison_map_coherentGenerator
    f n
