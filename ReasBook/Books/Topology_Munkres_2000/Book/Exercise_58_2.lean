module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Topology_Munkres_2000.Book.Example_52_1
public import Topology_Munkres_2000.Book.Exercise_52_1
public import Topology_Munkres_2000.Book.Exercise_54_7.Product
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
public import Topology_Munkres_2000.Book.Theorem_58_3.HomotopyEquiv
public import Topology_Munkres_2000.Book.Example_22_5.Torus
import all Topology_Munkres_2000.Book.Example_22_5.Torus
public import Topology_Munkres_2000.Book.Proposition_58_2.HomotopyEquiv
public import Topology_Munkres_2000.Book.Example_58_3
import all Topology_Munkres_2000.Book.Example_58_3.PlaneModels
public import Topology_Munkres_2000.Book.Definition_9_0_2
public import Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
public import Topology_Munkres_2000.Book.Definition_53_4.Torus
public import Topology_Munkres_2000.Book.Definition_53_5.FigureEight
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.CompactOpen

public section

/-- Helper for Exercise 58.2: a subset viewed inside a containing subspace is
homeomorphic to its direct ambient subtype. -/
private def nestedSubsetHomeomorph {X : Type*} [TopologicalSpace X]
    (P S : Set X) (hSP : S ⊆ P) :
    (Subtype.val ⁻¹' S : Set P) ≃ₜ S :=
  { toFun := fun x ↦ ⟨x.1.1, x.2⟩
    invFun := fun x ↦ ⟨⟨x.1, hSP x.2⟩, x.2⟩
    left_inv := fun x ↦ Subtype.ext (Subtype.coe_eta x.1 _)
    right_inv := fun x ↦ Subtype.coe_eta x _
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk fun x ↦ x.2
    continuous_invFun :=
      (continuous_subtype_val.subtype_mk fun x ↦ hSP x.2).subtype_mk fun x ↦ x.2 }

/-- Helper for Exercise 58.2: norm strictly greater than one implies nonzero. -/
private lemma normGtOne_subset_complZero :
    {x : EuclideanSpace ℝ (Fin 2) | 1 < ‖x‖} ⊆ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
  -- Positive norm excludes the origin, as required by polar coordinates.
  intro x hx
  have hxpos : 0 < ‖x‖ := zero_lt_one.trans hx
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using norm_pos_iff.mp hxpos

/-- Helper for Exercise 58.2: norm at least one implies nonzero. -/
private lemma normGeOne_subset_complZero :
    {x : EuclideanSpace ℝ (Fin 2) | 1 ≤ ‖x‖} ⊆ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
  -- The unit lower bound again supplies the nonzero hypothesis of polar coordinates.
  intro x hx
  have hxpos : 0 < ‖x‖ := zero_lt_one.trans_le hx
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using norm_pos_iff.mp hxpos

/-- Helper for Exercise 58.2: polar coordinates record the norm in their radial component. -/
private lemma polarNormGtOne_iff
    (x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
    1 < ‖x.1‖ ↔ 1 < ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).2 : ℝ) := by
  -- Use the computation rule for the second polar coordinate.
  rw [homeomorphUnitSphereProd_apply_snd_coe]

/-- Helper for Exercise 58.2: polar coordinates record weak unit-radius bounds in their
radial component. -/
private lemma polarNormGeOne_iff
    (x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
    1 ≤ ‖x.1‖ ↔ 1 ≤ ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).2 : ℝ) := by
  -- The same computation rule also preserves non-strict inequalities.
  rw [homeomorphUnitSphereProd_apply_snd_coe]

/-- Helper for Exercise 58.2: a radius strictly greater than one is positive. -/
private lemma gtOne_mem_IoiZero {r : ℝ} (hr : 1 < r) : r ∈ Set.Ioi (0 : ℝ) := by
  -- Compare the radius with zero through one.
  exact zero_lt_one.trans hr

/-- Helper for Exercise 58.2: a radius at least one is positive. -/
private lemma geOne_mem_IoiZero {r : ℝ} (hr : 1 ≤ r) : r ∈ Set.Ioi (0 : ℝ) := by
  -- Compare the radius with zero through its unit lower bound.
  exact zero_lt_one.trans_le hr

/-- Helper for Exercise 58.2: imposing radius greater than one after polar coordinates
is the product with `Set.Ioi 1`. -/
private def polarRadiusGtOneHomeomorph :
    {z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Ioi (0 : ℝ) //
      1 < z.2.1} ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Ioi (1 : ℝ) :=
  { toFun := fun z ↦ (z.1.1, ⟨z.1.2.1, z.2⟩)
    invFun := fun z ↦ ⟨(z.1, ⟨z.2.1, gtOne_mem_IoiZero z.2.2⟩), z.2.2⟩
    left_inv := fun z ↦
      Subtype.ext (Prod.ext rfl (Subtype.coe_eta z.1.2 _))
    right_inv := fun z ↦ Prod.ext rfl (Subtype.coe_eta z.2 _)
    continuous_toFun :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk
          fun z ↦ z.2)
    continuous_invFun :=
      ((continuous_fst.prodMk
          ((continuous_subtype_val.comp continuous_snd).subtype_mk
            fun z ↦ gtOne_mem_IoiZero z.2.2)).subtype_mk fun z ↦ z.2.2) }

/-- Helper for Exercise 58.2: imposing radius at least one after polar coordinates
is the product with `Set.Ici 1`. -/
private def polarRadiusGeOneHomeomorph :
    {z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Ioi (0 : ℝ) //
      1 ≤ z.2.1} ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Ici (1 : ℝ) :=
  { toFun := fun z ↦ (z.1.1, ⟨z.1.2.1, z.2⟩)
    invFun := fun z ↦ ⟨(z.1, ⟨z.2.1, geOne_mem_IoiZero z.2.2⟩), z.2.2⟩
    left_inv := fun z ↦
      Subtype.ext (Prod.ext rfl (Subtype.coe_eta z.1.2 _))
    right_inv := fun z ↦ Prod.ext rfl (Subtype.coe_eta z.2 _)
    continuous_toFun :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk
          fun z ↦ z.2)
    continuous_invFun :=
      ((continuous_fst.prodMk
          ((continuous_subtype_val.comp continuous_snd).subtype_mk
            fun z ↦ geOne_mem_IoiZero z.2.2)).subtype_mk fun z ↦ z.2.2) }

/-- Helper for Exercise 58.2: the exterior of the closed unit disk has angular and
strict radial polar coordinates. -/
private noncomputable def exteriorClosedDiskPolarHomeomorph :
    {x : EuclideanSpace ℝ (Fin 2) // 1 < ‖x‖} ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Ioi (1 : ℝ) :=
  (nestedSubsetHomeomorph ({0}ᶜ) {x | 1 < ‖x‖} normGtOne_subset_complZero).symm.trans <|
    ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2))).subtype polarNormGtOne_iff).trans
      polarRadiusGtOneHomeomorph

/-- Helper for Exercise 58.2: the exterior of the open unit disk has angular and
weak radial polar coordinates. -/
private noncomputable def exteriorOpenDiskPolarHomeomorph :
    {x : EuclideanSpace ℝ (Fin 2) // 1 ≤ ‖x‖} ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Ici (1 : ℝ) :=
  (nestedSubsetHomeomorph ({0}ᶜ) {x | 1 ≤ ‖x‖} normGeOne_subset_complZero).symm.trans <|
    ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2))).subtype polarNormGeOne_iff).trans
      polarRadiusGeOneHomeomorph

/-- Helper for Exercise 58.2: complex coordinates identify the Euclidean unit sphere
with the canonical circle. -/
private lemma euclideanPlaneComplex_mem_unitSphere (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ Metric.sphere (0 : ℂ) 1 := by
  -- Both predicates reduce to the norm-one equation preserved by the linear isometry.
  simp only [Metric.mem_sphere, dist_zero_right]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm ▸ Iff.rfl

/-- Helper for Exercise 58.2: the Euclidean unit sphere is homeomorphic to `Circle`. -/
private noncomputable def euclideanSphereHomeomorphCircle :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    euclideanPlaneComplex_mem_unitSphere

/-- Helper for Exercise 58.2: the radial-whisker space contains the unit-radius copy of
its angular space and arbitrary radii over `D`. -/
private abbrev RadialWhisker (S : Type*) [TopologicalSpace S] (D : Set S) :=
  {z : S × Set.Ioi (0 : ℝ) // z.2.1 = 1 ∨ z.1 ∈ D}

/-- Helper for Exercise 58.2: projection forgets the radial coordinate of a radial whisker. -/
private def radialWhiskerProjection (S : Type*) [TopologicalSpace S] (D : Set S) :
    C(RadialWhisker S D, S) :=
  ⟨fun z ↦ z.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- Helper for Exercise 58.2: radius one belongs to every radial whisker. -/
private lemma radialWhiskerSection_mem (S : Type*) [TopologicalSpace S]
    (D : Set S) (s : S) :
    ((s, ⟨1, Set.mem_Ioi.mpr zero_lt_one⟩) : S × Set.Ioi (0 : ℝ)).2.1 = 1 ∨ s ∈ D := by
  -- The defining disjunction holds through its unit-radius branch.
  exact Or.inl rfl

/-- Helper for Exercise 58.2: the unit-radius section embeds the angular space in its
radial whisker. -/
private def radialWhiskerSection (S : Type*) [TopologicalSpace S] (D : Set S) :
    C(S, RadialWhisker S D) :=
  ⟨fun s ↦ ⟨(s, ⟨1, Set.mem_Ioi.mpr zero_lt_one⟩), radialWhiskerSection_mem S D s⟩,
    (continuous_id.prodMk continuous_const).subtype_mk fun s ↦
      radialWhiskerSection_mem S D s⟩

/-- Helper for Exercise 58.2: linearly moving a positive radius toward one stays positive. -/
private def radialWhiskerRadius (t : unitInterval) (r : Set.Ioi (0 : ℝ)) : ℝ :=
  1 + (t : ℝ) * (r.1 - 1)

/-- Helper for Exercise 58.2: the interpolated radial-whisker radius is positive. -/
private lemma radialWhiskerRadius_pos (t : unitInterval) (r : Set.Ioi (0 : ℝ)) :
    0 < radialWhiskerRadius t r := by
  -- Express the interpolation as a convex combination of two positive radii.
  rcases t.2.2.eq_or_lt with hone | hlt
  · unfold radialWhiskerRadius
    rw [hone]
    norm_num
    exact r.2
  · have hmul : 0 ≤ (t : ℝ) * r.1 := mul_nonneg t.2.1 r.2.le
    unfold radialWhiskerRadius
    nlinarith

/-- Helper for Exercise 58.2: radial interpolation preserves the radial-whisker predicate. -/
private lemma radialWhiskerInterpolation_mem
    (S : Type*) [TopologicalSpace S] (D : Set S)
    (t : unitInterval) (z : RadialWhisker S D) :
    radialWhiskerRadius t z.1.2 = 1 ∨ z.1.1 ∈ D := by
  -- Unit-radius points remain fixed; all other points retain their angular membership in `D`.
  rcases z.2 with hunit | hD
  · left
    unfold radialWhiskerRadius
    rw [hunit]
    ring
  · exact Or.inr hD

/-- Helper for Exercise 58.2: the radial contraction evaluated at a parameter and point. -/
private def radialWhiskerHomotopyValue
    (S : Type*) [TopologicalSpace S] (D : Set S)
    (tz : unitInterval × RadialWhisker S D) : RadialWhisker S D :=
  ⟨(tz.2.1.1, ⟨radialWhiskerRadius tz.1 tz.2.1.2,
      radialWhiskerRadius_pos tz.1 tz.2.1.2⟩),
    radialWhiskerInterpolation_mem S D tz.1 tz.2⟩

/-- Helper for Exercise 58.2: the radial contraction varies continuously. -/
private lemma continuous_radialWhiskerHomotopyValue
    (S : Type*) [TopologicalSpace S] (D : Set S) :
    Continuous (radialWhiskerHomotopyValue S D) := by
  -- Continuity is componentwise after exposing the affine radius formula.
  unfold radialWhiskerHomotopyValue radialWhiskerRadius
  fun_prop

/-- Helper for Exercise 58.2: the radial contraction starts at the unit-radius section. -/
private lemma radialWhiskerHomotopyValue_zero
    (S : Type*) [TopologicalSpace S] (D : Set S) (z : RadialWhisker S D) :
    radialWhiskerHomotopyValue S D (0, z) =
      radialWhiskerSection S D (radialWhiskerProjection S D z) := by
  -- At parameter zero, the affine radius is exactly one.
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    norm_num [radialWhiskerHomotopyValue, radialWhiskerRadius, radialWhiskerSection,
      radialWhiskerProjection]

/-- Helper for Exercise 58.2: the radial contraction ends at the original point. -/
private lemma radialWhiskerHomotopyValue_one
    (S : Type*) [TopologicalSpace S] (D : Set S) (z : RadialWhisker S D) :
    radialWhiskerHomotopyValue S D (1, z) = z := by
  -- At parameter one, the affine radius recovers the original radius.
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    norm_num [radialWhiskerHomotopyValue, radialWhiskerRadius]

/-- Helper for Exercise 58.2: radial interpolation is a homotopy from the section-projection
composite to the identity. -/
private def radialWhiskerHomotopy
    (S : Type*) [TopologicalSpace S] (D : Set S) :
    ContinuousMap.Homotopy
      ((radialWhiskerSection S D).comp (radialWhiskerProjection S D))
      (ContinuousMap.id (RadialWhisker S D)) :=
  { toFun := radialWhiskerHomotopyValue S D
    continuous_toFun := continuous_radialWhiskerHomotopyValue S D
    map_zero_left := radialWhiskerHomotopyValue_zero S D
    map_one_left := radialWhiskerHomotopyValue_one S D }

/-- Helper for Exercise 58.2: projection after the unit-radius section is homotopic to the
identity of the angular space. -/
private lemma radialWhiskerProjection_section_homotopic
    (S : Type*) [TopologicalSpace S] (D : Set S) :
    ((radialWhiskerProjection S D).comp (radialWhiskerSection S D)).Homotopic
      (ContinuousMap.id S) := by
  -- The composite is pointwise the identity, hence reflexively homotopic to it.
  have heq : (radialWhiskerProjection S D).comp (radialWhiskerSection S D) =
      ContinuousMap.id S := by
    ext s
    rfl
  rw [heq]

/-- Helper for Exercise 58.2: every radial whisker is homotopy equivalent to its angular
space. -/
private def radialWhiskerHomotopyEquiv
    (S : Type*) [TopologicalSpace S] (D : Set S) :
    ContinuousMap.HomotopyEquiv (RadialWhisker S D) S :=
  { toFun := radialWhiskerProjection S D
    invFun := radialWhiskerSection S D
    left_inv := ⟨radialWhiskerHomotopy S D⟩
    right_inv := radialWhiskerProjection_section_homotopic S D }

/-- Helper for Exercise 58.2: a homotopy equivalence induces a multiplicative equivalence
of fundamental groups. -/
private noncomputable def ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  MulEquiv.ofBijective (FundamentalGroup.map e.toFun x)
    (e.fundamentalGroupMap_bijective x)

/-- Helper for Exercise 58.2: the unit directions on the positive horizontal ray. -/
private def positiveRayDirections :
    Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  {s | 0 < s.1 0 ∧ s.1 1 = 0}

/-- Helper for Exercise 58.2: the unit directions in the open right half-plane. -/
private def rightHalfPlaneDirections :
    Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  {s | 0 < s.1 0}

/-- Helper for Exercise 58.2: each coordinate of the angular polar component is the
corresponding coordinate divided by the norm. -/
private lemma polarDirection_apply
    (x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) (i : Fin 2) :
    ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).1 :
      EuclideanSpace ℝ (Fin 2)) i = ‖x.1‖⁻¹ * x.1 i := by
  -- Expand the angular-coordinate computation rule and evaluate the scalar multiple.
  rw [homeomorphUnitSphereProd_apply_fst_coe]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]

/-- Helper for Exercise 58.2: the circle-plus-positive-ray predicate matches the generic
radial-whisker predicate in polar coordinates. -/
private lemma polarCircleUnionRay_iff
    (x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
    (‖x.1‖ = 1 ∨ (0 < x.1 0 ∧ x.1 1 = 0)) ↔
      ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).2.1 = 1 ∨
        (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).1 ∈
          positiveRayDirections) := by
  -- The radial equality is immediate; positive scaling preserves the ray direction.
  have hxnorm : 0 < ‖x.1‖ := norm_pos_iff.mpr x.2
  have hinv : 0 < ‖x.1‖⁻¹ := inv_pos.mpr hxnorm
  constructor
  · intro hx
    rcases hx with hcircle | hray
    · left
      rwa [homeomorphUnitSphereProd_apply_snd_coe]
    · right
      change 0 < ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).1 :
        EuclideanSpace ℝ (Fin 2)) 0 ∧
          ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).1 :
            EuclideanSpace ℝ (Fin 2)) 1 = 0
      rw [polarDirection_apply x 0, polarDirection_apply x 1]
      exact ⟨mul_pos hinv hray.1, mul_eq_zero_of_right _ hray.2⟩
  · intro hx
    rcases hx with hcircle | hray
    · left
      rwa [homeomorphUnitSphereProd_apply_snd_coe] at hcircle
    · right
      change 0 < ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).1 :
        EuclideanSpace ℝ (Fin 2)) 0 ∧
          ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).1 :
            EuclideanSpace ℝ (Fin 2)) 1 = 0 at hray
      rw [polarDirection_apply x 0, polarDirection_apply x 1] at hray
      exact ⟨pos_of_mul_pos_right hray.1 hinv.le,
        (mul_eq_zero.mp hray.2).resolve_left hinv.ne'⟩

/-- Helper for Exercise 58.2: the circle-plus-right-half-plane predicate matches the generic
radial-whisker predicate in polar coordinates. -/
private lemma polarCircleUnionHalfPlane_iff
    (x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
    (‖x.1‖ = 1 ∨ 0 < x.1 0) ↔
      ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).2.1 = 1 ∨
        (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).1 ∈
          rightHalfPlaneDirections) := by
  -- As above, the positive normalization factor preserves the sign of the first coordinate.
  have hxnorm : 0 < ‖x.1‖ := norm_pos_iff.mpr x.2
  have hinv : 0 < ‖x.1‖⁻¹ := inv_pos.mpr hxnorm
  constructor
  · intro hx
    rcases hx with hcircle | hhalf
    · left
      rwa [homeomorphUnitSphereProd_apply_snd_coe]
    · right
      change 0 < ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).1 :
        EuclideanSpace ℝ (Fin 2)) 0
      rw [polarDirection_apply x 0]
      exact mul_pos hinv hhalf
  · intro hx
    rcases hx with hcircle | hhalf
    · left
      rwa [homeomorphUnitSphereProd_apply_snd_coe] at hcircle
    · right
      change 0 < ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).1 :
        EuclideanSpace ℝ (Fin 2)) 0 at hhalf
      rw [polarDirection_apply x 0] at hhalf
      exact pos_of_mul_pos_right hhalf hinv.le

/-- Helper for Exercise 58.2: the positive-ray polar predicate also matches the nested
preimage spelling used by `Homeomorph.subtype`. -/
private lemma polarCircleUnionRay_preimage_iff
    (x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
    x ∈ Subtype.val ⁻¹'
        {y : EuclideanSpace ℝ (Fin 2) | ‖y‖ = 1 ∨ (0 < y 0 ∧ y 1 = 0)} ↔
      ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).2.1 = 1 ∨
        (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).1 ∈
          positiveRayDirections) := by
  -- Unfolding preimage membership recovers the preceding polar equivalence exactly.
  exact polarCircleUnionRay_iff x

/-- Helper for Exercise 58.2: the half-plane polar predicate also matches the nested
preimage spelling used by `Homeomorph.subtype`. -/
private lemma polarCircleUnionHalfPlane_preimage_iff
    (x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
    x ∈ Subtype.val ⁻¹'
        {y : EuclideanSpace ℝ (Fin 2) | ‖y‖ = 1 ∨ 0 < y 0} ↔
      ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).2.1 = 1 ∨
        (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2)) x).1 ∈
          rightHalfPlaneDirections) := by
  -- Unfolding preimage membership recovers the preceding polar equivalence exactly.
  exact polarCircleUnionHalfPlane_iff x

/-- Helper for Exercise 58.2: every point of the circle union the positive ray is nonzero. -/
private lemma circleUnionRay_subset_complZero :
    {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ = 1 ∨ (0 < x 0 ∧ x 1 = 0)} ⊆
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
  -- Either unit norm or a positive first coordinate excludes the origin.
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hzero
  subst x
  rcases hx with hnorm | hcoord
  · simp only [norm_zero, zero_ne_one] at hnorm
  · have : ¬(0 : ℝ) < 0 := lt_irrefl 0
    apply this
    simpa only [WithLp.ofLp_zero, Pi.zero_apply] using hcoord.1

/-- Helper for Exercise 58.2: every point of the circle union the right half-plane is nonzero. -/
private lemma circleUnionHalfPlane_subset_complZero :
    {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ = 1 ∨ 0 < x 0} ⊆
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
  -- The two branches exclude zero for the same norm and coordinate reasons.
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hzero
  subst x
  rcases hx with hnorm | hcoord
  · simp only [norm_zero, zero_ne_one] at hnorm
  · have : ¬(0 : ℝ) < 0 := lt_irrefl 0
    apply this
    simpa only [WithLp.ofLp_zero, Pi.zero_apply] using hcoord

/-- Helper for Exercise 58.2: polar coordinates identify the circle union the positive ray
with its radial-whisker model. -/
private noncomputable def circleUnionRayPolarHomeomorph :
    {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1 ∨ (0 < x 0 ∧ x 1 = 0)} ≃ₜ
      RadialWhisker (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        positiveRayDirections :=
  (nestedSubsetHomeomorph ({0}ᶜ)
    {x | ‖x‖ = 1 ∨ (0 < x 0 ∧ x 1 = 0)} circleUnionRay_subset_complZero).symm.trans
      ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2))).subtype
        polarCircleUnionRay_preimage_iff)

/-- Helper for Exercise 58.2: polar coordinates identify the circle union the right
half-plane with its radial-whisker model. -/
private noncomputable def circleUnionHalfPlanePolarHomeomorph :
    {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1 ∨ 0 < x 0} ≃ₜ
      RadialWhisker (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        rightHalfPlaneDirections :=
  (nestedSubsetHomeomorph ({0}ᶜ)
    {x | ‖x‖ = 1 ∨ 0 < x 0} circleUnionHalfPlane_subset_complZero).symm.trans
      ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 2))).subtype
        polarCircleUnionHalfPlane_preimage_iff)

/-- Helper for Exercise 58.2: the circle union the positive ray is homotopy equivalent
to `Circle`. -/
private noncomputable def circleUnionRayHomotopyEquivCircle :
    ContinuousMap.HomotopyEquiv
      {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1 ∨ (0 < x 0 ∧ x 1 = 0)} Circle :=
  circleUnionRayPolarHomeomorph.toHomotopyEquiv |>.trans
    (radialWhiskerHomotopyEquiv _ positiveRayDirections) |>.trans
      euclideanSphereHomeomorphCircle.toHomotopyEquiv

/-- Helper for Exercise 58.2: the circle union the right half-plane is homotopy equivalent
to `Circle`. -/
private noncomputable def circleUnionHalfPlaneHomotopyEquivCircle :
    ContinuousMap.HomotopyEquiv
      {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1 ∨ 0 < x 0} Circle :=
  circleUnionHalfPlanePolarHomeomorph.toHomotopyEquiv |>.trans
    (radialWhiskerHomotopyEquiv _ rightHalfPlaneDirections) |>.trans
      euclideanSphereHomeomorphCircle.toHomotopyEquiv

/-- Part (1) of Exercise 58.2: The fundamental group of the solid torus `B² × S¹` is infinite
cyclic. -/
theorem fundamentalGroup_solidTorus (p : B² × Circle) :
    Nonempty (FundamentalGroup (B² × Circle) p ≃* Multiplicative ℤ) := by
  -- Split the product fundamental group and discard the contractible disk factor.
  letI : Subsingleton (FundamentalGroup B² p.1) :=
    Convex.subsingleton_fundamentalGroup (convex_closedBall 0 1) p.1
  letI : Unique (FundamentalGroup B² p.1) :=
    ⟨⟨1⟩, fun x ↦ Subsingleton.elim x 1⟩
  -- Transport the remaining circle basepoint to `1` and use the standard winding number.
  exact ⟨(FundamentalGroup.prodMulEquiv p.1 p.2).trans <|
    MulEquiv.uniqueProd.trans <|
      (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected p.2 1).trans
        Circle.fundamentalGroupEquivInt⟩

/-- Helper for Exercise 58.2: one half belongs to the unit interval. -/
private lemma oneHalf_mem_unitInterval : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  -- The endpoint inequalities are numerical.
  norm_num

/-- Helper for Exercise 58.2: the midpoint of the unit interval. -/
private noncomputable def unitIntervalMidpoint : unitInterval :=
  ⟨1 / 2, oneHalf_mem_unitInterval⟩

/-- Helper for Exercise 58.2: the midpoint is not the zero endpoint. -/
private lemma unitIntervalMidpoint_ne_zero : unitIntervalMidpoint ≠ 0 := by
  -- Equality of subtypes would force `1/2 = 0` in `ℝ`.
  intro h
  have hval := congrArg Subtype.val h
  norm_num [unitIntervalMidpoint] at hval

/-- Helper for Exercise 58.2: the midpoint is not the one endpoint. -/
private lemma unitIntervalMidpoint_ne_one : unitIntervalMidpoint ≠ 1 := by
  -- Equality of subtypes would force `1/2 = 1` in `ℝ`.
  intro h
  have hval := congrArg Subtype.val h
  norm_num [unitIntervalMidpoint] at hval

/-- Helper for Exercise 58.2: endpoint identification with the midpoint is ordinary equality. -/
private lemma endpointSetoid_midpoint_iff (x : unitInterval) :
    unitInterval.endpointSetoid x unitIntervalMidpoint ↔ x = unitIntervalMidpoint := by
  -- The two exceptional endpoint branches are impossible for the midpoint.
  rw [unitInterval.endpointSetoid_iff]
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact hx
    · rcases hx with hx | hx
      · exact (unitIntervalMidpoint_ne_one hx.2).elim
      · exact (unitIntervalMidpoint_ne_zero hx.2).elim
  · exact Or.inl

/-- Helper for Exercise 58.2: the center of the unit square. -/
private noncomputable def puncturedSquareCenter : unitInterval × unitInterval :=
  (unitIntervalMidpoint, unitIntervalMidpoint)

/-- Helper for Exercise 58.2: the corresponding centered point of the additive torus. -/
private noncomputable def additiveTorusCenter : UnitAddCircle × UnitAddCircle :=
  ((1 / 2 : ℝ), (1 / 2 : ℝ))

/-- Helper for Exercise 58.2: the square center maps to the additive-torus center. -/
private lemma toTorus_puncturedSquareCenter :
    TorusSquare.toTorus puncturedSquareCenter = additiveTorusCenter := by
  -- Both maps are coordinatewise coercion of the real midpoint.
  rfl

/-- Helper for Exercise 58.2: the center is the unique square representative of the
centered additive-torus point. -/
private lemma toTorus_eq_additiveTorusCenter_iff
    (x : unitInterval × unitInterval) :
    TorusSquare.toTorus x = additiveTorusCenter ↔ x = puncturedSquareCenter := by
  -- The quotient relation is coordinatewise endpoint identification, whose exceptional
  -- endpoint branches cannot meet the midpoint.
  rw [← toTorus_puncturedSquareCenter]
  change TorusSquare.identified x puncturedSquareCenter ↔ x = puncturedSquareCenter
  rw [TorusSquare.identified_iff]
  unfold puncturedSquareCenter
  rw [endpointSetoid_midpoint_iff, endpointSetoid_midpoint_iff]
  constructor
  · intro h
    exact Prod.ext h.1 h.2
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Helper for Exercise 58.2: the punctured unit square above the centered torus puncture. -/
private abbrev CenteredPuncturedSquare :=
  {x : unitInterval × unitInterval //
    TorusSquare.toTorus x ≠ additiveTorusCenter}

/-- Helper for Exercise 58.2: the additive torus with its centered point deleted. -/
private abbrev CenteredPuncturedAdditiveTorus :=
  ({additiveTorusCenter}ᶜ : Set (UnitAddCircle × UnitAddCircle))

/-- Helper for Exercise 58.2: select a coordinate of a point in the unit square. -/
private def puncturedSquareCoordinate
    (x : unitInterval × unitInterval) (i : Fin 2) : unitInterval :=
  Fin.cases x.1 (fun _ ↦ x.2) i

/-- Helper for Exercise 58.2: coordinate zero selects the first square coordinate. -/
private lemma puncturedSquareCoordinate_zero (x : unitInterval × unitInterval) :
    puncturedSquareCoordinate x 0 = x.1 := by
  -- Evaluate `Fin.cases` at zero.
  rfl

/-- Helper for Exercise 58.2: coordinate one selects the second square coordinate. -/
private lemma puncturedSquareCoordinate_one (x : unitInterval × unitInterval) :
    puncturedSquareCoordinate x 1 = x.2 := by
  -- Evaluate `Fin.cases` at one.
  rfl

/-- Helper for Exercise 58.2: the maximum displacement of a punctured-square point
from the square center. -/
private noncomputable def puncturedSquareRadius (x : CenteredPuncturedSquare) : ℝ :=
  max |(x.1.1 : ℝ) - 1 / 2| |(x.1.2 : ℝ) - 1 / 2|

/-- Helper for Exercise 58.2: a punctured-square point has positive maximum displacement. -/
private lemma puncturedSquareRadius_pos (x : CenteredPuncturedSquare) :
    0 < puncturedSquareRadius x := by
  -- Zero maximum displacement would make both coordinates the midpoint and hit the puncture.
  have hnonneg : 0 ≤ puncturedSquareRadius x :=
    le_max_of_le_left (abs_nonneg _)
  refine hnonneg.lt_of_ne ?_
  intro hradius
  have hfirst_le : |(x.1.1 : ℝ) - 1 / 2| ≤ 0 := by
    simpa only [puncturedSquareRadius, hradius] using
      (le_max_left |(x.1.1 : ℝ) - 1 / 2| |(x.1.2 : ℝ) - 1 / 2|)
  have hsecond_le : |(x.1.2 : ℝ) - 1 / 2| ≤ 0 := by
    simpa only [puncturedSquareRadius, hradius] using
      (le_max_right |(x.1.1 : ℝ) - 1 / 2| |(x.1.2 : ℝ) - 1 / 2|)
  have hfirst : x.1.1 = unitIntervalMidpoint := by
    apply Subtype.ext
    have habs : |(x.1.1 : ℝ) - 1 / 2| = 0 :=
      le_antisymm hfirst_le (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  have hsecond : x.1.2 = unitIntervalMidpoint := by
    apply Subtype.ext
    have habs : |(x.1.2 : ℝ) - 1 / 2| = 0 :=
      le_antisymm hsecond_le (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  apply x.2
  rw [toTorus_eq_additiveTorusCenter_iff]
  exact Prod.ext hfirst hsecond

/-- Helper for Exercise 58.2: every unit-square point is at maximum displacement at most
one half. -/
private lemma puncturedSquareRadius_le_oneHalf (x : CenteredPuncturedSquare) :
    puncturedSquareRadius x ≤ 1 / 2 := by
  -- Each coordinate lies in `[0,1]`, hence differs from the midpoint by at most `1/2`.
  apply max_le
  · rw [abs_le]
    constructor <;> nlinarith [x.1.1.2.1, x.1.1.2.2]
  · rw [abs_le]
    constructor <;> nlinarith [x.1.2.2.1, x.1.2.2.2]

/-- Helper for Exercise 58.2: the radial boundary scale of a punctured-square point. -/
private noncomputable def puncturedSquareBoundaryScale (x : CenteredPuncturedSquare) : ℝ :=
  (2 * puncturedSquareRadius x)⁻¹

/-- Helper for Exercise 58.2: the maximum-displacement radius varies continuously. -/
private lemma continuous_puncturedSquareRadius :
    Continuous puncturedSquareRadius := by
  -- Absolute value and maximum preserve continuity of the two coordinate displacements.
  unfold puncturedSquareRadius
  fun_prop

/-- Helper for Exercise 58.2: the radial boundary scale varies continuously away from the
deleted center. -/
private lemma continuous_puncturedSquareBoundaryScale :
    Continuous puncturedSquareBoundaryScale := by
  -- Positivity of the radius makes inversion continuous on the punctured square.
  unfold puncturedSquareBoundaryScale
  apply Continuous.inv₀
  · exact continuous_const.mul continuous_puncturedSquareRadius
  · intro x
    exact mul_ne_zero (by norm_num) (puncturedSquareRadius_pos x).ne'

/-- Helper for Exercise 58.2: the radial boundary scale is at least one. -/
private lemma one_le_puncturedSquareBoundaryScale (x : CenteredPuncturedSquare) :
    1 ≤ puncturedSquareBoundaryScale x := by
  -- The positive doubled radius is at most one, so its inverse is at least one.
  rw [puncturedSquareBoundaryScale,
    one_le_inv₀ (mul_pos (by norm_num) (puncturedSquareRadius_pos x))]
  nlinarith [puncturedSquareRadius_le_oneHalf x]

/-- Helper for Exercise 58.2: a scaled displacement remains within one half of the center. -/
private lemma puncturedSquare_scaledDisplacement_abs_le
    (x : CenteredPuncturedSquare) (i : Fin 2) :
    |puncturedSquareBoundaryScale x *
        ((puncturedSquareCoordinate x.1 i : ℝ) - 1 / 2)| ≤ 1 / 2 := by
  -- The coordinate displacement is bounded by the maximum displacement, which is
  -- normalized to exactly one half by the boundary scale.
  have hcoord : |(puncturedSquareCoordinate x.1 i : ℝ) - 1 / 2| ≤
      puncturedSquareRadius x := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hscale_nonneg : 0 ≤ puncturedSquareBoundaryScale x :=
    (one_le_puncturedSquareBoundaryScale x).trans' zero_le_one
  rw [abs_mul, abs_of_nonneg hscale_nonneg]
  calc
    puncturedSquareBoundaryScale x *
        |(puncturedSquareCoordinate x.1 i : ℝ) - 1 / 2| ≤
        puncturedSquareBoundaryScale x * puncturedSquareRadius x :=
      mul_le_mul_of_nonneg_left hcoord hscale_nonneg
    _ = 1 / 2 := by
      rw [puncturedSquareBoundaryScale]
      field_simp [puncturedSquareRadius_pos x |>.ne']

/-- Helper for Exercise 58.2: each radial projection coordinate lies in the unit interval. -/
private lemma puncturedSquareProjectionCoordinate_mem
    (x : CenteredPuncturedSquare) (i : Fin 2) :
    1 / 2 + puncturedSquareBoundaryScale x *
        ((puncturedSquareCoordinate x.1 i : ℝ) - 1 / 2) ∈
      Set.Icc (0 : ℝ) 1 := by
  -- Translate the half-unit absolute bound into the two interval inequalities.
  have habs := puncturedSquare_scaledDisplacement_abs_le x i
  rw [abs_le] at habs
  rcases habs with ⟨hlower, hupper⟩
  constructor <;> linarith

/-- Helper for Exercise 58.2: the first radial projection coordinate lies in the unit interval. -/
private lemma puncturedSquareProjectionFirst_mem (x : CenteredPuncturedSquare) :
    1 / 2 + puncturedSquareBoundaryScale x * ((x.1.1 : ℝ) - 1 / 2) ∈
      Set.Icc (0 : ℝ) 1 := by
  -- Specialize the coordinatewise interval bound to the first coordinate.
  simpa only [puncturedSquareCoordinate_zero] using
    puncturedSquareProjectionCoordinate_mem x 0

/-- Helper for Exercise 58.2: the second radial projection coordinate lies in the unit interval. -/
private lemma puncturedSquareProjectionSecond_mem (x : CenteredPuncturedSquare) :
    1 / 2 + puncturedSquareBoundaryScale x * ((x.1.2 : ℝ) - 1 / 2) ∈
      Set.Icc (0 : ℝ) 1 := by
  -- Specialize the coordinatewise interval bound to the second coordinate.
  simpa only [puncturedSquareCoordinate_one] using
    puncturedSquareProjectionCoordinate_mem x 1

/-- Helper for Exercise 58.2: the radial projection from the deleted center to the square
boundary. -/
private noncomputable def puncturedSquareProjection
    (x : CenteredPuncturedSquare) : unitInterval × unitInterval :=
  (⟨1 / 2 + puncturedSquareBoundaryScale x * ((x.1.1 : ℝ) - 1 / 2),
      puncturedSquareProjectionFirst_mem x⟩,
    ⟨1 / 2 + puncturedSquareBoundaryScale x * ((x.1.2 : ℝ) - 1 / 2),
      puncturedSquareProjectionSecond_mem x⟩)

/-- Helper for Exercise 58.2: the four-edge boundary predicate of the unit square. -/
private def puncturedSquareBoundary : Set (unitInterval × unitInterval) :=
  {x | x.1 = 0 ∨ x.1 = 1 ∨ x.2 = 0 ∨ x.2 = 1}

/-- Helper for Exercise 58.2: the radial boundary scale normalizes the maximum displacement
to one half. -/
private lemma puncturedSquareBoundaryScale_mul_radius (x : CenteredPuncturedSquare) :
    puncturedSquareBoundaryScale x * puncturedSquareRadius x = 1 / 2 := by
  -- Cancel the positive radius in the reciprocal formula.
  rw [puncturedSquareBoundaryScale]
  field_simp [puncturedSquareRadius_pos x |>.ne']

/-- Helper for Exercise 58.2: a boundary point has maximum displacement exactly one half. -/
private lemma puncturedSquareRadius_eq_oneHalf_of_mem_boundary
    (x : CenteredPuncturedSquare) (hx : x.1 ∈ puncturedSquareBoundary) :
    puncturedSquareRadius x = 1 / 2 := by
  -- Every boundary branch contributes a coordinate with absolute displacement one half.
  apply le_antisymm (puncturedSquareRadius_le_oneHalf x)
  rcases hx with hx | hx | hx | hx
  · calc
      1 / 2 = |(x.1.1 : ℝ) - 1 / 2| := by rw [hx]; norm_num
      _ ≤ puncturedSquareRadius x := le_max_left _ _
  · calc
      1 / 2 = |(x.1.1 : ℝ) - 1 / 2| := by rw [hx]; norm_num
      _ ≤ puncturedSquareRadius x := le_max_left _ _
  · calc
      1 / 2 = |(x.1.2 : ℝ) - 1 / 2| := by rw [hx]; norm_num
      _ ≤ puncturedSquareRadius x := le_max_right _ _
  · calc
      1 / 2 = |(x.1.2 : ℝ) - 1 / 2| := by rw [hx]; norm_num
      _ ≤ puncturedSquareRadius x := le_max_right _ _

/-- Helper for Exercise 58.2: the radial boundary scale is one on the square boundary. -/
private lemma puncturedSquareBoundaryScale_eq_one_of_mem_boundary
    (x : CenteredPuncturedSquare) (hx : x.1 ∈ puncturedSquareBoundary) :
    puncturedSquareBoundaryScale x = 1 := by
  -- Substitute the boundary radius into the reciprocal scale.
  rw [puncturedSquareBoundaryScale,
    puncturedSquareRadius_eq_oneHalf_of_mem_boundary x hx]
  norm_num

/-- Helper for Exercise 58.2: radial projection lands on the square boundary. -/
private lemma puncturedSquareProjection_mem_boundary (x : CenteredPuncturedSquare) :
    puncturedSquareProjection x ∈ puncturedSquareBoundary := by
  -- A coordinate attaining the maximum displacement is sent to an endpoint.
  have hscale : 0 ≤ puncturedSquareBoundaryScale x :=
    zero_le_one.trans (one_le_puncturedSquareBoundaryScale x)
  rcases le_total |(x.1.1 : ℝ) - 1 / 2| |(x.1.2 : ℝ) - 1 / 2| with hfirst | hsecond
  · have hradius : puncturedSquareRadius x = |(x.1.2 : ℝ) - 1 / 2| :=
      max_eq_right hfirst
    have habs : |puncturedSquareBoundaryScale x * ((x.1.2 : ℝ) - 1 / 2)| =
        1 / 2 := by
      rw [abs_mul, abs_of_nonneg hscale, ← hradius,
        puncturedSquareBoundaryScale_mul_radius]
    rcases le_total 0 ((x.1.2 : ℝ) - 1 / 2) with hnonneg | hnonpos
    · right
      right
      right
      apply Subtype.ext
      rw [puncturedSquareProjection]
      rw [abs_of_nonneg (mul_nonneg hscale hnonneg)] at habs
      norm_num
      linarith
    · right
      right
      left
      apply Subtype.ext
      rw [puncturedSquareProjection]
      rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hscale hnonpos)] at habs
      norm_num
      linarith
  · have hradius : puncturedSquareRadius x = |(x.1.1 : ℝ) - 1 / 2| :=
      max_eq_left hsecond
    have habs : |puncturedSquareBoundaryScale x * ((x.1.1 : ℝ) - 1 / 2)| =
        1 / 2 := by
      rw [abs_mul, abs_of_nonneg hscale, ← hradius,
        puncturedSquareBoundaryScale_mul_radius]
    rcases le_total 0 ((x.1.1 : ℝ) - 1 / 2) with hnonneg | hnonpos
    · right
      left
      apply Subtype.ext
      rw [puncturedSquareProjection]
      rw [abs_of_nonneg (mul_nonneg hscale hnonneg)] at habs
      norm_num
      linarith
    · left
      apply Subtype.ext
      rw [puncturedSquareProjection]
      rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hscale hnonpos)] at habs
      norm_num
      linarith

/-- Helper for Exercise 58.2: no square-boundary point is the square center. -/
private lemma puncturedSquareBoundary_ne_center
    (x : unitInterval × unitInterval) (hx : x ∈ puncturedSquareBoundary) :
    x ≠ puncturedSquareCenter := by
  -- Each boundary branch would make the midpoint equal to an endpoint.
  intro hcenter
  have hfirst := congrArg Prod.fst hcenter
  have hsecond := congrArg Prod.snd hcenter
  rcases hx with hx | hx | hx | hx
  · exact unitIntervalMidpoint_ne_zero (hfirst.symm.trans hx)
  · exact unitIntervalMidpoint_ne_one (hfirst.symm.trans hx)
  · exact unitIntervalMidpoint_ne_zero (hsecond.symm.trans hx)
  · exact unitIntervalMidpoint_ne_one (hsecond.symm.trans hx)

/-- Helper for Exercise 58.2: radial projection remains over the punctured additive torus. -/
private lemma puncturedSquareProjection_avoids_center (x : CenteredPuncturedSquare) :
    TorusSquare.toTorus (puncturedSquareProjection x) ≠ additiveTorusCenter := by
  -- The center has a unique square representative, whereas the projection is on the boundary.
  intro hcenter
  apply puncturedSquareBoundary_ne_center _ (puncturedSquareProjection_mem_boundary x)
  exact (toTorus_eq_additiveTorusCenter_iff _).mp hcenter

/-- Helper for Exercise 58.2: the radial scale interpolating from one to the boundary scale. -/
private noncomputable def puncturedSquareHomotopyScale
    (t : unitInterval) (x : CenteredPuncturedSquare) : ℝ :=
  1 + (t : ℝ) * (puncturedSquareBoundaryScale x - 1)

/-- Helper for Exercise 58.2: the interpolated radial scale is at least one. -/
private lemma one_le_puncturedSquareHomotopyScale
    (t : unitInterval) (x : CenteredPuncturedSquare) :
    1 ≤ puncturedSquareHomotopyScale t x := by
  -- The interpolation parameter and the scale increment are nonnegative.
  unfold puncturedSquareHomotopyScale
  exact le_add_of_nonneg_right (mul_nonneg t.2.1
    (sub_nonneg.mpr (one_le_puncturedSquareBoundaryScale x)))

/-- Helper for Exercise 58.2: the interpolated radial scale does not exceed the boundary scale. -/
private lemma puncturedSquareHomotopyScale_le_boundaryScale
    (t : unitInterval) (x : CenteredPuncturedSquare) :
    puncturedSquareHomotopyScale t x ≤ puncturedSquareBoundaryScale x := by
  -- The unit-interval upper bound controls affine interpolation toward the endpoint scale.
  have hincrement : 0 ≤ puncturedSquareBoundaryScale x - 1 :=
    sub_nonneg.mpr (one_le_puncturedSquareBoundaryScale x)
  unfold puncturedSquareHomotopyScale
  nlinarith [t.2.2]

/-- Helper for Exercise 58.2: every interpolated radial coordinate lies in the unit interval. -/
private lemma puncturedSquareHomotopyCoordinate_mem
    (t : unitInterval) (x : CenteredPuncturedSquare) (i : Fin 2) :
    1 / 2 + puncturedSquareHomotopyScale t x *
        ((puncturedSquareCoordinate x.1 i : ℝ) - 1 / 2) ∈
      Set.Icc (0 : ℝ) 1 := by
  -- Dominate the intermediate displacement by the already bounded projection displacement.
  have hscale_nonneg : 0 ≤ puncturedSquareHomotopyScale t x :=
    zero_le_one.trans (one_le_puncturedSquareHomotopyScale t x)
  have hboundary_nonneg : 0 ≤ puncturedSquareBoundaryScale x :=
    zero_le_one.trans (one_le_puncturedSquareBoundaryScale x)
  have hcoord : |(puncturedSquareCoordinate x.1 i : ℝ) - 1 / 2| ≤
      puncturedSquareRadius x := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have habs : |puncturedSquareHomotopyScale t x *
      ((puncturedSquareCoordinate x.1 i : ℝ) - 1 / 2)| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hscale_nonneg]
    calc
      puncturedSquareHomotopyScale t x *
          |(puncturedSquareCoordinate x.1 i : ℝ) - 1 / 2| ≤
          puncturedSquareBoundaryScale x *
            |(puncturedSquareCoordinate x.1 i : ℝ) - 1 / 2| :=
        mul_le_mul_of_nonneg_right
          (puncturedSquareHomotopyScale_le_boundaryScale t x) (abs_nonneg _)
      _ ≤ puncturedSquareBoundaryScale x * puncturedSquareRadius x :=
        mul_le_mul_of_nonneg_left hcoord hboundary_nonneg
      _ = 1 / 2 := puncturedSquareBoundaryScale_mul_radius x
  rw [abs_le] at habs
  constructor <;> linarith [habs.1, habs.2]

/-- Helper for Exercise 58.2: the first interpolated radial coordinate lies in the unit interval. -/
private lemma puncturedSquareHomotopyFirst_mem
    (t : unitInterval) (x : CenteredPuncturedSquare) :
    1 / 2 + puncturedSquareHomotopyScale t x * ((x.1.1 : ℝ) - 1 / 2) ∈
      Set.Icc (0 : ℝ) 1 := by
  -- Specialize the coordinatewise bound to the first coordinate.
  simpa only [puncturedSquareCoordinate_zero] using
    puncturedSquareHomotopyCoordinate_mem t x 0

/-- Helper for Exercise 58.2: the second interpolated radial coordinate lies in the unit
interval. -/
private lemma puncturedSquareHomotopySecond_mem
    (t : unitInterval) (x : CenteredPuncturedSquare) :
    1 / 2 + puncturedSquareHomotopyScale t x * ((x.1.2 : ℝ) - 1 / 2) ∈
      Set.Icc (0 : ℝ) 1 := by
  -- Specialize the coordinatewise bound to the second coordinate.
  simpa only [puncturedSquareCoordinate_one] using
    puncturedSquareHomotopyCoordinate_mem t x 1

/-- Helper for Exercise 58.2: the square radial homotopy as a point of the unit square. -/
private noncomputable def puncturedSquareHomotopyPoint
    (t : unitInterval) (x : CenteredPuncturedSquare) : unitInterval × unitInterval :=
  (⟨1 / 2 + puncturedSquareHomotopyScale t x * ((x.1.1 : ℝ) - 1 / 2),
      puncturedSquareHomotopyFirst_mem t x⟩,
    ⟨1 / 2 + puncturedSquareHomotopyScale t x * ((x.1.2 : ℝ) - 1 / 2),
      puncturedSquareHomotopySecond_mem t x⟩)

/-- Helper for Exercise 58.2: the square radial homotopy never reaches the deleted center. -/
private lemma puncturedSquareHomotopyPoint_avoids_center
    (t : unitInterval) (x : CenteredPuncturedSquare) :
    TorusSquare.toTorus (puncturedSquareHomotopyPoint t x) ≠ additiveTorusCenter := by
  -- A positive scale can reach the center only if the original displacement was zero.
  intro h
  have hcenter := (toTorus_eq_additiveTorusCenter_iff _).mp h
  have hfirst := congrArg (fun y : unitInterval × unitInterval ↦ (y.1 : ℝ)) hcenter
  have hsecond := congrArg (fun y : unitInterval × unitInterval ↦ (y.2 : ℝ)) hcenter
  have hscale : puncturedSquareHomotopyScale t x ≠ 0 :=
    (zero_lt_one.trans_le (one_le_puncturedSquareHomotopyScale t x)).ne'
  have hfirst' :
      1 / 2 + puncturedSquareHomotopyScale t x * ((x.1.1 : ℝ) - 1 / 2) =
        1 / 2 := by
    simpa only [puncturedSquareHomotopyPoint, puncturedSquareCenter,
      unitIntervalMidpoint] using hfirst
  have hsecond' :
      1 / 2 + puncturedSquareHomotopyScale t x * ((x.1.2 : ℝ) - 1 / 2) =
        1 / 2 := by
    simpa only [puncturedSquareHomotopyPoint, puncturedSquareCenter,
      unitIntervalMidpoint] using hsecond
  have hxfirst : (x.1.1 : ℝ) = 1 / 2 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hscale
    linarith
  have hxsecond : (x.1.2 : ℝ) = 1 / 2 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hscale
    linarith
  apply x.2
  apply (toTorus_eq_additiveTorusCenter_iff _).mpr
  apply Prod.ext <;> apply Subtype.ext
  · exact hxfirst
  · exact hxsecond

/-- Helper for Exercise 58.2: the square radial homotopy as a punctured-square point. -/
private noncomputable def puncturedSquareHomotopyValue
    (t : unitInterval) (x : CenteredPuncturedSquare) : CenteredPuncturedSquare :=
  ⟨puncturedSquareHomotopyPoint t x, puncturedSquareHomotopyPoint_avoids_center t x⟩

/-- Helper for Exercise 58.2: the interpolated radial scale varies continuously in time and
space. -/
private lemma continuous_puncturedSquareHomotopyScale :
    Continuous (fun z : unitInterval × CenteredPuncturedSquare ↦
      puncturedSquareHomotopyScale z.1 z.2) := by
  -- The scale is affine in time and in the continuous boundary scale.
  unfold puncturedSquareHomotopyScale
  exact continuous_const.add
    ((continuous_subtype_val.comp continuous_fst).mul
      ((continuous_puncturedSquareBoundaryScale.comp continuous_snd).sub continuous_const))

/-- Helper for Exercise 58.2: the radial homotopy on the punctured square is continuous. -/
private lemma continuous_puncturedSquareHomotopyValue :
    Continuous (fun z : unitInterval × CenteredPuncturedSquare ↦
      puncturedSquareHomotopyValue z.1 z.2) := by
  -- Check continuity on the two real coordinate formulas, then lift through the subtypes.
  have hfirst : Continuous
      (fun z : unitInterval × CenteredPuncturedSquare ↦ (z.2.1.1 : ℝ)) := by
    fun_prop
  have hsecond : Continuous
      (fun z : unitInterval × CenteredPuncturedSquare ↦ (z.2.1.2 : ℝ)) := by
    fun_prop
  have hhalf : Continuous
      (fun _ : unitInterval × CenteredPuncturedSquare ↦ (1 / 2 : ℝ)) :=
    continuous_const
  have hfirstCoordinate : Continuous
      (fun z : unitInterval × CenteredPuncturedSquare ↦
        1 / 2 + puncturedSquareHomotopyScale z.1 z.2 *
          ((z.2.1.1 : ℝ) - 1 / 2)) :=
    hhalf.add
      (continuous_puncturedSquareHomotopyScale.mul (hfirst.sub hhalf))
  have hsecondCoordinate : Continuous
      (fun z : unitInterval × CenteredPuncturedSquare ↦
        1 / 2 + puncturedSquareHomotopyScale z.1 z.2 *
          ((z.2.1.2 : ℝ) - 1 / 2)) :=
    hhalf.add
      (continuous_puncturedSquareHomotopyScale.mul (hsecond.sub hhalf))
  unfold puncturedSquareHomotopyValue puncturedSquareHomotopyPoint
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact hfirstCoordinate
  · apply Continuous.subtype_mk
    exact hsecondCoordinate

/-- Helper for Exercise 58.2: the radial homotopy starts at the original square point. -/
private lemma puncturedSquareHomotopyValue_zero (x : CenteredPuncturedSquare) :
    puncturedSquareHomotopyValue 0 x = x := by
  -- At time zero the interpolated scale is one in both coordinates.
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    norm_num [puncturedSquareHomotopyValue, puncturedSquareHomotopyPoint,
      puncturedSquareHomotopyScale]
  · apply Subtype.ext
    norm_num [puncturedSquareHomotopyValue, puncturedSquareHomotopyPoint,
      puncturedSquareHomotopyScale]

/-- Helper for Exercise 58.2: the endpoint of the radial homotopy is radial projection to the
square boundary. -/
private lemma puncturedSquareHomotopyValue_one (x : CenteredPuncturedSquare) :
    (puncturedSquareHomotopyValue 1 x).1 = puncturedSquareProjection x := by
  -- At time one the interpolated scale is exactly the boundary scale.
  apply Prod.ext
  · apply Subtype.ext
    norm_num [puncturedSquareHomotopyValue, puncturedSquareHomotopyPoint,
      puncturedSquareHomotopyScale, puncturedSquareProjection]
  · apply Subtype.ext
    norm_num [puncturedSquareHomotopyValue, puncturedSquareHomotopyPoint,
      puncturedSquareHomotopyScale, puncturedSquareProjection]

/-- Helper for Exercise 58.2: the radial homotopy fixes every square-boundary point. -/
private lemma puncturedSquareHomotopyValue_eq_of_mem_boundary
    (t : unitInterval) (x : CenteredPuncturedSquare)
    (hx : x.1 ∈ puncturedSquareBoundary) :
    puncturedSquareHomotopyValue t x = x := by
  -- Boundary radius makes the target scale one, so interpolation is constant.
  have hscale := puncturedSquareBoundaryScale_eq_one_of_mem_boundary x hx
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    simp only [puncturedSquareHomotopyValue, puncturedSquareHomotopyPoint,
      puncturedSquareHomotopyScale, hscale, sub_self, mul_zero, add_zero, one_mul]
    ring
  · apply Subtype.ext
    simp only [puncturedSquareHomotopyValue, puncturedSquareHomotopyPoint,
      puncturedSquareHomotopyScale, hscale, sub_self, mul_zero, add_zero, one_mul]
    ring

/-- Helper for Exercise 58.2: endpoint-equivalent interval points are equal or are both
endpoints. -/
private lemma endpointSetoid_eq_or_both_endpoints
    {x y : unitInterval} (hxy : unitInterval.endpointSetoid x y) :
    x = y ∨ ((x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = 1)) := by
  -- Separate ordinary equality from the two possible endpoint identifications.
  rw [unitInterval.endpointSetoid_iff] at hxy
  rcases hxy with hxy | hxy | hxy
  · exact Or.inl hxy
  · exact Or.inr ⟨Or.inl hxy.1, Or.inr hxy.2⟩
  · exact Or.inr ⟨Or.inr hxy.1, Or.inl hxy.2⟩

/-- Helper for Exercise 58.2: torus-equivalent square points are equal or both lie on the
square boundary. -/
private lemma identifiedSquarePoints_eq_or_both_mem_boundary
    {x y : unitInterval × unitInterval} (hxy : TorusSquare.identified x y) :
    x = y ∨ (x ∈ puncturedSquareBoundary ∧ y ∈ puncturedSquareBoundary) := by
  -- If neither coordinate uses endpoint identification, the points are equal; otherwise
  -- the exceptional coordinate places both representatives on opposite boundary edges.
  rw [TorusSquare.identified_iff] at hxy
  rcases endpointSetoid_eq_or_both_endpoints hxy.1 with hfirst | hfirst
  · rcases endpointSetoid_eq_or_both_endpoints hxy.2 with hsecond | hsecond
    · exact Or.inl (Prod.ext hfirst hsecond)
    · right
      constructor
      · rcases hsecond.1 with hxzero | hxone
        · exact Or.inr (Or.inr (Or.inl hxzero))
        · exact Or.inr (Or.inr (Or.inr hxone))
      · rcases hsecond.2 with hyzero | hyone
        · exact Or.inr (Or.inr (Or.inl hyzero))
        · exact Or.inr (Or.inr (Or.inr hyone))
  · right
    constructor
    · rcases hfirst.1 with hxzero | hxone
      · exact Or.inl hxzero
      · exact Or.inr (Or.inl hxone)
    · rcases hfirst.2 with hyzero | hyone
      · exact Or.inl hyzero
      · exact Or.inr (Or.inl hyone)

/-- Helper for Exercise 58.2: radial homotopy preserves the fibers of the square-to-torus
quotient map. -/
private lemma puncturedSquareHomotopy_respectsTorusFibers
    (t : unitInterval) (x y : CenteredPuncturedSquare)
    (hxy : TorusSquare.toTorus x.1 = TorusSquare.toTorus y.1) :
    TorusSquare.toTorus (puncturedSquareHomotopyValue t x).1 =
      TorusSquare.toTorus (puncturedSquareHomotopyValue t y).1 := by
  -- Fiber equality is the square identification relation. Nontrivial fibers occur only on
  -- the boundary, which the radial homotopy fixes pointwise.
  have hidentified : TorusSquare.identified x.1 y.1 := hxy
  rcases identifiedSquarePoints_eq_or_both_mem_boundary hidentified with heq | hboundary
  · have hsubtype : x = y := Subtype.ext heq
    rw [hsubtype]
  · rw [puncturedSquareHomotopyValue_eq_of_mem_boundary t x hboundary.1,
      puncturedSquareHomotopyValue_eq_of_mem_boundary t y hboundary.2]
    exact hxy

/-- Helper for Exercise 58.2: the restricted square-to-torus quotient map on the deleted
center. -/
private def puncturedSquareQuotientMapValue
    (x : CenteredPuncturedSquare) : CenteredPuncturedAdditiveTorus :=
  ⟨TorusSquare.toTorus x.1, x.2⟩

/-- Helper for Exercise 58.2: the restricted square-to-torus quotient map is continuous. -/
private lemma continuous_puncturedSquareQuotientMapValue :
    Continuous puncturedSquareQuotientMapValue := by
  -- Restrict the coordinatewise continuous quotient map to the deleted-center subtypes.
  have hcoordinate : Continuous (fun x : unitInterval ↦ (x : UnitAddCircle)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  unfold puncturedSquareQuotientMapValue TorusSquare.toTorus
  apply Continuous.subtype_mk
  exact (hcoordinate.comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (hcoordinate.comp (continuous_snd.comp continuous_subtype_val))

/-- Helper for Exercise 58.2: the restricted square-to-torus quotient as a continuous map. -/
private def puncturedSquareQuotientMap :
    C(CenteredPuncturedSquare, CenteredPuncturedAdditiveTorus) :=
  ⟨puncturedSquareQuotientMapValue, continuous_puncturedSquareQuotientMapValue⟩

/-- Helper for Exercise 58.2: deleting the centered puncture preserves the quotient-map
property of the unit square. -/
private lemma puncturedSquareQuotientMap_isQuotientMap :
    Topology.IsQuotientMap puncturedSquareQuotientMap := by
  -- The centered puncture complement is open, so quotient maps restrict to its preimage.
  exact TorusSquare.toTorus_isQuotientMap.restrictPreimage_isOpen isOpen_compl_singleton

/-- Helper for Exercise 58.2: a selected square representative of a centered punctured-torus
point. -/
private noncomputable def puncturedSquareRepresentative
    (z : CenteredPuncturedAdditiveTorus) : CenteredPuncturedSquare :=
  Function.surjInv puncturedSquareQuotientMap_isQuotientMap.surjective z

/-- Helper for Exercise 58.2: the selected square representative maps back to its torus point. -/
private lemma puncturedSquareQuotientMap_representative
    (z : CenteredPuncturedAdditiveTorus) :
    puncturedSquareQuotientMap (puncturedSquareRepresentative z) = z := by
  -- This is the right-inverse property of the selected representative.
  exact Function.surjInv_eq puncturedSquareQuotientMap_isQuotientMap.surjective z

/-- Helper for Exercise 58.2: the radial square homotopy descended to the centered punctured
additive torus. -/
private noncomputable def centeredAdditiveTorusHomotopyValue
    (t : unitInterval) (z : CenteredPuncturedAdditiveTorus) :
    CenteredPuncturedAdditiveTorus :=
  puncturedSquareQuotientMap
    (puncturedSquareHomotopyValue t (puncturedSquareRepresentative z))

/-- Helper for Exercise 58.2: descending the radial homotopy and then pulling it back to the
square recovers the original square formula. -/
private lemma centeredAdditiveTorusHomotopyValue_quotientMap
    (t : unitInterval) (x : CenteredPuncturedSquare) :
    centeredAdditiveTorusHomotopyValue t (puncturedSquareQuotientMap x) =
      puncturedSquareQuotientMap (puncturedSquareHomotopyValue t x) := by
  -- The chosen representative and `x` lie in the same quotient fiber, so fiber compatibility
  -- makes their radial images agree.
  apply Subtype.ext
  apply puncturedSquareHomotopy_respectsTorusFibers
  exact congrArg Subtype.val
    (puncturedSquareQuotientMap_representative (puncturedSquareQuotientMap x))

/-- Helper for Exercise 58.2: the descended radial homotopy is continuous. -/
private lemma continuous_centeredAdditiveTorusHomotopyValue :
    Continuous (fun z : unitInterval × CenteredPuncturedAdditiveTorus ↦
      centeredAdditiveTorusHomotopyValue z.1 z.2) := by
  -- Test continuity after the quotient map on the spatial factor; the pullback is the already
  -- continuous square homotopy followed by the quotient map.
  apply puncturedSquareQuotientMap_isQuotientMap.continuous_lift_prod_right
  have hpullback :
      (fun z : unitInterval × CenteredPuncturedSquare ↦
        centeredAdditiveTorusHomotopyValue z.1 (puncturedSquareQuotientMap z.2)) =
      (fun z : unitInterval × CenteredPuncturedSquare ↦
        puncturedSquareQuotientMap (puncturedSquareHomotopyValue z.1 z.2)) := by
    funext z
    exact centeredAdditiveTorusHomotopyValue_quotientMap z.1 z.2
  rw [hpullback]
  exact continuous_puncturedSquareQuotientMapValue.comp
    continuous_puncturedSquareHomotopyValue

/-- Helper for Exercise 58.2: the descended radial homotopy starts at the identity. -/
private lemma centeredAdditiveTorusHomotopyValue_zero
    (z : CenteredPuncturedAdditiveTorus) :
    centeredAdditiveTorusHomotopyValue 0 z = z := by
  -- Reduce to time zero on the selected square representative and its right-inverse property.
  rw [centeredAdditiveTorusHomotopyValue,
    puncturedSquareHomotopyValue_zero,
    puncturedSquareQuotientMap_representative]

/-- Helper for Exercise 58.2: the two additive coordinate axes inside the centered punctured
torus. -/
private def centeredAdditiveTorusAxes : Set CenteredPuncturedAdditiveTorus :=
  {z | z.1.2 = 0 ∨ z.1.1 = 0}

/-- Helper for Exercise 58.2: a unit-interval representative of additive zero is an endpoint. -/
private lemma unitInterval_eq_zero_or_one_of_coe_eq_zero
    (x : unitInterval) (hx : (x : UnitAddCircle) = 0) :
    x = 0 ∨ x = 1 := by
  -- Additive zero has exactly the two endpoint representatives in the closed unit interval.
  have hsetoid : unitInterval.endpointSetoid x 0 := hx
  rcases endpointSetoid_eq_or_both_endpoints hsetoid with heq | hendpoints
  · exact Or.inl heq
  · exact hendpoints.1

/-- Helper for Exercise 58.2: the image of the square boundary lies in the additive coordinate
axes. -/
private lemma toTorus_mem_centeredAdditiveTorusAxes_of_mem_boundary
    (x : CenteredPuncturedSquare) (hx : x.1 ∈ puncturedSquareBoundary) :
    puncturedSquareQuotientMap x ∈ centeredAdditiveTorusAxes := by
  -- Each of the four square edges maps to additive zero in one torus coordinate.
  rcases hx with hx | hx | hx | hx
  · right
    change (x.1.1 : UnitAddCircle) = 0
    rw [hx]
    rfl
  · right
    change (x.1.1 : UnitAddCircle) = 0
    rw [hx]
    exact AddCircle.coe_period (1 : ℝ)
  · left
    change (x.1.2 : UnitAddCircle) = 0
    rw [hx]
    rfl
  · left
    change (x.1.2 : UnitAddCircle) = 0
    rw [hx]
    exact AddCircle.coe_period (1 : ℝ)

/-- Helper for Exercise 58.2: a square representative of an additive-axis point lies on the
square boundary. -/
private lemma mem_boundary_of_quotientMap_mem_centeredAdditiveTorusAxes
    (x : CenteredPuncturedSquare)
    (hx : puncturedSquareQuotientMap x ∈ centeredAdditiveTorusAxes) :
    x.1 ∈ puncturedSquareBoundary := by
  -- A zero additive coordinate forces its interval representative to be zero or one.
  rcases hx with hsecond | hfirst
  · rcases unitInterval_eq_zero_or_one_of_coe_eq_zero x.1.2 hsecond with hzero | hone
    · exact Or.inr (Or.inr (Or.inl hzero))
    · exact Or.inr (Or.inr (Or.inr hone))
  · rcases unitInterval_eq_zero_or_one_of_coe_eq_zero x.1.1 hfirst with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (Or.inl hone)

/-- Helper for Exercise 58.2: the descended radial endpoint lies on the additive coordinate
axes. -/
private lemma centeredAdditiveTorusHomotopyValue_one_mem
    (z : CenteredPuncturedAdditiveTorus) :
    centeredAdditiveTorusHomotopyValue 1 z ∈ centeredAdditiveTorusAxes := by
  -- The selected square representative projects to the boundary at time one.
  unfold centeredAdditiveTorusHomotopyValue
  apply toTorus_mem_centeredAdditiveTorusAxes_of_mem_boundary
  rw [puncturedSquareHomotopyValue_one]
  exact puncturedSquareProjection_mem_boundary _

/-- Helper for Exercise 58.2: the descended radial homotopy fixes the additive coordinate axes. -/
private lemma centeredAdditiveTorusHomotopyValue_eq_of_mem_axes
    (t : unitInterval) (z : CenteredPuncturedAdditiveTorus)
    (hz : z ∈ centeredAdditiveTorusAxes) :
    centeredAdditiveTorusHomotopyValue t z = z := by
  -- The selected representative of an axis point is a boundary point, and boundary points
  -- are fixed before passing to the quotient.
  have hrepresentative :
      puncturedSquareQuotientMap (puncturedSquareRepresentative z) ∈
        centeredAdditiveTorusAxes := by
    rw [puncturedSquareQuotientMap_representative]
    exact hz
  have hboundary :=
    mem_boundary_of_quotientMap_mem_centeredAdditiveTorusAxes _ hrepresentative
  rw [centeredAdditiveTorusHomotopyValue,
    puncturedSquareHomotopyValue_eq_of_mem_boundary t _ hboundary,
    puncturedSquareQuotientMap_representative]

/-- Helper for Exercise 58.2: the descended endpoint map into the additive coordinate axes. -/
private noncomputable def centeredAdditiveTorusAxesRetractionMap :
    C(CenteredPuncturedAdditiveTorus, centeredAdditiveTorusAxes) :=
  ⟨fun z ↦ ⟨centeredAdditiveTorusHomotopyValue 1 z,
      centeredAdditiveTorusHomotopyValue_one_mem z⟩,
    (continuous_centeredAdditiveTorusHomotopyValue.comp
      (continuous_const.prodMk continuous_id)).subtype_mk
        centeredAdditiveTorusHomotopyValue_one_mem⟩

/-- Helper for Exercise 58.2: the descended endpoint map is the identity on the additive axes. -/
private lemma centeredAdditiveTorusAxesRetractionMap_leftInverse :
    Function.LeftInverse centeredAdditiveTorusAxesRetractionMap
      (Subtype.val : centeredAdditiveTorusAxes → CenteredPuncturedAdditiveTorus) := by
  -- Fixedness of the descended homotopy at time one gives the retraction law.
  intro z
  apply Subtype.ext
  exact centeredAdditiveTorusHomotopyValue_eq_of_mem_axes 1 z.1 z.2

/-- Helper for Exercise 58.2: the descended endpoint map is a retraction onto the additive
axes. -/
private noncomputable def centeredAdditiveTorusAxesRetraction :
    Set.Retraction centeredAdditiveTorusAxes :=
  ⟨centeredAdditiveTorusAxesRetractionMap,
    centeredAdditiveTorusAxesRetractionMap_leftInverse⟩

/-- Helper for Exercise 58.2: the descended homotopy ends at the ambient retraction map. -/
private lemma centeredAdditiveTorusHomotopyValue_one
    (z : CenteredPuncturedAdditiveTorus) :
    centeredAdditiveTorusHomotopyValue 1 z =
      centeredAdditiveTorusAxesRetraction.toAmbient z := by
  -- Both sides evaluate to the same descended endpoint.
  rfl

/-- Helper for Exercise 58.2: the descended radial formula is a homotopy to the additive-axis
retraction. -/
private noncomputable def centeredAdditiveTorusAxesHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id CenteredPuncturedAdditiveTorus)
      centeredAdditiveTorusAxesRetraction.toAmbient :=
  { toFun := fun tz ↦ centeredAdditiveTorusHomotopyValue tz.1 tz.2
    continuous_toFun := continuous_centeredAdditiveTorusHomotopyValue
    map_zero_left := centeredAdditiveTorusHomotopyValue_zero
    map_one_left := centeredAdditiveTorusHomotopyValue_one }

/-- Helper for Exercise 58.2: the descended radial homotopy remains fixed on the additive axes. -/
private lemma centeredAdditiveTorusAxesHomotopy_fixed
    (t : unitInterval) (z : CenteredPuncturedAdditiveTorus)
    (hz : z ∈ centeredAdditiveTorusAxes) :
    centeredAdditiveTorusAxesHomotopy (t, z) =
      (ContinuousMap.id CenteredPuncturedAdditiveTorus) z := by
  -- Use the fixed-axis specification of the descended value.
  exact centeredAdditiveTorusHomotopyValue_eq_of_mem_axes t z hz

/-- Helper for Exercise 58.2: the descended radial homotopy is relative to the additive axes. -/
private noncomputable def centeredAdditiveTorusAxesHomotopyRel :
    ContinuousMap.HomotopyRel (ContinuousMap.id CenteredPuncturedAdditiveTorus)
      centeredAdditiveTorusAxesRetraction.toAmbient centeredAdditiveTorusAxes :=
  { toHomotopy := centeredAdditiveTorusAxesHomotopy
    prop' := centeredAdditiveTorusAxesHomotopy_fixed }

/-- Helper for Exercise 58.2: the additive coordinate axes deformation retract the centered
punctured additive torus. -/
private theorem centeredAdditiveTorusAxes_isDeformationRetract :
    Set.IsDeformationRetract centeredAdditiveTorusAxes := by
  -- Package the descended retraction and its homotopy relative to the axes.
  rw [Set.isDeformationRetract_iff]
  exact ⟨centeredAdditiveTorusAxesRetraction, ⟨centeredAdditiveTorusAxesHomotopyRel⟩⟩

/-- Helper for Exercise 58.2: coordinatewise circle-additive-circle coordinates on the torus. -/
private noncomputable def torusHomeomorphAdditiveTorus :
    Torus ≃ₜ UnitAddCircle × UnitAddCircle :=
  (AddCircle.homeomorphCircle one_ne_zero).symm.prodCongr
    (AddCircle.homeomorphCircle one_ne_zero).symm

/-- Helper for Exercise 58.2: translation sends the chosen deleted torus point to the additive
center. -/
private noncomputable def torusCenteringHomeomorph (q : Torus) :
    Torus ≃ₜ UnitAddCircle × UnitAddCircle :=
  torusHomeomorphAdditiveTorus.trans
    (Homeomorph.addLeft (additiveTorusCenter - torusHomeomorphAdditiveTorus q))

/-- Helper for Exercise 58.2: the centering homeomorphism sends its chosen point to the fixed
additive center. -/
private lemma torusCenteringHomeomorph_apply_self (q : Torus) :
    torusCenteringHomeomorph q q = additiveTorusCenter := by
  -- Translation by the difference from the center cancels the point's additive coordinates.
  change additiveTorusCenter - torusHomeomorphAdditiveTorus q +
      torusHomeomorphAdditiveTorus q = additiveTorusCenter
  exact sub_add_cancel _ _

/-- Helper for Exercise 58.2: centering carries the complement of `q` to the complement of the
fixed additive center. -/
private lemma torusCenteringHomeomorph_ne_center_iff
    (q x : Torus) :
    x ≠ q ↔ torusCenteringHomeomorph q x ≠ additiveTorusCenter := by
  -- Injectivity converts equality with the centered value back to equality with `q`.
  constructor
  · intro hx hcenter
    apply hx
    apply (torusCenteringHomeomorph q).injective
    exact hcenter.trans (torusCenteringHomeomorph_apply_self q).symm
  · intro hcenter hx
    apply hcenter
    rw [hx, torusCenteringHomeomorph_apply_self]

/-- Helper for Exercise 58.2: an arbitrary punctured torus is homeomorphic to the centered
punctured additive torus. -/
private noncomputable def puncturedTorusHomeomorphCentered (q : Torus) :
    {x : Torus // x ≠ q} ≃ₜ CenteredPuncturedAdditiveTorus :=
  (torusCenteringHomeomorph q).subtype (torusCenteringHomeomorph_ne_center_iff q)

/-- Helper for Exercise 58.2: the direct additive coordinate-axis subset of the additive torus. -/
private def additiveTorusAxes : Set (UnitAddCircle × UnitAddCircle) :=
  {z | z.2 = 0 ∨ z.1 = 0}

/-- Helper for Exercise 58.2: the additive half-period is not additive zero. -/
private lemma additiveCircleHalf_ne_zero : ((1 / 2 : ℝ) : UnitAddCircle) ≠ 0 := by
  -- A zero half-period would make the interval midpoint one of its endpoints.
  intro hhalf
  have hmidpoint : (unitIntervalMidpoint : UnitAddCircle) = 0 := hhalf
  rcases unitInterval_eq_zero_or_one_of_coe_eq_zero unitIntervalMidpoint hmidpoint with
    hzero | hone
  · exact unitIntervalMidpoint_ne_zero hzero
  · exact unitIntervalMidpoint_ne_one hone

/-- Helper for Exercise 58.2: the additive coordinate axes avoid the centered puncture. -/
private lemma additiveTorusAxes_subset_center_complement :
    additiveTorusAxes ⊆ ({additiveTorusCenter}ᶜ : Set (UnitAddCircle × UnitAddCircle)) := by
  -- Equality with the center would identify a zero axis coordinate with the nonzero half-period.
  intro z hz hcenter
  rcases hz with hsecond | hfirst
  · apply additiveCircleHalf_ne_zero
    exact (congrArg Prod.snd hcenter).symm.trans hsecond
  · apply additiveCircleHalf_ne_zero
    exact (congrArg Prod.fst hcenter).symm.trans hfirst

/-- Helper for Exercise 58.2: coordinatewise additive-circle-to-circle coordinates. -/
private noncomputable def additiveTorusHomeomorphTorus :
    UnitAddCircle × UnitAddCircle ≃ₜ Torus :=
  (AddCircle.homeomorphCircle one_ne_zero).prodCongr
    (AddCircle.homeomorphCircle one_ne_zero)

/-- Helper for Exercise 58.2: additive zero maps to the circle basepoint, and only additive zero
does so. -/
private lemma addCircleHomeomorphCircle_eq_one_iff (x : UnitAddCircle) :
    AddCircle.homeomorphCircle one_ne_zero x = 1 ↔ x = 0 := by
  -- Compare with the explicit image of zero and use injectivity of the homeomorphism.
  have hzero : AddCircle.homeomorphCircle one_ne_zero (0 : UnitAddCircle) = 1 := by
    rw [AddCircle.homeomorphCircle_apply]
    exact AddCircle.toCircle_zero
  constructor
  · intro hx
    apply (AddCircle.homeomorphCircle one_ne_zero).injective
    exact hx.trans hzero.symm
  · intro hx
    rw [hx]
    exact hzero

/-- Helper for Exercise 58.2: additive coordinate axes correspond exactly to the figure-eight
carrier. -/
private lemma additiveTorusAxes_iff_figureEight
    (z : UnitAddCircle × UnitAddCircle) :
    z ∈ additiveTorusAxes ↔ additiveTorusHomeomorphTorus z ∈ FigureEight.carrier := by
  -- Coordinatewise, additive zero is precisely the circle basepoint one.
  rw [FigureEight.mem_iff]
  unfold additiveTorusAxes additiveTorusHomeomorphTorus
  change (z.2 = 0 ∨ z.1 = 0) ↔
    (AddCircle.homeomorphCircle one_ne_zero z.2 = 1 ∨
      AddCircle.homeomorphCircle one_ne_zero z.1 = 1)
  rw [addCircleHomeomorphCircle_eq_one_iff,
    addCircleHomeomorphCircle_eq_one_iff]

/-- Helper for Exercise 58.2: the additive coordinate axes are homeomorphic to the figure eight. -/
private noncomputable def centeredAdditiveTorusAxesHomeomorphFigureEight :
    centeredAdditiveTorusAxes ≃ₜ FigureEight :=
  (nestedSubsetHomeomorph ({additiveTorusCenter}ᶜ)
      additiveTorusAxes additiveTorusAxes_subset_center_complement).trans
    (additiveTorusHomeomorphTorus.subtype additiveTorusAxes_iff_figureEight)

/-- Helper for Exercise 58.2: the figure-eight carrier is path connected. -/
private lemma figureEight_isPathConnected :
    IsPathConnected FigureEight.carrier := by
  -- Realize the carrier as the union of the ranges of its two coordinate circles.
  let firstCircle : Circle → Torus := fun z ↦ (z, 1)
  let secondCircle : Circle → Torus := fun z ↦ (1, z)
  have hfirst : IsPathConnected (Set.range firstCircle) := by
    apply isPathConnected_range
    unfold firstCircle
    fun_prop
  have hsecond : IsPathConnected (Set.range secondCircle) := by
    apply isPathConnected_range
    unfold secondCircle
    fun_prop
  have hintersection :
      (Set.range firstCircle ∩ Set.range secondCircle).Nonempty := by
    refine ⟨((1 : Circle), (1 : Circle)), ?_, ?_⟩
    · exact ⟨1, rfl⟩
    · exact ⟨1, rfl⟩
  have hunion := hfirst.union hsecond hintersection
  have hrange :
      Set.range firstCircle ∪ Set.range secondCircle = FigureEight.carrier := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨u, hu⟩ | ⟨v, hv⟩
      · exact (FigureEight.mem_iff z).mpr
          (Or.inl (congrArg Prod.snd hu.symm))
      · exact (FigureEight.mem_iff z).mpr
          (Or.inr (congrArg Prod.fst hv.symm))
    · intro hz
      rcases (FigureEight.mem_iff z).mp hz with hz | hz
      · left
        refine ⟨z.1, ?_⟩
        exact Prod.ext rfl hz.symm
      · right
        refine ⟨z.2, ?_⟩
        exact Prod.ext hz.symm rfl
  rw [← hrange]
  exact hunion

/-- Exercise 58.2 (2): The fundamental group of a torus with one point removed is the
fundamental group of the figure eight. -/
theorem fundamentalGroup_puncturedTorus (q : Torus) (p : {x : Torus // x ≠ q}) :
    Nonempty
      (FundamentalGroup {x : Torus // x ≠ q} p ≃*
        FundamentalGroup FigureEight FigureEight.basepoint) := by
  -- Center the puncture, pass through the descended square-boundary deformation retract,
  -- identify its additive axes with the figure eight, and finally move the basepoint.
  letI : PathConnectedSpace FigureEight :=
    isPathConnected_iff_pathConnectedSpace.mp figureEight_isPathConnected
  obtain ⟨eRetract⟩ := centeredAdditiveTorusAxes_isDeformationRetract.nonempty_homotopyEquiv
  exact ⟨((puncturedTorusHomeomorphCentered q).fundamentalGroupMulEquiv p).trans <|
    (eRetract.symm.fundamentalGroupMulEquiv
      (puncturedTorusHomeomorphCentered q p)).trans <|
    (centeredAdditiveTorusAxesHomeomorphFigureEight.fundamentalGroupMulEquiv
      (eRetract.symm (puncturedTorusHomeomorphCentered q p))).trans <|
    FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      (centeredAdditiveTorusAxesHomeomorphFigureEight
        (eRetract.symm (puncturedTorusHomeomorphCentered q p)))
      FigureEight.basepoint⟩

/-- Exercise 58.2 (3): The fundamental group of the cylinder `S¹ × I` is infinite cyclic. -/
theorem fundamentalGroup_cylinder (p : Circle × Set.Icc (0 : ℝ) 1) :
    Nonempty (FundamentalGroup (Circle × Set.Icc (0 : ℝ) 1) p ≃* Multiplicative ℤ) := by
  -- The interval factor is convex, so the product decomposition leaves only the circle factor.
  exact ⟨(FundamentalGroup.prodMulEquivLeftOfSubsingleton p.1 p.2
      (Convex.subsingleton_fundamentalGroup (convex_Icc 0 1) p.2)).trans <|
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected p.1 1).trans
      Circle.fundamentalGroupEquivInt⟩

/-- Exercise 58.2 (4): The fundamental group of the infinite cylinder `S¹ × ℝ` is infinite
cyclic. -/
theorem fundamentalGroup_infiniteCylinder (p : Circle × ℝ) :
    Nonempty (FundamentalGroup (Circle × ℝ) p ≃* Multiplicative ℤ) := by
  -- Contractibility makes the real-line factor invisible to the product fundamental group.
  exact ⟨(FundamentalGroup.prodMulEquivLeftOfSubsingleton p.1 p.2 inferInstance).trans <|
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected p.1 1).trans
      Circle.fundamentalGroupEquivInt⟩

/-- Helper for Exercise 58.2: the positive unit vector in a coordinate direction belongs
to the Euclidean unit sphere. -/
private lemma positiveCoordinateDirection_mem (i : Fin 3) :
    EuclideanSpace.single i (1 : ℝ) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- A standard coordinate vector has norm one.
  simp only [Metric.mem_sphere, dist_zero_right, PiLp.norm_single, norm_one]

/-- Helper for Exercise 58.2: the positive unit vector in a coordinate direction. -/
private noncomputable def positiveCoordinateDirection (i : Fin 3) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨EuclideanSpace.single i 1, positiveCoordinateDirection_mem i⟩

/-- Helper for Exercise 58.2: the three positive coordinate directions removed from the
unit sphere. -/
private noncomputable def threeCoordinateDirectionComplement :
    Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  {s | s ≠ positiveCoordinateDirection 0 ∧
    s ≠ positiveCoordinateDirection 1 ∧
    s ≠ positiveCoordinateDirection 2}

/-- Helper for Exercise 58.2: the angular complement of the three positive coordinate
directions. -/
private abbrev ThreeCoordinateDirectionComplement :=
  threeCoordinateDirectionComplement

/-- Helper for Exercise 58.2: the complement of the three nonnegative coordinate rays
contains no zero vector. -/
private lemma threeRaysComplement_subset_complZero :
    {x : EuclideanSpace ℝ (Fin 3) |
      x ∉ Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 0 t.1) ∪
        Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 1 t.1) ∪
        Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 2 t.1)} ⊆
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) := by
  -- The origin lies on the first deleted ray, so every point of the complement is nonzero.
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hzero
  apply hx
  left
  left
  refine ⟨⟨0, Set.mem_Ici.mpr le_rfl⟩, ?_⟩
  rw [hzero]
  ext i
  simp only [WithLp.ofLp_zero, Pi.zero_apply, PiLp.single_apply]
  split <;> rfl

/-- Helper for Exercise 58.2: a positive scalar multiple of a coordinate unit vector is
the corresponding coordinate vector. -/
private lemma smul_positiveCoordinateDirection
    (i : Fin 3) (r : ℝ) :
    r • (positiveCoordinateDirection i).1 = EuclideanSpace.single i r := by
  -- Check the equality coordinatewise.
  ext j
  simp only [positiveCoordinateDirection, WithLp.ofLp_smul, Pi.smul_apply,
    smul_eq_mul, PiLp.single_apply]
  split
  · simp
  · simp

/-- Helper for Exercise 58.2: under polar coordinates, lying on a nonnegative coordinate ray
is exactly having its positive coordinate direction. -/
private lemma polarDirection_eq_positiveCoordinateDirection_iff
    (x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))) (i : Fin 3) :
    (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3)) x).1 =
        positiveCoordinateDirection i ↔
      x.1 ∈ Set.range
        (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single i t.1) := by
  -- Use the inverse polar formula in both directions, avoiding coordinate division.
  let e := homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3))
  constructor
  · intro hdirection
    let r := (e x).2
    refine ⟨⟨r.1, Set.mem_Ici.mpr r.2.le⟩, ?_⟩
    have hrecover := congrArg Subtype.val (e.symm_apply_apply x)
    rw [homeomorphUnitSphereProd_symm_apply_coe] at hrecover
    calc
      EuclideanSpace.single i r.1 = r.1 • (positiveCoordinateDirection i).1 :=
        (smul_positiveCoordinateDirection i r.1).symm
      _ = r.1 • (e x).1.1 :=
        congrArg (fun s ↦ r.1 • s.1) hdirection.symm
      _ = x.1 := hrecover
  · rintro ⟨t, ht⟩
    have htpos : 0 < t.1 := by
      rcases (Set.mem_Ici.mp t.2).eq_or_lt with hzero | hpos
      · exfalso
        apply x.2
        rw [Set.mem_singleton_iff]
        calc
          x.1 = EuclideanSpace.single i t.1 := ht.symm
          _ = EuclideanSpace.single i 0 := congrArg (EuclideanSpace.single i) hzero.symm
          _ = 0 := by
            ext j
            simp only [PiLp.single_apply, WithLp.ofLp_zero, Pi.zero_apply]
            split <;> rfl
      · exact hpos
    let r : Set.Ioi (0 : ℝ) := ⟨t.1, htpos⟩
    have hinverse : e.symm (positiveCoordinateDirection i, r) = x := by
      apply Subtype.ext
      rw [homeomorphUnitSphereProd_symm_apply_coe]
      exact (smul_positiveCoordinateDirection i t.1).trans ht
    calc
      (e x).1 = (e (e.symm (positiveCoordinateDirection i, r))).1 :=
        congrArg (fun z ↦ (e z).1) hinverse.symm
      _ = positiveCoordinateDirection i :=
        congrArg Prod.fst (e.apply_symm_apply (positiveCoordinateDirection i, r))

/-- Helper for Exercise 58.2: the three-ray complement predicate becomes deletion of the
three positive coordinate directions under polar coordinates. -/
private lemma polarThreeRays_iff
    (x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))) :
    x ∈ Subtype.val ⁻¹'
        {y : EuclideanSpace ℝ (Fin 3) |
          y ∉ Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 0 t.1) ∪
            Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 1 t.1) ∪
            Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 2 t.1)} ↔
      (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3)) x).1 ∈
        threeCoordinateDirectionComplement := by
  -- De Morgan's law and the three one-ray polar characterizations close the predicate bridge.
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_union,
    threeCoordinateDirectionComplement]
  rw [← polarDirection_eq_positiveCoordinateDirection_iff x 0,
    ← polarDirection_eq_positiveCoordinateDirection_iff x 1,
    ← polarDirection_eq_positiveCoordinateDirection_iff x 2]
  tauto

/-- Helper for Exercise 58.2: separating an angular predicate from the positive radial
coordinate gives a product homeomorphism. -/
private def angularRadialProductHomeomorph
    {S : Type*} [TopologicalSpace S] (D : Set S) :
    {z : S × Set.Ioi (0 : ℝ) // z.1 ∈ D} ≃ₜ D × Set.Ioi (0 : ℝ) :=
  { toFun := fun z ↦ (⟨z.1.1, z.2⟩, z.1.2)
    invFun := fun z ↦ ⟨(z.1.1, z.2), z.1.2⟩
    left_inv := fun _ ↦ Subtype.ext rfl
    right_inv := fun _ ↦ Prod.ext (Subtype.ext rfl) rfl
    continuous_toFun :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk fun z ↦ z.2).prodMk
        (continuous_snd.comp continuous_subtype_val)
    continuous_invFun :=
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk
        fun z ↦ z.1.2 }

/-- Helper for Exercise 58.2: polar coordinates identify the three-ray complement with
its angular complement times a positive radial coordinate. -/
private noncomputable def threeRaysPolarHomeomorph :
    {x : EuclideanSpace ℝ (Fin 3) //
      x ∉ Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 0 t.1) ∪
        Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 1 t.1) ∪
        Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 2 t.1)} ≃ₜ
      ThreeCoordinateDirectionComplement × Set.Ioi (0 : ℝ) :=
  (nestedSubsetHomeomorph ({0}ᶜ)
      {x : EuclideanSpace ℝ (Fin 3) |
        x ∉ Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 0 t.1) ∪
          Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 1 t.1) ∪
          Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 2 t.1)}
      threeRaysComplement_subset_complZero).symm.trans <|
    ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3))).subtype
      polarThreeRays_iff).trans <|
        angularRadialProductHomeomorph threeCoordinateDirectionComplement

/-- Helper for Exercise 58.2: distinct coordinate indices give distinct positive
coordinate directions. -/
private lemma positiveCoordinateDirection_ne
    {i j : Fin 3} (hij : i ≠ j) :
    positiveCoordinateDirection i ≠ positiveCoordinateDirection j := by
  -- Evaluate a hypothetical equality at coordinate `i`.
  intro h
  have hcoord := congrArg (fun x : EuclideanSpace ℝ (Fin 3) ↦ x i)
    (congrArg Subtype.val h)
  simp only [positiveCoordinateDirection, PiLp.single_apply, if_pos,
    if_neg hij] at hcoord
  norm_num at hcoord

/-- Helper for Exercise 58.2: deleting all three coordinate directions in particular
deletes the third direction. -/
private lemma threeCoordinateDirectionComplement_subset_thirdComplement :
    threeCoordinateDirectionComplement ⊆
      ({positiveCoordinateDirection 2}ᶜ :
        Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  -- Retain the third non-equality from the defining conjunction.
  intro s hs
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs.2.2

/-- Helper for Exercise 58.2: the first direction lies in the complement of the third. -/
private lemma firstDirection_mem_thirdComplement :
    positiveCoordinateDirection 0 ∈
      ({positiveCoordinateDirection 2}ᶜ :
        Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  -- The coordinate indices are distinct.
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
    (positiveCoordinateDirection_ne (by decide : (0 : Fin 3) ≠ 2))

/-- Helper for Exercise 58.2: the second direction lies in the complement of the third. -/
private lemma secondDirection_mem_thirdComplement :
    positiveCoordinateDirection 1 ∈
      ({positiveCoordinateDirection 2}ᶜ :
        Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  -- The coordinate indices are distinct.
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
    (positiveCoordinateDirection_ne (by decide : (1 : Fin 3) ≠ 2))

/-- Helper for Exercise 58.2: the ambient Euclidean space of the coordinate two-sphere
has dimension three. -/
private lemma coordinateSphereTwo_finrank :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1 := by
  -- Use the standard finite-dimensional Euclidean-space formula.
  exact (finrank_euclideanSpace_fin :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1)

/-- Helper for Exercise 58.2: the dimension fact required by stereographic projection. -/
private instance coordinateSphereTwo_finrankFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) :=
  ⟨coordinateSphereTwo_finrank⟩

/-- Helper for Exercise 58.2: stereographic projection from a sphere point is a
homeomorphism from its complement to the Euclidean plane. -/
private noncomputable def puncturedCoordinateSphereHomeomorphPlane
    (b : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ({b}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ≃ₜ
      EuclideanSpace ℝ (Fin 2) :=
  ((Homeomorph.setCongr (stereographic'_source (n := 2) b).symm).trans
    (stereographic' 2 b).toHomeomorphSourceTarget).trans
      ((Homeomorph.setCongr (stereographic'_target (n := 2) b)).trans
        (Homeomorph.Set.univ _))

/-- Helper for Exercise 58.2: stereographic coordinates from the third direction,
followed by the standard complex coordinates. -/
private noncomputable def thirdDirectionStereographicChart :
    ({positiveCoordinateDirection 2}ᶜ :
      Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ≃ₜ ℂ :=
  (puncturedCoordinateSphereHomeomorphPlane (positiveCoordinateDirection 2)).trans
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph

/-- Helper for Exercise 58.2: the first positive coordinate direction as a point of the
third-direction stereographic chart. -/
private noncomputable def firstDirectionInThirdComplement :
    ({positiveCoordinateDirection 2}ᶜ :
      Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  ⟨positiveCoordinateDirection 0, firstDirection_mem_thirdComplement⟩

/-- Helper for Exercise 58.2: the second positive coordinate direction as a point of the
third-direction stereographic chart. -/
private noncomputable def secondDirectionInThirdComplement :
    ({positiveCoordinateDirection 2}ᶜ :
      Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  ⟨positiveCoordinateDirection 1, secondDirection_mem_thirdComplement⟩

/-- Helper for Exercise 58.2: within the third-direction chart, deleting the first two
directions is deleting their two chart images. -/
private lemma thirdDirectionStereographicChart_punctures_iff
    (x : ({positiveCoordinateDirection 2}ᶜ :
      Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))) :
    x.1 ∈ threeCoordinateDirectionComplement ↔
      thirdDirectionStereographicChart x ≠
          thirdDirectionStereographicChart firstDirectionInThirdComplement ∧
        thirdDirectionStereographicChart x ≠
          thirdDirectionStereographicChart secondDirectionInThirdComplement := by
  -- Injectivity of the chart translates the two remaining puncture inequalities exactly.
  have hfirst : x.1 ≠ positiveCoordinateDirection 0 ↔
      thirdDirectionStereographicChart x ≠
        thirdDirectionStereographicChart firstDirectionInThirdComplement := by
    rw [thirdDirectionStereographicChart.injective.ne_iff]
    constructor
    · intro hne heq
      exact hne (congrArg Subtype.val heq)
    · intro hne heq
      apply hne
      exact Subtype.ext heq
  have hsecond : x.1 ≠ positiveCoordinateDirection 1 ↔
      thirdDirectionStereographicChart x ≠
        thirdDirectionStereographicChart secondDirectionInThirdComplement := by
    rw [thirdDirectionStereographicChart.injective.ne_iff]
    constructor
    · intro hne heq
      exact hne (congrArg Subtype.val heq)
    · intro hne heq
      apply hne
      exact Subtype.ext heq
  have hthird : x.1 ≠ positiveCoordinateDirection 2 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.2
  change (x.1 ≠ positiveCoordinateDirection 0 ∧
      x.1 ≠ positiveCoordinateDirection 1 ∧
      x.1 ≠ positiveCoordinateDirection 2) ↔ _
  rw [hfirst, hsecond]
  tauto

/-- Helper for Exercise 58.2: the affine coefficient normalizing two distinct complex
punctures to distance one. -/
private noncomputable def twoPunctureNormalizationCoefficient (p q : ℂ) : ℂ :=
  (q - p)⁻¹

/-- Helper for Exercise 58.2: the affine translation sends the first puncture to `-1/2`. -/
private noncomputable def twoPunctureNormalizationTranslation (p q : ℂ) : ℂ :=
  DoublyPuncturedPlane.leftPuncture - twoPunctureNormalizationCoefficient p q * p

/-- Helper for Exercise 58.2: distinct punctures give a nonzero affine coefficient. -/
private lemma twoPunctureNormalizationCoefficient_ne_zero
    (p q : ℂ) (hpq : p ≠ q) : twoPunctureNormalizationCoefficient p q ≠ 0 := by
  -- The inverse of their nonzero difference is nonzero.
  exact inv_ne_zero (sub_ne_zero.mpr hpq.symm)

/-- Helper for Exercise 58.2: the affine homeomorphism used to normalize two punctures. -/
private noncomputable def twoPunctureNormalizationHomeomorph
    (p q : ℂ) (hpq : p ≠ q) : ℂ ≃ₜ ℂ :=
  affineHomeomorph (twoPunctureNormalizationCoefficient p q)
    (twoPunctureNormalizationTranslation p q)
    (twoPunctureNormalizationCoefficient_ne_zero p q hpq)

/-- Helper for Exercise 58.2: affine normalization sends the first puncture to the
canonical left puncture. -/
private lemma twoPunctureNormalizationHomeomorph_apply_left
    (p q : ℂ) (hpq : p ≠ q) :
    twoPunctureNormalizationHomeomorph p q hpq p =
      DoublyPuncturedPlane.leftPuncture := by
  -- The translation was chosen to cancel the scaled first puncture.
  simp only [twoPunctureNormalizationHomeomorph, affineHomeomorph_apply,
    twoPunctureNormalizationTranslation]
  ring

/-- Helper for Exercise 58.2: affine normalization sends the second puncture to the
canonical right puncture. -/
private lemma twoPunctureNormalizationHomeomorph_apply_right
    (p q : ℂ) (hpq : p ≠ q) :
    twoPunctureNormalizationHomeomorph p q hpq q =
      DoublyPuncturedPlane.rightPuncture := by
  -- The scaled difference of the punctures is one, leaving the two half-unit endpoints.
  have hdiff : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  simp only [twoPunctureNormalizationHomeomorph, affineHomeomorph_apply,
    twoPunctureNormalizationTranslation, twoPunctureNormalizationCoefficient]
  calc
    (q - p)⁻¹ * q +
        (DoublyPuncturedPlane.leftPuncture - (q - p)⁻¹ * p) =
      DoublyPuncturedPlane.leftPuncture + (q - p)⁻¹ * (q - p) := by ring
    _ = DoublyPuncturedPlane.leftPuncture + 1 := by
      rw [inv_mul_cancel₀ hdiff]
    _ = DoublyPuncturedPlane.rightPuncture := by
      norm_num [DoublyPuncturedPlane.leftPuncture,
        DoublyPuncturedPlane.rightPuncture]

/-- Helper for Exercise 58.2: affine normalization preserves the two-puncture complement
predicate. -/
private lemma twoPunctureNormalizationHomeomorph_mem_iff
    (p q : ℂ) (hpq : p ≠ q) (z : ℂ) :
    (z ≠ p ∧ z ≠ q) ↔
      (twoPunctureNormalizationHomeomorph p q hpq z ≠
          DoublyPuncturedPlane.leftPuncture ∧
        twoPunctureNormalizationHomeomorph p q hpq z ≠
          DoublyPuncturedPlane.rightPuncture) := by
  -- Replace each canonical puncture by its affine preimage and use injectivity.
  rw [← twoPunctureNormalizationHomeomorph_apply_left p q hpq,
    ← twoPunctureNormalizationHomeomorph_apply_right p q hpq,
    (twoPunctureNormalizationHomeomorph p q hpq).injective.ne_iff,
    (twoPunctureNormalizationHomeomorph p q hpq).injective.ne_iff]

/-- Helper for Exercise 58.2: any complex plane with two distinct punctures is
homeomorphic to the normalized doubly punctured plane. -/
private noncomputable def twoPuncturePlaneNormalizationHomeomorph
    (p q : ℂ) (hpq : p ≠ q) : TwoPuncturePlane p q ≃ₜ DoublyPuncturedPlane :=
  (twoPunctureNormalizationHomeomorph p q hpq).subtype
    (twoPunctureNormalizationHomeomorph_mem_iff p q hpq)

/-- Helper for Exercise 58.2: the stereographic images of the first two coordinate
directions are distinct. -/
private lemma firstSecondStereographicImages_ne :
    thirdDirectionStereographicChart firstDirectionInThirdComplement ≠
      thirdDirectionStereographicChart secondDirectionInThirdComplement := by
  -- Injectivity reduces the claim to distinct coordinate directions.
  apply thirdDirectionStereographicChart.injective.ne
  intro h
  apply positiveCoordinateDirection_ne (by decide : (0 : Fin 3) ≠ 1)
  exact congrArg Subtype.val h

/-- Helper for Exercise 58.2: the complement of the three positive coordinate directions
is homeomorphic to the normalized doubly punctured plane. -/
private noncomputable def
    threeCoordinateDirectionComplementHomeomorphDoublyPuncturedPlane :
    ThreeCoordinateDirectionComplement ≃ₜ DoublyPuncturedPlane :=
  (nestedSubsetHomeomorph
      ({positiveCoordinateDirection 2}ᶜ :
        Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
      threeCoordinateDirectionComplement
      threeCoordinateDirectionComplement_subset_thirdComplement).symm.trans <|
    (thirdDirectionStereographicChart.subtype
      thirdDirectionStereographicChart_punctures_iff).trans <|
        twoPuncturePlaneNormalizationHomeomorph
          (thirdDirectionStereographicChart firstDirectionInThirdComplement)
          (thirdDirectionStereographicChart secondDirectionInThirdComplement)
          firstSecondStereographicImages_ne

/-- Helper for Exercise 58.2: every point of the canonical planar theta carrier avoids
the two normalized punctures. -/
private lemma planarTheta_avoidsNormalizedPunctures :
    PlanarTheta.carrier ⊆
      {z : ℂ | z ≠ DoublyPuncturedPlane.leftPuncture ∧
        z ≠ DoublyPuncturedPlane.rightPuncture} := by
  -- Neither real puncture lies on the unit circle or on the vertical diameter.
  intro z hz
  constructor
  · intro hleft
    subst z
    rw [PlanarTheta.mem_iff] at hz
    rcases hz with hz | hz
    · norm_num [DoublyPuncturedPlane.leftPuncture, Complex.norm_def] at hz
    · norm_num [DoublyPuncturedPlane.leftPuncture] at hz
  · intro hright
    subst z
    rw [PlanarTheta.mem_iff] at hz
    rcases hz with hz | hz
    · norm_num [DoublyPuncturedPlane.rightPuncture, Complex.norm_def] at hz
    · norm_num [DoublyPuncturedPlane.rightPuncture] at hz

/-- Helper for Exercise 58.2: the nested planar-theta retract is homeomorphic to the
direct planar theta carrier. -/
private noncomputable def planarThetaRetractHomeomorph :
    PlanarTheta.inDoublyPuncturedPlane ≃ₜ PlanarTheta :=
  nestedSubsetHomeomorph
    {z : ℂ | z ≠ DoublyPuncturedPlane.leftPuncture ∧
      z ≠ DoublyPuncturedPlane.rightPuncture}
    PlanarTheta.carrier planarTheta_avoidsNormalizedPunctures

/-- Helper for Exercise 58.2: the unit circle component of `PlanarTheta`. -/
private def planarThetaCircle : Set ℂ :=
  {z | ‖z‖ = 1}

/-- Helper for Exercise 58.2: the closed vertical diameter component of `PlanarTheta`. -/
private def planarThetaDiameter : Set ℂ :=
  {z | z.re = 0 ∧ z.im ∈ Set.Icc (-1 : ℝ) 1}

/-- Helper for Exercise 58.2: the vertical diameter is convex. -/
private lemma planarThetaDiameter_convex : Convex ℝ planarThetaDiameter := by
  -- Coordinatewise affine combinations preserve zero real part and the interval bounds.
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hxre, hxim⟩
  rcases hy with ⟨hyre, hyim⟩
  constructor
  · simp only [Complex.add_re, Complex.smul_re, hxre, hyre, smul_eq_mul,
      mul_zero, add_zero]
  · constructor
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
      nlinarith [hxim.1, hyim.1]
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
      nlinarith [hxim.2, hyim.2]

/-- Helper for Exercise 58.2: the canonical planar theta carrier is path connected. -/
private lemma planarTheta_isPathConnected : IsPathConnected PlanarTheta.carrier := by
  -- Join the path-connected unit circle and convex diameter at the point `I`.
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hcircle : IsPathConnected planarThetaCircle := by
    have hsphere := isPathConnected_sphere hrank (0 : ℂ) (r := 1) zero_le_one
    have hset : Metric.sphere (0 : ℂ) 1 = planarThetaCircle := by
      ext z
      simp only [Metric.mem_sphere, dist_zero_right, planarThetaCircle, Set.mem_setOf_eq]
    rwa [hset] at hsphere
  have hdiameter : IsPathConnected planarThetaDiameter :=
    planarThetaDiameter_convex.isPathConnected
      ⟨Complex.I, by simp [planarThetaDiameter]⟩
  have hinter : (planarThetaCircle ∩ planarThetaDiameter).Nonempty := by
    exact ⟨Complex.I, by simp [planarThetaCircle, planarThetaDiameter]⟩
  have hunion := hcircle.union hdiameter hinter
  have hcarrier : planarThetaCircle ∪ planarThetaDiameter = PlanarTheta.carrier := by
    ext z
    rw [PlanarTheta.mem_iff]
    rfl
  rwa [hcarrier] at hunion

/-- Exercise 58.2 (5): The fundamental group of `ℝ³` with its three nonnegative coordinate
axes deleted is the fundamental group of the figure eight. -/
theorem fundamentalGroup_complement_threeRays
    (p : {x : EuclideanSpace ℝ (Fin 3) //
      x ∉ Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 0 t.1) ∪
        Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 1 t.1) ∪
        Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 2 t.1)}) :
    Nonempty
      (FundamentalGroup
        {x : EuclideanSpace ℝ (Fin 3) //
          x ∉ Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 0 t.1) ∪
            Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 1 t.1) ∪
            Set.range (fun t : Set.Ici (0 : ℝ) ↦ EuclideanSpace.single 2 t.1)} p ≃*
        FundamentalGroup FigureEight FigureEight.basepoint) := by
  -- Polar coordinates split off the contractible positive radial factor.
  let ePolar := threeRaysPolarHomeomorph
  let z := ePolar p
  let eAngular := threeCoordinateDirectionComplementHomeomorphDoublyPuncturedPlane
  obtain ⟨eRetract⟩ := planarTheta_isDeformationRetract.nonempty_homotopyEquiv
  let eTheta : ContinuousMap.HomotopyEquiv DoublyPuncturedPlane PlanarTheta :=
    eRetract.symm.trans planarThetaRetractHomeomorph.toHomotopyEquiv
  letI : PathConnectedSpace PlanarTheta :=
    isPathConnected_iff_pathConnectedSpace.mp planarTheta_isPathConnected
  obtain ⟨eFigureEight⟩ := figureEightFundamentalGroup_mulEquiv_planarTheta
  -- Normalize the angular complement, retract to theta, and transport the resulting basepoint.
  exact ⟨(ePolar.fundamentalGroupMulEquiv p).trans <|
    (FundamentalGroup.prodMulEquivLeftOfSubsingleton z.1 z.2
      (Convex.subsingleton_fundamentalGroup (convex_Ioi 0) z.2)).trans <|
    (eAngular.fundamentalGroupMulEquiv z.1).trans <|
    (eTheta.fundamentalGroupMulEquiv (eAngular z.1)).trans <|
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      (eTheta (eAngular z.1)) PlanarTheta.basepoint).trans eFigureEight.symm⟩

/-- Exercise 58.2 (6): The fundamental group of the exterior of the closed unit disk in
`ℝ²` is infinite cyclic. -/
theorem fundamentalGroup_exterior_closedDisk
    (p : {x : EuclideanSpace ℝ (Fin 2) // 1 < ‖x‖}) :
    Nonempty
      (FundamentalGroup {x : EuclideanSpace ℝ (Fin 2) // 1 < ‖x‖} p ≃* Multiplicative ℤ) := by
  -- Polar coordinates split the exterior into its angular sphere and a convex radial factor.
  let e := exteriorClosedDiskPolarHomeomorph
  exact ⟨(e.fundamentalGroupMulEquiv p).trans <|
    (FundamentalGroup.prodMulEquivLeftOfSubsingleton (e p).1 (e p).2
      (Convex.subsingleton_fundamentalGroup (convex_Ioi 1) (e p).2)).trans <|
        (euclideanSphereHomeomorphCircle.fundamentalGroupMulEquiv (e p).1).trans <|
          (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
            (euclideanSphereHomeomorphCircle (e p).1) 1).trans
              Circle.fundamentalGroupEquivInt⟩

/-- Exercise 58.2 (7): The fundamental group of the exterior of the open unit disk in `ℝ²`
is infinite cyclic. -/
theorem fundamentalGroup_exterior_openDisk
    (p : {x : EuclideanSpace ℝ (Fin 2) // 1 ≤ ‖x‖}) :
    Nonempty
      (FundamentalGroup {x : EuclideanSpace ℝ (Fin 2) // 1 ≤ ‖x‖} p ≃* Multiplicative ℤ) := by
  -- The weak radial inequality gives the same angular factor and a convex closed ray.
  let e := exteriorOpenDiskPolarHomeomorph
  exact ⟨(e.fundamentalGroupMulEquiv p).trans <|
    (FundamentalGroup.prodMulEquivLeftOfSubsingleton (e p).1 (e p).2
      (Convex.subsingleton_fundamentalGroup (convex_Ici 1) (e p).2)).trans <|
        (euclideanSphereHomeomorphCircle.fundamentalGroupMulEquiv (e p).1).trans <|
          (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
            (euclideanSphereHomeomorphCircle (e p).1) 1).trans
              Circle.fundamentalGroupEquivInt⟩

/-- Exercise 58.2 (8): The open unit disk in `ℝ²` has trivial fundamental group. -/
instance fundamentalGroup_openDisk (p : {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ < 1}) :
    Subsingleton (FundamentalGroup {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ < 1} p) := by
  -- Rewrite the norm condition as the open unit ball and use convexity.
  have hconvex : Convex ℝ {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ < 1} := by
    have hset : {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ < 1} = Metric.ball 0 1 := by
      ext x
      simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]
    rw [hset]
    exact convex_ball (0 : EuclideanSpace ℝ (Fin 2)) 1
  exact hconvex.subsingleton_fundamentalGroup p

/-- Exercise 58.2 (9): The union in `ℝ²` of the unit circle and the positive horizontal ray
has infinite cyclic fundamental group. -/
theorem fundamentalGroup_circle_union_ray
    (p : {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1 ∨ (0 < x 0 ∧ x 1 = 0)}) :
    Nonempty
      (FundamentalGroup
        {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1 ∨ (0 < x 0 ∧ x 1 = 0)} p ≃*
        Multiplicative ℤ) := by
  -- Contract the polar radial whisker, then compute the fundamental group of its circle model.
  let e := circleUnionRayHomotopyEquivCircle
  exact ⟨(e.fundamentalGroupMulEquiv p).trans <|
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (e p) 1).trans
      Circle.fundamentalGroupEquivInt⟩

/-- Exercise 58.2 (10): The union in `ℝ²` of the unit circle and the open right half-plane
has infinite cyclic fundamental group. -/
theorem fundamentalGroup_circle_union_halfPlane
    (p : {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1 ∨ 0 < x 0}) :
    Nonempty
      (FundamentalGroup {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1 ∨ 0 < x 0} p ≃*
        Multiplicative ℤ) := by
  -- The half-plane contributes only contractible radial whiskers over the same angular circle.
  let e := circleUnionHalfPlaneHomotopyEquivCircle
  exact ⟨(e.fundamentalGroupMulEquiv p).trans <|
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (e p) 1).trans
      Circle.fundamentalGroupEquivInt⟩

/-- Helper for Exercise 58.2: the circle together with the horizontal axis. -/
private abbrev CircleUnionAxis :=
  {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1 ∨ x 1 = 0}

/-- Helper for Exercise 58.2: the unit circle together with its horizontal diameter,
viewed inside the circle-axis union. -/
private def boundedHorizontalTheta : Set CircleUnionAxis :=
  {x | ‖x.1‖ = 1 ∨ (x.1 1 = 0 ∧ x.1 0 ∈ Set.Icc (-1 : ℝ) 1)}

/-- Helper for Exercise 58.2: the scalar that linearly interpolates from the identity
to radial clipping at the closed unit disk. -/
private noncomputable def circleUnionAxisClippingScale
    (t : unitInterval) (x : CircleUnionAxis) : ℝ :=
  1 - (t : ℝ) + (t : ℝ) * (max 1 ‖x.1‖)⁻¹

/-- Helper for Exercise 58.2: the clipping scale at time zero is one. -/
private lemma circleUnionAxisClippingScale_zero (x : CircleUnionAxis) :
    circleUnionAxisClippingScale 0 x = 1 := by
  -- Substitute the zero endpoint in the affine interpolation.
  simp [circleUnionAxisClippingScale]

/-- Helper for Exercise 58.2: the clipping scale at time one is the reciprocal max-norm. -/
private lemma circleUnionAxisClippingScale_one (x : CircleUnionAxis) :
    circleUnionAxisClippingScale 1 x = (max 1 ‖x.1‖)⁻¹ := by
  -- Substitute the one endpoint in the affine interpolation.
  simp [circleUnionAxisClippingScale]

/-- Helper for Exercise 58.2: radial clipping preserves the circle-axis union. -/
private lemma circleUnionAxisClipping_mem (t : unitInterval) (x : CircleUnionAxis) :
    ‖circleUnionAxisClippingScale t x • x.1‖ = 1 ∨
      (circleUnionAxisClippingScale t x • x.1) 1 = 0 := by
  -- Circle points have scale one, while scalar multiplication preserves the axis equation.
  rcases x.2 with hcircle | haxis
  · left
    have hscale : circleUnionAxisClippingScale t x = 1 := by
      simp only [circleUnionAxisClippingScale, hcircle, max_self, inv_one, mul_one]
      ring
    rw [hscale, one_smul, hcircle]
  · right
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, haxis, mul_zero]

/-- Helper for Exercise 58.2: the radial clipping homotopy evaluated at a parameter
and a point of the circle-axis union. -/
private noncomputable def circleUnionAxisClippingValue
    (t : unitInterval) (x : CircleUnionAxis) : CircleUnionAxis :=
  ⟨circleUnionAxisClippingScale t x • x.1, circleUnionAxisClipping_mem t x⟩

/-- Helper for Exercise 58.2: the underlying point of the clipping value is its scalar formula. -/
private lemma circleUnionAxisClippingValue_coe
    (t : unitInterval) (x : CircleUnionAxis) :
    (circleUnionAxisClippingValue t x).1 = circleUnionAxisClippingScale t x • x.1 := by
  -- Expose the value projection without rewriting through its membership proof.
  rfl

/-- Helper for Exercise 58.2: the radial clipping homotopy is continuous. -/
private lemma continuous_circleUnionAxisClippingValue :
    Continuous fun tx : unitInterval × CircleUnionAxis ↦
      circleUnionAxisClippingValue tx.1 tx.2 := by
  -- The denominator is bounded below by one, so inversion is continuous on the image.
  have ht : Continuous fun tx : unitInterval × CircleUnionAxis ↦ (tx.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous fun tx : unitInterval × CircleUnionAxis ↦ tx.2.1 :=
    continuous_subtype_val.comp continuous_snd
  have hmax : Continuous fun tx : unitInterval × CircleUnionAxis ↦ max 1 ‖tx.2.1‖ :=
    continuous_const.max hx.norm
  have hmax_ne : ∀ tx : unitInterval × CircleUnionAxis, max 1 ‖tx.2.1‖ ≠ 0 := by
    intro tx
    exact (zero_lt_one.trans_le (le_max_left 1 ‖tx.2.1‖)).ne'
  have hscale : Continuous fun tx : unitInterval × CircleUnionAxis ↦
      1 - (tx.1 : ℝ) + (tx.1 : ℝ) * (max 1 ‖tx.2.1‖)⁻¹ :=
    (continuous_const.sub ht).add (ht.mul (hmax.inv₀ hmax_ne))
  exact (hscale.smul hx).subtype_mk fun tx ↦ circleUnionAxisClipping_mem tx.1 tx.2

/-- Helper for Exercise 58.2: radial clipping begins at the identity. -/
private lemma circleUnionAxisClippingValue_zero (x : CircleUnionAxis) :
    circleUnionAxisClippingValue 0 x = x := by
  -- At parameter zero the interpolation scalar is one.
  apply Subtype.ext
  calc
    (circleUnionAxisClippingValue 0 x).1 =
        circleUnionAxisClippingScale 0 x • x.1 :=
      circleUnionAxisClippingValue_coe 0 x
    _ = 1 • x.1 := congrArg (fun a : ℝ ↦ a • x.1)
      (circleUnionAxisClippingScale_zero x)
    _ = x.1 := one_smul ℝ x.1

/-- Helper for Exercise 58.2: the clipped endpoint has norm at most one. -/
private lemma circleUnionAxisClippingValue_one_norm_le (x : CircleUnionAxis) :
    ‖(circleUnionAxisClippingValue 1 x).1‖ ≤ 1 := by
  -- Dividing by `max 1 ‖x‖` makes the endpoint norm at most one.
  rw [circleUnionAxisClippingValue_coe, circleUnionAxisClippingScale_one]
  simp only [norm_smul, norm_inv, Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_of_le_left zero_le_one)]
  exact inv_mul_le_one_of_le₀ (le_max_right 1 ‖x.1‖)
    (le_max_of_le_left zero_le_one)

/-- Helper for Exercise 58.2: the clipped endpoint lies in the bounded horizontal theta graph. -/
private lemma circleUnionAxisClippingValue_one_mem (x : CircleUnionAxis) :
    circleUnionAxisClippingValue 1 x ∈ boundedHorizontalTheta := by
  -- Circle points remain on the circle; axis points acquire coordinates in `[-1, 1]`.
  rcases x.2 with hcircle | haxis
  · left
    have hscale : circleUnionAxisClippingScale 1 x = 1 := by
      rw [circleUnionAxisClippingScale_one, hcircle, max_self, inv_one]
    simpa only [circleUnionAxisClippingValue, hscale, one_smul] using hcircle
  · right
    refine ⟨?_, ?_⟩
    · simp only [circleUnionAxisClippingValue, WithLp.ofLp_smul, Pi.smul_apply,
        smul_eq_mul, haxis, mul_zero]
    · let y := (circleUnionAxisClippingValue 1 x).1
      change y 0 ∈ Set.Icc (-1 : ℝ) 1
      rw [Set.mem_Icc]
      have hynorm : ‖y‖ ≤ 1 := circleUnionAxisClippingValue_one_norm_le x
      have hsq := EuclideanSpace.real_norm_sq_eq y
      simp only [Fin.sum_univ_two] at hsq
      have hcoord_sq : (y 0) ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (y 1), norm_nonneg y]
      constructor
      · nlinarith [sq_nonneg (y 0 + 1)]
      · nlinarith [sq_nonneg (y 0 - 1)]

/-- Helper for Exercise 58.2: points of the bounded horizontal theta graph have norm at most one
unless they already lie on its circle. -/
private lemma boundedHorizontalTheta_axis_norm_le
    (x : CircleUnionAxis) (haxis : x.1 1 = 0)
    (hbound : x.1 0 ∈ Set.Icc (-1 : ℝ) 1) : ‖x.1‖ ≤ 1 := by
  -- The Euclidean norm square reduces to the square of the bounded horizontal coordinate.
  have hsq := EuclideanSpace.real_norm_sq_eq x.1
  simp only [Fin.sum_univ_two, haxis] at hsq
  have hcoord_sq : (x.1 0) ^ 2 ≤ 1 := by
    rcases hbound with ⟨hlower, hupper⟩
    nlinarith [sq_nonneg (x.1 0 + 1), sq_nonneg (x.1 0 - 1)]
  nlinarith [norm_nonneg x.1]

/-- Helper for Exercise 58.2: radial clipping fixes the bounded horizontal theta graph. -/
private lemma circleUnionAxisClippingValue_of_mem
    (t : unitInterval) (x : CircleUnionAxis) (hx : x ∈ boundedHorizontalTheta) :
    circleUnionAxisClippingValue t x = x := by
  -- Both branches have norm at most one, making the clipping denominator equal to one.
  have hnorm : ‖x.1‖ ≤ 1 := by
    rcases hx with hcircle | haxis
    · exact hcircle.le
    · exact boundedHorizontalTheta_axis_norm_le x haxis.1 haxis.2
  apply Subtype.ext
  have hscale : circleUnionAxisClippingScale t x = 1 := by
    simp only [circleUnionAxisClippingScale, max_eq_left hnorm, inv_one, mul_one]
    ring
  calc
    (circleUnionAxisClippingValue t x).1 =
        circleUnionAxisClippingScale t x • x.1 :=
      circleUnionAxisClippingValue_coe t x
    _ = 1 • x.1 := congrArg (fun a : ℝ ↦ a • x.1) hscale
    _ = x.1 := one_smul ℝ x.1

/-- Helper for Exercise 58.2: the endpoint clipping map into the bounded theta graph. -/
private noncomputable def circleUnionAxisClippingRetractionMap :
    C(CircleUnionAxis, boundedHorizontalTheta) :=
  ⟨fun x ↦ ⟨circleUnionAxisClippingValue 1 x,
      circleUnionAxisClippingValue_one_mem x⟩,
    continuous_circleUnionAxisClippingValue.comp
      (continuous_const.prodMk continuous_id) |>.subtype_mk
        circleUnionAxisClippingValue_one_mem⟩

/-- Helper for Exercise 58.2: endpoint clipping is the identity on the bounded theta graph. -/
private lemma circleUnionAxisClippingRetraction_leftInverse :
    Function.LeftInverse circleUnionAxisClippingRetractionMap
      (Subtype.val : boundedHorizontalTheta → CircleUnionAxis) := by
  -- Apply fixedness at time one and then extensionality of the nested subtype.
  intro x
  apply Subtype.ext
  exact circleUnionAxisClippingValue_of_mem 1 x.1 x.2

/-- Helper for Exercise 58.2: endpoint clipping is a retraction. -/
private noncomputable def circleUnionAxisClippingRetraction :
    Set.Retraction boundedHorizontalTheta :=
  ⟨circleUnionAxisClippingRetractionMap,
    circleUnionAxisClippingRetraction_leftInverse⟩

/-- Helper for Exercise 58.2: the clipping homotopy ends at its retraction's ambient map. -/
private lemma circleUnionAxisClippingValue_one (x : CircleUnionAxis) :
    circleUnionAxisClippingValue 1 x = circleUnionAxisClippingRetraction.toAmbient x := by
  -- Both sides have the same clipped underlying point.
  rfl

/-- Helper for Exercise 58.2: radial clipping defines the endpoint homotopy. -/
private noncomputable def circleUnionAxisClippingHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id CircleUnionAxis)
      circleUnionAxisClippingRetraction.toAmbient :=
  { toFun := fun tx ↦ circleUnionAxisClippingValue tx.1 tx.2
    continuous_toFun := continuous_circleUnionAxisClippingValue
    map_zero_left := circleUnionAxisClippingValue_zero
    map_one_left := circleUnionAxisClippingValue_one }

/-- Helper for Exercise 58.2: the clipping homotopy remains fixed on the bounded theta graph. -/
private lemma circleUnionAxisClippingHomotopy_fixed
    (t : unitInterval) (x : CircleUnionAxis) (hx : x ∈ boundedHorizontalTheta) :
    circleUnionAxisClippingHomotopy (t, x) = (ContinuousMap.id CircleUnionAxis) x := by
  -- This is the fixed-point specification of the clipping value.
  exact circleUnionAxisClippingValue_of_mem t x hx

/-- Helper for Exercise 58.2: radial clipping is a homotopy relative to the bounded theta graph. -/
private noncomputable def circleUnionAxisClippingHomotopyRel :
    ContinuousMap.HomotopyRel (ContinuousMap.id CircleUnionAxis)
      circleUnionAxisClippingRetraction.toAmbient boundedHorizontalTheta :=
  { toHomotopy := circleUnionAxisClippingHomotopy
    prop' := circleUnionAxisClippingHomotopy_fixed }

/-- Helper for Exercise 58.2: the bounded horizontal theta graph is a deformation retract
of the circle-axis union. -/
private theorem circleUnionAxis_isDeformationRetract_boundedHorizontalTheta :
    Set.IsDeformationRetract boundedHorizontalTheta := by
  -- Package the clipping retraction and its relative homotopy.
  rw [Set.isDeformationRetract_iff]
  exact ⟨circleUnionAxisClippingRetraction, ⟨circleUnionAxisClippingHomotopyRel⟩⟩

/-- Helper for Exercise 58.2: rotation through a quarter turn after standard complex
coordinates sends the horizontal direction to the vertical direction. -/
private noncomputable def horizontalThetaRotation :
    EuclideanSpace ℝ (Fin 2) ≃ₜ ℂ :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.trans
    (Homeomorph.mulLeft₀ Complex.I Complex.I_ne_zero)

/-- Helper for Exercise 58.2: quarter-turn complex coordinates preserve the norm. -/
private lemma horizontalThetaRotation_norm (x : EuclideanSpace ℝ (Fin 2)) :
    ‖horizontalThetaRotation x‖ = ‖x‖ := by
  -- Both the real-linear coordinate isometry and multiplication by `I` preserve norm.
  change ‖Complex.I * Complex.orthonormalBasisOneI.repr.symm x‖ = ‖x‖
  rw [Complex.norm_mul, Complex.norm_I, one_mul]
  exact Complex.orthonormalBasisOneI.repr.symm.norm_map x

/-- Helper for Exercise 58.2: the real coordinate after quarter-turn rotation is minus
the second Euclidean coordinate. -/
private lemma horizontalThetaRotation_re (x : EuclideanSpace ℝ (Fin 2)) :
    (horizontalThetaRotation x).re = -x 1 := by
  -- Evaluate the standard complex coordinate formula and multiplication by `I`.
  change (Complex.I * Complex.orthonormalBasisOneI.repr.symm x).re = -x 1
  rw [Complex.I_mul_re, Complex.orthonormalBasisOneI_repr_symm_apply]
  simp

/-- Helper for Exercise 58.2: the imaginary coordinate after quarter-turn rotation is
the first Euclidean coordinate. -/
private lemma horizontalThetaRotation_im (x : EuclideanSpace ℝ (Fin 2)) :
    (horizontalThetaRotation x).im = x 0 := by
  -- The same coordinate calculation identifies the vertical coordinate.
  change (Complex.I * Complex.orthonormalBasisOneI.repr.symm x).im = x 0
  rw [Complex.orthonormalBasisOneI_repr_symm_apply]
  simp [Complex.mul_im]

/-- Helper for Exercise 58.2: the bounded horizontal theta predicate is carried to
the canonical planar theta predicate by quarter-turn rotation. -/
private lemma horizontalThetaRotation_mem_iff (x : EuclideanSpace ℝ (Fin 2)) :
    (‖x‖ = 1 ∨ (x 1 = 0 ∧ x 0 ∈ Set.Icc (-1 : ℝ) 1)) ↔
      horizontalThetaRotation x ∈ PlanarTheta.carrier := by
  -- Rewrite norm and coordinate projections to the canonical vertical-diameter normal form.
  rw [PlanarTheta.mem_iff, horizontalThetaRotation_norm,
    horizontalThetaRotation_re, horizontalThetaRotation_im]
  constructor
  · intro hx
    rcases hx with hcircle | hdiameter
    · exact Or.inl hcircle
    · exact Or.inr ⟨neg_eq_zero.mpr hdiameter.1, hdiameter.2⟩
  · intro hx
    rcases hx with hcircle | hdiameter
    · exact Or.inl hcircle
    · exact Or.inr ⟨neg_eq_zero.mp hdiameter.1, hdiameter.2⟩

/-- Helper for Exercise 58.2: the bounded theta carrier is contained in the full
circle-axis carrier. -/
private lemma boundedHorizontalTheta_subset_circleUnionAxis :
    {x : EuclideanSpace ℝ (Fin 2) |
      ‖x‖ = 1 ∨ (x 1 = 0 ∧ x 0 ∈ Set.Icc (-1 : ℝ) 1)} ⊆
      {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ = 1 ∨ x 1 = 0} := by
  -- Forget the horizontal boundedness condition in the axis branch.
  intro x hx
  exact hx.imp_right And.left

/-- Helper for Exercise 58.2: the bounded horizontal theta graph is homeomorphic to
the canonical planar theta graph. -/
private noncomputable def boundedHorizontalThetaHomeomorphPlanarTheta :
    boundedHorizontalTheta ≃ₜ PlanarTheta :=
  (nestedSubsetHomeomorph
      {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ = 1 ∨ x 1 = 0}
      {x : EuclideanSpace ℝ (Fin 2) |
        ‖x‖ = 1 ∨ (x 1 = 0 ∧ x 0 ∈ Set.Icc (-1 : ℝ) 1)}
      boundedHorizontalTheta_subset_circleUnionAxis).trans
    (horizontalThetaRotation.subtype horizontalThetaRotation_mem_iff)

/-- Exercise 58.2 (11): The union in `ℝ²` of the unit circle and the horizontal axis has
fundamental group isomorphic to that of the figure eight. -/
theorem fundamentalGroup_circle_union_axis
    (p : {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1 ∨ x 1 = 0}) :
    Nonempty
      (FundamentalGroup {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1 ∨ x 1 = 0} p ≃*
        FundamentalGroup FigureEight FigureEight.basepoint) := by
  -- Pass from the full axis union to the bounded theta retract and rotate it to `PlanarTheta`.
  obtain ⟨eRetract⟩ :=
    circleUnionAxis_isDeformationRetract_boundedHorizontalTheta.nonempty_homotopyEquiv
  let e : ContinuousMap.HomotopyEquiv CircleUnionAxis PlanarTheta :=
    eRetract.symm.trans boundedHorizontalThetaHomeomorphPlanarTheta.toHomotopyEquiv
  letI : PathConnectedSpace PlanarTheta :=
    isPathConnected_iff_pathConnectedSpace.mp planarTheta_isPathConnected
  obtain ⟨eFigureEight⟩ := figureEightFundamentalGroup_mulEquiv_planarTheta
  -- Transport the image basepoint to the canonical theta basepoint and reverse the known model.
  exact ⟨(e.fundamentalGroupMulEquiv p).trans <|
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      (e p) PlanarTheta.basepoint).trans eFigureEight.symm⟩

/-- Helper for Exercise 58.2: the complement of the strictly positive horizontal ray is
star convex at the origin. -/
lemma complementPositiveRay_isStarConvex :
    Set.IsStarConvex ℝ
      {x : EuclideanSpace ℝ (Fin 2) | ¬(0 < x 0 ∧ x 1 = 0)} := by
  -- The origin lies in the complement and will be the common star center.
  have horigin : (0 : EuclideanSpace ℝ (Fin 2)) ∈
      {x : EuclideanSpace ℝ (Fin 2) | ¬(0 < x 0 ∧ x 1 = 0)} := by
    simp only [Set.mem_setOf_eq, WithLp.ofLp_zero, Pi.zero_apply, lt_self_iff_false,
      false_and, not_false_eq_true]
  refine Set.IsStarConvex.of_starConvex horigin ?_
  rw [starConvex_iff_forall_pos horigin]
  intro y hy a b ha hb hab
  -- A positive point on the segment would force its nonzero endpoint onto the deleted ray.
  simp only [smul_zero, zero_add]
  intro hdeleted
  apply hy
  have hcoord0 : 0 < b * y 0 := by
    simpa only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] using hdeleted.1
  have hcoord1 : b * y 1 = 0 := by
    simpa only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] using hdeleted.2
  constructor
  · nlinarith
  · exact (mul_eq_zero.mp hcoord1).resolve_left hb.ne'

/-- Exercise 58.2 (12): The plane with the positive horizontal ray deleted has trivial
fundamental group. -/
instance fundamentalGroup_complement_positiveRay
    (p : {x : EuclideanSpace ℝ (Fin 2) // ¬(0 < x 0 ∧ x 1 = 0)}) :
    Subsingleton
      (FundamentalGroup {x : EuclideanSpace ℝ (Fin 2) // ¬(0 < x 0 ∧ x 1 = 0)} p) := by
  -- Star convexity contracts the ray complement and therefore trivializes every based loop.
  letI : SimplyConnectedSpace
      {x : EuclideanSpace ℝ (Fin 2) // ¬(0 < x 0 ∧ x 1 = 0)} :=
    complementPositiveRay_isStarConvex.isSimplyConnected
  infer_instance
