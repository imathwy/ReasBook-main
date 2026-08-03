module

public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Topology_Munkres_2000.Book.Proposition_55_1.Triangle
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Convex.PartitionOfUnity
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.PartitionOfUnity

public section

open scoped CoveringDimension

open Set Function

/-- Helper for Proposition 55.1: the standard triangle is convex. -/
private lemma standardTriangleConvex : Convex ℝ standardTriangle := by
  -- Each of the three defining inequalities is preserved by a convex combination.
  rw [convex_iff_segment_subset]
  intro x hx y hy
  rw [segment_subset_iff]
  intro a b ha hb hab
  rw [mem_standardTriangle] at hx hy ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor
  · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  constructor
  · exact add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1)
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.2.2),
      mul_nonneg hb (sub_nonneg.mpr hy.2.2)]

/-- Helper for Proposition 55.1: the standard triangle is bounded. -/
private lemma standardTriangleBounded : Bornology.IsBounded standardTriangle := by
  -- The coordinate inequalities place the triangle inside a bounded square.
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2, ?_⟩
  intro x hx
  rw [mem_standardTriangle] at hx
  rw [EuclideanSpace.norm_eq]
  have hx0 : x 0 ≤ 1 := by
    linarith [hx.2.2, hx.2.1]
  have hx1 : x 1 ≤ 1 := by
    linarith [hx.2.2, hx.1]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs]
  rw [abs_of_nonneg hx.1, abs_of_nonneg hx.2.1, Real.sqrt_le_iff]
  constructor
  · norm_num
  · nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- Helper for Proposition 55.1: the standard triangle has nonempty interior. -/
private lemma standardTriangleInteriorNonempty :
    (interior standardTriangle).Nonempty := by
  -- A ball around the point with both coordinates `1 / 4` stays in the triangle.
  let c : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun _ ↦ 1 / 4)
  refine ⟨c, mem_interior_iff_mem_nhds.mpr ?_⟩
  have hradius : 0 < (1 / 8 : ℝ) := by
    norm_num
  refine Filter.mem_of_superset
    (Metric.ball_mem_nhds c hradius) ?_
  intro x hx
  rw [Metric.mem_ball] at hx
  rw [mem_standardTriangle]
  have hcoord (i : Fin 2) : |x i - c i| < 1 / 8 := by
    rw [← Real.dist_eq]
    exact (PiLp.dist_apply_le x c i).trans_lt hx
  have h0 := hcoord 0
  have h1 := hcoord 1
  change |x 0 - 1 / 4| < 1 / 8 at h0
  change |x 1 - 1 / 4| < 1 / 8 at h1
  rw [abs_lt] at h0 h1
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- Helper for Proposition 55.1: the standard triangle is closed. -/
private lemma standardTriangleClosed : IsClosed standardTriangle := by
  -- Express the triangle as an intersection of three closed half-spaces.
  have htriangle : standardTriangle =
      {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1} := by
    ext x
    exact mem_standardTriangle x
  rw [htriangle]
  have hc0 : Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) := by
    fun_prop
  have hc1 : Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1) := by
    fun_prop
  exact (isClosed_le continuous_const hc0).inter
    ((isClosed_le continuous_const hc1).inter
      (isClosed_le (hc0.add hc1) continuous_const))

/-- Helper for Proposition 55.1: the boundary of the standard triangle. -/
private abbrev standardTriangleBoundary : Set (EuclideanSpace ℝ (Fin 2)) :=
  frontier standardTriangle

/-- Helper for Proposition 55.1: the three affine barycentric-coordinate functions on
the ambient Euclidean plane. -/
private def standardTriangleAmbientBarycentricCoordinate
    (x : EuclideanSpace ℝ (Fin 2)) : Fin 3 → ℝ :=
  fun i ↦ if i = 0 then x 0 else if i = 1 then x 1 else 1 - x 0 - x 1

/-- Helper for Proposition 55.1: projection onto the first Euclidean coordinate. -/
private def standardTriangleFirstCoordinate :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0

/-- Helper for Proposition 55.1: projection onto the second Euclidean coordinate. -/
private def standardTriangleSecondCoordinate :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1

/-- Helper for Proposition 55.1: the sum of the two Euclidean coordinates. -/
private def standardTriangleCoordinateSum :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  standardTriangleFirstCoordinate + standardTriangleSecondCoordinate

/-- Helper for Proposition 55.1: the zeroth ambient barycentric coordinate is the
first coordinate projection. -/
private lemma standardTriangleAmbientBarycentricCoordinate_zero
    (x : EuclideanSpace ℝ (Fin 2)) :
    standardTriangleAmbientBarycentricCoordinate x 0 =
      standardTriangleFirstCoordinate x := by
  simp [standardTriangleAmbientBarycentricCoordinate, standardTriangleFirstCoordinate]

/-- Helper for Proposition 55.1: the first ambient barycentric coordinate is the
second coordinate projection. -/
private lemma standardTriangleAmbientBarycentricCoordinate_one
    (x : EuclideanSpace ℝ (Fin 2)) :
    standardTriangleAmbientBarycentricCoordinate x 1 =
      standardTriangleSecondCoordinate x := by
  simp [standardTriangleAmbientBarycentricCoordinate, standardTriangleSecondCoordinate]

/-- Helper for Proposition 55.1: the last ambient barycentric coordinate is one minus
the coordinate sum. -/
private lemma standardTriangleAmbientBarycentricCoordinate_two
    (x : EuclideanSpace ℝ (Fin 2)) :
    standardTriangleAmbientBarycentricCoordinate x 2 =
      1 - standardTriangleCoordinateSum x := by
  simp [standardTriangleAmbientBarycentricCoordinate, standardTriangleCoordinateSum,
    standardTriangleFirstCoordinate, standardTriangleSecondCoordinate]
  ring

/-- Helper for Proposition 55.1: the first-coordinate projection is surjective. -/
private lemma standardTriangleFirstCoordinate_surjective :
    Function.Surjective standardTriangleFirstCoordinate := by
  -- A constant coordinate vector maps to its common coordinate.
  intro y
  refine ⟨WithLp.toLp 2 (fun _ : Fin 2 ↦ y), ?_⟩
  rfl

/-- Helper for Proposition 55.1: the second-coordinate projection is surjective. -/
private lemma standardTriangleSecondCoordinate_surjective :
    Function.Surjective standardTriangleSecondCoordinate := by
  -- A constant coordinate vector maps to its common coordinate.
  intro y
  refine ⟨WithLp.toLp 2 (fun _ : Fin 2 ↦ y), ?_⟩
  rfl

/-- Helper for Proposition 55.1: the sum-of-coordinates functional is surjective. -/
private lemma standardTriangleCoordinateSum_surjective :
    Function.Surjective standardTriangleCoordinateSum := by
  -- The constant vector with both coordinates `y / 2` has coordinate sum `y`.
  intro y
  refine ⟨WithLp.toLp 2 (fun _ : Fin 2 ↦ y / 2), ?_⟩
  simp [standardTriangleCoordinateSum, standardTriangleFirstCoordinate,
    standardTriangleSecondCoordinate]

/-- Helper for Proposition 55.1: interior points of the standard triangle are exactly
the points satisfying all three defining inequalities strictly. -/
private lemma mem_interior_standardTriangle_iff
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ interior standardTriangle ↔ 0 < x 0 ∧ 0 < x 1 ∧ x 0 + x 1 < 1 := by
  -- Write the triangle as an intersection of inverse images of real half-lines.
  have hset : standardTriangle =
      standardTriangleFirstCoordinate ⁻¹' Ici 0 ∩
        (standardTriangleSecondCoordinate ⁻¹' Ici 0 ∩
          standardTriangleCoordinateSum ⁻¹' Iic 1) := by
    ext y
    rw [mem_standardTriangle]
    rfl
  rw [hset, interior_inter, interior_inter,
    standardTriangleFirstCoordinate.interior_preimage
      standardTriangleFirstCoordinate_surjective,
    standardTriangleSecondCoordinate.interior_preimage
      standardTriangleSecondCoordinate_surjective,
    standardTriangleCoordinateSum.interior_preimage
      standardTriangleCoordinateSum_surjective,
    interior_Ici, interior_Iic]
  rfl

/-- Helper for Proposition 55.1: the standard real-coordinate isometry preserves the
unit-sphere predicate when the Euclidean plane is identified with `ℂ`. -/
private lemma euclideanPlaneComplexHomeomorph_mem_sphere
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ Metric.sphere (0 : ℂ) 1 := by
  -- Both sphere predicates say that the norm of the same isometric vector is one.
  simp only [Metric.mem_sphere, dist_zero_right]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm ▸ Iff.rfl

/-- Helper for Proposition 55.1: the boundary of the standard triangle is homeomorphic
to the circle. -/
private lemma standardTriangleBoundaryHomeomorphicCircle :
    Nonempty (standardTriangleBoundary ≃ₜ Circle) := by
  -- Gauge rescaling carries the triangle frontier to the Euclidean unit sphere.
  obtain ⟨e, _, hclosure, hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      standardTriangleConvex standardTriangleInteriorNonempty standardTriangleBounded
  rw [standardTriangleClosed.closure_eq] at hclosure
  let planeToComplex : EuclideanSpace ℝ (Fin 2) ≃ₜ ℂ :=
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph
  let sphereToCircle :
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle :=
    planeToComplex.subtype euclideanPlaneComplexHomeomorph_mem_sphere
  -- Restrict the ambient homeomorphism and compose it with complex coordinates.
  exact ⟨((e.image standardTriangleBoundary).trans
    (Homeomorph.setCongr hfrontier)).trans sphereToCircle⟩

/-- Helper for Proposition 55.1: the identity of the standard triangle boundary is not
nullhomotopic. -/
private lemma standardTriangleBoundaryIdNotNullhomotopic :
    ¬ (ContinuousMap.id standardTriangleBoundary).Nullhomotopic := by
  -- A nullhomotopic identity would contract the boundary and hence contract the circle.
  intro hid
  obtain ⟨e⟩ := standardTriangleBoundaryHomeomorphicCircle
  letI : ContractibleSpace standardTriangleBoundary :=
    (contractible_iff_id_nullhomotopic standardTriangleBoundary).mpr hid
  letI : ContractibleSpace Circle := e.symm.contractibleSpace
  have hsub : Subsingleton (FundamentalGroup Circle 1) := inferInstance
  have hsubInt : Subsingleton (Multiplicative ℤ) :=
    Circle.fundamentalGroupEquivInt.toEquiv.subsingleton_congr.mp hsub
  exact not_subsingleton_iff_nontrivial.mpr inferInstance hsubInt

/-- Helper for Proposition 55.1: the three barycentric coordinates of a point in the
standard triangle. -/
private def standardTriangleBarycentricCoordinate
    (x : standardTriangle) : Fin 3 → ℝ :=
  standardTriangleAmbientBarycentricCoordinate x.1

/-- Helper for Proposition 55.1: every barycentric coordinate of a point in the
standard triangle is nonnegative. -/
private lemma standardTriangleBarycentricCoordinate_nonneg
    (x : standardTriangle) (i : Fin 3) :
    0 ≤ standardTriangleBarycentricCoordinate x i := by
  -- The three cases are exactly the three inequalities defining the triangle.
  have hx := (mem_standardTriangle x.1).mp x.2
  fin_cases i
  · exact hx.1
  · exact hx.2.1
  · have hthird : 0 ≤ 1 - x.1 0 - x.1 1 := by
      linarith [hx.2.2]
    simpa [standardTriangleBarycentricCoordinate,
      standardTriangleAmbientBarycentricCoordinate] using hthird

/-- Helper for Proposition 55.1: the barycentric coordinates of a point in the
standard triangle sum to one. -/
private lemma standardTriangleBarycentricCoordinate_sum
    (x : standardTriangle) :
    ∑ i, standardTriangleBarycentricCoordinate x i = 1 := by
  -- Expand the three coordinates; the two affine terms cancel.
  simp [standardTriangleBarycentricCoordinate,
    standardTriangleAmbientBarycentricCoordinate, Fin.sum_univ_three]

/-- Helper for Proposition 55.1: some barycentric coordinate is strictly positive. -/
private lemma standardTriangleBarycentricCoordinate_exists_pos
    (x : standardTriangle) :
    ∃ i, 0 < standardTriangleBarycentricCoordinate x i := by
  -- If all three coordinates vanished, their sum could not be one.
  by_contra hnone
  push Not at hnone
  have h0 := standardTriangleBarycentricCoordinate_nonneg x 0
  have h1 := standardTriangleBarycentricCoordinate_nonneg x 1
  have h2 := standardTriangleBarycentricCoordinate_nonneg x 2
  have hsum := standardTriangleBarycentricCoordinate_sum x
  rw [Fin.sum_univ_three] at hsum
  linarith [hnone 0, hnone 1, hnone 2]

/-- Helper for Proposition 55.1: the frontier of the closed triangle is contained in
the triangle. -/
private lemma standardTriangleBoundary_subset :
    standardTriangleBoundary ⊆ standardTriangle := by
  -- The frontier lies in the closure, which equals the triangle because it is closed.
  intro x hx
  rw [← standardTriangleClosed.closure_eq]
  exact frontier_subset_closure hx

/-- Helper for Proposition 55.1: a boundary point regarded as a point of the standard
triangle. -/
private def standardTriangleBoundaryInclusionValue
    (x : standardTriangleBoundary) : standardTriangle :=
  ⟨x.1, standardTriangleBoundary_subset x.2⟩

/-- Helper for Proposition 55.1: vanishing of a barycentric coordinate places a
triangle point on its frontier. -/
private lemma mem_standardTriangleBoundary_of_barycentricCoordinate_eq_zero
    (x : standardTriangle) (i : Fin 3)
    (hi : standardTriangleBarycentricCoordinate x i = 0) :
    x.1 ∈ standardTriangleBoundary := by
  -- An interior point satisfies all three barycentric inequalities strictly.
  rw [mem_frontier_iff_notMem_interior x.2]
  intro hxInterior
  rw [mem_interior_standardTriangle_iff] at hxInterior
  fin_cases i
  · have hi0 : x.1 0 = 0 := by
      simpa [standardTriangleBarycentricCoordinate,
        standardTriangleAmbientBarycentricCoordinate] using hi
    exact hxInterior.1.ne' hi0
  · have hi1 : x.1 1 = 0 := by
      simpa [standardTriangleBarycentricCoordinate,
        standardTriangleAmbientBarycentricCoordinate] using hi
    exact hxInterior.2.1.ne' hi1
  · have hthird : 0 < 1 - x.1 0 - x.1 1 := by
      linarith [hxInterior.2.2]
    have hi2 : 1 - x.1 0 - x.1 1 = 0 := by
      simpa [standardTriangleBarycentricCoordinate,
        standardTriangleAmbientBarycentricCoordinate] using hi
    exact hthird.ne' hi2

/-- Helper for Proposition 55.1: every point on the triangle frontier has a vanishing
barycentric coordinate. -/
private lemma standardTriangleBoundary_exists_barycentricCoordinate_eq_zero
    (x : standardTriangleBoundary) :
    ∃ i, standardTriangleBarycentricCoordinate
      (standardTriangleBoundaryInclusionValue x) i = 0 := by
  -- Otherwise all three nonnegative coordinates would be strict, making the point interior.
  by_contra hnone
  push Not at hnone
  have hnotInterior : x.1 ∉ interior standardTriangle :=
    (mem_frontier_iff_notMem_interior
      (standardTriangleBoundary_subset x.2)).mp x.2
  apply hnotInterior
  rw [mem_interior_standardTriangle_iff]
  have h0 := standardTriangleBarycentricCoordinate_nonneg
    (standardTriangleBoundaryInclusionValue x) 0
  have h1 := standardTriangleBarycentricCoordinate_nonneg
    (standardTriangleBoundaryInclusionValue x) 1
  have h2 := standardTriangleBarycentricCoordinate_nonneg
    (standardTriangleBoundaryInclusionValue x) 2
  have hp0 : 0 < x.1 0 := lt_of_le_of_ne h0 (Ne.symm (hnone 0))
  have hp1 : 0 < x.1 1 := lt_of_le_of_ne h1 (Ne.symm (hnone 1))
  have hp2 : 0 < 1 - x.1 0 - x.1 1 := by
    exact lt_of_le_of_ne h2 (Ne.symm (hnone 2))
  have hpsum : x.1 0 + x.1 1 < 1 := by
    linarith
  exact ⟨hp0, hp1, hpsum⟩

/-- Helper for Proposition 55.1: the open barycentric star associated to a vertex of
the standard triangle. -/
private def standardTriangleStar (i : Fin 3) : Set standardTriangle :=
  {x | 0 < standardTriangleBarycentricCoordinate x i}

/-- Helper for Proposition 55.1: every barycentric star is open. -/
private lemma standardTriangleStar_isOpen (i : Fin 3) :
    IsOpen (standardTriangleStar i) := by
  -- Each coordinate is an affine continuous real-valued function.
  have hcontinuous : Continuous
      (fun x : standardTriangle ↦ standardTriangleBarycentricCoordinate x i) := by
    by_cases hi0 : i = 0
    · subst i
      have hfirst : Continuous
          (fun x : standardTriangle ↦ standardTriangleFirstCoordinate x.1) := by
        fun_prop
      simpa only [standardTriangleBarycentricCoordinate,
        standardTriangleAmbientBarycentricCoordinate_zero] using hfirst
    by_cases hi1 : i = 1
    · subst i
      have hsecond : Continuous
          (fun x : standardTriangle ↦ standardTriangleSecondCoordinate x.1) := by
        fun_prop
      simpa only [standardTriangleBarycentricCoordinate,
        standardTriangleAmbientBarycentricCoordinate_one] using hsecond
    have hi2 : i = 2 := by
      omega
    subst i
    have hthird : Continuous
        (fun x : standardTriangle ↦ 1 - standardTriangleCoordinateSum x.1) := by
      fun_prop
    simpa only [standardTriangleBarycentricCoordinate,
      standardTriangleAmbientBarycentricCoordinate_two] using hthird
  exact isOpen_lt continuous_const hcontinuous

/-- Helper for Proposition 55.1: every member of the three-star family is open. -/
private lemma standardTriangleStars_isOpen :
    ∀ U ∈ Set.range standardTriangleStar, IsOpen U := by
  -- A range member inherits openness from its vertex index.
  intro U hU
  obtain ⟨i, rfl⟩ := hU
  exact standardTriangleStar_isOpen i

/-- Helper for Proposition 55.1: the three barycentric stars cover the standard
triangle. -/
private lemma standardTriangleStars_cover :
    ⋃₀ Set.range standardTriangleStar = Set.univ := by
  -- At each point, choose a strictly positive barycentric coordinate.
  apply eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := standardTriangleBarycentricCoordinate_exists_pos x
  exact mem_sUnion.mpr ⟨standardTriangleStar i, Set.mem_range_self i, hi⟩

/-- Helper for Proposition 55.1: an open set-indexed cover of a metric space admits a
subordinate partition of unity indexed by its members. -/
private lemma existsSubordinatePartitionOfUnityForSetCover
    {X : Type*} [TopologicalSpace X] [NormalSpace X] [ParacompactSpace X]
    (𝒰 : Set (Set X))
    (hopen : ∀ U ∈ 𝒰, IsOpen U) (hcover : ⋃₀ 𝒰 = Set.univ) :
    ∃ ρ : PartitionOfUnity {U : Set X // U ∈ 𝒰} X Set.univ,
      ρ.IsSubordinate fun U ↦ U.1 := by
  -- Use the standard partition theorem after expressing the `sUnion` cover as an indexed union.
  apply PartitionOfUnity.exists_isSubordinate isClosed_univ
  · intro U
    exact hopen U.1 U.2
  · intro x _
    have hx : x ∈ ⋃₀ 𝒰 := by
      rw [hcover]
      exact Set.mem_univ x
    obtain ⟨U, hU, hxU⟩ := mem_sUnion.mp hx
    exact mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩

/-- Helper for Proposition 55.1: a nonzero subordinate partition coefficient forces
membership in its associated cover member. -/
private lemma mem_openSetCover_of_partition_ne_zero
    {X ι : Type*} [TopologicalSpace X] {s : Set X}
    (ρ : PartitionOfUnity ι X s) (U : ι → Set X)
    (hρ : ρ.IsSubordinate U) {i : ι} {x : X} (hix : ρ i x ≠ 0) :
    x ∈ U i := by
  -- Support is contained in topological support, which subordination places in `U i`.
  exact hρ i (subset_tsupport (ρ i) hix)

/-- Helper for Proposition 55.1: the active support of a subordinate partition is no
larger than the point multiplicity of its set-indexed cover. -/
private lemma activePartitionSupport_card_le
    {X : Type*} [TopologicalSpace X] {𝒰 : Set (Set X)} {n : ℕ}
    (horder : 𝒰.HasOrderLE n)
    (ρ : PartitionOfUnity {U : Set X // U ∈ 𝒰} X Set.univ)
    (hρ : ρ.IsSubordinate fun U ↦ U.1) (x : X) :
    (ρ.finsupport x).card ≤ n := by
  classical
  -- Inject active subtype indices into the family of cover members containing `x`.
  let active : Set {U : Set X // U ∈ 𝒰} := ↑(ρ.finsupport x)
  have himage : (fun U : {U : Set X // U ∈ 𝒰} ↦ U.1) '' active ⊆
      {U ∈ 𝒰 | x ∈ U} := by
    rintro U ⟨V, hVactive, rfl⟩
    have hVne : ρ V x ≠ 0 := by
      simpa [active] using hVactive
    exact ⟨V.2, mem_openSetCover_of_partition_ne_zero ρ
      (fun W ↦ W.1) hρ hVne⟩
  have hactiveEncard : Set.encard active ≤ n := by
    calc
      Set.encard active = Set.encard
          ((fun U : {U : Set X // U ∈ 𝒰} ↦ U.1) '' active) :=
        (Subtype.val_injective.encard_image active).symm
      _ ≤ Set.encard {U ∈ 𝒰 | x ∈ U} := Set.encard_mono himage
      _ ≤ n := (Set.hasOrderLE_iff.mp horder) x
  have hactiveEq : active = (↑(ρ.finsupport x) :
      Set {U : Set X // U ∈ 𝒰}) := rfl
  rw [hactiveEq, Set.encard_coe_eq_coe_finsetCard] at hactiveEncard
  exact_mod_cast hactiveEncard

/-- Helper for Proposition 55.1: the vertex opposite the `i`-th barycentric face. -/
private def standardTriangleVertex (i : Fin 3) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![if i = 0 then 1 else 0, if i = 1 then 1 else 0]

/-- Helper for Proposition 55.1: every standard vertex belongs to the triangle. -/
private lemma standardTriangleVertex_mem (i : Fin 3) :
    standardTriangleVertex i ∈ standardTriangle := by
  -- Check the three possible vertices against the defining inequalities.
  fin_cases i
  · norm_num [standardTriangleVertex, mem_standardTriangle]
  · norm_num [standardTriangleVertex, mem_standardTriangle]
  · norm_num [standardTriangleVertex, mem_standardTriangle]

/-- Helper for Proposition 55.1: the barycentric coordinate of a standard vertex is
the corresponding Kronecker delta. -/
private lemma standardTriangleVertex_barycentricCoordinate
    (i j : Fin 3) :
    standardTriangleAmbientBarycentricCoordinate (standardTriangleVertex i) j =
      if i = j then 1 else 0 := by
  -- The nine coordinate values follow directly from the three explicit vertices.
  fin_cases i
  · fin_cases j
    · norm_num [standardTriangleAmbientBarycentricCoordinate, standardTriangleVertex]
    · norm_num [standardTriangleAmbientBarycentricCoordinate, standardTriangleVertex]
    · norm_num [standardTriangleAmbientBarycentricCoordinate, standardTriangleVertex]
  · fin_cases j
    · norm_num [standardTriangleAmbientBarycentricCoordinate, standardTriangleVertex]
    · norm_num [standardTriangleAmbientBarycentricCoordinate, standardTriangleVertex]
    · norm_num [standardTriangleAmbientBarycentricCoordinate, standardTriangleVertex]
  · fin_cases j
    · norm_num [standardTriangleAmbientBarycentricCoordinate, standardTriangleVertex]
    · norm_num [standardTriangleAmbientBarycentricCoordinate, standardTriangleVertex]
    · norm_num [standardTriangleAmbientBarycentricCoordinate, standardTriangleVertex]

/-- Helper for Proposition 55.1: the partition-weighted sum of a chosen family of
standard vertices. -/
private noncomputable def standardTrianglePartitionVertexMap
    {X ι : Type*} [TopologicalSpace X]
    (ρ : PartitionOfUnity ι X Set.univ) (label : ι → Fin 3)
    (x : X) : EuclideanSpace ℝ (Fin 2) :=
  ∑ᶠ i, ρ i x • standardTriangleVertex (label i)

/-- Helper for Proposition 55.1: the partition-weighted vertex map is continuous. -/
private lemma continuous_standardTrianglePartitionVertexMap
    {X ι : Type*} [TopologicalSpace X]
    (ρ : PartitionOfUnity ι X Set.univ) (label : ι → Fin 3) :
    Continuous (standardTrianglePartitionVertexMap ρ label) := by
  -- Local finiteness of the partition turns the pointwise vertex sum into a continuous map.
  apply ρ.continuous_finsum_smul
  intro i x _
  exact continuousAt_const

/-- Helper for Proposition 55.1: the partition-weighted vertex map takes values in the
standard triangle. -/
private lemma standardTrianglePartitionVertexMap_mem
    {X ι : Type*} [TopologicalSpace X]
    (ρ : PartitionOfUnity ι X Set.univ) (label : ι → Fin 3) (x : X) :
    standardTrianglePartitionVertexMap ρ label x ∈ standardTriangle := by
  -- Convexity contains every partition-weighted average of the three vertices.
  unfold standardTrianglePartitionVertexMap
  exact ρ.finsum_smul_mem_convex
    (g := fun i _ ↦ standardTriangleVertex (label i)) (Set.mem_univ x)
    (fun i _ ↦ standardTriangleVertex_mem (label i)) standardTriangleConvex

/-- Helper for Proposition 55.1: an affine barycentric coordinate commutes with a
finite weighted sum whose weights sum to one. -/
private lemma standardTriangleAmbientBarycentricCoordinate_finset_sum
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (z : ι → EuclideanSpace ℝ (Fin 2))
    (hsum : ∑ i ∈ s, w i = 1) (j : Fin 3) :
    standardTriangleAmbientBarycentricCoordinate
        (∑ i ∈ s, w i • z i) j =
      ∑ i ∈ s, w i * standardTriangleAmbientBarycentricCoordinate (z i) j := by
  -- The first two coordinates are linear; the third uses the unit total weight.
  by_cases hj0 : j = 0
  · subst j
    simp only [standardTriangleAmbientBarycentricCoordinate_zero, map_sum,
      map_smul, smul_eq_mul]
  by_cases hj1 : j = 1
  · subst j
    simp only [standardTriangleAmbientBarycentricCoordinate_one, map_sum,
      map_smul, smul_eq_mul]
  have hj2 : j = 2 := by
    omega
  subst j
  simp only [standardTriangleAmbientBarycentricCoordinate_two, map_sum,
    map_smul, smul_eq_mul]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, hsum]

/-- Helper for Proposition 55.1: at every point, an active support of size at most two
misses one of the three vertex labels. -/
private lemma exists_label_not_active
    {X ι : Type*} [TopologicalSpace X]
    (ρ : PartitionOfUnity ι X Set.univ) (label : ι → Fin 3)
    (hcard : ∀ x, (ρ.finsupport x).card ≤ 2) (x : X) :
    ∃ j : Fin 3, ∀ i ∈ ρ.finsupport x, label i ≠ j := by
  classical
  -- The image of at most two active indices cannot exhaust the three-element label type.
  let activeLabels := (ρ.finsupport x).image label
  have hlabelsCard : activeLabels.card ≤ 2 := by
    exact (Finset.card_image_le.trans (hcard x))
  have hproper : activeLabels.card < (Finset.univ : Finset (Fin 3)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hproper
  refine ⟨j, ?_⟩
  intro i hi hij
  apply hj
  exact Finset.mem_image.mpr ⟨i, hi, hij⟩

/-- Helper for Proposition 55.1: a vertex label absent from the active partition support
gives a zero barycentric coordinate of the weighted vertex map. -/
private lemma standardTrianglePartitionVertexMap_coordinate_eq_zero
    {X ι : Type*} [TopologicalSpace X]
    (ρ : PartitionOfUnity ι X Set.univ) (label : ι → Fin 3)
    (x : X) (j : Fin 3)
    (hmissing : ∀ i ∈ ρ.finsupport x, label i ≠ j) :
    standardTriangleAmbientBarycentricCoordinate
      (standardTrianglePartitionVertexMap ρ label x) j = 0 := by
  classical
  -- Replace the locally finite sum by its active finset and evaluate the affine coordinate.
  unfold standardTrianglePartitionVertexMap
  rw [← ρ.sum_finsupport_smul_eq_finsum
    (fun i _ ↦ standardTriangleVertex (label i))]
  rw [standardTriangleAmbientBarycentricCoordinate_finset_sum
    (ρ.finsupport x) (fun i ↦ ρ i x) (fun i ↦ standardTriangleVertex (label i))
    (ρ.sum_finsupport (Set.mem_univ x)) j]
  apply Finset.sum_eq_zero
  intro i hi
  rw [standardTriangleVertex_barycentricCoordinate, if_neg (hmissing i hi), mul_zero]

/-- Helper for Proposition 55.1: if at most two partition coefficients are active, the
weighted vertex map lands on the triangle boundary. -/
private lemma standardTrianglePartitionVertexMap_mem_boundary
    {X ι : Type*} [TopologicalSpace X]
    (ρ : PartitionOfUnity ι X Set.univ) (label : ι → Fin 3)
    (hcard : ∀ x, (ρ.finsupport x).card ≤ 2) (x : X) :
    standardTrianglePartitionVertexMap ρ label x ∈ standardTriangleBoundary := by
  -- Choose a missing label and invoke the zero-coordinate frontier criterion.
  obtain ⟨j, hj⟩ := exists_label_not_active ρ label hcard x
  let y : standardTriangle :=
    ⟨standardTrianglePartitionVertexMap ρ label x,
      standardTrianglePartitionVertexMap_mem ρ label x⟩
  apply mem_standardTriangleBoundary_of_barycentricCoordinate_eq_zero y j
  exact standardTrianglePartitionVertexMap_coordinate_eq_zero ρ label x j hj

/-- Helper for Proposition 55.1: subordination to labelled stars makes the weighted
vertex map preserve every vanishing barycentric coordinate. -/
private lemma standardTrianglePartitionVertexMap_preserves_zero
    {ι : Type*}
    (ρ : PartitionOfUnity ι standardTriangle Set.univ)
    (U : ι → Set standardTriangle) (label : ι → Fin 3)
    (hρ : ρ.IsSubordinate U)
    (hlabel : ∀ i, U i ⊆ standardTriangleStar (label i))
    (x : standardTriangle) (j : Fin 3)
    (hxj : standardTriangleBarycentricCoordinate x j = 0) :
    standardTriangleAmbientBarycentricCoordinate
      (standardTrianglePartitionVertexMap ρ label x) j = 0 := by
  -- An active coefficient comes from a star positive at `x`, so its label cannot be `j`.
  apply standardTrianglePartitionVertexMap_coordinate_eq_zero
  intro i hi hij
  have hine : ρ i x ≠ 0 := by
    simpa only [ρ.mem_finsupport, mem_support] using hi
  have hxStar : x ∈ standardTriangleStar (label i) :=
    hlabel i (mem_openSetCover_of_partition_ne_zero ρ U hρ hine)
  rw [standardTriangleStar, mem_setOf_eq, hij, hxj] at hxStar
  exact lt_irrefl 0 hxStar

/-- Helper for Proposition 55.1: the triangle-boundary inclusion is continuous. -/
private lemma continuous_standardTriangleBoundaryInclusionValue :
    Continuous standardTriangleBoundaryInclusionValue := by
  -- Both subtype layers retain the same ambient Euclidean point.
  exact continuous_subtype_val.subtype_mk _

/-- Helper for Proposition 55.1: the boundary included in the standard triangle as a
bundled continuous map. -/
private def standardTriangleBoundaryInclusion :
    C(standardTriangleBoundary, standardTriangle) :=
  ⟨standardTriangleBoundaryInclusionValue,
    continuous_standardTriangleBoundaryInclusionValue⟩

/-- Helper for Proposition 55.1: the boundary-valued weighted vertex map determined by
an order-two active-support bound. -/
private noncomputable def standardTriangleBoundaryPartitionMap
    {ι : Type*} (ρ : PartitionOfUnity ι standardTriangle Set.univ)
    (label : ι → Fin 3) (hcard : ∀ x, (ρ.finsupport x).card ≤ 2) :
    C(standardTriangle, standardTriangleBoundary) :=
  ⟨fun x ↦ ⟨standardTrianglePartitionVertexMap ρ label x,
      standardTrianglePartitionVertexMap_mem_boundary ρ label hcard x⟩,
    (continuous_standardTrianglePartitionVertexMap ρ label).subtype_mk _⟩

/-- Helper for Proposition 55.1: the boundary-valued partition map has the expected
ambient weighted-vertex value. -/
private lemma standardTriangleBoundaryPartitionMap_coe
    {ι : Type*} (ρ : PartitionOfUnity ι standardTriangle Set.univ)
    (label : ι → Fin 3) (hcard : ∀ x, (ρ.finsupport x).card ≤ 2)
    (x : standardTriangle) :
    (standardTriangleBoundaryPartitionMap ρ label hcard x).1 =
      standardTrianglePartitionVertexMap ρ label x := rfl

/-- Helper for Proposition 55.1: barycentric coordinates preserve affine combinations
whose coefficients sum to one. -/
private lemma standardTriangleAmbientBarycentricCoordinate_affineCombination
    (a b : ℝ) (hab : a + b = 1)
    (x y : EuclideanSpace ℝ (Fin 2)) (j : Fin 3) :
    standardTriangleAmbientBarycentricCoordinate (a • x + b • y) j =
      a * standardTriangleAmbientBarycentricCoordinate x j +
        b * standardTriangleAmbientBarycentricCoordinate y j := by
  -- The first two coordinates are linear and the third uses `a + b = 1`.
  by_cases hj0 : j = 0
  · subst j
    simp only [standardTriangleAmbientBarycentricCoordinate_zero, map_add,
      map_smul, smul_eq_mul]
  by_cases hj1 : j = 1
  · subst j
    simp only [standardTriangleAmbientBarycentricCoordinate_one, map_add,
      map_smul, smul_eq_mul]
  have hj2 : j = 2 := by
    omega
  subst j
  simp only [standardTriangleAmbientBarycentricCoordinate_two, map_add,
    map_smul, smul_eq_mul]
  linarith

/-- Helper for Proposition 55.1: the straight-line interpolation between a
boundary-preserving map and the boundary identity. -/
private def standardTriangleBoundaryStraightLineValue
    (k : C(standardTriangle, standardTriangleBoundary))
    (t : unitInterval) (x : standardTriangleBoundary) :
    EuclideanSpace ℝ (Fin 2) :=
  (1 - (t : ℝ)) • (k (standardTriangleBoundaryInclusion x)).1 +
    (t : ℝ) • x.1

/-- Helper for Proposition 55.1: a face-preserving boundary map has a straight-line
interpolation that remains on the triangle boundary. -/
private lemma standardTriangleBoundaryStraightLineValue_mem
    (k : C(standardTriangle, standardTriangleBoundary))
    (hface : ∀ x : standardTriangleBoundary, ∀ j : Fin 3,
      standardTriangleBarycentricCoordinate
        (standardTriangleBoundaryInclusionValue x) j = 0 →
      standardTriangleAmbientBarycentricCoordinate
        (k (standardTriangleBoundaryInclusion x)).1 j = 0)
    (t : unitInterval) (x : standardTriangleBoundary) :
    standardTriangleBoundaryStraightLineValue k t x ∈ standardTriangleBoundary := by
  -- Both endpoints lie in the triangle, so convexity contains the interpolating segment.
  have hcoeff : (1 - (t : ℝ)) + (t : ℝ) = 1 := by
    ring
  have hmapTriangle :
      (k (standardTriangleBoundaryInclusion x)).1 ∈ standardTriangle :=
    standardTriangleBoundary_subset (k (standardTriangleBoundaryInclusion x)).2
  have hvalueTriangle :
      standardTriangleBoundaryStraightLineValue k t x ∈ standardTriangle := by
    exact standardTriangleConvex hmapTriangle
      (standardTriangleBoundary_subset x.2)
      (sub_nonneg.mpr t.2.2) t.2.1 hcoeff
  -- A zero coordinate of `x` is also zero at the mapped endpoint and along the segment.
  obtain ⟨j, hxj⟩ :=
    standardTriangleBoundary_exists_barycentricCoordinate_eq_zero x
  have hmapj := hface x j hxj
  let y : standardTriangle :=
    ⟨standardTriangleBoundaryStraightLineValue k t x, hvalueTriangle⟩
  apply mem_standardTriangleBoundary_of_barycentricCoordinate_eq_zero y j
  dsimp only [y, standardTriangleBarycentricCoordinate]
  unfold standardTriangleBoundaryStraightLineValue
  rw [standardTriangleAmbientBarycentricCoordinate_affineCombination
    (1 - (t : ℝ)) (t : ℝ) hcoeff]
  rw [hmapj]
  change standardTriangleAmbientBarycentricCoordinate x.1 j = 0 at hxj
  rw [hxj]
  ring

/-- Helper for Proposition 55.1: the boundary straight-line interpolation is continuous. -/
private lemma continuous_standardTriangleBoundaryStraightLineValue
    (k : C(standardTriangle, standardTriangleBoundary))
    (hface : ∀ x : standardTriangleBoundary, ∀ j : Fin 3,
      standardTriangleBarycentricCoordinate
        (standardTriangleBoundaryInclusionValue x) j = 0 →
      standardTriangleAmbientBarycentricCoordinate
        (k (standardTriangleBoundaryInclusion x)).1 j = 0) :
    Continuous (fun p : unitInterval × standardTriangleBoundary ↦
      (⟨standardTriangleBoundaryStraightLineValue k p.1 p.2,
        standardTriangleBoundaryStraightLineValue_mem k hface p.1 p.2⟩ :
          standardTriangleBoundary)) := by
  -- Continuity follows in the ambient vector space and then through the subtype.
  apply Continuous.subtype_mk
  unfold standardTriangleBoundaryStraightLineValue
  fun_prop

/-- Helper for Proposition 55.1: the boundary interpolation starts at the given map. -/
private lemma standardTriangleBoundaryStraightLineValue_zero
    (k : C(standardTriangle, standardTriangleBoundary))
    (hface : ∀ x : standardTriangleBoundary, ∀ j : Fin 3,
      standardTriangleBarycentricCoordinate
        (standardTriangleBoundaryInclusionValue x) j = 0 →
      standardTriangleAmbientBarycentricCoordinate
        (k (standardTriangleBoundaryInclusion x)).1 j = 0)
    (x : standardTriangleBoundary) :
    (⟨standardTriangleBoundaryStraightLineValue k 0 x,
      standardTriangleBoundaryStraightLineValue_mem k hface 0 x⟩ :
        standardTriangleBoundary) =
      k (standardTriangleBoundaryInclusion x) := by
  -- At time zero only the mapped endpoint remains.
  apply Subtype.ext
  simp [standardTriangleBoundaryStraightLineValue]

/-- Helper for Proposition 55.1: the boundary interpolation ends at the identity. -/
private lemma standardTriangleBoundaryStraightLineValue_one
    (k : C(standardTriangle, standardTriangleBoundary))
    (hface : ∀ x : standardTriangleBoundary, ∀ j : Fin 3,
      standardTriangleBarycentricCoordinate
        (standardTriangleBoundaryInclusionValue x) j = 0 →
      standardTriangleAmbientBarycentricCoordinate
        (k (standardTriangleBoundaryInclusion x)).1 j = 0)
    (x : standardTriangleBoundary) :
    (⟨standardTriangleBoundaryStraightLineValue k 1 x,
      standardTriangleBoundaryStraightLineValue_mem k hface 1 x⟩ :
        standardTriangleBoundary) = x := by
  -- At time one only the original boundary point remains.
  apply Subtype.ext
  simp [standardTriangleBoundaryStraightLineValue]

/-- Helper for Proposition 55.1: a face-preserving boundary map is homotopic to the
boundary identity. -/
private lemma standardTriangleBoundaryMap_homotopic_id
    (k : C(standardTriangle, standardTriangleBoundary))
    (hface : ∀ x : standardTriangleBoundary, ∀ j : Fin 3,
      standardTriangleBarycentricCoordinate
        (standardTriangleBoundaryInclusionValue x) j = 0 →
      standardTriangleAmbientBarycentricCoordinate
        (k (standardTriangleBoundaryInclusion x)).1 j = 0) :
    (k.comp standardTriangleBoundaryInclusion).Homotopic
      (ContinuousMap.id standardTriangleBoundary) := by
  -- Assemble the homotopy from the continuity, boundary-membership, and endpoint interface.
  exact ⟨{
    toFun := fun p ↦
      ⟨standardTriangleBoundaryStraightLineValue k p.1 p.2,
        standardTriangleBoundaryStraightLineValue_mem k hface p.1 p.2⟩
    continuous_toFun := continuous_standardTriangleBoundaryStraightLineValue k hface
    map_zero_left := standardTriangleBoundaryStraightLineValue_zero k hface
    map_one_left := standardTriangleBoundaryStraightLineValue_one k hface
  }⟩

/-- Helper for Proposition 55.1: an order-two open refinement of the three
barycentric stars would contradict the boundary-circle obstruction. -/
private lemma orderTwoStarRefinementImpossible
    (ℬ : Set (Set standardTriangle))
    (hrefines : IsOpenRefinement ℬ (Set.range standardTriangleStar))
    (hcovers : ⋃₀ ℬ = Set.univ) (horder : ℬ.HasOrderLE 2) : False := by
  classical
  -- Label every refinement member by a barycentric star containing it.
  have hlabelExists (B : {U : Set standardTriangle // U ∈ ℬ}) :
      ∃ i : Fin 3, B.1 ⊆ standardTriangleStar i := by
    obtain ⟨U, hU, hBU⟩ := hrefines.subset_of_mem B.2
    obtain ⟨i, rfl⟩ := hU
    exact ⟨i, hBU⟩
  choose label hlabel using hlabelExists
  have hopen : ∀ U ∈ ℬ, IsOpen U := by
    intro U hU
    exact hrefines.isOpen_of_mem hU
  letI : CompactSpace standardTriangle := isCompact_iff_compactSpace.mp
    (Metric.isCompact_of_isClosed_isBounded
      standardTriangleClosed standardTriangleBounded)
  obtain ⟨ρ, hρ⟩ :=
    existsSubordinatePartitionOfUnityForSetCover ℬ hopen hcovers
  -- The order bound controls the active partition support pointwise.
  have hcard : ∀ x, (ρ.finsupport x).card ≤ 2 := by
    intro x
    exact activePartitionSupport_card_le horder ρ hρ x
  let k : C(standardTriangle, standardTriangleBoundary) :=
    standardTriangleBoundaryPartitionMap ρ label hcard
  -- Subordination to stars makes `k` preserve each face of the triangle.
  have hface : ∀ x : standardTriangleBoundary, ∀ j : Fin 3,
      standardTriangleBarycentricCoordinate
        (standardTriangleBoundaryInclusionValue x) j = 0 →
      standardTriangleAmbientBarycentricCoordinate
        (k (standardTriangleBoundaryInclusion x)).1 j = 0 := by
    intro x j hxj
    have hkcoe : (k (standardTriangleBoundaryInclusion x)).1 =
        standardTrianglePartitionVertexMap ρ label
          (standardTriangleBoundaryInclusion x) :=
      standardTriangleBoundaryPartitionMap_coe ρ label hcard
        (standardTriangleBoundaryInclusion x)
    rw [hkcoe]
    exact standardTrianglePartitionVertexMap_preserves_zero ρ
      (fun U ↦ U.1) label hρ hlabel
      (standardTriangleBoundaryInclusion x) j hxj
  have hhomotopy := standardTriangleBoundaryMap_homotopic_id k hface
  -- Since `k` extends over the contractible triangle, its boundary restriction is nullhomotopic.
  have htriangleNonempty : (standardTriangle : Set _).Nonempty :=
    ⟨standardTriangleVertex 2, standardTriangleVertex_mem 2⟩
  letI : ContractibleSpace standardTriangle :=
    standardTriangleConvex.contractibleSpace htriangleNonempty
  have hrestrictionNull :
      (k.comp standardTriangleBoundaryInclusion).Nullhomotopic :=
    (id_nullhomotopic standardTriangle).comp_right k |>.comp_left
      standardTriangleBoundaryInclusion
  obtain ⟨b, hconstant⟩ := hrestrictionNull
  have hidNull : (ContinuousMap.id standardTriangleBoundary).Nullhomotopic :=
    ⟨b, hhomotopy.symm.trans hconstant⟩
  exact standardTriangleBoundaryIdNotNullhomotopic hidNull

/-- Helper for Proposition 55.1: the standard triangle does not have covering dimension
at most one. -/
private lemma standardTriangleNotHasCoveringDimensionLEOne :
    ¬ HasCoveringDimensionLE standardTriangle 1 := by
  -- Apply the hypothetical bound to the explicit three-star open cover.
  intro hdim
  obtain ⟨ℬ, hrefines, hcovers, horder⟩ :=
    hdim (Set.range standardTriangleStar)
      standardTriangleStars_isOpen
      standardTriangleStars_cover
  exact orderTwoStarRefinementImpossible ℬ hrefines hcovers horder

/-- Proposition 55.1: The standard closed triangle in `ℝ²` has covering dimension at least two. -/
theorem standardTriangle_two_le_coveringDimension :
    (2 : ℕ∞) ≤ dim standardTriangle := by
  -- A failure of the lower bound would give the excluded dimension-one bound.
  by_contra htwo
  have hdim_lt_two : dim standardTriangle < (2 : ℕ) := by
    exact lt_of_not_ge htwo
  have hdim_le_one : dim standardTriangle ≤ (1 : WithBot ℕ∞) := by
    exact ENat.WithBot.lt_add_one_iff.mp hdim_lt_two
  exact standardTriangleNotHasCoveringDimensionLEOne
    ((coveringDimension_le_iff standardTriangle 1).mp hdim_le_one)

end
