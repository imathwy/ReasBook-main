module

public import Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
public import Topology_Munkres_2000.Book.Definition_78_3.Boundary

public section

open Set

namespace Complex

/-- Helper for Exercise 78.3: the complex closed unit disk used for the Cayley chart. -/
abbrev UnitClosedDisk := Metric.closedBall (0 : ℂ) 1

/-- Helper for Exercise 78.3: the complex closed right half-plane. -/
abbrev ClosedRightHalfPlane := {w : ℂ // 0 ≤ w.re}

/-- Helper for Exercise 78.3: the point `1` belongs to the complex closed unit disk. -/
lemma one_mem_unitClosedDisk : (1 : ℂ) ∈ Metric.closedBall 0 1 := by
  -- The distinguished omitted point has norm exactly one.
  simp [Metric.mem_closedBall]

/-- Helper for Exercise 78.3: the distinguished pole in the complex closed unit disk. -/
def unitClosedDiskOne : UnitClosedDisk :=
  ⟨1, one_mem_unitClosedDisk⟩

/-- Helper for Exercise 78.3: membership away from the disk pole gives a nonzero Cayley
denominator. -/
lemma one_sub_ne_zero_of_mem_pole_compl (z : UnitClosedDisk)
    (hz : z ∈ ({unitClosedDiskOne}ᶜ : Set UnitClosedDisk)) : (1 : ℂ) - z ≠ 0 := by
  -- Equality of the denominator to zero would identify the subtype point with the pole.
  intro h
  have hzval : (z : ℂ) = 1 := by
    linear_combination -h
  exact hz (Subtype.ext hzval)

/-- Helper for Exercise 78.3: points of the complex closed disk have norm-square at most one. -/
lemma normSq_le_one_of_mem_unitClosedDisk (z : UnitClosedDisk) : normSq z ≤ 1 := by
  -- Square the defining norm inequality and rewrite it as `normSq`.
  have hz : ‖(z : ℂ)‖ ≤ 1 := by
    have hzdist : dist (z : ℂ) 0 ≤ 1 := z.property
    simpa only [dist_zero_right] using hzdist
  rw [normSq_eq_norm_sq]
  nlinarith [sq_le_sq₀ (norm_nonneg (z : ℂ)) zero_le_one |>.mpr hz]

/-- Helper for Exercise 78.3: away from the pole, the real part of the Cayley transform is
the normalized deficit of the norm-square. -/
lemma cayley_re_eq (z : ℂ) (hz : (1 : ℂ) - z ≠ 0) :
    ((1 + z) / (1 - z)).re = (1 - normSq z) / normSq (1 - z) := by
  -- Expand real parts and clear the nonzero norm-square denominator.
  have hnorm : normSq (1 - z) ≠ 0 := (normSq_pos.mpr hz).ne'
  rw [div_re]
  field_simp [hnorm]
  norm_num [normSq_apply]
  ring

/-- Helper for Exercise 78.3: the Cayley transform of a disk point lies in the closed right
half-plane. -/
lemma cayley_re_nonneg (z : UnitClosedDisk) :
    0 ≤ ((1 + (z : ℂ)) / (1 - z)).re := by
  -- At the pole division is zero; elsewhere use the norm-square formula.
  by_cases hz : (z : ℂ) = 1
  · simp [hz]
  · have hden : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    rw [cayley_re_eq z hden]
    exact div_nonneg (sub_nonneg.mpr (normSq_le_one_of_mem_unitClosedDisk z))
      (normSq_nonneg _)

/-- Helper for Exercise 78.3: a point in the closed right half-plane cannot equal `-1`. -/
lemma add_one_ne_zero_of_re_nonneg (w : ClosedRightHalfPlane) : (w : ℂ) + 1 ≠ 0 := by
  -- The real part of `-1` contradicts the half-plane inequality.
  intro h
  have hw : (w : ℂ) = -1 := by
    linear_combination h
  have := w.property
  norm_num [hw] at this

/-- Helper for Exercise 78.3: the inverse Cayley transform of a right-half-plane point has
norm at most one. -/
lemma inverseCayley_norm_le_one (w : ClosedRightHalfPlane) :
    ‖((w : ℂ) - 1) / ((w : ℂ) + 1)‖ ≤ 1 := by
  -- Compare the two norm-squares; their difference is four times the real part.
  have hden : 0 < normSq ((w : ℂ) + 1) :=
    normSq_pos.mpr (add_one_ne_zero_of_re_nonneg w)
  have hsq : normSq ((w : ℂ) - 1) ≤ normSq ((w : ℂ) + 1) := by
    rw [normSq_apply, normSq_apply]
    norm_num at ⊢
    nlinarith [w.property]
  apply (sq_le_sq₀ (norm_nonneg (((w : ℂ) - 1) / ((w : ℂ) + 1))) zero_le_one).mp
  rw [Complex.sq_norm, one_pow, normSq_div]
  exact (div_le_one hden).mpr hsq

/-- Helper for Exercise 78.3: the inverse Cayley transform never equals the omitted disk pole. -/
lemma inverseCayley_ne_one (w : ClosedRightHalfPlane) :
    ((w : ℂ) - 1) / ((w : ℂ) + 1) ≠ 1 := by
  -- Clearing the nonzero denominator would otherwise force `-1 = 1`.
  have hden := add_one_ne_zero_of_re_nonneg w
  intro h
  field_simp [hden] at h
  have hre := congrArg re h
  norm_num at hre
  nlinarith

/-- Helper for Exercise 78.3: inverse Cayley followed by Cayley fixes every point away from the
disk pole. -/
lemma inverseCayley_cayley (z : ℂ) (hz : (1 : ℂ) - z ≠ 0) :
    (((1 + z) / (1 - z)) - 1) / (((1 + z) / (1 - z)) + 1) = z := by
  -- Clear the Cayley denominator and normalize the resulting field identity.
  field_simp [hz]
  ring

/-- Helper for Exercise 78.3: Cayley followed by inverse Cayley fixes the closed right
half-plane. -/
lemma cayley_inverseCayley (w : ClosedRightHalfPlane) :
    (1 + (((w : ℂ) - 1) / ((w : ℂ) + 1))) /
      (1 - (((w : ℂ) - 1) / ((w : ℂ) + 1))) = w := by
  -- The half-plane condition supplies the only nonzero denominator needed by the identity.
  have hden := add_one_ne_zero_of_re_nonneg w
  field_simp [hden]
  ring

/-- Helper for Exercise 78.3: the Cayley transform as a map into the closed right half-plane. -/
noncomputable def unitClosedDiskCayleyToFun (z : UnitClosedDisk) : ClosedRightHalfPlane :=
  ⟨(1 + (z : ℂ)) / (1 - z), cayley_re_nonneg z⟩

/-- Helper for Exercise 78.3: the inverse Cayley transform as a map into the closed unit disk. -/
lemma inverseCayley_mem_unitClosedDisk (w : ClosedRightHalfPlane) :
    ((w : ℂ) - 1) / ((w : ℂ) + 1) ∈ Metric.closedBall (0 : ℂ) 1 := by
  -- Rewrite closed-ball membership as the norm bound already established above.
  rw [Metric.mem_closedBall, dist_zero_right]
  exact inverseCayley_norm_le_one w

/-- Helper for Exercise 78.3: the inverse Cayley transform as a map into the closed unit disk. -/
noncomputable def unitClosedDiskCayleyInvFun (w : ClosedRightHalfPlane) : UnitClosedDisk :=
  ⟨((w : ℂ) - 1) / ((w : ℂ) + 1), inverseCayley_mem_unitClosedDisk w⟩

/-- Helper for Exercise 78.3: the Cayley map sends its source into its full target. -/
lemma unitClosedDiskCayley_map_source (z : UnitClosedDisk)
    (_hz : z ∈ ({unitClosedDiskOne}ᶜ : Set UnitClosedDisk)) :
    unitClosedDiskCayleyToFun z ∈ (Set.univ : Set ClosedRightHalfPlane) := by
  -- The target of the partial homeomorphism is the full half-plane.
  exact Set.mem_univ _

/-- Helper for Exercise 78.3: the inverse Cayley map lands away from the disk pole. -/
lemma unitClosedDiskCayley_map_target (w : ClosedRightHalfPlane)
    (_hw : w ∈ (Set.univ : Set ClosedRightHalfPlane)) :
    unitClosedDiskCayleyInvFun w ∈ ({unitClosedDiskOne}ᶜ : Set UnitClosedDisk) := by
  -- Subtype equality with the pole would contradict the explicit inverse formula.
  intro h
  exact inverseCayley_ne_one w (congrArg Subtype.val h)

/-- Helper for Exercise 78.3: the inverse Cayley map is a left inverse on the chart source. -/
lemma unitClosedDiskCayley_left_inv (z : UnitClosedDisk)
    (hz : z ∈ ({unitClosedDiskOne}ᶜ : Set UnitClosedDisk)) :
    unitClosedDiskCayleyInvFun (unitClosedDiskCayleyToFun z) = z := by
  -- Reduce subtype equality to the algebraic Cayley inverse identity.
  apply Subtype.ext
  exact inverseCayley_cayley z (one_sub_ne_zero_of_mem_pole_compl z hz)

/-- Helper for Exercise 78.3: the inverse Cayley map is a right inverse on the full target. -/
lemma unitClosedDiskCayley_right_inv (w : ClosedRightHalfPlane)
    (_hw : w ∈ (Set.univ : Set ClosedRightHalfPlane)) :
    unitClosedDiskCayleyToFun (unitClosedDiskCayleyInvFun w) = w := by
  -- Reduce subtype equality to the algebraic Cayley inverse identity.
  apply Subtype.ext
  exact cayley_inverseCayley w

/-- Helper for Exercise 78.3: the Cayley map is continuous on the disk with its pole removed. -/
lemma continuousOn_unitClosedDiskCayleyToFun :
    ContinuousOn unitClosedDiskCayleyToFun
      ({unitClosedDiskOne}ᶜ : Set UnitClosedDisk) := by
  -- Continuity of division holds because the source excludes the zero denominator.
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  exact (continuous_const.add continuous_subtype_val).continuousOn.div
    (continuous_const.sub continuous_subtype_val).continuousOn
    (fun z hz ↦ one_sub_ne_zero_of_mem_pole_compl z hz)

/-- Helper for Exercise 78.3: the inverse Cayley map is continuous on the closed right
half-plane. -/
lemma continuousOn_unitClosedDiskCayleyInvFun :
    ContinuousOn unitClosedDiskCayleyInvFun (Set.univ : Set ClosedRightHalfPlane) := by
  -- The half-plane inequality keeps the inverse denominator nonzero everywhere.
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  exact (continuous_subtype_val.sub continuous_const).continuousOn.div
    (continuous_subtype_val.add continuous_const).continuousOn
    (fun w _hw ↦ add_one_ne_zero_of_re_nonneg w)

/-- Helper for Exercise 78.3: the Cayley source is open in the complex closed unit disk. -/
lemma isOpen_unitClosedDisk_pole_compl :
    IsOpen ({unitClosedDiskOne}ᶜ : Set UnitClosedDisk) := by
  -- A singleton is closed in the metric disk, so its complement is open.
  exact isOpen_compl_singleton

/-- Helper for Exercise 78.3: the Cayley partial homeomorphism from the punctured closed disk to
the closed right half-plane. -/
noncomputable def unitClosedBallCayleyChart :
    OpenPartialHomeomorph UnitClosedDisk ClosedRightHalfPlane :=
  { toFun := unitClosedDiskCayleyToFun
    invFun := unitClosedDiskCayleyInvFun
    source := {unitClosedDiskOne}ᶜ
    target := Set.univ
    map_source' := unitClosedDiskCayley_map_source
    map_target' := unitClosedDiskCayley_map_target
    left_inv' := unitClosedDiskCayley_left_inv
    right_inv' := unitClosedDiskCayley_right_inv
    continuousOn_toFun := continuousOn_unitClosedDiskCayleyToFun
    continuousOn_invFun := continuousOn_unitClosedDiskCayleyInvFun
    open_source := isOpen_unitClosedDisk_pole_compl
    open_target := isOpen_univ }

end Complex

namespace ClosedUnitDisk

/-- Helper for Exercise 78.3: the orthonormal identification of the Euclidean plane with `ℂ`
preserves the closed unit ball. -/
lemma planeComplex_mem_unitClosedDisk_iff (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ Metric.closedBall (0 : ℂ) 1 := by
  -- The basis equivalence is an isometry and sends zero to zero.
  simp only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]

/-- Helper for Exercise 78.3: the closed Euclidean unit disk is homeomorphic to the complex
closed unit disk. -/
noncomputable def planeComplexHomeomorph : B² ≃ₜ Complex.UnitClosedDisk :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    planeComplex_mem_unitClosedDisk_iff

/-- Helper for Exercise 78.3: complex coordinates identify the closed right half-plane with
`EuclideanHalfSpace 2`. -/
lemma complexRightHalfPlane_mem_halfSpace_iff (w : ℂ) :
    0 ≤ w.re ↔ 0 ≤ Complex.orthonormalBasisOneI.repr w 0 := by
  -- The zeroth coordinate of the standard real basis representation is the real part.
  simp

/-- Helper for Exercise 78.3: the complex closed right half-plane is homeomorphic to the
Euclidean half-space model. -/
noncomputable def complexRightHalfPlaneHomeomorph :
    Complex.ClosedRightHalfPlane ≃ₜ EuclideanHalfSpace 2 :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype
    complexRightHalfPlane_mem_halfSpace_iff

/-- Helper for Exercise 78.3: the boundary pole omitted by the first Cayley chart. -/
noncomputable def cayleyPole : B² :=
  planeComplexHomeomorph.symm Complex.unitClosedDiskOne

/-- Helper for Exercise 78.3: the Cayley chart on the Euclidean closed disk, transported to the
standard half-space model. -/
noncomputable def cayleyChart : OpenPartialHomeomorph B² (EuclideanHalfSpace 2) :=
  (planeComplexHomeomorph.transOpenPartialHomeomorph
    Complex.unitClosedBallCayleyChart).transHomeomorph
      complexRightHalfPlaneHomeomorph

/-- Helper for Exercise 78.3: the Cayley chart is defined precisely off its boundary pole. -/
lemma cayleyChart_source : cayleyChart.source = ({cayleyPole}ᶜ : Set B²) := by
  -- Pull the punctured complex-disk source back through the coordinate homeomorphism.
  ext x
  simp only [mem_compl_iff, mem_singleton_iff]
  exact not_congr planeComplexHomeomorph.toEquiv.apply_eq_iff_eq_symm_apply

/-- Helper for Exercise 78.3: negation preserves the Euclidean closed unit disk. -/
lemma neg_mem_closedUnitDisk_iff (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      -x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  -- Both points have the same distance from the origin.
  simp [Metric.mem_closedBall]

/-- Helper for Exercise 78.3: the antipodal homeomorphism of the closed unit disk. -/
noncomputable def negHomeomorph : B² ≃ₜ B² :=
  (Homeomorph.neg (EuclideanSpace ℝ (Fin 2))).subtype neg_mem_closedUnitDisk_iff

/-- Helper for Exercise 78.3: the Cayley chart based at the antipodal pole. -/
noncomputable def oppositeCayleyChart : OpenPartialHomeomorph B² (EuclideanHalfSpace 2) :=
  negHomeomorph.transOpenPartialHomeomorph cayleyChart

/-- Helper for Exercise 78.3: the antipodal chart is defined off the pole opposite to the first
Cayley pole. -/
lemma oppositeCayleyChart_source :
    oppositeCayleyChart.source = ({negHomeomorph.symm cayleyPole}ᶜ : Set B²) := by
  -- Pull the first chart source back through the antipodal homeomorphism.
  unfold oppositeCayleyChart
  rw [Homeomorph.transOpenPartialHomeomorph_source, cayleyChart_source]
  ext x
  simp only [mem_compl_iff, mem_singleton_iff]
  exact not_congr negHomeomorph.toEquiv.apply_eq_iff_eq_symm_apply

/-- Helper for Exercise 78.3: the two Cayley poles are distinct. -/
lemma cayleyPole_ne_antipode : cayleyPole ≠ negHomeomorph.symm cayleyPole := by
  -- In complex coordinates the two poles are `1` and `-1`.
  intro h
  have hcoord := congrArg (fun x : B² ↦
    ((planeComplexHomeomorph x : Complex.UnitClosedDisk) : ℂ)) h
  norm_num [cayleyPole, planeComplexHomeomorph, negHomeomorph,
    Complex.unitClosedDiskOne] at hcoord

/-- Helper for Exercise 78.3: the two-element Cayley atlas on the closed disk. -/
def cayleyAtlas : Set (OpenPartialHomeomorph B² (EuclideanHalfSpace 2)) :=
  {cayleyChart, oppositeCayleyChart}

/-- Helper for Exercise 78.3: select the antipodal chart only at the pole omitted by the first
chart. -/
noncomputable def cayleyChartAt (x : B²) :
    OpenPartialHomeomorph B² (EuclideanHalfSpace 2) :=
  @ite _ (x = cayleyPole) (Classical.decEq B² x cayleyPole) oppositeCayleyChart cayleyChart

/-- Helper for Exercise 78.3: the selected Cayley chart belongs to the atlas and contains its
base point. -/
lemma cayleyChartAt_spec (x : B²) :
    x ∈ (cayleyChartAt x).source ∧ cayleyChartAt x ∈ cayleyAtlas := by
  -- Away from the first pole use its chart; at the pole use the antipodal chart.
  classical
  by_cases hx : x = cayleyPole
  · subst x
    simp only [cayleyChartAt, if_pos]
    constructor
    · rw [oppositeCayleyChart_source]
      exact cayleyPole_ne_antipode
    · exact Set.mem_insert_of_mem cayleyChart (Set.mem_singleton oppositeCayleyChart)
  · simp only [cayleyChartAt, if_neg hx]
    constructor
    · rw [cayleyChart_source]
      exact hx
    · exact Set.mem_insert cayleyChart {oppositeCayleyChart}

/-- Helper for Exercise 78.3: the half-space charted-space structure defined by the two Cayley
charts. -/
@[implicit_reducible]
noncomputable def halfSpaceChartedSpace : ChartedSpace (EuclideanHalfSpace 2) B² :=
  { atlas := cayleyAtlas
    chartAt := cayleyChartAt
    mem_chart_source := fun x ↦ (cayleyChartAt_spec x).1
    chart_mem_atlas := fun x ↦ (cayleyChartAt_spec x).2 }

end ClosedUnitDisk

/-- Exercise 78.3. The closed unit ball in `ℝ²` admits a half-space atlas making it a
topological `2`-manifold with boundary. -/
theorem closedUnitBall_isTwoManifoldWithBoundary :
    ∃ c : ChartedSpace (EuclideanHalfSpace 2) B²,
      Surface.IsManifoldWithBoundary c := by
  -- Install the explicit Cayley atlas so the order-zero manifold instance can use it.
  letI : ChartedSpace (EuclideanHalfSpace 2) B² :=
    ClosedUnitDisk.halfSpaceChartedSpace
  refine ⟨ClosedUnitDisk.halfSpaceChartedSpace, ?_⟩
  -- The metric subtype supplies separation/countability, and every charted space is `C⁰`.
  rw [Surface.isManifoldWithBoundary_iff]
  exact ⟨inferInstance, inferInstance, inferInstance⟩
