module

public import Topology_Munkres_2000.Book.Definition_74_6.Presentation
public import Topology_Munkres_2000.Book.Exercise_74_3.Quotient
public import Topology_Munkres_2000.Book.Example_22_5.Torus
public import Topology_Munkres_2000.Book.Proposition_74_1
public import Topology_Munkres_2000.Book.Exercise_74_4.CrosscapPL
public import Topology_Munkres_2000.Book.Exercise_74_4.FanPL
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public meta import Mathlib.Data.Fintype.Basic
public meta import Mathlib.Data.Fintype.Prod
public meta import Mathlib.Data.Fin.VecNotation

import all Topology_Munkres_2000.Book.Definition_74_6.Presentation
import all Topology_Munkres_2000.Book.Definition_74_1.CyclicPolygon
import all Topology_Munkres_2000.Book.Definition_74_3
import all Topology_Munkres_2000.Book.Exercise_74_3.Quotient
import all Topology_Munkres_2000.Book.Example_22_5.Torus

public section

open scoped Topology

namespace NonorientableSurfacePresentation

/-- The standard two-fold projective plane. -/
abbrev twoFoldProjectivePlane := mFoldProjectivePlane 2 Nat.one_lt_two

/-- The standard four-fold projective plane. -/
-- The canonical arithmetic witness keeps the abbreviation body proof-free.
abbrev fourFoldProjectivePlane := mFoldProjectivePlane 4 (Nat.one_lt_succ_succ 2)

end NonorientableSurfacePresentation

namespace KleinProjectiveCut

/-- Helper for Exercise 74.4: the closed lower triangle in the unit square. -/
abbrev LowerTriangle :=
  {point : unitInterval × unitInterval // point.2 ≤ point.1}

/-- Helper for Exercise 74.4: the closed upper triangle in the unit square. -/
abbrev UpperTriangle :=
  {point : unitInterval × unitInterval // point.1 ≤ point.2}

/-- Helper for Exercise 74.4: the square cut into separately tagged lower and upper triangles. -/
abbrev Carrier := LowerTriangle ⊕ UpperTriangle

/-- Helper for Exercise 74.4: forget the triangle tag and reassemble the cut unit square. -/
abbrev toSquare : Carrier → unitInterval × unitInterval :=
  Sum.elim Subtype.val Subtype.val

/-- Helper for Exercise 74.4: the lower half of the unit square is closed. -/
lemma lowerTriangle_isClosed :
    IsClosed {point : unitInterval × unitInterval | point.2 ≤ point.1} := by
  -- Closedness is the inverse image of the closed order relation under the two projections.
  exact isClosed_le continuous_snd continuous_fst

/-- Helper for Exercise 74.4: the upper half of the unit square is closed. -/
lemma upperTriangle_isClosed :
    IsClosed {point : unitInterval × unitInterval | point.1 ≤ point.2} := by
  -- Exchange the projections in the same closed-order argument.
  exact isClosed_le continuous_fst continuous_snd

/-- Helper for Exercise 74.4: forgetting the triangle tag is continuous. -/
lemma continuous_toSquare : Continuous toSquare := by
  -- Continuity out of a sum is checked independently on its two subtype summands.
  exact Continuous.sumElim continuous_subtype_val continuous_subtype_val

/-- Helper for Exercise 74.4: every square point belongs to at least one of the two closed
triangles. -/
lemma toSquare_surjective : Function.Surjective toSquare := by
  -- Totality of the coordinate order selects the lower or upper tagged copy.
  intro point
  rcases le_total point.2 point.1 with hlower | hupper
  · exact ⟨Sum.inl ⟨point, hlower⟩, rfl⟩
  · exact ⟨Sum.inr ⟨point, hupper⟩, rfl⟩

/-- Helper for Exercise 74.4: reassembling the two closed triangles is a quotient map onto the
unit square. -/
lemma isQuotientMap_toSquare : Topology.IsQuotientMap toSquare := by
  -- The tagged triangles are compact, so a continuous surjection to the Hausdorff square is
  -- automatically a quotient map.
  letI : CompactSpace LowerTriangle :=
    lowerTriangle_isClosed.isClosedEmbedding_subtypeVal.compactSpace
  letI : CompactSpace UpperTriangle :=
    upperTriangle_isClosed.isClosedEmbedding_subtypeVal.compactSpace
  exact Topology.IsQuotientMap.of_surjective_continuous toSquare_surjective continuous_toSquare

/-- Helper for Exercise 74.4: a horizontal coordinate in the cut square traverses one
half of the first circle in the torus double cover of the Klein bottle. -/
noncomputable def halfCircleCoordinate (x : unitInterval) : Circle :=
  AddCircle.homeomorphCircle one_ne_zero (((x : ℝ) / 2 : ℝ) : UnitAddCircle)

/-- Helper for Exercise 74.4: the half-circle coordinate varies continuously. -/
lemma continuous_halfCircleCoordinate : Continuous halfCircleCoordinate := by
  -- It is the composite of scalar division, the additive-circle quotient, and its circle model.
  unfold halfCircleCoordinate
  fun_prop

/-- Helper for Exercise 74.4: the vertical coordinate traverses the full second circle. -/
noncomputable def fullCircleCoordinate (y : unitInterval) : Circle :=
  AddCircle.homeomorphCircle one_ne_zero (y : UnitAddCircle)

/-- Helper for Exercise 74.4: the full-circle coordinate varies continuously. -/
lemma continuous_fullCircleCoordinate : Continuous fullCircleCoordinate := by
  -- Use the interval inclusion into the additive circle followed by the circle homeomorphism.
  unfold fullCircleCoordinate
  fun_prop

/-- Helper for Exercise 74.4: map the two tagged triangles through the half-torus
fundamental domain and then to the Klein-bottle quotient. -/
noncomputable def toKlein : Carrier → KleinBottle :=
  fun z ↦ KleinBottle.quotientMap
    (halfCircleCoordinate (toSquare z).1, fullCircleCoordinate (toSquare z).2)

/-- Helper for Exercise 74.4: the half-torus map to the Klein bottle is continuous. -/
lemma continuous_toKlein : Continuous toKlein := by
  -- Reassemble the square, map its two coordinates to the torus, and apply the quotient map.
  apply KleinBottle.quotientMap.continuous.comp
  exact (continuous_halfCircleCoordinate.comp
      (continuous_fst.comp continuous_toSquare)).prodMk
    (continuous_fullCircleCoordinate.comp (continuous_snd.comp continuous_toSquare))

/-- Helper for Exercise 74.4: the regular diamond used as the intermediate cut-and-paste
polygon. -/
abbrev Diamond := {point : ℝ × ℝ // |point.1| + |point.2| ≤ 1}

/-- Helper for Exercise 74.4: the lower triangle is flipped affinely onto the right half of
the regular diamond. -/
def lowerAffine (point : LowerTriangle) : ℝ × ℝ :=
  (1 - (point.1.1 : ℝ), (point.1.1 : ℝ) - 2 * (point.1.2 : ℝ))

/-- Helper for Exercise 74.4: the upper triangle is flipped affinely onto the left half of
the regular diamond. -/
def upperAffine (point : UpperTriangle) : ℝ × ℝ :=
  (-(point.1.1 : ℝ), 2 * (point.1.2 : ℝ) - (point.1.1 : ℝ) - 1)

/-- Helper for Exercise 74.4: the lower affine branch lands in the regular diamond. -/
lemma lowerAffine_mem_diamond (point : LowerTriangle) :
    |(lowerAffine point).1| + |(lowerAffine point).2| ≤ 1 := by
  -- The second coordinate has absolute value at most `x`, while the first is `1 - x`.
  have hx0 : 0 ≤ (point.1.1 : ℝ) := point.1.1.property.1
  have hx1 : (point.1.1 : ℝ) ≤ 1 := point.1.1.property.2
  have hy0 : 0 ≤ (point.1.2 : ℝ) := point.1.2.property.1
  have hyx : (point.1.2 : ℝ) ≤ point.1.1 := point.2
  have hsecond : |(point.1.1 : ℝ) - 2 * point.1.2| ≤ point.1.1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  change |1 - (point.1.1 : ℝ)| +
      |(point.1.1 : ℝ) - 2 * point.1.2| ≤ 1
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- Helper for Exercise 74.4: the upper affine branch lands in the regular diamond. -/
lemma upperAffine_mem_diamond (point : UpperTriangle) :
    |(upperAffine point).1| + |(upperAffine point).2| ≤ 1 := by
  -- The second coordinate has absolute value at most `1 - x`, while the first is `-x`.
  have hx0 : 0 ≤ (point.1.1 : ℝ) := point.1.1.property.1
  have hx1 : (point.1.1 : ℝ) ≤ 1 := point.1.1.property.2
  have hy1 : (point.1.2 : ℝ) ≤ 1 := point.1.2.property.2
  have hxy : (point.1.1 : ℝ) ≤ point.1.2 := point.2
  have hsecond : |2 * (point.1.2 : ℝ) - point.1.1 - 1| ≤ 1 - point.1.1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  change |-(point.1.1 : ℝ)| +
      |2 * (point.1.2 : ℝ) - point.1.1 - 1| ≤ 1
  rw [abs_neg, abs_of_nonneg hx0]
  linarith

/-- Helper for Exercise 74.4: the lower branch bundled with its diamond-membership proof. -/
def lowerReassemble : LowerTriangle → Diamond :=
  fun point ↦ ⟨lowerAffine point, lowerAffine_mem_diamond point⟩

/-- Helper for Exercise 74.4: the upper branch bundled with its diamond-membership proof. -/
def upperReassemble : UpperTriangle → Diamond :=
  fun point ↦ ⟨upperAffine point, upperAffine_mem_diamond point⟩

/-- Helper for Exercise 74.4: flip and paste the two triangular pieces into the diamond. -/
def reassemble : Carrier → Diamond :=
  Sum.elim lowerReassemble upperReassemble

/-- Helper for Exercise 74.4: the lower affine branch varies continuously. -/
lemma continuous_lowerAffine : Continuous lowerAffine := by
  -- Both coordinates are affine combinations of the two subtype projections.
  unfold lowerAffine
  fun_prop

/-- Helper for Exercise 74.4: the upper affine branch varies continuously. -/
lemma continuous_upperAffine : Continuous upperAffine := by
  -- Both coordinates are affine combinations of the two subtype projections.
  unfold upperAffine
  fun_prop

/-- Helper for Exercise 74.4: the bundled lower branch is continuous into the diamond. -/
lemma continuous_lowerReassemble : Continuous lowerReassemble := by
  -- Continuity into a subtype is continuity of the underlying affine coordinates.
  rw [continuous_induced_rng]
  exact continuous_lowerAffine

/-- Helper for Exercise 74.4: the bundled upper branch is continuous into the diamond. -/
lemma continuous_upperReassemble : Continuous upperReassemble := by
  -- Continuity into a subtype is continuity of the underlying affine coordinates.
  rw [continuous_induced_rng]
  exact continuous_upperAffine

/-- Helper for Exercise 74.4: the complete flip-and-paste reassembly is continuous. -/
lemma continuous_reassemble : Continuous reassemble := by
  -- A map out of the tagged sum is continuous on exactly when both branches are continuous.
  exact Continuous.sumElim continuous_lowerReassemble continuous_upperReassemble

/-- Helper for Exercise 74.4: the affine lower branch is injective. -/
lemma lowerAffine_injective : Function.Injective lowerAffine := by
  -- Recover `x` from the first coordinate and then `y` from the second.
  intro p q hpq
  have hx : (p.1.1 : ℝ) = q.1.1 := by
    have hfirst := congrArg Prod.fst hpq
    simp only [lowerAffine] at hfirst
    linarith
  have hy : (p.1.2 : ℝ) = q.1.2 := by
    have hsecond := congrArg Prod.snd hpq
    simp only [lowerAffine] at hsecond
    linarith
  apply Subtype.ext
  exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)

/-- Helper for Exercise 74.4: the affine upper branch is injective. -/
lemma upperAffine_injective : Function.Injective upperAffine := by
  -- Recover `x` from the first coordinate and then `y` from the second.
  intro p q hpq
  have hx : (p.1.1 : ℝ) = q.1.1 := by
    have hfirst := congrArg Prod.fst hpq
    simp only [upperAffine] at hfirst
    linarith
  have hy : (p.1.2 : ℝ) = q.1.2 := by
    have hsecond := congrArg Prod.snd hpq
    simp only [upperAffine] at hsecond
    linarith
  apply Subtype.ext
  exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)

/-- Helper for Exercise 74.4: the two affine branches meet exactly along the pasted diagonal
seam. -/
lemma lowerAffine_eq_upperAffine_iff (lower : LowerTriangle) (upper : UpperTriangle) :
    lowerAffine lower = upperAffine upper ↔
      lower.1.1 = 1 ∧ upper.1.1 = 0 ∧ upper.1.2 = unitInterval.symm lower.1.2 := by
  constructor
  · intro heq
    have hfirst := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    simp only [lowerAffine, upperAffine] at hfirst hsecond
    have hlower : (lower.1.1 : ℝ) = 1 := by
      have hlower_le : (lower.1.1 : ℝ) ≤ 1 := lower.1.1.property.2
      have hupper_nonneg : 0 ≤ (upper.1.1 : ℝ) := upper.1.1.property.1
      linarith
    have hupper : (upper.1.1 : ℝ) = 0 := by linarith
    refine ⟨Subtype.ext hlower, Subtype.ext hupper, ?_⟩
    apply Subtype.ext
    rw [unitInterval.coe_symm_eq]
    linarith
  · rintro ⟨hlower, hupper, hvertical⟩
    apply Prod.ext
    · simp only [lowerAffine, upperAffine]
      rw [hlower, hupper]
      norm_num
    · simp only [lowerAffine, upperAffine]
      rw [hlower, hupper, hvertical, unitInterval.coe_symm_eq]
      norm_num
      ring

/-- Helper for Exercise 74.4: equality of the bundled branch values has the same exact seam
normal form. -/
lemma reassemble_inl_eq_inr_iff (lower : LowerTriangle) (upper : UpperTriangle) :
    reassemble (Sum.inl lower) = reassemble (Sum.inr upper) ↔
      lower.1.1 = 1 ∧ upper.1.1 = 0 ∧ upper.1.2 = unitInterval.symm lower.1.2 := by
  -- Push the subtype equality down to the affine coordinates and apply the seam calculation.
  constructor
  · intro heq
    exact (lowerAffine_eq_upperAffine_iff lower upper).mp (congrArg Subtype.val heq)
  · intro hseam
    apply Subtype.ext
    exact (lowerAffine_eq_upperAffine_iff lower upper).mpr hseam

/-- Helper for Exercise 74.4: every point of the regular diamond is obtained from one of the
two triangular affine branches. -/
lemma reassemble_surjective : Function.Surjective reassemble := by
  -- Invert the right branch when `a ≥ 0` and the left branch when `a ≤ 0`.
  intro z
  rcases le_total 0 z.1.1 with ha | ha
  · have haAbs : |z.1.1| = z.1.1 := abs_of_nonneg ha
    have hdiamond := z.property
    rw [haAbs] at hdiamond
    have haLe : z.1.1 ≤ 1 := by
      have hbNonneg : 0 ≤ |z.1.2| := abs_nonneg z.1.2
      linarith
    have hbAbs : |z.1.2| ≤ 1 - z.1.1 := by
      linarith
    have hbBounds := abs_le.mp hbAbs
    have hxMem : 1 - z.1.1 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith
    have hyMem : (1 - z.1.1 - z.1.2) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hbBounds.1, hbBounds.2]
    let x : unitInterval := ⟨1 - z.1.1, hxMem⟩
    let y : unitInterval := ⟨(1 - z.1.1 - z.1.2) / 2, hyMem⟩
    have hyx : y ≤ x := by
      change (1 - z.1.1 - z.1.2) / 2 ≤ 1 - z.1.1
      linarith [hbBounds.1]
    let point : LowerTriangle := ⟨(x, y), hyx⟩
    refine ⟨Sum.inl point, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · simp only [reassemble, Sum.elim_inl, lowerReassemble, lowerAffine, point, x]
      ring
    · simp only [reassemble, Sum.elim_inl, lowerReassemble, lowerAffine, point, x, y]
      ring
  · have haAbs : |z.1.1| = -z.1.1 := abs_of_nonpos ha
    have hdiamond := z.property
    rw [haAbs] at hdiamond
    have haLower : -1 ≤ z.1.1 := by
      have hbNonneg : 0 ≤ |z.1.2| := abs_nonneg z.1.2
      linarith
    have hbAbs : |z.1.2| ≤ 1 + z.1.1 := by
      linarith
    have hbBounds := abs_le.mp hbAbs
    have hxMem : -z.1.1 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith
    have hyMem : (1 - z.1.1 + z.1.2) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hbBounds.1, hbBounds.2]
    let x : unitInterval := ⟨-z.1.1, hxMem⟩
    let y : unitInterval := ⟨(1 - z.1.1 + z.1.2) / 2, hyMem⟩
    have hxy : x ≤ y := by
      change -z.1.1 ≤ (1 - z.1.1 + z.1.2) / 2
      linarith [hbBounds.1]
    let point : UpperTriangle := ⟨(x, y), hxy⟩
    refine ⟨Sum.inr point, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · simp only [reassemble, Sum.elim_inr, upperReassemble, upperAffine, point, x]
      ring
    · simp only [reassemble, Sum.elim_inr, upperReassemble, upperAffine, point, x, y]
      ring

/-- Helper for Exercise 74.4: affine reassembly presents the regular diamond as a quotient
of the two compact triangular pieces. -/
lemma isQuotientMap_reassemble : Topology.IsQuotientMap reassemble := by
  -- Compactness of the closed triangles and Hausdorffness of the diamond turn the verified
  -- continuous surjection into a quotient map.
  letI : CompactSpace LowerTriangle :=
    lowerTriangle_isClosed.isClosedEmbedding_subtypeVal.compactSpace
  letI : CompactSpace UpperTriangle :=
    upperTriangle_isClosed.isClosedEmbedding_subtypeVal.compactSpace
  exact Topology.IsQuotientMap.of_surjective_continuous
    reassemble_surjective continuous_reassemble

/-- Helper for Exercise 74.4: a convex set contains every nonnegative three-point
combination whose coefficients sum to one. -/
private lemma threePointCombination_mem {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) {a b c : ℝ} {x y z : E}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) :
    a • x + b • y + c • z ∈ s := by
  -- Package the three coefficients as a finite convex combination.
  let w : Fin 3 → ℝ := ![a, b, c]
  let p : Fin 3 → E := ![x, y, z]
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i _
    fin_cases i <;> simp only [w] <;> assumption
  have hweights : ∑ i ∈ (Finset.univ : Finset (Fin 3)), w i = 1 := by
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte, w, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
      add_assoc] using hsum
  have hpoints : ∀ i ∈ (Finset.univ : Finset (Fin 3)), p i ∈ s := by
    intro i _
    fin_cases i <;> simp only [p] <;> assumption
  have hcombination := hs.sum_mem hnonneg hweights hpoints
  simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte, w, p, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    add_zero, add_assoc] using hcombination

/-- Helper for Exercise 74.4: map each cut triangle affinely into the corresponding
triangle of the canonical `a a c c` four-gon. -/
noncomputable def canonicalProjectiveAffine :
    Carrier → EuclideanSpace ℝ (Fin 2) :=
  let P := NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two
  Sum.elim
    (fun point ↦
      (1 - (point.1.1 : ℝ)) • P.toPolygon.vertices 0 +
        ((point.1.1 : ℝ) - point.1.2) • P.toPolygon.vertices 1 +
          (point.1.2 : ℝ) • P.toPolygon.vertices 3)
    (fun point ↦
      (1 - (point.1.2 : ℝ)) • P.toPolygon.vertices 3 +
        ((point.1.2 : ℝ) - point.1.1) • P.toPolygon.vertices 1 +
          (point.1.1 : ℝ) • P.toPolygon.vertices 2)

/-- Helper for Exercise 74.4: the canonical affine reassembly lands in the standard
two-fold projective polygon. -/
lemma canonicalProjectiveAffine_mem_region (point : Carrier) :
    canonicalProjectiveAffine point ∈
      (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).region := by
  -- On either tagged triangle, its coordinate inequalities are exactly nonnegativity of
  -- the three barycentric weights.
  cases point with
  | inl point =>
      apply threePointCombination_mem
        (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).convex_region
      · exact sub_nonneg.mpr point.1.1.property.2
      · exact sub_nonneg.mpr point.property
      · exact point.1.2.property.1
      · ring
      · exact (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).vertex_mem_region 0
      · exact (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).vertex_mem_region 1
      · exact (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).vertex_mem_region 3
  | inr point =>
      apply threePointCombination_mem
        (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).convex_region
      · exact sub_nonneg.mpr point.1.2.property.2
      · exact sub_nonneg.mpr point.property
      · exact point.1.1.property.1
      · ring
      · exact (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).vertex_mem_region 3
      · exact (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).vertex_mem_region 1
      · exact (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).vertex_mem_region 2

/-- Helper for Exercise 74.4: the affine reassembly bundled as a map into the canonical
four-gon. -/
noncomputable def projectiveReassemble :
    Carrier → (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).region :=
  fun point ↦ ⟨canonicalProjectiveAffine point, canonicalProjectiveAffine_mem_region point⟩

/-- Helper for Exercise 74.4: the canonical affine map varies continuously on both cut
triangles. -/
lemma continuous_canonicalProjectiveAffine : Continuous canonicalProjectiveAffine := by
  -- Each branch is a finite affine combination of fixed polygon vertices.
  unfold canonicalProjectiveAffine
  apply Continuous.sumElim
  · fun_prop
  · fun_prop

/-- Helper for Exercise 74.4: the canonical two-fold projective polygon is the closed
`ℓ¹` unit diamond. -/
lemma mem_twoFoldPolygonRegion_iff_l1 (z : EuclideanSpace ℝ (Fin 2)) :
    z ∈ (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).region ↔
      |z 0| + |z 1| ≤ 1 := by
  -- The four supporting half-planes are the four signed versions of `x + y ≤ 1`.
  rw [CyclicPolygon.region_eq_iInter_supportingHalfspace]
  simp only [Set.mem_iInter]
  have hangleOne : 2 * Real.pi / (2 * 2 : ℝ) = Real.pi / 2 := by
    ring
  have hangleTwo : 2 * Real.pi * 2 / (2 * 2 : ℝ) = Real.pi := by
    ring
  have hangleThree : 2 * Real.pi * 3 / (2 * 2 : ℝ) = Real.pi + Real.pi / 2 := by
    ring
  constructor
  · intro hz
    have h0 := hz (0 : Fin 4)
    have h1 := hz (1 : Fin 4)
    have h2 := hz (2 : Fin 4)
    have h3 := hz (3 : Fin 4)
    simp [CyclicPolygon.supportingHalfspace, CyclicPolygon.signedArea,
      NonorientableSurfacePresentation.polygon, NonorientableSurfacePresentation.angles,
      CyclicPolygon.toPolygon_vertices, CyclicPolygon.vertex, finRotate_apply,
      hangleOne, hangleTwo, hangleThree, Real.sin_add_pi_div_two,
      Real.cos_add_pi_div_two] at h0 h1 h2 h3
    rcases le_total 0 (z 0) with hx | hx
    · rw [abs_of_nonneg hx]
      rcases le_total 0 (z 1) with hy | hy
      · rw [abs_of_nonneg hy]
        linarith
      · rw [abs_of_nonpos hy]
        linarith
    · rw [abs_of_nonpos hx]
      rcases le_total 0 (z 1) with hy | hy
      · rw [abs_of_nonneg hy]
        linarith
      · rw [abs_of_nonpos hy]
        linarith
  · intro hz i
    fin_cases i <;>
      simp [CyclicPolygon.supportingHalfspace, CyclicPolygon.signedArea,
        NonorientableSurfacePresentation.polygon, NonorientableSurfacePresentation.angles,
        CyclicPolygon.toPolygon_vertices, CyclicPolygon.vertex, finRotate_apply,
        hangleOne, hangleTwo, hangleThree, Real.sin_add_pi_div_two,
        Real.cos_add_pi_div_two] <;>
      have hx := le_abs_self (z 0) <;>
      have hnx := neg_le_abs (z 0) <;>
      have hy := le_abs_self (z 1) <;>
      have hny := neg_le_abs (z 1) <;>
      linarith

/-- Helper for Exercise 74.4: canonical polygon reassembly has the same two coordinates as
the affine diamond reassembly. -/
lemma canonicalProjectiveAffine_coordinates (point : Carrier) :
    canonicalProjectiveAffine point 0 = (reassemble point).1.1 ∧
      canonicalProjectiveAffine point 1 = (reassemble point).1.2 := by
  -- Compute the two coordinates separately on the lower and upper affine branches.
  have hangleOne : 2 * Real.pi / (2 * 2 : ℝ) = Real.pi / 2 := by
    ring
  have hangleTwo : 2 * Real.pi * 2 / (2 * 2 : ℝ) = Real.pi := by
    ring
  have hangleThree : 2 * Real.pi * 3 / (2 * 2 : ℝ) = Real.pi + Real.pi / 2 := by
    ring
  cases point with
  | inl point =>
      constructor <;>
        simp [canonicalProjectiveAffine, reassemble, lowerReassemble, lowerAffine,
          NonorientableSurfacePresentation.polygon,
          NonorientableSurfacePresentation.angles, CyclicPolygon.toPolygon_vertices,
          CyclicPolygon.vertex, hangleOne, hangleTwo, hangleThree,
          Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] <;>
        ring
  | inr point =>
      constructor <;>
        simp [canonicalProjectiveAffine, reassemble, upperReassemble, upperAffine,
          NonorientableSurfacePresentation.polygon,
          NonorientableSurfacePresentation.angles, CyclicPolygon.toPolygon_vertices,
          CyclicPolygon.vertex, hangleOne, hangleTwo, hangleThree,
          Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] <;>
        ring

/-- Helper for Exercise 74.4: every point of the canonical two-fold projective polygon is
obtained by affine reassembly of one of the two cut triangles. -/
lemma projectiveReassemble_surjective : Function.Surjective projectiveReassemble := by
  -- Regard the target point as a diamond point and use the already verified affine inverse.
  intro z
  let diamondPoint : Diamond :=
    ⟨(z.1 0, z.1 1), (mem_twoFoldPolygonRegion_iff_l1 z.1).mp z.property⟩
  obtain ⟨point, hpoint⟩ := reassemble_surjective diamondPoint
  refine ⟨point, ?_⟩
  have hzero : canonicalProjectiveAffine point 0 = z.1 0 := by
    calc
      canonicalProjectiveAffine point 0 = (reassemble point).1.1 :=
        (canonicalProjectiveAffine_coordinates point).1
      _ = z.1 0 := congrArg (fun w : Diamond ↦ w.1.1) hpoint
  have hone : canonicalProjectiveAffine point 1 = z.1 1 := by
    calc
      canonicalProjectiveAffine point 1 = (reassemble point).1.2 :=
        (canonicalProjectiveAffine_coordinates point).2
      _ = z.1 1 := congrArg (fun w : Diamond ↦ w.1.2) hpoint
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hzero
  · exact hone

/-- Helper for Exercise 74.4: the bundled canonical reassembly is continuous. -/
lemma continuous_projectiveReassemble : Continuous projectiveReassemble := by
  -- Continuity into the polygon subtype is continuity of the ambient affine formula.
  rw [continuous_induced_rng]
  exact continuous_canonicalProjectiveAffine

/-- Helper for Exercise 74.4: affine reassembly presents the canonical two-fold projective
polygon as a quotient of the two compact cut triangles. -/
lemma isQuotientMap_projectiveReassemble :
    Topology.IsQuotientMap projectiveReassemble := by
  -- Compactness of both triangle summands upgrades the continuous surjection to a quotient map.
  letI : CompactSpace LowerTriangle :=
    lowerTriangle_isClosed.isClosedEmbedding_subtypeVal.compactSpace
  letI : CompactSpace UpperTriangle :=
    upperTriangle_isClosed.isClosedEmbedding_subtypeVal.compactSpace
  exact Topology.IsQuotientMap.of_surjective_continuous
    projectiveReassemble_surjective continuous_projectiveReassemble

/-- Helper for Exercise 74.4: the bottom side of the lower cut triangle maps with its
original parameter to edge zero of the canonical four-gon. -/
lemma projectiveReassemble_lowerBottom (t : unitInterval) :
    projectiveReassemble (Sum.inl ⟨(t, 0), t.property.1⟩) =
      (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion
        ((NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint 0 t) := by
  -- Evaluate both sides as the same affine combination of vertices zero and one.
  apply Subtype.ext
  rw [(NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion_coe,
    (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint_coe_eq_lineMap,
    AffineMap.lineMap_apply_module]
  simp [projectiveReassemble, canonicalProjectiveAffine, finRotate_apply]

/-- Helper for Exercise 74.4: the top side of the upper cut triangle maps with its
original parameter to edge one of the canonical four-gon. -/
lemma projectiveReassemble_upperTop (t : unitInterval) :
    projectiveReassemble (Sum.inr ⟨(t, 1), t.property.2⟩) =
      (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion
        ((NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint 1 t) := by
  -- Evaluate both sides as the same affine combination of vertices one and two.
  apply Subtype.ext
  rw [(NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion_coe,
    (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint_coe_eq_lineMap,
    AffineMap.lineMap_apply_module]
  simp [projectiveReassemble, canonicalProjectiveAffine, finRotate_apply]

/-- Helper for Exercise 74.4: the diagonal of the upper cut triangle maps in reverse
parameter order to edge two of the canonical four-gon. -/
lemma projectiveReassemble_upperDiagonal (t : unitInterval) :
    projectiveReassemble (Sum.inr ⟨(t, t), le_rfl⟩) =
      (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion
        ((NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint 2
          (unitInterval.symm t)) := by
  -- Reversing the parameter exchanges the two affine endpoint coefficients.
  apply Subtype.ext
  rw [(NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion_coe,
    (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint_coe_eq_lineMap,
    AffineMap.lineMap_apply_module]
  simp [projectiveReassemble, canonicalProjectiveAffine, finRotate_apply,
    unitInterval.coe_symm_eq, add_comm]

/-- Helper for Exercise 74.4: the diagonal of the lower cut triangle maps in reverse
parameter order to edge three of the canonical four-gon. -/
lemma projectiveReassemble_lowerDiagonal (t : unitInterval) :
    projectiveReassemble (Sum.inl ⟨(t, t), le_rfl⟩) =
      (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion
        ((NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint 3
          (unitInterval.symm t)) := by
  -- The last cyclic edge runs from vertex three back to vertex zero.
  apply Subtype.ext
  rw [(NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion_coe,
    (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint_coe_eq_lineMap,
    AffineMap.lineMap_apply_module]
  simp [projectiveReassemble, canonicalProjectiveAffine, finRotate_apply,
    unitInterval.coe_symm_eq, add_comm]

/-- Helper for Exercise 74.4: the two affine branches agree on the edge along which the
cut triangles are pasted back together. -/
lemma projectiveReassemble_seam (t : unitInterval) :
    projectiveReassemble (Sum.inl ⟨(1, t), t.property.2⟩) =
      projectiveReassemble
        (Sum.inr ⟨(0, unitInterval.symm t), (unitInterval.symm t).property.1⟩) := by
  -- Complementary vertical parameters give the same combination of vertices one and three.
  apply Subtype.ext
  simp [projectiveReassemble, canonicalProjectiveAffine, unitInterval.coe_symm_eq,
    add_comm]

/-- Helper for Exercise 74.4: equality under canonical polygon reassembly is equivalent to
equality under the coordinatewise diamond reassembly. -/
lemma projectiveReassemble_eq_iff_reassemble (x y : Carrier) :
    projectiveReassemble x = projectiveReassemble y ↔ reassemble x = reassemble y := by
  -- Compare the two ambient coordinates, using the established coordinate bridge in both
  -- directions.
  constructor
  · intro hxy
    apply Subtype.ext
    apply Prod.ext
    · calc
        (reassemble x).1.1 = canonicalProjectiveAffine x 0 :=
          (canonicalProjectiveAffine_coordinates x).1.symm
        _ = canonicalProjectiveAffine y 0 :=
          congrArg (fun z :
            (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).region ↦ z.1 0) hxy
        _ = (reassemble y).1.1 := (canonicalProjectiveAffine_coordinates y).1
    · calc
        (reassemble x).1.2 = canonicalProjectiveAffine x 1 :=
          (canonicalProjectiveAffine_coordinates x).2.symm
        _ = canonicalProjectiveAffine y 1 :=
          congrArg (fun z :
            (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).region ↦ z.1 1) hxy
        _ = (reassemble y).1.2 := (canonicalProjectiveAffine_coordinates y).2
  · intro hxy
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i
    · calc
        canonicalProjectiveAffine x 0 = (reassemble x).1.1 :=
          (canonicalProjectiveAffine_coordinates x).1
        _ = (reassemble y).1.1 := congrArg (fun z : Diamond ↦ z.1.1) hxy
        _ = canonicalProjectiveAffine y 0 :=
          (canonicalProjectiveAffine_coordinates y).1.symm
    · calc
        canonicalProjectiveAffine x 1 = (reassemble x).1.2 :=
          (canonicalProjectiveAffine_coordinates x).2
        _ = (reassemble y).1.2 := congrArg (fun z : Diamond ↦ z.1.2) hxy
        _ = canonicalProjectiveAffine y 1 :=
          (canonicalProjectiveAffine_coordinates y).2.symm

end KleinProjectiveCut

namespace NonorientableSurfacePresentation

/-- Helper for Exercise 74.4: the positive orientation in the standard presentation is the
canonical cyclic edge parameterization. -/
lemma pasting_orientedPoint_eq_boundaryToRegion (m : ℕ) (hm : 1 < m)
    (i : Fin (2 * m)) (t : unitInterval) :
    (pasting m hm).orientedPoint i t =
      (polygon m hm).boundaryToRegion ((polygon m hm).edgePoint i t) := by
  -- Both sides include the same affine point of the positively oriented cyclic edge.
  apply Subtype.ext
  rw [CyclicPolygon.EdgePasting.orientedPoint_apply,
    CyclicPolygon.EdgePasting.includePoint_coe,
    (polygon m hm).boundaryToRegion_coe,
    (polygon m hm).edgePoint_coe_eq_lineMap,
    OrientedSegment.point_coe]
  simp only [pasting, CyclicPolygon.signedOrientation, if_true,
    CyclicPolygon.cyclicOrientation]

/-- Helper for Exercise 74.4: equally labelled standard edges with the same parameter are
directly related by the polygon pasting. -/
lemma pasting_related_orientedPoints (m : ℕ) (hm : 1 < m)
    (i j : Fin (2 * m)) (t : unitInterval)
    (hlabel : (pasting m hm).label i = (pasting m hm).label j) :
    (pasting m hm).Related
      ((polygon m hm).boundaryToRegion ((polygon m hm).edgePoint i t))
      ((polygon m hm).boundaryToRegion ((polygon m hm).edgePoint j t)) := by
  -- Use the source oriented point as the direct-relation witness; positive identification
  -- preserves its affine parameter.
  rw [(pasting m hm).related_iff]
  refine ⟨i, j, hlabel, ((pasting m hm).orientation i).point t, ?_, ?_⟩
  · rw [← (pasting m hm).orientedPoint_apply, pasting_orientedPoint_eq_boundaryToRegion]
  · rw [(pasting m hm).positiveIdentification_point]
    rw [← (pasting m hm).orientedPoint_apply, pasting_orientedPoint_eq_boundaryToRegion]

/-- Helper for Exercise 74.4: equally labelled standard edges have equal quotient images at
matching affine parameters. -/
lemma quotientMap_edgePoint_eq_of_label_eq (m : ℕ) (hm : 1 < m)
    (i j : Fin (2 * m)) (t : unitInterval)
    (hlabel : (pasting m hm).label i = (pasting m hm).label j) :
    quotientMap m hm
        ((polygon m hm).boundaryToRegion ((polygon m hm).edgePoint i t)) =
      quotientMap m hm
        ((polygon m hm).boundaryToRegion ((polygon m hm).edgePoint j t)) := by
  -- A direct edge relation generates an equality in the realization quotient.
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _
    (pasting_related_orientedPoints m hm i j t hlabel)

end NonorientableSurfacePresentation

namespace KleinProjectiveCut

/-- Helper for Exercise 74.4: the affine four-gon reassembly followed by its edge-pasting
quotient. -/
noncomputable abbrev toProjective :
    Carrier → NonorientableSurfacePresentation.twoFoldProjectivePlane :=
  NonorientableSurfacePresentation.quotientMap 2 Nat.one_lt_two ∘ projectiveReassemble

/-- Helper for Exercise 74.4: the canonical map from the cut triangles to the two-fold
projective plane is continuous. -/
lemma continuous_toProjective : Continuous toProjective := by
  -- Compose the continuous affine reassembly with the canonical polygon quotient.
  exact (NonorientableSurfacePresentation.isQuotientMap_quotientMap
    2 Nat.one_lt_two).continuous.comp continuous_projectiveReassemble

/-- Helper for Exercise 74.4: the canonical map from the cut triangles to the two-fold
projective plane is a quotient map. -/
lemma isQuotientMap_toProjective : Topology.IsQuotientMap toProjective := by
  -- Quotientness is stable under composing the affine and edge-pasting presentations.
  exact (NonorientableSurfacePresentation.isQuotientMap_quotientMap
    2 Nat.one_lt_two).comp isQuotientMap_projectiveReassemble

/-- Helper for Exercise 74.4: two tagged points over the same point of the cut square have
the same image in the projective-plane presentation. -/
lemma toProjective_eq_of_toSquare_eq (x y : Carrier) (hxy : toSquare x = toSquare y) :
    toProjective x = toProjective y := by
  -- Equal tags on one triangle are literal equality; opposite tags can occur only on the
  -- diagonal, whose two copies become the equally labelled last two polygon edges.
  have hcross (lower : LowerTriangle) (upper : UpperTriangle)
      (hcross : lower.1 = upper.1) :
      toProjective (Sum.inl lower) = toProjective (Sum.inr upper) := by
    have hdiag : lower.1.1 = lower.1.2 := by
      apply le_antisymm
      · rw [hcross]
        exact upper.property
      · exact lower.property
    have hlower : lower = ⟨(lower.1.1, lower.1.1), le_rfl⟩ := by
      apply Subtype.ext
      exact Prod.ext rfl hdiag.symm
    have hupper : upper = ⟨(lower.1.1, lower.1.1), le_rfl⟩ := by
      apply Subtype.ext
      exact hcross.symm.trans (Prod.ext rfl hdiag.symm)
    rw [hlower, hupper]
    simp only [toProjective, Function.comp_apply]
    rw [projectiveReassemble_lowerDiagonal, projectiveReassemble_upperDiagonal]
    exact NonorientableSurfacePresentation.quotientMap_edgePoint_eq_of_label_eq
      2 Nat.one_lt_two 3 2 (unitInterval.symm _) (by
        norm_num [NonorientableSurfacePresentation.pasting,
          NonorientableSurfacePresentation.boundaryLetter])
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          have hsource : x = y := Subtype.ext hxy
          subst y
          rfl
      | inr y =>
          change x.1 = y.1 at hxy
          exact hcross x y hxy
  | inr x =>
      cases y with
      | inl y =>
          exact (hcross y x hxy.symm).symm
      | inr y =>
          have hsource : x = y := Subtype.ext hxy
          subst y
          rfl

/-- Helper for Exercise 74.4: the two horizontal boundary representatives over one
horizontal coordinate have the same projective-plane image. -/
lemma toProjective_eq_of_horizontalEndpoint (x y : Carrier)
    (hfirst : (toSquare y).1 = (toSquare x).1)
    (hsecond : unitInterval.endpointSetoid (toSquare y).2 (toSquare x).2) :
    toProjective x = toProjective y := by
  -- Equal vertical parameters reduce to the preceding tag-independence lemma.  At the two
  -- endpoints, switch to the canonical bottom and top tags and identify edges zero and one.
  rw [unitInterval.endpointSetoid_iff] at hsecond
  rcases hsecond with hsecond | ⟨hy, hx⟩ | ⟨hy, hx⟩
  · apply toProjective_eq_of_toSquare_eq
    exact Prod.ext hfirst.symm hsecond.symm
  · let bottom : Carrier :=
      Sum.inl ⟨((toSquare x).1, 0), (toSquare x).1.property.1⟩
    let top : Carrier :=
      Sum.inr ⟨((toSquare x).1, 1), (toSquare x).1.property.2⟩
    have hxtop : toSquare x = toSquare top := by
      apply Prod.ext
      · rfl
      · exact hx
    have hybottom : toSquare y = toSquare bottom := by
      apply Prod.ext
      · exact hfirst
      · exact hy
    calc
      toProjective x = toProjective top := toProjective_eq_of_toSquare_eq _ _ hxtop
      _ = toProjective bottom := by
        simp only [toProjective, Function.comp_apply, top, bottom]
        rw [projectiveReassemble_upperTop, projectiveReassemble_lowerBottom]
        exact NonorientableSurfacePresentation.quotientMap_edgePoint_eq_of_label_eq
          2 Nat.one_lt_two 1 0 _ (by
            norm_num [NonorientableSurfacePresentation.pasting,
              NonorientableSurfacePresentation.boundaryLetter])
      _ = toProjective y := (toProjective_eq_of_toSquare_eq _ _ hybottom).symm
  · let bottom : Carrier :=
      Sum.inl ⟨((toSquare x).1, 0), (toSquare x).1.property.1⟩
    let top : Carrier :=
      Sum.inr ⟨((toSquare x).1, 1), (toSquare x).1.property.2⟩
    have hxbottom : toSquare x = toSquare bottom := by
      apply Prod.ext
      · rfl
      · exact hx
    have hytop : toSquare y = toSquare top := by
      apply Prod.ext
      · exact hfirst
      · exact hy
    calc
      toProjective x = toProjective bottom :=
        toProjective_eq_of_toSquare_eq _ _ hxbottom
      _ = toProjective top := by
        simp only [toProjective, Function.comp_apply, top, bottom]
        rw [projectiveReassemble_lowerBottom, projectiveReassemble_upperTop]
        exact NonorientableSurfacePresentation.quotientMap_edgePoint_eq_of_label_eq
          2 Nat.one_lt_two 0 1 _ (by
            norm_num [NonorientableSurfacePresentation.pasting,
              NonorientableSurfacePresentation.boundaryLetter])
      _ = toProjective y := (toProjective_eq_of_toSquare_eq _ _ hytop).symm

/-- Helper for Exercise 74.4: opposite vertical sides with reflected parameters have the
same projective-plane image, including the common endpoint class. -/
lemma toProjective_eq_of_reflectedVertical (x y : Carrier)
    (hsides : ((toSquare x).1 = 0 ∧ (toSquare y).1 = 1) ∨
      ((toSquare x).1 = 1 ∧ (toSquare y).1 = 0))
    (hsecond : unitInterval.endpointSetoid (toSquare y).2
      (unitInterval.symm (toSquare x).2)) :
    toProjective x = toProjective y := by
  -- First cross the exact reflected seam.  Any possible endpoint discrepancy on the target
  -- side is then handled by the horizontal endpoint lemma.
  rcases hsides with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · let left : Carrier :=
      Sum.inr ⟨(0, (toSquare x).2), (toSquare x).2.property.1⟩
    let right : Carrier :=
      Sum.inl ⟨(1, unitInterval.symm (toSquare x).2),
        (unitInterval.symm (toSquare x).2).property.2⟩
    have hxleft : toSquare x = toSquare left := by
      apply Prod.ext
      · exact hx
      · rfl
    have hrightfirst : (toSquare y).1 = (toSquare right).1 := by
      simpa only [right, toSquare, Sum.elim_inl] using hy
    calc
      toProjective x = toProjective left := toProjective_eq_of_toSquare_eq _ _ hxleft
      _ = toProjective right := by
        simp only [toProjective, Function.comp_apply, left, right]
        simpa only [unitInterval.symm_symm] using
          (congrArg (NonorientableSurfacePresentation.quotientMap 2 Nat.one_lt_two)
            (projectiveReassemble_seam (unitInterval.symm (toSquare x).2))).symm
      _ = toProjective y :=
        toProjective_eq_of_horizontalEndpoint right y hrightfirst hsecond
  · let right : Carrier :=
      Sum.inl ⟨(1, (toSquare x).2), (toSquare x).2.property.2⟩
    let left : Carrier :=
      Sum.inr ⟨(0, unitInterval.symm (toSquare x).2),
        (unitInterval.symm (toSquare x).2).property.1⟩
    have hxright : toSquare x = toSquare right := by
      apply Prod.ext
      · exact hx
      · rfl
    have hleftfirst : (toSquare y).1 = (toSquare left).1 := by
      simpa only [left, toSquare, Sum.elim_inr] using hy
    calc
      toProjective x = toProjective right := toProjective_eq_of_toSquare_eq _ _ hxright
      _ = toProjective left := by
        simp only [toProjective, Function.comp_apply, right, left]
        exact congrArg (NonorientableSurfacePresentation.quotientMap 2 Nat.one_lt_two)
          (projectiveReassemble_seam (toSquare x).2)
      _ = toProjective y :=
        toProjective_eq_of_horizontalEndpoint left y hleftfirst (by
          simpa only [left, toSquare, Sum.elim_inr, unitInterval.symm_symm] using hsecond)

end KleinProjectiveCut

namespace KleinBottle

/-- Helper for Exercise 74.4: the involution defining the Klein bottle is continuous. -/
lemma continuous_involution : Continuous involution := by
  -- Both coordinate operations are continuous on the product of circles.
  unfold involution
  fun_prop

/-- Helper for Exercise 74.4: saturating a set under the Klein-bottle quotient adds exactly
its image under the defining involution. -/
lemma quotientMap_preimage_image (U : Set (Circle × Circle)) :
    quotientMap ⁻¹' (quotientMap '' U) = U ∪ involution ⁻¹' U := by
  -- Normalize quotient equality and use involutivity to orient the second representative.
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [quotientMap_eq_iff] at hyx
    rcases hyx with rfl | hxy
    · exact Or.inl hy
    · apply Or.inr
      change involution x ∈ U
      rw [hxy, involution_involutive]
      exact hy
  · rintro (hx | hx)
    · exact ⟨x, hx, rfl⟩
    · refine ⟨involution x, hx, ?_⟩
      rw [quotientMap_eq_iff]
      exact Or.inr (involution_involutive x).symm

/-- Helper for Exercise 74.4: the orbit projection defining the Klein bottle is an open
quotient map. -/
lemma isOpenQuotientMap_quotientMap : IsOpenQuotientMap quotientMap := by
  -- A quotient image is open because its saturation is the union of an open set and its
  -- inverse image under the continuous involution.
  have hquot : Topology.IsQuotientMap
      (@Quotient.mk' (Circle × Circle) identified) := isQuotientMap_quotient_mk'
  refine IsOpenQuotientMap.of_isOpenMap_isQuotientMap ?_ hquot
  intro U hU
  rw [← hquot.isOpen_preimage]
  have hopen : IsOpen (quotientMap ⁻¹' (quotientMap '' U)) := by
    rw [quotientMap_preimage_image]
    exact hU.union (hU.preimage continuous_involution)
  have hmk : (@Quotient.mk' (Circle × Circle) identified) =
      (@Quotient.mk'' (Circle × Circle) identified) := rfl
  rw [hmk]
  simpa only [quotientMap, ContinuousMap.coe_mk] using hopen

/-- Helper for Exercise 74.4: the standard quotient model of the Klein bottle is Hausdorff. -/
instance instT2Space : T2Space KleinBottle := by
  -- The fiber relation is the closed union of the diagonal and the graph of the involution.
  apply (t2Space_iff_of_isOpenQuotientMap isOpenQuotientMap_quotientMap).2
  have hfiber : {q : (Circle × Circle) × (Circle × Circle) |
      quotientMap q.1 = quotientMap q.2} =
      {q | q.2 = q.1} ∪ {q | q.2 = involution q.1} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_union, quotientMap_eq_iff]
  rw [hfiber]
  exact (isClosed_eq continuous_snd continuous_fst).union
    (isClosed_eq continuous_snd (continuous_involution.comp continuous_fst))

/-- Helper for Exercise 74.4: the chosen half-circle parameter has no repeated values. -/
lemma halfCircleCoordinate_injective :
    Function.Injective KleinProjectiveCut.halfCircleCoordinate := by
  -- Pull equality back to additive-circle representatives lying in a single period.
  intro x y hxy
  unfold KleinProjectiveCut.halfCircleCoordinate at hxy
  apply (AddCircle.homeomorphCircle one_ne_zero).injective at hxy
  have hxmem : (x : ℝ) / 2 ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    constructor
    · linarith [x.property.1]
    · linarith [x.property.2]
  have hymem : (y : ℝ) / 2 ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    constructor
    · linarith [y.property.1]
    · linarith [y.property.2]
  have hreal : (x : ℝ) / 2 = (y : ℝ) / 2 :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico hxmem hymem).mp hxy
  apply Subtype.ext
  linarith

/-- Helper for Exercise 74.4: adding a half-turn to a circle argument gives its antipode. -/
lemma exp_add_pi (θ : ℝ) : Circle.exp (θ + Real.pi) = -Circle.exp θ := by
  -- On complex representatives this is the exponential identity `exp (π I) = -1`.
  apply Circle.ext
  rw [Circle.coe_exp, Circle.coe_neg, Circle.coe_exp]
  have hexponent : ((θ + Real.pi : ℝ) : ℂ) * Complex.I =
      (θ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexponent, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- Helper for Exercise 74.4: antipodal points in the selected closed half-circle occur
only at its two opposite endpoints. -/
lemma halfCircleCoordinate_eq_neg_iff (x y : unitInterval) :
    KleinProjectiveCut.halfCircleCoordinate y =
        -KleinProjectiveCut.halfCircleCoordinate x ↔
      (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  -- Convert antipodal equality to equality of real circle arguments modulo `2π`.
  unfold KleinProjectiveCut.halfCircleCoordinate
  rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply,
    AddCircle.toCircle_apply_mk, AddCircle.toCircle_apply_mk]
  rw [← exp_add_pi]
  constructor
  · intro hxy
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hxy
    norm_num at hm
    have hnormalized : (y : ℝ) = (x : ℝ) + 1 + 2 * (m : ℝ) := by
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      apply (mul_left_cancel₀ hpi)
      linear_combination hm
    have hmLower : (-1 : ℝ) ≤ (m : ℝ) := by
      linarith [x.property.2, y.property.1]
    have hmUpper : (m : ℝ) ≤ 0 := by
      linarith [x.property.1, y.property.2]
    have hmLowerInt : (-1 : ℤ) ≤ m := by exact_mod_cast hmLower
    have hmUpperInt : m ≤ (0 : ℤ) := by exact_mod_cast hmUpper
    have hmCases : m = -1 ∨ m = 0 := by omega
    have hxNonneg : 0 ≤ (x : ℝ) := x.property.1
    have hxLeOne : (x : ℝ) ≤ 1 := x.property.2
    have hyNonneg : 0 ≤ (y : ℝ) := y.property.1
    have hyLeOne : (y : ℝ) ≤ 1 := y.property.2
    rcases hmCases with rfl | rfl
    · right
      norm_num at hnormalized
      have hx : (x : ℝ) = 1 := by linarith
      have hy : (y : ℝ) = 0 := by linarith
      exact ⟨Subtype.ext hx, Subtype.ext hy⟩
    · left
      norm_num at hnormalized
      have hx : (x : ℝ) = 0 := by linarith
      have hy : (y : ℝ) = 1 := by linarith
      exact ⟨Subtype.ext hx, Subtype.ext hy⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have harg : 2 * Real.pi / 1 * (((1 : unitInterval) : ℝ) / 2) =
          Real.pi := by
        norm_num
        ring
      rw [harg]
      simpa using exp_add_pi 0
    · have harg : 2 * Real.pi / 1 * (((1 : unitInterval) : ℝ) / 2) =
          Real.pi := by
        norm_num
        ring
      rw [harg]
      have htwo : Real.pi + Real.pi = 2 * Real.pi := by ring
      rw [htwo, Circle.exp_two_pi]
      have hzero : 2 * Real.pi / 1 * (((0 : unitInterval) : ℝ) / 2) = 0 := by
        norm_num
      rw [hzero, Circle.exp_zero]

/-- Helper for Exercise 74.4: the full-circle parameter identifies precisely the two
orders of the interval endpoints. -/
lemma fullCircleCoordinate_eq_iff (x y : unitInterval) :
    KleinProjectiveCut.fullCircleCoordinate x =
        KleinProjectiveCut.fullCircleCoordinate y ↔
      x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  -- The circle homeomorphism transports the standard endpoint setoid characterization.
  unfold KleinProjectiveCut.fullCircleCoordinate
  simp only [AddCircle.homeomorphCircle_apply]
  constructor
  · intro hxy
    apply AddCircle.injective_toCircle one_ne_zero at hxy
    exact (unitInterval.endpointSetoid_iff x y).mp hxy
  · intro hxy
    exact congrArg (fun z : UnitAddCircle ↦ AddCircle.toCircle z)
      ((unitInterval.endpointSetoid_iff x y).mpr hxy)

/-- Helper for Exercise 74.4: reflecting the interval parameter inverts the full-circle
coordinate. -/
lemma fullCircleCoordinate_symm (x : unitInterval) :
    KleinProjectiveCut.fullCircleCoordinate (unitInterval.symm x) =
      (KleinProjectiveCut.fullCircleCoordinate x)⁻¹ := by
  -- The reflected real argument differs from the negative argument by one full period.
  unfold KleinProjectiveCut.fullCircleCoordinate
  rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply,
    AddCircle.toCircle_apply_mk, AddCircle.toCircle_apply_mk, ← Circle.exp_neg]
  apply Circle.exp_eq_exp.mpr
  refine ⟨1, ?_⟩
  rw [unitInterval.coe_symm_eq]
  norm_num
  ring

/-- Helper for Exercise 74.4: the fiber relation on the cut square consists of the horizontal
edge identification and the reflected vertical edge identification. -/
abbrev cutIdentified (x y : KleinProjectiveCut.Carrier) : Prop :=
  ((KleinProjectiveCut.toSquare y).1 = (KleinProjectiveCut.toSquare x).1 ∧
      unitInterval.endpointSetoid (KleinProjectiveCut.toSquare y).2
        (KleinProjectiveCut.toSquare x).2) ∨
    (((KleinProjectiveCut.toSquare x).1 = 0 ∧
        (KleinProjectiveCut.toSquare y).1 = 1) ∨
      ((KleinProjectiveCut.toSquare x).1 = 1 ∧
        (KleinProjectiveCut.toSquare y).1 = 0)) ∧
      unitInterval.endpointSetoid (KleinProjectiveCut.toSquare y).2
        (unitInterval.symm (KleinProjectiveCut.toSquare x).2)

/-- Helper for Exercise 74.4: equality in the Klein quotient is exactly the cut-square
fiber relation. -/
lemma toKlein_eq_iff_cutIdentified (x y : KleinProjectiveCut.Carrier) :
    KleinProjectiveCut.toKlein x = KleinProjectiveCut.toKlein y ↔ cutIdentified x y := by
  -- Expand one quotient step, then normalize its ordinary and involution branches separately.
  unfold KleinProjectiveCut.toKlein
  rw [quotientMap_eq_iff]
  simp only [involution, Prod.mk.injEq]
  constructor
  · rintro (⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩)
    · left
      exact ⟨halfCircleCoordinate_injective hfirst,
        (unitInterval.endpointSetoid_iff _ _).mpr
          ((fullCircleCoordinate_eq_iff _ _).mp hsecond)⟩
    · right
      refine ⟨(halfCircleCoordinate_eq_neg_iff _ _).mp hfirst, ?_⟩
      rw [← fullCircleCoordinate_symm] at hsecond
      exact (unitInterval.endpointSetoid_iff _ _).mpr
        ((fullCircleCoordinate_eq_iff _ _).mp hsecond)
  · rintro (⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩)
    · left
      constructor
      · exact congrArg KleinProjectiveCut.halfCircleCoordinate hfirst
      · exact (fullCircleCoordinate_eq_iff _ _).mpr
          ((unitInterval.endpointSetoid_iff _ _).mp hsecond)
    · right
      constructor
      · exact (halfCircleCoordinate_eq_neg_iff _ _).mpr hfirst
      · rw [← fullCircleCoordinate_symm]
        exact (fullCircleCoordinate_eq_iff _ _).mpr
          ((unitInterval.endpointSetoid_iff _ _).mp hsecond)

/-- Helper for Exercise 74.4: the Klein presentation is constant on every fiber of affine
reassembly into the canonical projective polygon. -/
lemma toKlein_factorsThrough_projectiveReassemble :
    Function.FactorsThrough KleinProjectiveCut.toKlein
      KleinProjectiveCut.projectiveReassemble := by
  -- Same-branch fibers are equal by affine injectivity; the two cross-branch fibers are the
  -- reflected vertical seam, already included in the normalized Klein relation.
  intro x y hxy
  have hreassemble : KleinProjectiveCut.reassemble x = KleinProjectiveCut.reassemble y :=
    (KleinProjectiveCut.projectiveReassemble_eq_iff_reassemble x y).mp hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          have hvalues : KleinProjectiveCut.lowerAffine x =
              KleinProjectiveCut.lowerAffine y :=
            congrArg Subtype.val hreassemble
          have hxySource : x = y := KleinProjectiveCut.lowerAffine_injective hvalues
          subst y
          rfl
      | inr y =>
          have hseam := (KleinProjectiveCut.reassemble_inl_eq_inr_iff x y).mp hreassemble
          apply (toKlein_eq_iff_cutIdentified _ _).mpr
          right
          constructor
          · exact Or.inr ⟨hseam.1, hseam.2.1⟩
          · exact (unitInterval.endpointSetoid_iff _ _).mpr (Or.inl hseam.2.2)
  | inr x =>
      cases y with
      | inl y =>
          have hseam :=
            (KleinProjectiveCut.reassemble_inl_eq_inr_iff y x).mp hreassemble.symm
          symm
          apply (toKlein_eq_iff_cutIdentified _ _).mpr
          right
          constructor
          · exact Or.inr ⟨hseam.1, hseam.2.1⟩
          · exact (unitInterval.endpointSetoid_iff _ _).mpr (Or.inl hseam.2.2)
      | inr y =>
          have hvalues : KleinProjectiveCut.upperAffine x =
              KleinProjectiveCut.upperAffine y :=
            congrArg Subtype.val hreassemble
          have hxySource : x = y := KleinProjectiveCut.upperAffine_injective hvalues
          subst y
          rfl

/-- Helper for Exercise 74.4: equality in the Klein presentation implies equality in the
canonical projective-polygon presentation. -/
lemma toProjective_eq_of_toKlein_eq (x y : KleinProjectiveCut.Carrier)
    (hxy : KleinProjectiveCut.toKlein x = KleinProjectiveCut.toKlein y) :
    KleinProjectiveCut.toProjective x = KleinProjectiveCut.toProjective y := by
  -- The normalized Klein relation has exactly the horizontal endpoint and reflected-side
  -- branches already handled by the two projective quotient lemmas.
  rw [toKlein_eq_iff_cutIdentified] at hxy
  rcases hxy with hhorizontal | hreflected
  · exact KleinProjectiveCut.toProjective_eq_of_horizontalEndpoint x y
      hhorizontal.1 hhorizontal.2
  · exact KleinProjectiveCut.toProjective_eq_of_reflectedVertical x y
      hreflected.1 hreflected.2

/-- Helper for Exercise 74.4: equality in the canonical projective-polygon presentation
implies equality in the Klein presentation. -/
lemma toKlein_eq_of_toProjective_eq (x y : KleinProjectiveCut.Carrier)
    (hxy : KleinProjectiveCut.toProjective x = KleinProjectiveCut.toProjective y) :
    KleinProjectiveCut.toKlein x = KleinProjectiveCut.toKlein y := by
  -- First descend the Klein map through affine reassembly.  It remains to check that the
  -- descended map is constant on each directly paired pair of polygon edges.
  let projectiveMap : C(KleinProjectiveCut.Carrier,
      (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).region) :=
    ⟨KleinProjectiveCut.projectiveReassemble,
      KleinProjectiveCut.continuous_projectiveReassemble⟩
  have hprojectiveMap : Topology.IsQuotientMap projectiveMap := by
    simpa only [projectiveMap, ContinuousMap.coe_mk] using
      KleinProjectiveCut.isQuotientMap_projectiveReassemble
  let kleinMap : C(KleinProjectiveCut.Carrier, KleinBottle) :=
    ⟨KleinProjectiveCut.toKlein, KleinProjectiveCut.continuous_toKlein⟩
  have kleinMap_factors : Function.FactorsThrough kleinMap projectiveMap := by
    simpa only [kleinMap, projectiveMap, ContinuousMap.coe_mk] using
      toKlein_factorsThrough_projectiveReassemble
  let descended : C(
      (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).region, KleinBottle) :=
    hprojectiveMap.lift kleinMap kleinMap_factors
  have descended_projectiveReassemble (z : KleinProjectiveCut.Carrier) :
      descended (KleinProjectiveCut.projectiveReassemble z) =
        KleinProjectiveCut.toKlein z := by
    have htriangle := congrArg
      (fun k : C(KleinProjectiveCut.Carrier, KleinBottle) ↦ k z)
      (hprojectiveMap.lift_comp kleinMap kleinMap_factors)
    simpa only [kleinMap, projectiveMap, ContinuousMap.coe_mk,
      ContinuousMap.comp_apply, descended] using htriangle
  have descended_related {a b :
      (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).region}
      (hab : (NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).Related a b) :
      descended a = descended b := by
    rw [(NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).related_iff] at hab
    obtain ⟨i, j, hlabel, z, ha, hb⟩ := hab
    let t : unitInterval :=
      ((NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).orientation i).parameter z
    have hz :
        ((NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).orientation i).point t =
          z := by
      exact ((NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).orientation i).point_parameter z
    have haEdge : a =
        (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion
          ((NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint i t) := by
      calc
        a = (NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).includePoint i z := ha
        _ = (NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).includePoint i
            (((NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).orientation i).point t) :=
          congrArg _ hz.symm
        _ = (NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).orientedPoint i t := rfl
        _ = (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion
            ((NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint i t) :=
          NonorientableSurfacePresentation.pasting_orientedPoint_eq_boundaryToRegion
            2 Nat.one_lt_two i t
    have hbEdge : b =
        (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion
          ((NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint j t) := by
      calc
        b = (NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).includePoint j
            ((NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).positiveIdentification
              i j z) := hb
        _ = (NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).includePoint j
            ((NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).positiveIdentification
              i j
                (((NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).orientation i).point
                  t)) := congrArg _ (congrArg _ hz.symm)
        _ = (NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).includePoint j
            (((NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).orientation j).point t) := by
          rw [(NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).positiveIdentification_point]
        _ = (NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).orientedPoint j t := rfl
        _ = (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion
            ((NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint j t) :=
          NonorientableSurfacePresentation.pasting_orientedPoint_eq_boundaryToRegion
            2 Nat.one_lt_two j t
    rw [haEdge, hbEdge]
    by_cases hij : i = j
    · subst j
      rfl
    have hblock : i.val / 2 = j.val / 2 := by
      have hlabel' : i.val / 2 + 1 = j.val / 2 + 1 := by
        simpa only [NonorientableSurfacePresentation.pasting,
          NonorientableSurfacePresentation.boundaryLetter] using hlabel
      omega
    have hcases : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
        (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by
      fin_cases i <;> fin_cases j
      all_goals norm_num at hblock
      all_goals norm_num at hij
      all_goals norm_num
      · exact Or.inl ⟨Fin.ext rfl, Fin.ext rfl⟩
      · exact Or.inr ⟨Fin.ext rfl, Fin.ext rfl⟩
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [← KleinProjectiveCut.projectiveReassemble_lowerBottom,
        ← KleinProjectiveCut.projectiveReassemble_upperTop,
        descended_projectiveReassemble, descended_projectiveReassemble]
      apply (toKlein_eq_iff_cutIdentified _ _).mpr
      left
      simp [KleinProjectiveCut.toSquare, unitInterval.endpointSetoid_iff]
    · rw [← KleinProjectiveCut.projectiveReassemble_upperTop,
        ← KleinProjectiveCut.projectiveReassemble_lowerBottom,
        descended_projectiveReassemble, descended_projectiveReassemble]
      apply (toKlein_eq_iff_cutIdentified _ _).mpr
      left
      simp [KleinProjectiveCut.toSquare, unitInterval.endpointSetoid_iff]
    · have hedgeTwo :
          KleinProjectiveCut.projectiveReassemble
              (Sum.inr ⟨(unitInterval.symm t, unitInterval.symm t), le_rfl⟩) =
            (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion
              ((NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint 2 t) := by
        simpa only [unitInterval.symm_symm] using
          KleinProjectiveCut.projectiveReassemble_upperDiagonal (unitInterval.symm t)
      have hedgeThree :
          KleinProjectiveCut.projectiveReassemble
              (Sum.inl ⟨(unitInterval.symm t, unitInterval.symm t), le_rfl⟩) =
            (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion
              ((NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint 3 t) := by
        simpa only [unitInterval.symm_symm] using
          KleinProjectiveCut.projectiveReassemble_lowerDiagonal (unitInterval.symm t)
      rw [← hedgeTwo, ← hedgeThree, descended_projectiveReassemble,
        descended_projectiveReassemble]
      rfl
    · have hedgeTwo :
          KleinProjectiveCut.projectiveReassemble
              (Sum.inr ⟨(unitInterval.symm t, unitInterval.symm t), le_rfl⟩) =
            (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion
              ((NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint 2 t) := by
        simpa only [unitInterval.symm_symm] using
          KleinProjectiveCut.projectiveReassemble_upperDiagonal (unitInterval.symm t)
      have hedgeThree :
          KleinProjectiveCut.projectiveReassemble
              (Sum.inl ⟨(unitInterval.symm t, unitInterval.symm t), le_rfl⟩) =
            (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).boundaryToRegion
              ((NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).edgePoint 3 t) := by
        simpa only [unitInterval.symm_symm] using
          KleinProjectiveCut.projectiveReassemble_lowerDiagonal (unitInterval.symm t)
      rw [← hedgeThree, ← hedgeTwo, descended_projectiveReassemble,
        descended_projectiveReassemble]
      rfl
  -- Quotient equality is generated by the direct edge relation, so compatibility propagates
  -- through reflexivity, symmetry, and transitivity.
  have hidentified :
      (NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).Identified
        (KleinProjectiveCut.projectiveReassemble x)
        (KleinProjectiveCut.projectiveReassemble y) := by
    exact Quotient.exact hxy
  have descended_identified {a b :
      (NonorientableSurfacePresentation.polygon 2 Nat.one_lt_two).region}
      (hab : (NonorientableSurfacePresentation.pasting 2 Nat.one_lt_two).Identified a b) :
      descended a = descended b := by
    induction hab with
    | rel a b hab => exact descended_related hab
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ihab ihbc => exact ihab.trans ihbc
  have hdescended : descended (KleinProjectiveCut.projectiveReassemble x) =
      descended (KleinProjectiveCut.projectiveReassemble y) :=
    descended_identified hidentified
  exact (descended_projectiveReassemble x).symm.trans
    (hdescended.trans (descended_projectiveReassemble y))

/-- Helper for Exercise 74.4: every circle point or its antipode occurs on the chosen
half-circle fundamental interval. -/
lemma halfCircleCoordinate_eq_or_eq_neg (z : Circle) :
    ∃ x : unitInterval,
      KleinProjectiveCut.halfCircleCoordinate x = z ∨
        KleinProjectiveCut.halfCircleCoordinate x = -z := by
  -- Choose the standard additive-circle representative and split it at the midpoint.
  let angle : UnitAddCircle := (AddCircle.homeomorphCircle one_ne_zero).symm z
  obtain ⟨r, hr, hrangle⟩ := AddCircle.eq_coe_Ico angle
  by_cases hlower : r ≤ 1 / 2
  · have hxmem : 2 * r ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith [hr.1]
      · linarith
    let x : unitInterval := ⟨2 * r, hxmem⟩
    refine ⟨x, Or.inl ?_⟩
    -- Doubling the interval coordinate cancels the half-circle rescaling.
    rw [KleinProjectiveCut.halfCircleCoordinate, ←
      (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply z]
    congr 1
    calc
      (((((x : unitInterval) : ℝ) / 2 : ℝ)) : UnitAddCircle) =
          (r : UnitAddCircle) := by
        have hreal : ((x : ℝ) / 2) = r := by
          simp only [x]
          ring
        exact congrArg (fun u : ℝ ↦ (u : UnitAddCircle)) hreal
      _ = angle := hrangle
      _ = (AddCircle.homeomorphCircle one_ne_zero).symm z := rfl
  · have hrhalf : 1 / 2 < r := lt_of_not_ge hlower
    have hxmem : 2 * r - 1 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · linarith [hr.2]
    let x : unitInterval := ⟨2 * r - 1, hxmem⟩
    refine ⟨x, Or.inr ?_⟩
    -- On the upper half, subtracting one half-turn produces the antipodal point.
    rw [KleinProjectiveCut.halfCircleCoordinate, ←
      (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply z,
      AddCircle.homeomorphCircle_apply]
    rw [AddCircle.homeomorphCircle_apply]
    change AddCircle.toCircle _ = -AddCircle.toCircle angle
    rw [AddCircle.toCircle_apply_mk, ← hrangle, AddCircle.toCircle_apply_mk]
    apply Circle.ext
    rw [Circle.coe_exp, Circle.coe_neg, Circle.coe_exp]
    have hexponent :
        ((2 * Real.pi / 1 * (((x : unitInterval) : ℝ) / 2) : ℝ) : ℂ) * Complex.I =
          ((2 * Real.pi / 1 * r : ℝ) : ℂ) * Complex.I -
            (Real.pi : ℂ) * Complex.I := by
      simp only [x]
      push_cast
      ring
    rw [hexponent, Complex.exp_sub, Complex.exp_pi_mul_I]
    ring

/-- Helper for Exercise 74.4: the full-circle coordinate covers the circle. -/
lemma fullCircleCoordinate_surjective :
    Function.Surjective KleinProjectiveCut.fullCircleCoordinate := by
  -- Represent the additive-circle inverse image in the unit interval.
  intro z
  let angle : UnitAddCircle := (AddCircle.homeomorphCircle one_ne_zero).symm z
  obtain ⟨r, hr, hrangle⟩ := AddCircle.eq_coe_Ico angle
  have hymem : r ∈ Set.Icc (0 : ℝ) 1 := ⟨hr.1, hr.2.le⟩
  let y : unitInterval := ⟨r, hymem⟩
  refine ⟨y, ?_⟩
  rw [KleinProjectiveCut.fullCircleCoordinate, ←
    (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply z]
  congr 1

/-- Helper for Exercise 74.4: the cut half-torus covers every Klein-bottle orbit. -/
lemma toKlein_surjective : Function.Surjective KleinProjectiveCut.toKlein := by
  -- Work with a torus representative and put its first coordinate in the chosen half-circle.
  intro z
  refine Quotient.inductionOn z ?_
  intro point
  obtain ⟨x, hx | hx⟩ := halfCircleCoordinate_eq_or_eq_neg point.1
  · obtain ⟨y, hy⟩ := fullCircleCoordinate_surjective point.2
    obtain ⟨source, hsource⟩ := KleinProjectiveCut.toSquare_surjective (x, y)
    refine ⟨source, ?_⟩
    -- The selected coordinates reproduce the original representative exactly.
    unfold KleinProjectiveCut.toKlein
    rw [hsource, hx, hy]
    rfl
  · obtain ⟨y, hy⟩ := fullCircleCoordinate_surjective point.2⁻¹
    obtain ⟨source, hsource⟩ := KleinProjectiveCut.toSquare_surjective (x, y)
    refine ⟨source, ?_⟩
    -- The antipodal representative differs by the defining Klein involution.
    unfold KleinProjectiveCut.toKlein
    rw [hsource, hx, hy]
    change quotientMap (-point.1, point.2⁻¹) = quotientMap point
    rw [quotientMap_eq_iff]
    have horbit : point = involution (-point.1, point.2⁻¹) := by
      simp only [involution, neg_neg, inv_inv]
    exact Or.inr horbit

/-- Helper for Exercise 74.4: the cut half-torus map is a quotient presentation of the
Klein bottle. -/
lemma isQuotientMap_toKlein : Topology.IsQuotientMap KleinProjectiveCut.toKlein := by
  -- Compactness of the cut triangles and Hausdorffness of the target upgrade the continuous
  -- surjection to a quotient map.
  letI : CompactSpace KleinProjectiveCut.LowerTriangle :=
    KleinProjectiveCut.lowerTriangle_isClosed.isClosedEmbedding_subtypeVal.compactSpace
  letI : CompactSpace KleinProjectiveCut.UpperTriangle :=
    KleinProjectiveCut.upperTriangle_isClosed.isClosedEmbedding_subtypeVal.compactSpace
  exact Topology.IsQuotientMap.of_surjective_continuous
    toKlein_surjective KleinProjectiveCut.continuous_toKlein

/-- Helper for Exercise 74.4: cutting and reassembling the Klein fundamental square gives a
pair of quotient presentations with exactly the same fibers as the standard `a a c c` four-gon. -/
lemma existsCutFlipPastePresentation :
    ∃ q : C(KleinProjectiveCut.Carrier, KleinBottle),
      ∃ p : C(KleinProjectiveCut.Carrier,
          NonorientableSurfacePresentation.twoFoldProjectivePlane),
        Topology.IsQuotientMap q ∧ Topology.IsQuotientMap p ∧
          ∀ x y, q x = q y ↔ p x = p y := by
  -- Route correction: the affine map now targets the canonical four-gon directly; its
  -- continuity, seam equation, and four boundary formulas are verified above.  The two
  -- directed kernel lemmas package the only generated-relation calculation.
  let q : C(KleinProjectiveCut.Carrier, KleinBottle) :=
    ⟨KleinProjectiveCut.toKlein, KleinProjectiveCut.continuous_toKlein⟩
  let p : C(KleinProjectiveCut.Carrier,
      NonorientableSurfacePresentation.twoFoldProjectivePlane) :=
    ⟨KleinProjectiveCut.toProjective, KleinProjectiveCut.continuous_toProjective⟩
  refine ⟨q, p, ?_, ?_, ?_⟩
  · simpa only [q, ContinuousMap.coe_mk] using isQuotientMap_toKlein
  · simpa only [p, ContinuousMap.coe_mk] using
      KleinProjectiveCut.isQuotientMap_toProjective
  · intro x y
    constructor
    · exact toProjective_eq_of_toKlein_eq x y
    · exact toKlein_eq_of_toProjective_eq x y

/-- Exercise 74.4 (a): The Klein bottle is homeomorphic to the two-fold projective plane. -/
theorem homeomorphicTwoFoldProjectivePlane :
    Nonempty (KleinBottle ≃ₜ NonorientableSurfacePresentation.twoFoldProjectivePlane) := by
  -- Compare the cut-and-paste quotient with the canonical `a a c c` polygon quotient.
  obtain ⟨q, p, hq, hp, hker⟩ := existsCutFlipPastePresentation
  obtain ⟨h, _⟩ := CyclicPolygon.existsHomeomorphOfQuotientPresentations q p hq
    hp (Homeomorph.refl _) (fun x y ↦ hker x y)
  exact ⟨h⟩

end KleinBottle

namespace NonorientableSurfacePresentation

/-- Helper for Exercise 74.4: local embedded sections of a quotient presentation descend to a
continuous map that is an embedding on a neighborhood of every quotient point. -/
lemma locallyEmbeddedLiftOfQuotientMap
    {S X Y : Type*} [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y]
    (q : C(S, X)) (hq : Topology.IsQuotientMap q) (g : C(S, Y))
    (hg : Function.FactorsThrough g q)
    (hlocal : ∀ x : X, ∃ U ∈ 𝓝 x, ∃ s : U → S, ∃ e : C(U, Y),
      (∀ u, q (s u) = u) ∧ (∀ u, e u = g (s u)) ∧ Topology.IsEmbedding e) :
    ∃ f : C(X, Y), ∀ x, ∃ U ∈ 𝓝 x, Topology.IsEmbedding (U.restrict f) := by
  -- Descend `g` once; the quotient computation rule identifies every local restriction.
  let f : C(X, Y) := hq.lift g hg
  refine ⟨f, ?_⟩
  intro x
  obtain ⟨U, hU, s, e, hs, he, hemb⟩ := hlocal x
  refine ⟨U, hU, ?_⟩
  have hrestriction : U.restrict f = e := by
    ext u
    calc
      f u = f (q (s u)) := congrArg f (hs u).symm
      _ = g (s u) := by
        have htriangle := congrArg (fun k : C(S, Y) ↦ k (s u))
          (hq.lift_comp g hg)
        exact htriangle
      _ = e u := (he u).symm
  -- Transport the supplied chart embedding across the quotient computation equality.
  rw [hrestriction]
  exact hemb

/-- Helper for Exercise 74.4: compact neighborhoods on which a compatible source map
reflects quotient fibers give embedded restrictions of the descended map. -/
lemma locallyEmbeddedLiftOfQuotientMap_of_compactFiberNeighborhoods
    {S X Y : Type*} [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] (q : C(S, X)) (hq : Topology.IsQuotientMap q) (g : C(S, Y))
    (hg : Function.FactorsThrough g q)
    (hlocal : ∀ x : X, ∃ U ∈ 𝓝 x, IsCompact U ∧
      ∀ a b : S, q a ∈ U → q b ∈ U → g a = g b → q a = q b) :
    ∃ f : C(X, Y), ∀ x, ∃ U ∈ 𝓝 x, Topology.IsEmbedding (U.restrict f) := by
  -- Descend the compatible map once and record its computation on source representatives.
  let f : C(X, Y) := hq.lift g hg
  have f_comp_q (a : S) : f (q a) = g a := by
    have htriangle := congrArg (fun k : C(S, Y) ↦ k a) (hq.lift_comp g hg)
    exact htriangle
  refine ⟨f, ?_⟩
  intro x
  obtain ⟨U, hU, hUcompact, hreflect⟩ := hlocal x
  refine ⟨U, hU, ?_⟩
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hUcompact
  -- Fiber reflection makes the restriction injective after choosing quotient representatives.
  have hinjective : Function.Injective (U.restrict f) := by
    intro u v huv
    obtain ⟨a, ha⟩ := hq.surjective u
    obtain ⟨b, hb⟩ := hq.surjective v
    apply Subtype.ext
    have hab : g a = g b := by
      calc
        g a = f (q a) := (f_comp_q a).symm
        _ = f u := congrArg f ha
        _ = f v := huv
        _ = f (q b) := congrArg f hb.symm
        _ = g b := f_comp_q b
    exact ha.symm.trans ((hreflect a b (ha ▸ u.property) (hb ▸ v.property) hab).trans hb)
  exact ((f.continuous.comp continuous_subtype_val).isClosedEmbedding hinjective).isEmbedding

end NonorientableSurfacePresentation

namespace CyclicPolygon

variable {n : ℕ}

/-- Helper for Exercise 74.4: the finite radial fan sends an indexed boundary parameter
and a radial parameter to the corresponding point of a cyclic polygon. -/
noncomputable def fanParameterization (P : CyclicPolygon n) (p : P.interior) :
    (Fin n × unitInterval) × unitInterval → P.region :=
  fun z ↦ P.radialPoint p (P.edgePoint z.1.1 z.1.2) z.2

/-- Helper for Exercise 74.4: radial fan parameterization is continuous. -/
lemma continuous_fanParameterization (P : CyclicPolygon n) (p : P.interior) :
    Continuous (P.fanParameterization p) := by
  -- First parameterize the boundary, then apply joint radial interpolation.
  exact (P.continuous_radialPoint p).comp
    ((P.continuous_edgePoint.comp continuous_fst).prodMk continuous_snd)

/-- Helper for Exercise 74.4: radial fan parameterization covers the filled polygon. -/
lemma fanParameterization_surjective (P : CyclicPolygon n) (p : P.interior) :
    Function.Surjective (P.fanParameterization p) := by
  -- Choose a radial boundary endpoint, then choose its indexed edge parameter.
  intro y
  obtain ⟨⟨x, t⟩, hxt⟩ := P.radialPoint_surjective p y
  obtain ⟨⟨i, s⟩, his⟩ := P.edgePoint_surjective x
  refine ⟨((i, s), t), ?_⟩
  simpa only [fanParameterization, his] using hxt

/-- Helper for Exercise 74.4: the finite radial fan is a quotient presentation of the
filled cyclic polygon. -/
lemma isQuotientMap_fanParameterization (P : CyclicPolygon n) (p : P.interior) :
    Topology.IsQuotientMap (P.fanParameterization p) := by
  -- A continuous surjection from the compact finite fan to the Hausdorff region is quotient.
  exact Topology.IsQuotientMap.of_surjective_continuous
    (P.fanParameterization_surjective p) (P.continuous_fanParameterization p)

/-- Helper for Exercise 74.4: radial parameter zero sends every indexed fan ray to its
common interior center. -/
lemma fanParameterization_radial_zero (P : CyclicPolygon n) (p : P.interior)
    (i : Fin n) (s : unitInterval) :
    (P.fanParameterization p ((i, s), 0) : EuclideanSpace ℝ (Fin 2)) = p := by
  -- The fan formula is the affine line map, whose zero endpoint is the chosen center.
  rw [fanParameterization, P.radialPoint_coe_eq_lineMap]
  exact AffineMap.lineMap_apply_zero _ _

/-- Helper for Exercise 74.4: radial parameter one sends an indexed fan ray to its
parameterized polygon-boundary endpoint. -/
lemma fanParameterization_radial_one (P : CyclicPolygon n) (p : P.interior)
    (i : Fin n) (s : unitInterval) :
    (P.fanParameterization p ((i, s), 1) : EuclideanSpace ℝ (Fin 2)) = P.edgePoint i s := by
  -- The one endpoint of the same affine line map is the selected edge point.
  rw [fanParameterization, P.radialPoint_coe_eq_lineMap]
  exact AffineMap.lineMap_apply_one _ _

namespace EdgePasting

variable {P : CyclicPolygon n} {S Y : Type*}

/-- Helper for Exercise 74.4: a map on a polygonal region factors through an edge-pasting
quotient exactly when it respects every direct paired-edge relation. -/
lemma factorsThrough_quotientMap_iff (pasting : P.EdgePasting S) (f : P.region → Y) :
    Function.FactorsThrough f pasting.quotientMap ↔
      ∀ x y, pasting.Related x y → f x = f y := by
  constructor
  · intro hf x y hxy
    -- A direct relation is one generating step in the quotient setoid.
    exact hf (Quotient.sound (Relation.EqvGen.rel x y hxy))
  · intro hrelated x y hxy
    -- Equality of quotient classes is the generated relation; induction propagates the
    -- direct compatibility through reflexivity, symmetry, and transitivity.
    have hidentified : Relation.EqvGen pasting.Related x y := Quotient.exact hxy
    clear hxy
    induction hidentified with
    | rel x y hrel => exact hrelated x y hrel
    | refl x => exact rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

end EdgePasting

end CyclicPolygon

namespace NonorientableSurfacePresentation

/-- Helper for Exercise 74.4: the radial fan followed by the octagonal edge quotient is
the canonical finite-source presentation used for the four-fold immersion. -/
noncomputable def fourFoldFanQuotientMap
    (p : (polygon 4 (Nat.one_lt_succ_succ 2)).interior) :
    (Fin 8 × unitInterval) × unitInterval → fourFoldProjectivePlane :=
  quotientMap 4 (Nat.one_lt_succ_succ 2) ∘
    (polygon 4 (Nat.one_lt_succ_succ 2)).fanParameterization p

/-- Helper for Exercise 74.4: the finite radial fan map onto the four-fold projective
plane is a quotient map. -/
lemma isQuotientMap_fourFoldFanQuotientMap
    (p : (polygon 4 (Nat.one_lt_succ_succ 2)).interior) :
    Topology.IsQuotientMap (fourFoldFanQuotientMap p) := by
  -- Compose the radial quotient presentation with the canonical edge-pasting quotient.
  exact (isQuotientMap_quotientMap 4 (Nat.one_lt_succ_succ 2)).comp
    ((polygon 4 (Nat.one_lt_succ_succ 2)).isQuotientMap_fanParameterization p)

/-- Helper for Exercise 74.4: the origin is an interior point of the canonical regular
octagon. -/
lemma fourFoldPolygonCenter_mem_interior :
    (0 : EuclideanSpace ℝ (Fin 2)) ∈
      (polygon 4 (Nat.one_lt_succ_succ 2)).interior := by
  -- Each supporting inequality is strict at the center; all eight determinants are the
  -- same positive quarter-turn determinant after evaluating the regular vertices.
  rw [CyclicPolygon.interior_eq_topologicalInterior,
    CyclicPolygon.region_eq_iInter_supportingHalfspace, interior_iInter_of_finite]
  apply Set.mem_iInter.mpr
  intro i
  rw [CyclicPolygon.supportingHalfspace,
    CyclicPolygon.interior_signedArea_sub_nonneg
      ((polygon 4 (Nat.one_lt_succ_succ 2)).cyclicEdgeVector_ne_zero i)
      ((polygon 4 (Nat.one_lt_succ_succ 2)).toPolygon.vertices i)]
  have hangleOne : 2 * Real.pi / (2 * 4 : ℝ) = Real.pi / 4 := by
    ring
  have hangleTwo : 2 * Real.pi * 2 / (2 * 4 : ℝ) = Real.pi / 2 := by
    ring
  have hangleThree :
      2 * Real.pi * 3 / (2 * 4 : ℝ) = Real.pi / 2 + Real.pi / 4 := by
    ring
  have hangleFour : 2 * Real.pi * 4 / (2 * 4 : ℝ) = Real.pi := by
    ring
  have hangleFive : 2 * Real.pi * 5 / (2 * 4 : ℝ) = Real.pi + Real.pi / 4 := by
    ring
  have hangleSix : 2 * Real.pi * 6 / (2 * 4 : ℝ) = Real.pi + Real.pi / 2 := by
    ring
  have hangleSeven :
      2 * Real.pi * 7 / (2 * 4 : ℝ) =
        Real.pi + (Real.pi / 2 + Real.pi / 4) := by
    ring
  fin_cases i <;>
    simp [CyclicPolygon.signedArea, polygon, angles, CyclicPolygon.toPolygon_vertices,
      CyclicPolygon.vertex, finRotate_apply, hangleOne, hangleTwo, hangleThree,
      hangleFour, hangleFive, hangleSix, hangleSeven, Real.sin_add, Real.cos_add,
      Real.sin_pi_div_four, Real.cos_pi_div_four] <;>
    try positivity
  all_goals nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)]

/-- Helper for Exercise 74.4: the origin bundled as the radial center of the canonical
regular octagon. -/
noncomputable def fourFoldPolygonCenter :
    (polygon 4 (Nat.one_lt_succ_succ 2)).interior :=
  ⟨0, fourFoldPolygonCenter_mem_interior⟩

/-- Helper for Exercise 74.4: equality under the finite fan quotient is exactly the
edge-pasting setoid relation between the corresponding polygon points. -/
lemma fourFoldFanQuotientMap_eq_iff_identified
    (p : (polygon 4 (Nat.one_lt_succ_succ 2)).interior)
    (a b : (Fin 8 × unitInterval) × unitInterval) :
    fourFoldFanQuotientMap p a = fourFoldFanQuotientMap p b ↔
      (pasting 4 (Nat.one_lt_succ_succ 2)).Identified
        ((polygon 4 (Nat.one_lt_succ_succ 2)).fanParameterization p a)
        ((polygon 4 (Nat.one_lt_succ_succ 2)).fanParameterization p b) := by
  -- Unfold the two compositional wrappers and expose equality in the quotient setoid.
  exact Quotient.eq

/-- Helper for Exercise 74.4: a polygon map respecting the paired octagon edges remains
fiber-compatible after precomposition with the finite radial fan. -/
lemma factorsThrough_fourFoldFanQuotientMap {Y : Type*}
    (p : (polygon 4 (Nat.one_lt_succ_succ 2)).interior)
    (f : (polygon 4 (Nat.one_lt_succ_succ 2)).region → Y)
    (hrelated : ∀ x y, (pasting 4 (Nat.one_lt_succ_succ 2)).Related x y →
      f x = f y) :
    Function.FactorsThrough
      (f ∘ (polygon 4 (Nat.one_lt_succ_succ 2)).fanParameterization p)
      (fourFoldFanQuotientMap p) := by
  -- First descend across the edge setoid, then pull the fiber condition back along the
  -- surjective radial parameterization.
  have hpolygon : Function.FactorsThrough f
      (quotientMap 4 (Nat.one_lt_succ_succ 2)) :=
    ((pasting 4 (Nat.one_lt_succ_succ 2)).factorsThrough_quotientMap_iff f).mpr
      hrelated
  exact hpolygon.comp_right
    ((polygon 4 (Nat.one_lt_succ_succ 2)).fanParameterization p)

/-- Helper for Exercise 74.4: vertices of the degree-three subdivision of the eight
triangles in the radial octagonal fan. -/
private inductive FourFoldSourceMeshVertex
  | center
  | innerRay (i : Fin 8)
  | outerRay (i : Fin 8)
  | panel (i : Fin 8)
  | boundaryFirst (i : Fin 8)
  | boundarySecond (i : Fin 8)
  | outer (i : Fin 8)
  deriving DecidableEq, Fintype

/-- Helper for Exercise 74.4: quotient-control vertices obtained by pairing corresponding
boundary controls and collapsing all octagon vertices. -/
private inductive FourFoldQuotientMeshVertex
  | center
  | innerRay (i : Fin 8)
  | outerRay (i : Fin 8)
  | panel (i : Fin 8)
  | boundary (pair : Fin 4) (second : Bool)
  | outer
  deriving DecidableEq, Fintype

/-- Helper for Exercise 74.4: the 72 small triangles in the degree-three subdivision of
the eight radial fan triangles. -/
private abbrev FourFoldSourceMeshFace := Fin 8 × Fin 9

/-- Helper for Exercise 74.4: the quotient-control index of every source-mesh vertex. -/
private def fourFoldSourceToQuotientVertex :
    FourFoldSourceMeshVertex → FourFoldQuotientMeshVertex
  | .center => .center
  | .innerRay i => .innerRay i
  | .outerRay i => .outerRay i
  | .panel i => .panel i
  | .boundaryFirst i => .boundary (Fin.ofNat 4 (i / 2)) false
  | .boundarySecond i => .boundary (Fin.ofNat 4 (i / 2)) true
  | .outer _ => .outer

/-- Helper for Exercise 74.4: cyclic successor of an octagonal fan sector. -/
private def fourFoldNextSector (i : Fin 8) : Fin 8 :=
  Fin.ofNat 8 (i + 1)

/-- Helper for Exercise 74.4: the three vertices of each small triangle in the subdivided
radial fan. -/
private def fourFoldSourceMeshFaceVertices
    (face : FourFoldSourceMeshFace) : Fin 3 → FourFoldSourceMeshVertex :=
  match face.2.1 with
  | 0 => ![.center, .innerRay face.1, .innerRay (fourFoldNextSector face.1)]
  | 1 => ![.innerRay face.1, .outerRay face.1, .panel face.1]
  | 2 => ![.innerRay (fourFoldNextSector face.1), .panel face.1,
      .outerRay (fourFoldNextSector face.1)]
  | 3 => ![.outerRay face.1, .outer face.1, .boundaryFirst face.1]
  | 4 => ![.panel face.1, .boundaryFirst face.1, .boundarySecond face.1]
  | 5 => ![.outerRay (fourFoldNextSector face.1), .boundarySecond face.1,
      .outer (fourFoldNextSector face.1)]
  | 6 => ![.innerRay face.1, .innerRay (fourFoldNextSector face.1), .panel face.1]
  | 7 => ![.outerRay face.1, .panel face.1, .boundaryFirst face.1]
  | _ => ![.panel face.1, .outerRay (fourFoldNextSector face.1),
      .boundarySecond face.1]

/-- Helper for Exercise 74.4: the first trisection parameter belongs to `unitInterval`. -/
private lemma oneThird_mem_unitInterval : (1 / 3 : ℝ) ∈ unitInterval := by
  -- Both endpoint inequalities are immediate rational inequalities.
  constructor <;> norm_num

/-- Helper for Exercise 74.4: the second trisection parameter belongs to `unitInterval`. -/
private lemma twoThirds_mem_unitInterval : (2 / 3 : ℝ) ∈ unitInterval := by
  -- Both endpoint inequalities are immediate rational inequalities.
  constructor <;> norm_num

/-- Helper for Exercise 74.4: the midpoint parameter belongs to `unitInterval`. -/
private lemma oneHalf_mem_unitInterval : (1 / 2 : ℝ) ∈ unitInterval := by
  -- Both endpoint inequalities are immediate rational inequalities.
  constructor <;> norm_num

/-- Helper for Exercise 74.4: the first trisection parameter of an interval. -/
private noncomputable def oneThird : unitInterval := ⟨1 / 3, oneThird_mem_unitInterval⟩

/-- Helper for Exercise 74.4: the second trisection parameter of an interval. -/
private noncomputable def twoThirds : unitInterval := ⟨2 / 3, twoThirds_mem_unitInterval⟩

/-- Helper for Exercise 74.4: the midpoint parameter of an interval. -/
private noncomputable def oneHalf : unitInterval := ⟨1 / 2, oneHalf_mem_unitInterval⟩

/-- Helper for Exercise 74.4: fan coordinates of every vertex in the degree-three
subdivision. -/
private noncomputable def fourFoldSourceMeshParameter :
    FourFoldSourceMeshVertex → (Fin 8 × unitInterval) × unitInterval
  | .center => ((0, 0), 0)
  | .innerRay i => ((i, 0), oneThird)
  | .outerRay i => ((i, 0), twoThirds)
  | .panel i => ((i, oneHalf), twoThirds)
  | .boundaryFirst i => ((i, oneThird), 1)
  | .boundarySecond i => ((i, twoThirds), 1)
  | .outer i => ((i, 0), 1)

/-- Helper for Exercise 74.4: the geometric realization of a source-mesh vertex in the
canonical octagon. -/
private noncomputable def fourFoldSourceMeshPoint (v : FourFoldSourceMeshVertex) :
    (polygon 4 (Nat.one_lt_succ_succ 2)).region :=
  (polygon 4 (Nat.one_lt_succ_succ 2)).fanParameterization
    fourFoldPolygonCenter (fourFoldSourceMeshParameter v)

/-- Helper for Exercise 74.4: the source subdivision has 49 vertices. -/
private lemma fourFoldSourceMeshVertex_card :
    Fintype.card FourFoldSourceMeshVertex = 49 := by
  -- The seven constructors contribute `1 + 6 * 8` vertices.
  decide

/-- Helper for Exercise 74.4: boundary pairing reduces the source controls to 34 quotient
vertices. -/
private lemma fourFoldQuotientMeshVertex_card :
    Fintype.card FourFoldQuotientMeshVertex = 34 := by
  -- The four eight-element interior rows, eight paired boundary controls, and two poles
  -- contribute `4 * 8 + 2` quotient controls.
  decide

/-- Helper for Exercise 74.4: the degree-three subdivision has 72 triangular faces. -/
private lemma fourFoldSourceMeshFace_card :
    Fintype.card FourFoldSourceMeshFace = 72 := by
  -- Each of the eight fan sectors contains nine small triangles.
  decide

/-- Helper for Exercise 74.4: corresponding first boundary controls on a paired edge have
the same quotient-control index. -/
private lemma fourFoldSourceToQuotientVertex_boundaryFirst_eq
    (i j : Fin 8) (hpair : i.1 / 2 = j.1 / 2) :
    fourFoldSourceToQuotientVertex (.boundaryFirst i) =
      fourFoldSourceToQuotientVertex (.boundaryFirst j) := by
  -- The quotient index remembers only the edge-pair number and the control position.
  simp only [fourFoldSourceToQuotientVertex]
  rw [hpair]

/-- Helper for Exercise 74.4: corresponding second boundary controls on a paired edge have
the same quotient-control index. -/
private lemma fourFoldSourceToQuotientVertex_boundarySecond_eq
    (i j : Fin 8) (hpair : i.1 / 2 = j.1 / 2) :
    fourFoldSourceToQuotientVertex (.boundarySecond i) =
      fourFoldSourceToQuotientVertex (.boundarySecond j) := by
  -- The same edge-pair calculation applies to the second trisection point.
  simp only [fourFoldSourceToQuotientVertex]
  rw [hpair]

/-- Helper for Exercise 74.4: all outer octagon vertices have the same quotient-control
index. -/
private lemma fourFoldSourceToQuotientVertex_outer_eq (i j : Fin 8) :
    fourFoldSourceToQuotientVertex (.outer i) =
      fourFoldSourceToQuotientVertex (.outer j) := by
  -- The quotient mesh has one common image for every polygon vertex.
  rfl

/-- Helper for Exercise 74.4: a first boundary-control vertex realizes the first
trisection point of its octagon edge. -/
private lemma fourFoldSourceMeshPoint_boundaryFirst (i : Fin 8) :
    fourFoldSourceMeshPoint (.boundaryFirst i) =
      (polygon 4 (Nat.one_lt_succ_succ 2)).boundaryToRegion
        ((polygon 4 (Nat.one_lt_succ_succ 2)).edgePoint i oneThird) := by
  -- At radial parameter one, the fan parameterization is its selected boundary point.
  apply Subtype.ext
  rw [fourFoldSourceMeshPoint, fourFoldSourceMeshParameter,
    (polygon 4 (Nat.one_lt_succ_succ 2)).boundaryToRegion_coe]
  exact (polygon 4 (Nat.one_lt_succ_succ 2)).fanParameterization_radial_one
    fourFoldPolygonCenter i oneThird

/-- Helper for Exercise 74.4: a second boundary-control vertex realizes the second
trisection point of its octagon edge. -/
private lemma fourFoldSourceMeshPoint_boundarySecond (i : Fin 8) :
    fourFoldSourceMeshPoint (.boundarySecond i) =
      (polygon 4 (Nat.one_lt_succ_succ 2)).boundaryToRegion
        ((polygon 4 (Nat.one_lt_succ_succ 2)).edgePoint i twoThirds) := by
  -- The same endpoint formula evaluates the second control on the polygon boundary.
  apply Subtype.ext
  rw [fourFoldSourceMeshPoint, fourFoldSourceMeshParameter,
    (polygon 4 (Nat.one_lt_succ_succ 2)).boundaryToRegion_coe]
  exact (polygon 4 (Nat.one_lt_succ_succ 2)).fanParameterization_radial_one
    fourFoldPolygonCenter i twoThirds

/-- Helper for Exercise 74.4: paired first boundary controls have equal images in the
four-fold projective plane. -/
private lemma quotientMap_fourFoldSourceMeshPoint_boundaryFirst_eq
    (i j : Fin 8) (hpair : i.1 / 2 = j.1 / 2) :
    quotientMap 4 (Nat.one_lt_succ_succ 2)
        (fourFoldSourceMeshPoint (.boundaryFirst i)) =
      quotientMap 4 (Nat.one_lt_succ_succ 2)
        (fourFoldSourceMeshPoint (.boundaryFirst j)) := by
  -- Evaluate the mesh controls on their edges, then use equality of the edge labels.
  rw [fourFoldSourceMeshPoint_boundaryFirst,
    fourFoldSourceMeshPoint_boundaryFirst]
  apply quotientMap_edgePoint_eq_of_label_eq
  simp only [pasting, boundaryLetter]
  omega

/-- Helper for Exercise 74.4: paired second boundary controls have equal images in the
four-fold projective plane. -/
private lemma quotientMap_fourFoldSourceMeshPoint_boundarySecond_eq
    (i j : Fin 8) (hpair : i.1 / 2 = j.1 / 2) :
    quotientMap 4 (Nat.one_lt_succ_succ 2)
        (fourFoldSourceMeshPoint (.boundarySecond i)) =
      quotientMap 4 (Nat.one_lt_succ_succ 2)
        (fourFoldSourceMeshPoint (.boundarySecond j)) := by
  -- The second trisection controls use the same paired-edge quotient computation.
  rw [fourFoldSourceMeshPoint_boundarySecond,
    fourFoldSourceMeshPoint_boundarySecond]
  apply quotientMap_edgePoint_eq_of_label_eq
  simp only [pasting, boundaryLetter]
  omega

/-- Helper for Exercise 74.4: the canonical finite number of a quotient-mesh vertex. -/
private def fourFoldQuotientMeshVertexNumber :
    FourFoldQuotientMeshVertex → Fin 34
  | .center => 0
  | .innerRay i => Fin.ofNat 34 (1 + i)
  | .outerRay i => Fin.ofNat 34 (9 + i)
  | .panel i => Fin.ofNat 34 (17 + i)
  | .boundary pair second =>
      Fin.ofNat 34 (25 + 2 * pair + if second then 1 else 0)
  | .outer => 33

/-- Helper for Exercise 74.4: an exact integer control table for the quotient triangulation
in three-dimensional Euclidean coordinates. -/
private def fourFoldTargetControlTable : Fin 34 → Fin 3 → ℤ := ![
  ![944, 3492, -5471],
  ![-6196, -5118, -2933],
  ![1700, -3052, 1687],
  ![-8231, -10341, 7486],
  ![11433, 3291, -6009],
  ![-4202, 1897, 2275],
  ![2206, -5006, -6038],
  ![2283, 1518, -7975],
  ![3899, 6757, -2387],
  ![1439, -5842, -9792],
  ![9061, -5755, 656],
  ![-4340, -5756, -6989],
  ![-10506, -10229, -11820],
  ![-10823, -3602, -3541],
  ![4504, 3121, 3046],
  ![4326, -4019, 4365],
  ![9649, 2973, 3043],
  ![-1467, 461, -4488],
  ![9924, 6436, 220],
  ![-4183, 2842, -554],
  ![-2443, 6015, 1672],
  ![1023, -5799, -6398],
  ![4417, -1619, 5601],
  ![9560, 3195, -9989],
  ![4096, -1014, 4580],
  ![-727, 3957, -7652],
  ![3920, 446, 2925],
  ![3716, 7718, -7755],
  ![-12374, -6109, -3096],
  ![-11652, 2370, 9833],
  ![4158, -3128, -6813],
  ![-2012, -7846, 4196],
  ![-8494, -8058, 3346],
  ![9062, 2404, 6667]
]

/-- Helper for Exercise 74.4: the integer target control assigned to a quotient-mesh
vertex. -/
private def fourFoldTargetControl
    (v : FourFoldQuotientMeshVertex) : Fin 3 → ℤ :=
  fourFoldTargetControlTable (fourFoldQuotientMeshVertexNumber v)

/-- Helper for Exercise 74.4: the quotient vertex occupying a given corner of a source
mesh face. -/
private def fourFoldQuotientFaceVertex
    (face : FourFoldSourceMeshFace) (corner : Fin 3) :
    FourFoldQuotientMeshVertex :=
  fourFoldSourceToQuotientVertex (fourFoldSourceMeshFaceVertices face corner)

/-- Helper for Exercise 74.4: subtraction of integer three-dimensional control vectors. -/
private def fourFoldControlSub (a b : Fin 3 → ℤ) : Fin 3 → ℤ :=
  fun i ↦ a i - b i

/-- Helper for Exercise 74.4: the signed volume of three integer control vectors. -/
private def fourFoldControlDet (a b c : Fin 3 → ℤ) : ℤ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) -
    a 1 * (b 0 * c 2 - b 2 * c 0) +
      a 2 * (b 0 * c 1 - b 1 * c 0)

/-- Helper for Exercise 74.4: casting an exact integer control determinant agrees with
the real determinant used by the positive-cone theorem. -/
private lemma fourFoldControlDet_cast (a b c : Fin 3 → ℤ) :
    (fourFoldControlDet a b c : ℝ) =
      FourFoldFanPL.det3 (fun i ↦ a i) (fun i ↦ b i) (fun i ↦ c i) := by
  -- Push the integer cast through the explicit determinant formula to reach the support API.
  simp only [fourFoldControlDet, FourFoldFanPL.det3_apply, Int.cast_add, Int.cast_sub,
    Int.cast_mul]

/-- Helper for Exercise 74.4: every target triangle has two linearly independent edge
vectors. -/
private abbrev fourFoldControlTriangleNondegenerate
    (face : FourFoldSourceMeshFace) : Prop :=
  let a := fourFoldTargetControl (fourFoldQuotientFaceVertex face 0)
  let b := fourFoldTargetControl (fourFoldQuotientFaceVertex face 1)
  let c := fourFoldTargetControl (fourFoldQuotientFaceVertex face 2)
  let u := fourFoldControlSub b a
  let w := fourFoldControlSub c a
  u 0 * w 1 - u 1 * w 0 ≠ 0 ∨
    u 0 * w 2 - u 2 * w 0 ≠ 0 ∨
      u 1 * w 2 - u 2 * w 1 ≠ 0

/-- Helper for Exercise 74.4: two quotient faces have only the displayed vertex in
common. -/
private abbrev fourFoldFacesMeetOnlyAt
    (face other : FourFoldSourceMeshFace) (v : FourFoldQuotientMeshVertex) : Prop :=
  ∀ i j : Fin 3,
    fourFoldQuotientFaceVertex face i = fourFoldQuotientFaceVertex other j →
      fourFoldQuotientFaceVertex face i = v

/-- Helper for Exercise 74.4: the two vertices of a triangular face other than a selected
corner. -/
private def fourFoldOtherFaceVertex
    (face : FourFoldSourceMeshFace) (corner : Fin 3) :
    Fin 2 → FourFoldQuotientMeshVertex :=
  match corner.1 with
  | 0 => ![fourFoldQuotientFaceVertex face 1, fourFoldQuotientFaceVertex face 2]
  | 1 => ![fourFoldQuotientFaceVertex face 0, fourFoldQuotientFaceVertex face 2]
  | _ => ![fourFoldQuotientFaceVertex face 0, fourFoldQuotientFaceVertex face 1]

/-- Helper for Exercise 74.4: the four signed maximal minors controlling intersection of
two triangular cones at a common vertex. -/
private def fourFoldLinkCofactor
    (face other : FourFoldSourceMeshFace) (corner otherCorner : Fin 3) : Fin 4 → ℤ :=
  let v := fourFoldTargetControl (fourFoldQuotientFaceVertex face corner)
  let u := fourFoldControlSub
    (fourFoldTargetControl (fourFoldOtherFaceVertex face corner 0)) v
  let w := fourFoldControlSub
    (fourFoldTargetControl (fourFoldOtherFaceVertex face corner 1)) v
  let x := fourFoldControlSub
    (fourFoldTargetControl (fourFoldOtherFaceVertex other otherCorner 0)) v
  let y := fourFoldControlSub
    (fourFoldTargetControl (fourFoldOtherFaceVertex other otherCorner 1)) v
  -- Route correction: these are the cofactors of `[u,w,-x,-y]`; the previous last
  -- three signs did not describe a kernel vector of that matrix.
  ![-fourFoldControlDet w x y, fourFoldControlDet u x y,
    fourFoldControlDet u w y, -fourFoldControlDet u w x]

/-- Helper for Exercise 74.4: the exact integer link cofactors cast to the corrected real
cofactors used by the positive-cone theorem. -/
private lemma fourFoldLinkCofactor_cast
    (face other : FourFoldSourceMeshFace) (corner otherCorner : Fin 3) :
    let v := fourFoldTargetControl (fourFoldQuotientFaceVertex face corner)
    let u := fourFoldControlSub
      (fourFoldTargetControl (fourFoldOtherFaceVertex face corner 0)) v
    let w := fourFoldControlSub
      (fourFoldTargetControl (fourFoldOtherFaceVertex face corner 1)) v
    let x := fourFoldControlSub
      (fourFoldTargetControl (fourFoldOtherFaceVertex other otherCorner 0)) v
    let y := fourFoldControlSub
      (fourFoldTargetControl (fourFoldOtherFaceVertex other otherCorner 1)) v
    ∀ i, (fourFoldLinkCofactor face other corner otherCorner i : ℝ) =
      FourFoldFanPL.correctedCofactors
        (fun j ↦ u j) (fun j ↦ w j) (fun j ↦ x j) (fun j ↦ y j) i := by
  -- Evaluate the four finite indices and rewrite each integer determinant through the
  -- propositional cast bridge.
  dsimp only
  intro i
  fin_cases i <;>
    simp [fourFoldLinkCofactor, FourFoldFanPL.correctedCofactors_zero,
      FourFoldFanPL.correctedCofactors_one, FourFoldFanPL.correctedCofactors_two,
      FourFoldFanPL.correctedCofactors_three, fourFoldControlDet_cast]

/-- Helper for Exercise 74.4: nonadjacent target link edges span cones meeting only at
their common vertex. -/
private abbrev fourFoldLinkConesSeparated
    (face other : FourFoldSourceMeshFace) (corner otherCorner : Fin 3) : Prop :=
  let k := fourFoldLinkCofactor face other corner otherCorner
  (∀ i, k i ≠ 0) ∧ ¬ (∀ i, 0 < k i) ∧ ¬ (∀ i, k i < 0)

/-- Helper for Exercise 74.4: an exact separated-link certificate rules out a nonzero
intersection of the corresponding real positive cones. -/
private lemma fourFoldLinkConesSeparated_noPositiveConeIntersection
    (face other : FourFoldSourceMeshFace) (corner otherCorner : Fin 3)
    (hseparated : fourFoldLinkConesSeparated face other corner otherCorner)
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    let v := fourFoldTargetControl (fourFoldQuotientFaceVertex face corner)
    let u := fourFoldControlSub
      (fourFoldTargetControl (fourFoldOtherFaceVertex face corner 0)) v
    let w := fourFoldControlSub
      (fourFoldTargetControl (fourFoldOtherFaceVertex face corner 1)) v
    let x := fourFoldControlSub
      (fourFoldTargetControl (fourFoldOtherFaceVertex other otherCorner 0)) v
    let y := fourFoldControlSub
      (fourFoldTargetControl (fourFoldOtherFaceVertex other otherCorner 1)) v
    a • (fun j ↦ (u j : ℝ)) + b • (fun j ↦ (w j : ℝ)) =
        c • (fun j ↦ (x j : ℝ)) + d • (fun j ↦ (y j : ℝ)) →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  -- Normalize the finite predicate and use its cast bridge to supply the three semantic
  -- sign conditions of the real cone theorem.
  dsimp only
  intro hlinear
  dsimp only [fourFoldLinkConesSeparated] at hseparated
  apply FourFoldFanPL.mixedCofactors_noPositiveConeIntersection _ _ _ _
    a b c d ha hb hc hd
  · intro i
    rw [← fourFoldLinkCofactor_cast face other corner otherCorner i]
    exact_mod_cast hseparated.1 i
  · intro hallPositive
    apply hseparated.2.1
    intro i
    have hi := hallPositive i
    rw [← fourFoldLinkCofactor_cast face other corner otherCorner i] at hi
    exact_mod_cast hi
  · intro hallNegative
    apply hseparated.2.2
    intro i
    have hi := hallNegative i
    rw [← fourFoldLinkCofactor_cast face other corner otherCorner i] at hi
    exact_mod_cast hi
  · exact hlinear

/-- Helper for Exercise 74.4: the exact control table is nondegenerate on faces and has
embedded cyclic links at every quotient vertex. -/
private abbrev FourFoldControlTableHasEmbeddedLinks : Prop :=
  (∀ face : FourFoldSourceMeshFace,
      fourFoldControlTriangleNondegenerate face) ∧
    ∀ (face other : FourFoldSourceMeshFace) (corner otherCorner : Fin 3),
      fourFoldQuotientFaceVertex face corner =
          fourFoldQuotientFaceVertex other otherCorner →
        fourFoldFacesMeetOnlyAt face other
            (fourFoldQuotientFaceVertex face corner) →
          fourFoldLinkConesSeparated face other corner otherCorner

/-- Helper for Exercise 74.4: every face in the proposed integer control table is
nondegenerate. -/
private lemma fourFoldControlTable_hasNondegenerateFaces :
    ∀ face : FourFoldSourceMeshFace,
      fourFoldControlTriangleNondegenerate face := by
  -- Evaluate all 72 pairs of edge vectors using exact integer arithmetic.
  native_decide

/-- Helper for Exercise 74.4: the proposed integer control table does not satisfy the
full embedded-link certificate. -/
private lemma fourFoldControlTable_not_hasEmbeddedLinks :
    ¬ FourFoldControlTableHasEmbeddedLinks := by
  -- Route correction: exact evaluation exposes failed nonadjacent link-cone pairs, so the
  -- old certificate claim was false and the affected links must be subdivided or replaced.
  native_decide
 
/-- Helper for Exercise 74.4: exact integer controls for vertices 0 through 17 of the
certified Klein-bottle mesh. -/
private def standardKleinControlBlock0 : Fin 18 → Fin 3 → ℤ := ![
  ![-88024592029238160, -1414213562372095100, -6775740164562613000],
  ![1369514937044257000, -707106781182547500, -6850782940166012000],
  ![1369514937045257000, 707106781195547500, -6850782940147012000],
  ![-88024592026238160, 1414213562389095100, -6775740164499613000],
  ![-1506027127608505300, 707106781211547500, -6769177470330078000],
  ![-1506027127607505300, -707106781150547500, -6769177470239078000],
  ![21339045465979244, -1999999999951000000, -6891242919012535000],
  ![-478820663415506400, -448287736020026670, -5581223422795117000],
  ![1950000000008999700, -999999999919000000, -7014805769924953000],
  ![-301712263905973200, 100000000, -5370346078496330000],
  ![1950000000010999700, 1000000000121000000, -7014805769322953000],
  ![-478820663411506400, 448287736228026670, -5581223421579117000],
  ![21339045471979244, 2000000000169000000, -6891242917158535000],
  ![-948258700011852600, 448287736280026700, -5803409070572558000],
  ![-1895571759488477600, 1000000000225000000, -6747328208615511000],
  ![-1205766911462023800, 256000000, -5875029853824248000],
  ![-1895571759486477600, -999999999711000000, -6747328207077511000],
  ![-948258700007852600, -448287735760026700, -5803409067484558000]
]

/-- Helper for Exercise 74.4: exact integer controls for vertices 18 through 35 of the
certified Klein-bottle mesh. -/
private def standardKleinControlBlock1 : Fin 18 → Fin 3 → ℤ := ![
  ![-3833904499980998700, -1414213562012095100, -287685838049556200],
  ![-2773244328200177300, -707106780786547500, 324686598787237600],
  ![-2773244328199177300, 707106781627547500, 324686600048237600],
  ![-3833904499977998700, 1414213562857095100, -287685834260556200],
  ![-4894564671756820000, 707106781715547500, -900058268437350900],
  ![-4894564671755820000, -707106780610547500, -900058266780350900],
  ![-3499999999974999000, -1999999999375000000, -866025388159439300],
  ![-2275856131931986000, -448287735408026670, -2468666671226055000],
  ![-1999999999972999600, -999999999271000000, 19683000000],
  ![-2051712263887973000, 784000000, -2339257144298795000],
  ![-1999999999970999600, 1000000000841000000, 24389000000],
  ![-2275856131927986000, 448287736984026670, -2468666661802055600],
  ![-3499999999968999000, 2000000000961000000, -866025373993439300],
  ![-2724143868010012700, 448287737108026700, -2727485701136576400],
  ![-4999999999967000000, 1000000001089000000, -1732050771631877200],
  ![-2948287736050026000, 1156000000, -2856895217151836000],
  ![-4999999999965000000, -999999998775000000, -1732050764693877200],
  ![-2724143868006012300, -448287734788026700, -2727485687248577000]
]

/-- Helper for Exercise 74.4: exact integer controls for vertices 36 through 53 of the
certified Klein-bottle mesh. -/
private def standardKleinControlBlock2 : Fin 18 → Fin 3 → ℤ := ![
  ![-5823950815902522000, -1414213561004095100, 3464101665790754000],
  ![-6617709530486871000, -707106779742547500, 2239356798618165400],
  ![-6617709530485871000, 707106782707547500, 2239356803065165400],
  ![-5823950815899522000, 1414213563973095100, 3464101679137754000],
  ![-5109266088291631000, 707106782867547500, 4688846555450343000],
  ![-5109266088290631000, -707106779422547500, 4688846560617343000],
  ![-5978660954498020000, -1999999998151000000, 3427141383724780500],
  ![-4594070937024960000, -448287734148026670, 3205282655219233000],
  ![-7049999999955000000, -999999997975000000, 1818653439072321500],
  ![-4499999999953999000, 2116000000, 2946463622268713000],
  ![-7049999999953000000, 1000000002209000000, 1818653451770321500],
  ![-4594070937020960000, 448287738388026670, 3205282680627233000],
  ![-5978660954492020000, 2000000002401000000, 3427141421866780500],
  ![-4551770335982320500, 448287738584026700, 3722920785240275000],
  ![-4895571759452477000, 1000000002601000000, 5015277537072633000],
  ![-4485041649160004000, 2704000000, 3981739845950795000],
  ![-4895571759450477000, -999999997191000000, 5015277553298633000],
  ![-4551770335978320500, -448287733168026700, 3722920817704275000]
]

/-- Helper for Exercise 74.4: exact integer controls for vertices 54 through 71 of the
certified Klein-bottle mesh. -/
private def standardKleinControlBlock3 : Fin 18 → Fin 3 → ℤ := ![
  ![1667809000055000000, -1414213559348095100, 3464101781512753000],
  ![1667809000055999200, -707106778050547500, 2239356919362164600],
  ![1667809000056999200, 707106784435547500, 2239356928939164600],
  ![1667809000058000000, 1414213565737095100, 3464101810249753000],
  ![1667809000058999200, 707106784667547500, 4688846691908342000],
  ![1667809000059999200, -707106777586547500, 4688846702529342000],
  ![1000000000060999100, -1999999996279000000, 3464101842118754000],
  ![-999999999938000000, -448287732240026670, 3205282808363232800],
  ![1000000000062999100, -999999996031000000, 1732051057615877000],
  ![-999999999935999600, 4096000000, 2946463787076712500],
  ![1000000000064999100, 1000000004225000000, 1732051082193877000],
  ![-999999999934000400, 448287740440026670, 3205282857531232800],
  ![1000000000066999100, 2000000004489000000, 3464101915900754000],
  ![-999999999932000000, 448287740708026700, 3722920974672274700],
  ![1000000000068999100, 1000000004761000000, 5196152751215631000],
  ![-999999999929999600, 4900000000, 3981740048342794500],
  ![1000000000070999100, -999999994959000000, 5196152780617631000],
  ![-999999999928000400, -448287730900026700, 3722921033488274700]
]

/-- Helper for Exercise 74.4: exact integer controls for vertices 72 through 89 of the
certified Klein-bottle mesh. -/
private def standardKleinControlBlock4 : Fin 18 → Fin 3 → ℤ := ![
  ![5911975408042761000, -1414213557044095100, 3311638938442859300],
  ![5248194593556614000, -707106775710547500, 4611426601651846000],
  ![5248194593557614000, 707106786811547500, 4611426618302846000],
  ![5911975408045761000, 1414213568149095100, 3311638988401859300],
  ![6615293216023136000, 707106787115547500, 2080331440458734700],
  ![6615293216024136000, -707106775102547500, 2080331458477734700],
  ![5957321909161041000, -1999999993759000000, 3464102108176754400],
  ![5072891600572466000, -448287729684026670, 2375941365271883800],
  ![5100000000081000000, -999999993439000000, 5196152954147632000],
  ![4801712263997973000, 6724000000, 2423883105931617000],
  ![5100000000083000000, 1000000006889000000, 5196152994493632000],
  ![5072891600576466000, 448287743140026670, 2375941445975883800],
  ![5957321909167041000, 2000000007225000000, 3464102229262754400],
  ![5500029036144174000, 448287743480026700, 2080489049132283300],
  ![6791143519093955000, 1000000007569000000, 1732051466071877600],
  ![5690808560778027000, 7744000000, 1893290834049453000],
  ![6791143519095955000, -999999992079000000, 1732051512537877600],
  ![5500029036148174000, -448287727984026700, 2080489142076283300]
]

/-- Helper for Exercise 74.4: exact integer controls for vertices 90 through 107 of the
certified Klein-bottle mesh. -/
private def standardKleinControlBlock5 : Fin 18 → Fin 3 → ℤ := ![
  ![2166095500091000000, -1414213554092095100, -3176415016658197000],
  ![1105435328312179000, -707106772722547500, -2564042555845402600],
  ![1105435328313179000, 707106789835547500, -2564042530176402600],
  ![2166095500094000000, 1414213571209095100, -3176414939645197000],
  ![3226755671874821000, 707106790211547500, -3788787348549991000],
  ![3226755671875821000, -707106771970547500, -3788787321188991000],
  ![2500000000097000000, -1999999990591000000, -2598075298680315000],
  ![3275856132055986000, -448287726480026670, -736614940041177600],
  ![1000000000098999800, -999999990199000000, -1732049837269876700],
  ![3051712264015973000, 10000000000, -607205358681917600],
  ![1000000000100999800, 1000000010201000000, -1732049777267876700],
  ![3275856132059986000, 448287746488026670, -736614820025177100],
  ![2500000000103000000, 2000000010609000000, -2598075118626315000],
  ![3724143868146013600, 448287746900026700, -995433801471698300],
  ![4000000000104999600, 1000000011025000000, -3464100457512754000],
  ![3948287736190025400, 11236000000, -1124843257870959000],
  ![4000000000106999600, -999999988551000000, -3464100390094754000],
  ![3724143868150014000, -448287724420026700, -995433666623697900]
]

/-- Helper for Exercise 74.4: the exact perturbed integer control of every vertex in the
certified Klein-bottle mesh. -/
private def standardKleinControl (vertex : Fin 108) : Fin 3 → ℤ :=
  match vertex.1 / 18 with
  | 0 => standardKleinControlBlock0 (Fin.ofNat 18 vertex)
  | 1 => standardKleinControlBlock1 (Fin.ofNat 18 vertex)
  | 2 => standardKleinControlBlock2 (Fin.ofNat 18 vertex)
  | 3 => standardKleinControlBlock3 (Fin.ofNat 18 vertex)
  | 4 => standardKleinControlBlock4 (Fin.ofNat 18 vertex)
  | _ => standardKleinControlBlock5 (Fin.ofNat 18 vertex)

/-- Helper for Exercise 74.4: triangle incidences 0 through 35 of the certified
Klein-bottle mesh. -/
private def standardKleinFaceBlock0 : Fin 36 → Fin 3 → Fin 108 := ![
  ![6, 8, 7],
  ![42, 44, 43],
  ![78, 80, 79],
  ![8, 10, 9],
  ![44, 46, 45],
  ![80, 82, 81],
  ![10, 12, 11],
  ![46, 48, 47],
  ![82, 84, 83],
  ![12, 14, 13],
  ![48, 50, 49],
  ![84, 86, 85],
  ![14, 16, 15],
  ![50, 52, 51],
  ![86, 88, 87],
  ![16, 6, 17],
  ![52, 42, 53],
  ![88, 78, 89],
  ![6, 7, 0],
  ![42, 43, 36],
  ![78, 79, 72],
  ![8, 9, 1],
  ![44, 45, 37],
  ![80, 81, 73],
  ![10, 11, 2],
  ![46, 47, 38],
  ![82, 83, 74],
  ![12, 13, 3],
  ![48, 49, 39],
  ![84, 85, 75],
  ![14, 15, 4],
  ![50, 51, 40],
  ![86, 87, 76],
  ![16, 17, 5],
  ![52, 53, 41],
  ![88, 89, 77]
]

/-- Helper for Exercise 74.4: triangle incidences 36 through 71 of the certified
Klein-bottle mesh. -/
private def standardKleinFaceBlock1 : Fin 36 → Fin 3 → Fin 108 := ![
  ![6, 17, 0],
  ![42, 53, 36],
  ![78, 89, 72],
  ![8, 7, 1],
  ![44, 43, 37],
  ![80, 79, 73],
  ![10, 9, 2],
  ![46, 45, 38],
  ![82, 81, 74],
  ![12, 11, 3],
  ![48, 47, 39],
  ![84, 83, 75],
  ![14, 13, 4],
  ![50, 49, 40],
  ![86, 85, 76],
  ![16, 15, 5],
  ![52, 51, 41],
  ![88, 87, 77],
  ![24, 26, 25],
  ![60, 62, 61],
  ![96, 98, 97],
  ![26, 28, 27],
  ![62, 64, 63],
  ![98, 100, 99],
  ![28, 30, 29],
  ![64, 66, 65],
  ![100, 102, 101],
  ![30, 32, 31],
  ![66, 68, 67],
  ![102, 104, 103],
  ![32, 34, 33],
  ![68, 70, 69],
  ![104, 106, 105],
  ![34, 24, 35],
  ![70, 60, 71],
  ![106, 96, 107]
]

/-- Helper for Exercise 74.4: triangle incidences 72 through 107 of the certified
Klein-bottle mesh. -/
private def standardKleinFaceBlock2 : Fin 36 → Fin 3 → Fin 108 := ![
  ![24, 25, 18],
  ![60, 61, 54],
  ![96, 97, 90],
  ![26, 27, 19],
  ![62, 63, 55],
  ![98, 99, 91],
  ![28, 29, 20],
  ![64, 65, 56],
  ![100, 101, 92],
  ![30, 31, 21],
  ![66, 67, 57],
  ![102, 103, 93],
  ![32, 33, 22],
  ![68, 69, 58],
  ![104, 105, 94],
  ![34, 35, 23],
  ![70, 71, 59],
  ![106, 107, 95],
  ![24, 35, 18],
  ![60, 71, 54],
  ![96, 107, 90],
  ![26, 25, 19],
  ![62, 61, 55],
  ![98, 97, 91],
  ![28, 27, 20],
  ![64, 63, 56],
  ![100, 99, 92],
  ![30, 29, 21],
  ![66, 65, 57],
  ![102, 101, 93],
  ![32, 31, 22],
  ![68, 67, 58],
  ![104, 103, 94],
  ![34, 33, 23],
  ![70, 69, 59],
  ![106, 105, 95]
]

/-- Helper for Exercise 74.4: triangle incidences 108 through 143 of the certified
Klein-bottle mesh. -/
private def standardKleinFaceBlock3 : Fin 36 → Fin 3 → Fin 108 := ![
  ![6, 8, 106],
  ![6, 106, 96],
  ![42, 44, 34],
  ![42, 34, 24],
  ![78, 80, 70],
  ![78, 70, 60],
  ![8, 10, 104],
  ![8, 104, 106],
  ![44, 46, 32],
  ![44, 32, 34],
  ![80, 82, 68],
  ![80, 68, 70],
  ![10, 12, 102],
  ![10, 102, 104],
  ![46, 48, 30],
  ![46, 30, 32],
  ![82, 84, 66],
  ![82, 66, 68],
  ![12, 14, 100],
  ![12, 100, 102],
  ![48, 50, 28],
  ![48, 28, 30],
  ![84, 86, 64],
  ![84, 64, 66],
  ![14, 16, 98],
  ![14, 98, 100],
  ![50, 52, 26],
  ![50, 26, 28],
  ![86, 88, 62],
  ![86, 62, 64],
  ![16, 6, 96],
  ![16, 96, 98],
  ![52, 42, 24],
  ![52, 24, 26],
  ![88, 78, 60],
  ![88, 60, 62]
]

/-- Helper for Exercise 74.4: triangle incidences 144 through 179 of the certified
Klein-bottle mesh. -/
private def standardKleinFaceBlock4 : Fin 36 → Fin 3 → Fin 108 := ![
  ![0, 18, 25],
  ![0, 25, 7],
  ![36, 54, 61],
  ![36, 61, 43],
  ![72, 90, 97],
  ![72, 97, 79],
  ![1, 19, 27],
  ![1, 27, 9],
  ![37, 55, 63],
  ![37, 63, 45],
  ![73, 91, 99],
  ![73, 99, 81],
  ![2, 20, 29],
  ![2, 29, 11],
  ![38, 56, 65],
  ![38, 65, 47],
  ![74, 92, 101],
  ![74, 101, 83],
  ![3, 21, 31],
  ![3, 31, 13],
  ![39, 57, 67],
  ![39, 67, 49],
  ![75, 93, 103],
  ![75, 103, 85],
  ![4, 22, 33],
  ![4, 33, 15],
  ![40, 58, 69],
  ![40, 69, 51],
  ![76, 94, 105],
  ![76, 105, 87],
  ![5, 23, 35],
  ![5, 35, 17],
  ![41, 59, 71],
  ![41, 71, 53],
  ![77, 95, 107],
  ![77, 107, 89]
]

/-- Helper for Exercise 74.4: triangle incidences 180 through 215 of the certified
Klein-bottle mesh. -/
private def standardKleinFaceBlock5 : Fin 36 → Fin 3 → Fin 108 := ![
  ![0, 18, 35],
  ![0, 35, 17],
  ![36, 54, 71],
  ![36, 71, 53],
  ![72, 90, 107],
  ![72, 107, 89],
  ![1, 19, 25],
  ![1, 25, 7],
  ![37, 55, 61],
  ![37, 61, 43],
  ![73, 91, 97],
  ![73, 97, 79],
  ![2, 20, 27],
  ![2, 27, 9],
  ![38, 56, 63],
  ![38, 63, 45],
  ![74, 92, 99],
  ![74, 99, 81],
  ![3, 21, 29],
  ![3, 29, 11],
  ![39, 57, 65],
  ![39, 65, 47],
  ![75, 93, 101],
  ![75, 101, 83],
  ![4, 22, 31],
  ![4, 31, 13],
  ![40, 58, 67],
  ![40, 67, 49],
  ![76, 94, 103],
  ![76, 103, 85],
  ![5, 23, 33],
  ![5, 33, 15],
  ![41, 59, 69],
  ![41, 69, 51],
  ![77, 95, 105],
  ![77, 105, 87]
]

/-- Helper for Exercise 74.4: the three vertices of every triangle in the certified
Klein-bottle mesh. -/
private def standardKleinFace (face : Fin 216) : Fin 3 → Fin 108 :=
  match face.1 / 36 with
  | 0 => standardKleinFaceBlock0 (Fin.ofNat 36 face)
  | 1 => standardKleinFaceBlock1 (Fin.ofNat 36 face)
  | 2 => standardKleinFaceBlock2 (Fin.ofNat 36 face)
  | 3 => standardKleinFaceBlock3 (Fin.ofNat 36 face)
  | 4 => standardKleinFaceBlock4 (Fin.ofNat 36 face)
  | _ => standardKleinFaceBlock5 (Fin.ofNat 36 face)

/-- Helper for Exercise 74.4: the signed volume from a mesh triangle to a fourth control
vertex. -/
private def standardKleinFaceVolume (face : Fin 216) (vertex : Fin 108) : ℤ :=
  let a := standardKleinControl (standardKleinFace face 0)
  let b := standardKleinControl (standardKleinFace face 1)
  let c := standardKleinControl (standardKleinFace face 2)
  fourFoldControlDet (fourFoldControlSub b a) (fourFoldControlSub c a)
    (fourFoldControlSub (standardKleinControl vertex) a)

/-- Helper for Exercise 74.4: a triangle of the exact Klein mesh has nonzero affine area. -/
private abbrev standardKleinFaceNondegenerate (face : Fin 216) : Prop :=
  let a := standardKleinControl (standardKleinFace face 0)
  let b := standardKleinControl (standardKleinFace face 1)
  let c := standardKleinControl (standardKleinFace face 2)
  let u := fourFoldControlSub b a
  let w := fourFoldControlSub c a
  u 0 * w 1 - u 1 * w 0 ≠ 0 ∨
    u 0 * w 2 - u 2 * w 0 ≠ 0 ∨
      u 1 * w 2 - u 2 * w 1 ≠ 0

/-- Helper for Exercise 74.4: two triangles of the exact Klein mesh share an edge. -/
private abbrev standardKleinFacesShareEdge (face other : Fin 216) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧
    ∃ k l : Fin 3,
      standardKleinFace face i = standardKleinFace other k ∧
        standardKleinFace face j = standardKleinFace other l

/-- Helper for Exercise 74.4: the affine planes of two mesh triangles are distinct. -/
private abbrev standardKleinFacesHaveDistinctPlanes (face other : Fin 216) : Prop :=
  ∃ corner : Fin 3,
    standardKleinFaceVolume face (standardKleinFace other corner) ≠ 0

/-- Helper for Exercise 74.4: two mesh triangles meet only at a displayed vertex. -/
private abbrev standardKleinFacesMeetOnlyAt
    (face other : Fin 216) (vertex : Fin 108) : Prop :=
  ∀ i j : Fin 3, standardKleinFace face i = standardKleinFace other j →
    standardKleinFace face i = vertex

/-- Helper for Exercise 74.4: the two vertices of an exact Klein-mesh triangle other than a
selected corner. -/
private def standardKleinOtherFaceVertex
    (face : Fin 216) (corner : Fin 3) : Fin 2 → Fin 108 :=
  match corner.1 with
  | 0 => ![standardKleinFace face 1, standardKleinFace face 2]
  | 1 => ![standardKleinFace face 0, standardKleinFace face 2]
  | _ => ![standardKleinFace face 0, standardKleinFace face 1]

/-- Helper for Exercise 74.4: corrected integer cofactors for two exact Klein-mesh triangles
meeting at selected corners. -/
private def standardKleinLinkCofactor
    (face other : Fin 216) (corner otherCorner : Fin 3) : Fin 4 → ℤ :=
  let vertex := standardKleinControl (standardKleinFace face corner)
  let u := fourFoldControlSub
    (standardKleinControl (standardKleinOtherFaceVertex face corner 0)) vertex
  let w := fourFoldControlSub
    (standardKleinControl (standardKleinOtherFaceVertex face corner 1)) vertex
  let x := fourFoldControlSub
    (standardKleinControl (standardKleinOtherFaceVertex other otherCorner 0)) vertex
  let y := fourFoldControlSub
    (standardKleinControl (standardKleinOtherFaceVertex other otherCorner 1)) vertex
  ![-fourFoldControlDet w x y, fourFoldControlDet u x y,
    fourFoldControlDet u w y, -fourFoldControlDet u w x]

/-- Helper for Exercise 74.4: the two positive link cones have only their common vertex in
common. -/
private abbrev standardKleinLinkSeparated
    (face other : Fin 216) (corner otherCorner : Fin 3) : Prop :=
  let cofactors := standardKleinLinkCofactor face other corner otherCorner
  (∀ i, cofactors i ≠ 0) ∧ ¬ (∀ i, 0 < cofactors i) ∧ ¬ (∀ i, cofactors i < 0)

/-- Helper for Exercise 74.4: a triangle meets the selected attachment triangle. -/
private abbrev standardKleinFaceMeetsAttachment (face : Fin 216) : Prop :=
  ∃ i j : Fin 3, standardKleinFace face i = standardKleinFace 114 j

/-- Helper for Exercise 74.4: the selected attachment triangle strictly supports every
nonattachment vertex in an incident triangle. -/
private abbrev standardKleinAttachmentSupportsFace (face : Fin 216) : Prop :=
  standardKleinFaceMeetsAttachment face →
    ∀ corner : Fin 3,
      (∀ attachmentCorner : Fin 3,
        standardKleinFace face corner ≠ standardKleinFace 114 attachmentCorner) →
      standardKleinFaceVolume 114 (standardKleinFace face corner) < 0

/-- Helper for Exercise 74.4: the exact mesh satisfies the finite local-immersion and
supporting-face conditions needed for the reflected Klein double. -/
private abbrev standardKleinControlConditions : Prop :=
  (∀ face : Fin 216, standardKleinFaceNondegenerate face) ∧
    (∀ (face other : Fin 216), face ≠ other →
      standardKleinFacesShareEdge face other →
        standardKleinFacesHaveDistinctPlanes face other) ∧
    (∀ (face other : Fin 216) (corner otherCorner : Fin 3),
      standardKleinFace face corner = standardKleinFace other otherCorner →
        standardKleinFacesMeetOnlyAt face other (standardKleinFace face corner) →
          standardKleinLinkSeparated face other corner otherCorner) ∧
    ∀ face : Fin 216, standardKleinAttachmentSupportsFace face

/-- Helper for Exercise 74.4: every face of the exact Klein control mesh is nondegenerate. -/
private lemma standardKleinControl_hasNondegenerateFaces :
    ∀ face : Fin 216, standardKleinFaceNondegenerate face := by
  -- Evaluate all 216 exact cross products in the six-block control table.
  native_decide

/-- Helper for Exercise 74.4: edge-adjacent exact Klein-mesh triangles lie in distinct affine
planes. -/
private lemma standardKleinControl_hasDistinctAdjacentPlanes :
    ∀ (face other : Fin 216), face ≠ other →
      standardKleinFacesShareEdge face other →
        standardKleinFacesHaveDistinctPlanes face other := by
  -- Exhaust the finite incidence relation and evaluate the signed fourth-point volumes.
  native_decide

/-- Helper for Exercise 74.4: every pair of exact Klein-mesh triangles meeting only at a vertex
has separated positive link cones. -/
private lemma standardKleinControl_hasSeparatedVertexLinks :
    ∀ (face other : Fin 216) (corner otherCorner : Fin 3),
      standardKleinFace face corner = standardKleinFace other otherCorner →
        standardKleinFacesMeetOnlyAt face other (standardKleinFace face corner) →
          standardKleinLinkSeparated face other corner otherCorner := by
  -- Check the corrected four-cofactor sign criterion on every vertex-only face pair.
  native_decide

/-- Helper for Exercise 74.4: triangle 114 strictly supports all three incident closed vertex
stars away from the attachment triangle. -/
private lemma standardKleinAttachment_strictlySupportsIncidentStars :
    ∀ face : Fin 216, standardKleinAttachmentSupportsFace face := by
  -- Exact signed volumes place every nonattachment star vertex on the same strict side.
  native_decide

/-- Helper for Exercise 74.4: the exact Klein mesh has embedded vertex links and a strictly
supporting attachment face. -/
private lemma standardKleinControlCertificate : standardKleinControlConditions := by
  -- Assemble the independently checked face, edge, link, and supporting-plane certificates.
  exact ⟨standardKleinControl_hasNondegenerateFaces,
    standardKleinControl_hasDistinctAdjacentPlanes,
    standardKleinControl_hasSeparatedVertexLinks,
    standardKleinAttachment_strictlySupportsIncidentStars⟩

/-- Helper for Exercise 74.4: a face retained after deleting the attachment triangle. -/
private abbrev StandardKleinRetainedFace := {face : Fin 216 // face ≠ 114}

/-- Helper for Exercise 74.4: the two tagged copies of every retained Klein-mesh face. -/
private abbrev StandardKleinDoubleFace := Fin 2 × StandardKleinRetainedFace

/-- Helper for Exercise 74.4: the disjoint triangular-cell carrier of the punctured Klein
double. -/
private abbrev StandardKleinDoubleCarrier :=
  StandardKleinDoubleFace × stdSimplex ℝ (Fin 3)

/-- Helper for Exercise 74.4: every retained face of the punctured Klein mesh remains
nondegenerate. -/
private lemma standardKleinRetainedFace_nonDegenerate
    (face : StandardKleinRetainedFace) : standardKleinFaceNondegenerate face := by
  -- Restrict the already certified face statement to the punctured mesh.
  exact standardKleinControlCertificate.1 face

/-- Helper for Exercise 74.4: the three corners of the attachment triangle are distinct. -/
private lemma standardKleinAttachmentFace_injective :
    Function.Injective (standardKleinFace 114) := by
  -- This is the finite incidence check needed to regard face 114 as a genuine triangle.
  native_decide

/-- Helper for Exercise 74.4: face 114 has the three displayed attachment vertices. -/
private lemma standardKleinAttachmentFace_spec :
    standardKleinFace 114 = ![8, 10, 104] := by
  -- Normalize the selected face through the finite six-block incidence table.
  native_decide

/-- Helper for Exercise 74.4: the ordered endpoints of an edge of a standard Klein-mesh
triangle. -/
private def standardKleinFaceEdge (face : Fin 216) : Fin 3 → Fin 2 → Fin 108
  | 0 => ![standardKleinFace face 0, standardKleinFace face 1]
  | 1 => ![standardKleinFace face 1, standardKleinFace face 2]
  | _ => ![standardKleinFace face 2, standardKleinFace face 0]

/-- Helper for Exercise 74.4: the orientation-independent vertex pair of a standard
Klein-mesh edge. -/
private def standardKleinUndirectedEdge (face : Fin 216) (edge : Fin 3) : Fin 108 × Fin 108 :=
  let endpoints := standardKleinFaceEdge face edge
  (min (endpoints 0) (endpoints 1), max (endpoints 0) (endpoints 1))

/-- Helper for Exercise 74.4: all occurrences of a geometric edge in the closed standard
Klein mesh. -/
private def standardKleinEdgeIncidences (face : Fin 216) (edge : Fin 3) :
    Finset (Fin 216 × Fin 3) :=
  Finset.univ.filter fun candidate ↦
    standardKleinUndirectedEdge candidate.1 candidate.2 =
      standardKleinUndirectedEdge face edge

/-- Helper for Exercise 74.4: all occurrences of a geometric edge after deleting the
distinguished attachment face. -/
private def standardKleinRetainedEdgeIncidences
    (face : StandardKleinRetainedFace) (edge : Fin 3) :
    Finset (StandardKleinRetainedFace × Fin 3) :=
  Finset.univ.filter fun candidate ↦
    standardKleinUndirectedEdge candidate.1 candidate.2 =
      standardKleinUndirectedEdge face edge

/-- Helper for Exercise 74.4: the finite incidence conditions needed before cutting the
punctured standard Klein mesh into a fundamental polygon. -/
private abbrev standardKleinPuncturedMeshConditions : Prop :=
  (∀ (face : Fin 216) (edge : Fin 3),
      (standardKleinEdgeIncidences face edge).card = 2) ∧
    (∀ (face : StandardKleinRetainedFace) (edge : Fin 3),
      (standardKleinRetainedEdgeIncidences face edge).card = 1 ↔
        ∃ attachmentEdge : Fin 3,
          standardKleinUndirectedEdge face edge =
            standardKleinUndirectedEdge 114 attachmentEdge) ∧
    (Finset.univ.filter (fun faceEdge : StandardKleinRetainedFace × Fin 3 ↦
      (standardKleinRetainedEdgeIncidences faceEdge.1 faceEdge.2).card = 1)).card = 3 ∧
    (Finset.univ.image (fun faceEdge : Fin 216 × Fin 3 ↦
      standardKleinUndirectedEdge faceEdge.1 faceEdge.2)).card = 324

/-- Helper for Exercise 74.4: the standard Klein table is a closed triangular mesh, and
deleting face 114 exposes precisely its three attachment edges. -/
private lemma standardKleinPuncturedMesh_certificate :
    standardKleinPuncturedMeshConditions := by
  -- Exhaust the finite face-edge table once, recording closed incidence, punctured boundary,
  -- its three boundary edges, and the 324 distinct geometric edges.
  native_decide

/-- Helper for Exercise 74.4: every geometric edge of the closed standard Klein mesh occurs
in exactly two triangle-edge slots. -/
private lemma standardKleinClosedEdgeIncidence
    (face : Fin 216) (edge : Fin 3) :
    (standardKleinEdgeIncidences face edge).card = 2 := by
  -- Project the closed-edge assertion from the unified finite mesh certificate.
  exact standardKleinPuncturedMesh_certificate.1 face edge

/-- Helper for Exercise 74.4: a retained edge becomes boundary exactly when it was paired
with an edge of the deleted attachment triangle. -/
private lemma standardKleinRetainedEdge_boundary_iff
    (face : StandardKleinRetainedFace) (edge : Fin 3) :
    (standardKleinRetainedEdgeIncidences face edge).card = 1 ↔
      ∃ attachmentEdge : Fin 3,
        standardKleinUndirectedEdge face edge =
          standardKleinUndirectedEdge 114 attachmentEdge := by
  -- Project the exact boundary characterization from the same finite certificate.
  exact standardKleinPuncturedMesh_certificate.2.1 face edge

/-- Helper for Exercise 74.4: deleting the attachment triangle leaves exactly three
boundary edge occurrences. -/
private lemma standardKleinRetainedBoundary_card :
    (Finset.univ.filter (fun faceEdge : StandardKleinRetainedFace × Fin 3 ↦
      (standardKleinRetainedEdgeIncidences faceEdge.1 faceEdge.2).card = 1)).card = 3 := by
  -- The third certificate field counts the exposed attachment cycle.
  exact standardKleinPuncturedMesh_certificate.2.2.1

/-- Helper for Exercise 74.4: the standard 216-face Klein mesh has 324 geometric edges. -/
private lemma standardKleinUndirectedEdge_range_card :
    (Finset.univ.image (fun faceEdge : Fin 216 × Fin 3 ↦
      standardKleinUndirectedEdge faceEdge.1 faceEdge.2)).card = 324 := by
  -- The final certificate field counts orientation-independent edge pairs.
  exact standardKleinPuncturedMesh_certificate.2.2.2

/-- Helper for Exercise 74.4: raw breadth-first face indices for the relative cut. -/
private def standardKleinRelativeCutOrderData : Array (Fin 216) := #[
  0, 108, 39, 18, 115, 109, 21, 187, 145, 36, 68, 71,
  138, 3, 151, 186, 144, 15, 181, 107, 86, 92, 89, 139,
  42, 150, 193, 93, 72, 180, 33, 175, 214, 172, 104, 74,
  184, 178, 56, 132, 24, 75, 192, 54, 90, 51, 174, 215,
  208, 173, 65, 148, 185, 179, 95, 12, 133, 6, 157, 57,
  96, 156, 141, 69, 211, 87, 210, 53, 209, 32, 121, 83,
  149, 38, 35, 77, 190, 30, 59, 126, 120, 45, 199, 135,
  78, 134, 140, 111, 169, 105, 14, 50, 167, 166, 101, 20,
  191, 17, 154, 48, 98, 9, 127, 27, 198, 128, 60, 13,
  16, 110, 168, 66, 136, 11, 29, 202, 62, 2, 41, 142,
  155, 205, 80, 196, 163, 99, 162, 10, 129, 52, 31, 37,
  34, 1, 117, 84, 204, 143, 137, 130, 47, 203, 112, 23,
  113, 197, 160, 81, 49, 28, 122, 213, 171, 19, 183, 177,
  40, 116, 102, 55, 58, 131, 8, 161, 119, 5, 70, 44,
  63, 207, 165, 46, 7, 123, 212, 170, 147, 182, 176, 22,
  189, 4, 94, 73, 97, 76, 61, 124, 26, 67, 118, 91,
  88, 206, 164, 201, 25, 106, 85, 146, 153, 188, 43, 79,
  194, 152, 100, 125, 103, 82, 200, 159, 195, 158, 64
]

/-- Helper for Exercise 74.4: a breadth-first ordering of all retained faces, rooted at
face zero, for cutting the punctured Klein mesh along a dual spanning tree. -/
private def standardKleinRelativeCutOrder (rank : Fin 215) : Fin 216 :=
  standardKleinRelativeCutOrderData.getD rank.1 0

/-- Helper for Exercise 74.4: raw parent ranks for the nonroot relative-cut faces. -/
private def standardKleinRelativeCutParentRankData : Array (Fin 215) := #[
  0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 5, 5,
  6, 6, 7, 8, 9, 9, 10, 10, 11, 11, 12, 13,
  14, 14, 15, 16, 16, 17, 18, 19, 20, 20, 21, 21,
  22, 23, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33,
  33, 34, 35, 36, 37, 38, 39, 39, 40, 40, 41, 42,
  42, 43, 44, 45, 46, 46, 47, 48, 49, 50, 50, 51,
  52, 53, 54, 54, 55, 56, 56, 57, 57, 58, 59, 60,
  62, 62, 63, 64, 65, 67, 68, 68, 71, 71, 72, 72,
  73, 75, 77, 78, 79, 79, 81, 82, 83, 84, 85, 86,
  87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98,
  99, 100, 100, 103, 104, 104, 105, 105, 107, 107, 108, 108,
  109, 109, 110, 110, 112, 112, 113, 114, 115, 117, 118, 119,
  120, 122, 125, 127, 127, 128, 129, 130, 131, 131, 132, 133,
  134, 135, 137, 138, 139, 140, 141, 142, 143, 144, 145, 147,
  148, 149, 149, 150, 150, 151, 152, 153, 154, 155, 156, 156,
  157, 159, 159, 160, 160, 161, 161, 162, 164, 164, 166, 166,
  169, 170, 171, 172, 174, 175, 176, 179, 180, 181, 184, 184,
  185, 186, 187, 193, 194, 194, 195, 200, 203, 207
]

/-- Helper for Exercise 74.4: the rank of the parent face for every nonroot face in the
explicit relative cut ordering. -/
private def standardKleinRelativeCutParentRank (child : Fin 214) : Fin 215 :=
  standardKleinRelativeCutParentRankData.getD child.1 0

/-- Helper for Exercise 74.4: raw child-edge slots for the relative-cut tree seams. -/
private def standardKleinRelativeCutChildEdgeData : Array (Fin 3) := #[
  0, 0, 0, 2, 0, 2, 2, 2, 2, 0, 0, 1, 2, 2, 2, 2, 1, 2,
  0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 1, 1, 1, 2, 2, 1,
  1, 0, 1, 2, 1, 2, 1, 2, 2, 2, 0, 0, 0, 1, 1, 0, 0, 0,
  0, 0, 2, 2, 2, 1, 0, 1, 1, 2, 1, 0, 1, 0, 1, 1, 0, 0,
  1, 1, 2, 1, 0, 0, 1, 0, 0, 1, 1, 2, 1, 2, 1, 1, 2, 1,
  1, 1, 1, 2, 1, 1, 1, 1, 2, 0, 0, 0, 2, 2, 1, 2, 0, 0,
  2, 2, 1, 0, 1, 1, 0, 1, 2, 1, 0, 0, 2, 2, 1, 2, 1, 0,
  0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 0, 0, 2, 0, 0, 2, 2,
  1, 1, 2, 0, 0, 1, 2, 2, 2, 2, 2, 0, 2, 2, 0, 0, 0, 1,
  1, 2, 2, 0, 1, 2, 2, 2, 2, 0, 0, 2, 2, 2, 2, 2, 2, 2,
  0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 2, 2, 0, 1, 1,
  2, 2, 2, 0, 2, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0
]

/-- Helper for Exercise 74.4: the edge slot of each nonroot face used by its parent seam. -/
private def standardKleinRelativeCutChildEdge (child : Fin 214) : Fin 3 :=
  standardKleinRelativeCutChildEdgeData.getD child.1 0

/-- Helper for Exercise 74.4: raw parent-edge slots for the relative-cut tree seams. -/
private def standardKleinRelativeCutParentEdgeData : Array (Fin 3) := #[
  0, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 2, 0, 1, 0, 0, 0, 1,
  1, 2, 1, 2, 2, 1, 0, 1, 1, 1, 0, 2, 1, 1, 1, 2, 2, 1,
  1, 1, 2, 2, 1, 0, 0, 2, 2, 0, 2, 0, 2, 0, 1, 2, 2, 1,
  0, 2, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 2, 2, 2, 0, 2, 2,
  2, 2, 2, 1, 2, 1, 2, 0, 1, 1, 0, 2, 2, 0, 0, 1, 2, 0,
  2, 1, 1, 2, 2, 1, 0, 1, 2, 1, 0, 2, 2, 0, 2, 0, 0, 0,
  0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 1, 2, 1, 1, 1, 0,
  0, 2, 1, 2, 1, 2, 0, 1, 1, 0, 1, 2, 0, 2, 2, 0, 2, 1,
  1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 1, 0, 2, 1, 1, 2, 0,
  1, 1, 0, 1, 2, 0, 1, 1, 2, 0, 2, 0, 0, 1, 0, 0, 2, 1,
  0, 1, 2, 1, 2, 1, 2, 2, 1, 0, 1, 2, 0, 0, 1, 2, 1, 1,
  0, 1, 0, 1, 2, 1, 1, 1, 2, 1, 1, 0, 1, 1, 1, 1
]

/-- Helper for Exercise 74.4: the matching parent edge slot for each explicit tree seam. -/
private def standardKleinRelativeCutParentEdge (child : Fin 214) : Fin 3 :=
  standardKleinRelativeCutParentEdgeData.getD child.1 0

/-- Helper for Exercise 74.4: the concrete relative cut is an exact ranked dual tree of the
punctured mesh. -/
private abbrev standardKleinRelativeCutTreeConditions : Prop :=
  Function.Injective standardKleinRelativeCutOrder ∧
    (∀ rank, standardKleinRelativeCutOrder rank ≠ 114) ∧
    (∀ face : Fin 216, face ≠ 114 →
      ∃ rank, standardKleinRelativeCutOrder rank = face) ∧
    ∀ child : Fin 214,
      (standardKleinRelativeCutParentRank child).1 < child.1 + 1 ∧
        standardKleinUndirectedEdge
            (standardKleinRelativeCutOrder
              (standardKleinRelativeCutParentRank child))
              (standardKleinRelativeCutParentEdge child) =
          standardKleinUndirectedEdge
            (standardKleinRelativeCutOrder child.succ)
              (standardKleinRelativeCutChildEdge child)

/-- Helper for Exercise 74.4: the cut order contains no duplicate face. -/
private lemma standardKleinRelativeCutOrder_injective :
    Function.Injective standardKleinRelativeCutOrder := by
  -- Evaluate equality on the committed 215-entry ordering.
  native_decide

/-- Helper for Exercise 74.4: every face in the cut order is retained. -/
private lemma standardKleinRelativeCutOrder_ne_attachment :
    ∀ rank, standardKleinRelativeCutOrder rank ≠ 114 := by
  -- The deleted attachment face does not occur in the explicit ordering.
  native_decide

/-- Helper for Exercise 74.4: the cut order covers every retained face. -/
private lemma standardKleinRelativeCutOrder_surjective_on_retained :
    ∀ face : Fin 216, face ≠ 114 →
      ∃ rank, standardKleinRelativeCutOrder rank = face := by
  -- Search the finite committed ordering for each of the 215 retained face indices.
  native_decide

/-- Helper for Exercise 74.4: every parent seam descends strictly in the cut rank. -/
private lemma standardKleinRelativeCutParentRank_lt :
    ∀ child : Fin 214,
      (standardKleinRelativeCutParentRank child).1 < child.1 + 1 := by
  -- Compare the 214 committed parent ranks with their successor ranks.
  native_decide

/-- Helper for Exercise 74.4: every child-parent pair uses two slots of the same geometric
mesh edge. -/
private lemma standardKleinRelativeCutParentSeam_matches :
    ∀ child : Fin 214,
      standardKleinUndirectedEdge
          (standardKleinRelativeCutOrder
            (standardKleinRelativeCutParentRank child))
            (standardKleinRelativeCutParentEdge child) =
        standardKleinUndirectedEdge
          (standardKleinRelativeCutOrder child.succ)
            (standardKleinRelativeCutChildEdge child) := by
  -- Evaluate both endpoint pairs for each explicit oriented parent seam.
  native_decide

/-- Helper for Exercise 74.4: the explicit 215-face ordering covers every retained face
once, and its 214 parent seams match geometric edges with strict rank descent. -/
private lemma standardKleinRelativeCutTree_certificate :
    standardKleinRelativeCutTreeConditions := by
  -- Assemble the independently checked coverage, rank, and explicit seam certificates.
  exact ⟨standardKleinRelativeCutOrder_injective,
    standardKleinRelativeCutOrder_ne_attachment,
    standardKleinRelativeCutOrder_surjective_on_retained,
    fun child ↦ ⟨standardKleinRelativeCutParentRank_lt child,
      standardKleinRelativeCutParentSeam_matches child⟩⟩

-- Route correction: the doubled mesh is first normalized by global barycentric weights;
-- the polygon cut and the Euclidean target will consume this quotient interface separately.

/-- Helper for Exercise 74.4: the global weight of a mesh vertex in one retained simplex
cell. -/
private def standardKleinDoubleGlobalWeight
    (point : StandardKleinDoubleCarrier) (vertex : Fin 108) : ℝ :=
  ∑ corner : Fin 3,
    if standardKleinFace point.1.2 corner = vertex then point.2.1 corner else 0

/-- Helper for Exercise 74.4: global vertex weights are the canonical standard-simplex map
along the retained face's vertex function. -/
private lemma standardKleinDoubleGlobalWeight_eq_map
    (point : StandardKleinDoubleCarrier) :
    (fun vertex ↦ standardKleinDoubleGlobalWeight point vertex) =
      (stdSimplex.map (standardKleinFace point.1.2) point.2 : Fin 108 → ℝ) := by
  -- Normalize both constructions to the finite sum over corners mapping to each vertex.
  funext vertex
  simp only [standardKleinDoubleGlobalWeight, stdSimplex.map_coe,
    FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  rfl

/-- Helper for Exercise 74.4: a mesh vertex belongs to the deleted attachment triangle. -/
private abbrev standardKleinAttachmentVertex (vertex : Fin 108) : Prop :=
  vertex = standardKleinFace 114 0 ∨
    vertex = standardKleinFace 114 1 ∨ vertex = standardKleinFace 114 2

/-- Helper for Exercise 74.4: all barycentric weight is supported on the deleted attachment
triangle. -/
private def standardKleinOnAttachmentBoundary
    (point : StandardKleinDoubleCarrier) : Prop :=
  ∀ vertex, ¬ standardKleinAttachmentVertex vertex →
    standardKleinDoubleGlobalWeight point vertex = 0

/-- Helper for Exercise 74.4: two retained simplex representatives have the same global
mesh-vertex weights. -/
private def standardKleinSameGlobalWeights
    (x y : StandardKleinDoubleCarrier) : Prop :=
  (fun vertex ↦ standardKleinDoubleGlobalWeight x vertex) =
    fun vertex ↦ standardKleinDoubleGlobalWeight y vertex

/-- Helper for Exercise 74.4: the attachment-aware code of the doubled punctured Klein
mesh duplicates attachment weights and records the copy tag elsewhere. -/
private def standardKleinDoubleCode
    (point : StandardKleinDoubleCarrier) : (Fin 2 × Fin 108) → ℝ :=
  fun index ↦
    if index.1 = point.1.1 ∨ standardKleinAttachmentVertex index.2 then
      standardKleinDoubleGlobalWeight point index.2
    else 0

/-- Helper for Exercise 74.4: a fixed cell's global vertex-weight coordinates vary
continuously with its simplex coordinates. -/
private lemma continuous_standardKleinDoubleGlobalWeight
    (face : StandardKleinDoubleFace) :
    Continuous (fun point : stdSimplex ℝ (Fin 3) ↦
      (fun vertex ↦ standardKleinDoubleGlobalWeight (face, point) vertex)) := by
  -- Each global coordinate is a finite sum of selected simplex coordinates.
  refine continuous_pi ?_
  intro vertex
  apply continuous_finset_sum
  intro corner _
  by_cases hcorner : standardKleinFace face.2 corner = vertex
  · simp only [hcorner, if_true]
    have hcoordinate := (continuous_apply corner).comp
      (continuous_subtype_val :
        Continuous (fun point : stdSimplex ℝ (Fin 3) ↦ point.1))
    exact hcoordinate
  · simp only [hcorner, if_false]
    exact continuous_const

/-- Helper for Exercise 74.4: the attachment-aware doubled-mesh code is continuous. -/
private lemma continuous_standardKleinDoubleCode :
    Continuous standardKleinDoubleCode := by
  -- The cell tag is discrete; on each cell every code coordinate is either a global weight
  -- coordinate or the constant zero function.
  refine continuous_prod_of_discrete_left.mpr ?_
  intro face
  refine continuous_pi ?_
  intro index
  by_cases hindex : index.1 = face.1 ∨ standardKleinAttachmentVertex index.2
  · simp only [standardKleinDoubleCode, hindex, if_true]
    exact continuous_pi_iff.mp (continuous_standardKleinDoubleGlobalWeight face) index.2
  · simp only [standardKleinDoubleCode, hindex, if_false]
    exact continuous_const

/-- Helper for Exercise 74.4: equality of doubled-mesh codes is exactly equality of global
weights, with distinct copy tags allowed only on the attachment boundary. -/
private lemma standardKleinDoubleCode_eq_iff
    (x y : StandardKleinDoubleCarrier) :
    standardKleinDoubleCode x = standardKleinDoubleCode y ↔
      standardKleinSameGlobalWeights x y ∧
        (x.1.1 = y.1.1 ∨
          standardKleinOnAttachmentBoundary x ∧
            standardKleinOnAttachmentBoundary y) := by
  constructor
  · intro hcode
    by_cases htag : x.1.1 = y.1.1
    · -- Equal tags expose the same global-weight coordinate in both codes.
      have hweights : standardKleinSameGlobalWeights x y := by
        funext vertex
        have hcoordinate := congrFun hcode (x.1.1, vertex)
        simpa only [standardKleinDoubleCode, true_or, if_true, htag] using hcoordinate
      exact ⟨hweights, Or.inl htag⟩
    · -- With distinct tags, nonattachment coordinates occur on only one copy and hence
      -- vanish; attachment coordinates remain duplicated on both copies.
      have hweights : standardKleinSameGlobalWeights x y := by
        funext vertex
        by_cases hvis : standardKleinAttachmentVertex vertex
        · have hcoordinate := congrFun hcode (x.1.1, vertex)
          simpa only [standardKleinDoubleCode, true_or, hvis, or_true, if_true] using
            hcoordinate
        · have hxzero := congrFun hcode (x.1.1, vertex)
          have hyzero := congrFun hcode (y.1.1, vertex)
          have hxy : standardKleinDoubleGlobalWeight x vertex = 0 := by
            simpa only [standardKleinDoubleCode, true_or, hvis, or_false, htag, if_true,
              if_false] using hxzero
          have hyx : 0 = standardKleinDoubleGlobalWeight y vertex := by
            simpa only [standardKleinDoubleCode, true_or, hvis, or_false, htag,
              Ne.symm htag, if_true, if_false] using hyzero
          exact hxy.trans hyx
      have hxBoundary : standardKleinOnAttachmentBoundary x := by
        intro vertex hvis
        have hcoordinate := congrFun hcode (x.1.1, vertex)
        simpa only [standardKleinDoubleCode, true_or, hvis, or_false, htag, if_true,
          if_false] using hcoordinate
      have hyBoundary : standardKleinOnAttachmentBoundary y := by
        intro vertex hvis
        have hcoordinate := congrFun hcode (y.1.1, vertex)
        have hzero : 0 = standardKleinDoubleGlobalWeight y vertex := by
          simpa only [standardKleinDoubleCode, true_or, hvis, or_false, htag,
            Ne.symm htag, if_true, if_false] using hcoordinate
        exact hzero.symm
      exact ⟨hweights, Or.inr ⟨hxBoundary, hyBoundary⟩⟩
  · rintro ⟨hweights, htag | ⟨hxBoundary, hyBoundary⟩⟩
    · -- Equal tags make the two code masks identical, so global-weight equality closes
      -- every coordinate.
      funext index
      have hcoordinate := congrFun hweights index.2
      simp only [standardKleinDoubleCode, htag]
      rw [hcoordinate]
    · -- On the attachment all coordinates are duplicated; off it both boundary-supported
      -- representatives have zero weight regardless of the selected copy coordinate.
      funext index
      by_cases hvis : standardKleinAttachmentVertex index.2
      · have hcoordinate := congrFun hweights index.2
        simpa only [standardKleinDoubleCode, hvis, or_true, if_true] using hcoordinate
      · have hxzero : standardKleinDoubleCode x index = 0 := by
          simp only [standardKleinDoubleCode, hvis, or_false]
          split
          · exact hxBoundary index.2 hvis
          · rfl
        have hyzero : standardKleinDoubleCode y index = 0 := by
          simp only [standardKleinDoubleCode, hvis, or_false]
          split
          · exact hyBoundary index.2 hvis
          · rfl
        exact hxzero.trans hyzero.symm

/-- Helper for Exercise 74.4: the compact code model of the doubled punctured Klein mesh. -/
private abbrev StandardKleinDoubleModel := Set.range standardKleinDoubleCode

/-- Helper for Exercise 74.4: every doubled-mesh code belongs to its code model. -/
private lemma standardKleinDoubleCode_mem_range (point : StandardKleinDoubleCarrier) :
    standardKleinDoubleCode point ∈ Set.range standardKleinDoubleCode := by
  -- The point itself is the required range witness.
  exact ⟨point, rfl⟩

/-- Helper for Exercise 74.4: the canonical map from simplex cells onto the doubled-mesh
code model. -/
private def standardKleinDoubleQuotient :
    StandardKleinDoubleCarrier → StandardKleinDoubleModel :=
  fun point ↦ ⟨standardKleinDoubleCode point,
    standardKleinDoubleCode_mem_range point⟩

/-- Helper for Exercise 74.4: the canonical doubled-mesh code map is continuous. -/
private lemma continuous_standardKleinDoubleQuotient :
    Continuous standardKleinDoubleQuotient := by
  -- Continuity into the range subtype is continuity of the underlying code.
  rw [continuous_induced_rng]
  exact continuous_standardKleinDoubleCode

/-- Helper for Exercise 74.4: bundle the doubled-mesh code quotient as a continuous map. -/
private def standardKleinDoubleQuotientMap :
    C(StandardKleinDoubleCarrier, StandardKleinDoubleModel) :=
  ⟨standardKleinDoubleQuotient, continuous_standardKleinDoubleQuotient⟩

/-- Helper for Exercise 74.4: the canonical doubled-mesh code map is surjective. -/
private lemma standardKleinDoubleQuotient_surjective :
    Function.Surjective standardKleinDoubleQuotient := by
  -- Unpack a range witness and reuse its representing simplex-cell point.
  rintro ⟨_, point, rfl⟩
  exact ⟨point, rfl⟩

/-- Helper for Exercise 74.4: global barycentric coding gives a compact quotient
presentation of the doubled punctured Klein mesh, with its exact normalized kernel. -/
private lemma standardKleinDoubleCodePresentation :
    Topology.IsQuotientMap standardKleinDoubleQuotient ∧
      ∀ x y, standardKleinDoubleQuotient x = standardKleinDoubleQuotient y ↔
        standardKleinSameGlobalWeights x y ∧
          (x.1.1 = y.1.1 ∨
            standardKleinOnAttachmentBoundary x ∧
              standardKleinOnAttachmentBoundary y) := by
  constructor
  · -- A continuous surjection from the compact finite cell family to its Hausdorff range
    -- is a quotient map.
    exact Topology.IsQuotientMap.of_surjective_continuous
      standardKleinDoubleQuotient_surjective continuous_standardKleinDoubleQuotient
  · intro x y
    rw [Subtype.ext_iff]
    exact standardKleinDoubleCode_eq_iff x y

/-- Helper for Exercise 74.4: the global code model of the doubled punctured Klein mesh is
compact. -/
private lemma standardKleinDoubleModel_isCompact :
    IsCompact (Set.univ : Set StandardKleinDoubleModel) := by
  -- The model is the continuous image of the compact finite family of simplex cells.
  have himage := isCompact_univ.image continuous_standardKleinDoubleQuotient
  rw [Set.image_univ,
    Set.range_eq_univ.mpr standardKleinDoubleQuotient_surjective] at himage
  exact himage

/-- Helper for Exercise 74.4: every global barycentric vertex weight is nonnegative. -/
private lemma standardKleinDoubleGlobalWeight_nonnegative
    (point : StandardKleinDoubleCarrier) (vertex : Fin 108) :
    0 ≤ standardKleinDoubleGlobalWeight point vertex := by
  -- Each summand is either a nonnegative simplex coordinate or zero.
  unfold standardKleinDoubleGlobalWeight
  apply Finset.sum_nonneg
  intro corner _
  split
  · exact point.2.2.1 corner
  · exact le_rfl

/-- Helper for Exercise 74.4: the global barycentric vertex weights sum to one. -/
private lemma standardKleinDoubleGlobalWeight_sum
    (point : StandardKleinDoubleCarrier) :
    ∑ vertex : Fin 108, standardKleinDoubleGlobalWeight point vertex = 1 := by
  -- Exchange the finite sums; each simplex corner contributes at its unique global vertex.
  unfold standardKleinDoubleGlobalWeight
  rw [Finset.sum_comm]
  have heq (corner : Fin 3) (vertex : Fin 108) :
      (standardKleinFace point.1.2 corner = vertex) =
        (vertex = standardKleinFace point.1.2 corner) := by
    exact propext eq_comm
  simp_rw [heq]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change (∑ corner, point.2.1 corner) = 1
  exact point.2.2.2

/-- Helper for Exercise 74.4: the coordinate dot product used for affine-plane reflection. -/
private def dotThree (u v : Fin 3 → ℝ) : ℝ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Helper for Exercise 74.4: the explicit three-coordinate formula is the finite dot
product. -/
private lemma dotThree_eq_dotProduct (u v : Fin 3 → ℝ) :
    dotThree u v = dotProduct u v := by
  -- Expand the dot product over the three finite coordinates.
  unfold dotThree dotProduct
  rw [Fin.sum_univ_three]

/-- Helper for Exercise 74.4: the signed coordinate relative to an affine plane. -/
private def affinePlaneCoordinate
    (origin normal point : Fin 3 → ℝ) : ℝ :=
  dotThree normal (fun i ↦ point i - origin i)

/-- Helper for Exercise 74.4: the three-coordinate dot product commutes with finite
weighted sums. -/
private lemma dotThree_weighted_sum
    {I : Type*} [Fintype I] (normal : Fin 3 → ℝ)
    (weight : I → ℝ) (point : I → Fin 3 → ℝ) :
    dotThree normal (fun coordinate ↦ ∑ i, weight i * point i coordinate) =
      ∑ i, weight i * dotThree normal (point i) := by
  -- Repackage the weighted coordinate function as a vector sum and use dot-product linearity.
  have hfunction :
      (fun coordinate ↦ ∑ i, weight i * point i coordinate) =
        ∑ i, weight i • point i := by
    funext coordinate
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [dotThree_eq_dotProduct, hfunction]
  calc
    normal ⬝ᵥ ∑ i, weight i • point i =
        ∑ i, normal ⬝ᵥ (weight i • point i) :=
      dotProduct_sum normal Finset.univ (fun i ↦ weight i • point i)
    _ = ∑ i, weight i * dotThree normal (point i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [dotProduct_smul, smul_eq_mul, dotThree_eq_dotProduct]

/-- Helper for Exercise 74.4: an affine coordinate commutes with a finite weighted sum
whose weights sum to one. -/
private lemma affinePlaneCoordinate_weighted_sum
    {I : Type*} [Fintype I] (origin normal : Fin 3 → ℝ)
    (weight : I → ℝ) (point : I → Fin 3 → ℝ)
    (hsum : ∑ i, weight i = 1) :
    affinePlaneCoordinate origin normal
        (fun coordinate ↦ ∑ i, weight i * point i coordinate) =
      ∑ i, weight i * affinePlaneCoordinate origin normal (point i) := by
  -- Separate the linear dot product from the affine origin correction.
  unfold affinePlaneCoordinate
  calc
    dotThree normal
          (fun coordinate ↦ ∑ i, weight i * point i coordinate - origin coordinate) =
        dotThree normal (fun coordinate ↦ ∑ i, weight i * point i coordinate) -
          dotThree normal origin := by
      unfold dotThree
      ring
    _ = (∑ i, weight i * dotThree normal (point i)) -
          dotThree normal origin := by
      rw [dotThree_weighted_sum]
    _ = ∑ i, weight i *
        dotThree normal (fun coordinate ↦ point i coordinate - origin coordinate) := by
      calc
        (∑ i, weight i * dotThree normal (point i)) - dotThree normal origin =
            (∑ i, weight i * dotThree normal (point i)) -
              ∑ i, weight i * dotThree normal origin := by
          rw [← Finset.sum_mul, hsum, one_mul]
        _ = ∑ i, (weight i * dotThree normal (point i) -
            weight i * dotThree normal origin) := by
          rw [Finset.sum_sub_distrib]
        _ = ∑ i, weight i *
            dotThree normal (fun coordinate ↦ point i coordinate - origin coordinate) := by
          apply Finset.sum_congr rfl
          intro i _
          unfold dotThree
          ring

/-- Helper for Exercise 74.4: the squared length of an affine-plane normal. -/
private def normalSquare (normal : Fin 3 → ℝ) : ℝ :=
  dotThree normal normal

/-- Helper for Exercise 74.4: reflection in an affine plane with the displayed normal. -/
private noncomputable def reflectAcrossAffinePlane
    (origin normal point : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i ↦ point i -
    (2 * affinePlaneCoordinate origin normal point / normalSquare normal) * normal i

/-- Helper for Exercise 74.4: moving a point along a plane normal changes its signed
coordinate by the scalar times the squared normal length. -/
private lemma affinePlaneCoordinate_sub_normal
    (origin normal point : Fin 3 → ℝ) (scalar : ℝ) :
    affinePlaneCoordinate origin normal
        (fun i ↦ point i - scalar * normal i) =
      affinePlaneCoordinate origin normal point - scalar * normalSquare normal := by
  -- The three coordinate products distribute over the common normal displacement.
  unfold affinePlaneCoordinate normalSquare dotThree
  ring

/-- Helper for Exercise 74.4: affine-plane reflection negates the signed normal coordinate. -/
private lemma affinePlaneCoordinate_reflectAcross
    (origin normal point : Fin 3 → ℝ) (hnormal : normalSquare normal ≠ 0) :
    affinePlaneCoordinate origin normal
        (reflectAcrossAffinePlane origin normal point) =
      -affinePlaneCoordinate origin normal point := by
  -- First collect the coordinate calculation into one squared-norm factor, then cancel it.
  unfold reflectAcrossAffinePlane
  calc
    affinePlaneCoordinate origin normal
          (fun i ↦ point i -
            (2 * affinePlaneCoordinate origin normal point / normalSquare normal) *
              normal i) =
        affinePlaneCoordinate origin normal point -
          (2 * affinePlaneCoordinate origin normal point / normalSquare normal) *
            normalSquare normal := by
      exact affinePlaneCoordinate_sub_normal origin normal point
        (2 * affinePlaneCoordinate origin normal point / normalSquare normal)
    _ = affinePlaneCoordinate origin normal point -
        2 * affinePlaneCoordinate origin normal point := by
      rw [div_mul_cancel₀ _ hnormal]
    _ = -affinePlaneCoordinate origin normal point := by
      ring

/-- Helper for Exercise 74.4: affine-plane reflection fixes every point of its plane. -/
private lemma reflectAcrossAffinePlane_eq_self
    (origin normal point : Fin 3 → ℝ)
    (hpoint : affinePlaneCoordinate origin normal point = 0) :
    reflectAcrossAffinePlane origin normal point = point := by
  -- A zero signed coordinate makes the normal correction vanish in every component.
  funext i
  simp only [reflectAcrossAffinePlane, hpoint, mul_zero, zero_div, zero_mul, sub_zero]

/-- Helper for Exercise 74.4: the exact integer normal to attachment face 114. -/
private def standardKleinAttachmentNormalInt : Fin 3 → ℤ :=
  let a := standardKleinControl (standardKleinFace 114 0)
  let b := standardKleinControl (standardKleinFace 114 1)
  let c := standardKleinControl (standardKleinFace 114 2)
  let u := fourFoldControlSub b a
  let w := fourFoldControlSub c a
  ![u 1 * w 2 - u 2 * w 1, u 2 * w 0 - u 0 * w 2,
    u 0 * w 1 - u 1 * w 0]

/-- Helper for Exercise 74.4: the attachment-face normal is nonzero over the integers. -/
private lemma standardKleinAttachmentNormalInt_ne_zero :
    standardKleinAttachmentNormalInt ≠ 0 := by
  -- Evaluate the three exact cross-product coordinates of the certified attachment face.
  native_decide

/-- Helper for Exercise 74.4: the attachment origin in real Euclidean coordinates. -/
private def standardKleinAttachmentOrigin : Fin 3 → ℝ :=
  fun i ↦ standardKleinControl (standardKleinFace 114 0) i

/-- Helper for Exercise 74.4: the real normal to the attachment plane. -/
private def standardKleinAttachmentNormal : Fin 3 → ℝ :=
  fun i ↦ standardKleinAttachmentNormalInt i

/-- Helper for Exercise 74.4: the real attachment normal is the cross product of the two
attachment edge vectors. -/
private lemma standardKleinAttachmentNormal_apply (coordinate : Fin 3) :
    standardKleinAttachmentNormal coordinate =
      let a := fun i ↦ (standardKleinControl (standardKleinFace 114 0) i : ℝ)
      let b := fun i ↦ (standardKleinControl (standardKleinFace 114 1) i : ℝ)
      let c := fun i ↦ (standardKleinControl (standardKleinFace 114 2) i : ℝ)
      match coordinate.1 with
      | 0 => (b 1 - a 1) * (c 2 - a 2) - (b 2 - a 2) * (c 1 - a 1)
      | 1 => (b 2 - a 2) * (c 0 - a 0) - (b 0 - a 0) * (c 2 - a 2)
      | _ => (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) := by
  -- Cast the exact integer cross product coordinatewise.
  fin_cases coordinate <;>
    simp [standardKleinAttachmentNormal, standardKleinAttachmentNormalInt,
      fourFoldControlSub]

/-- Helper for Exercise 74.4: the real attachment-face normal is nonzero. -/
private lemma standardKleinAttachmentNormal_ne_zero :
    standardKleinAttachmentNormal ≠ 0 := by
  -- If the cast normal vanished, injectivity of the integer cast would kill every coordinate.
  intro hzero
  apply standardKleinAttachmentNormalInt_ne_zero
  funext i
  have hcoordinate := congrFun hzero i
  simp only [standardKleinAttachmentNormal, Pi.zero_apply] at hcoordinate
  exact_mod_cast hcoordinate

/-- Helper for Exercise 74.4: the squared real attachment normal is nonzero. -/
private lemma standardKleinAttachmentNormalSquare_ne_zero :
    normalSquare standardKleinAttachmentNormal ≠ 0 := by
  -- A sum of three real squares can vanish only when every normal coordinate vanishes.
  intro hsquare
  apply standardKleinAttachmentNormal_ne_zero
  have hzero0 : standardKleinAttachmentNormal 0 = 0 := by
    unfold normalSquare dotThree at hsquare
    nlinarith [sq_nonneg (standardKleinAttachmentNormal 0),
      sq_nonneg (standardKleinAttachmentNormal 1),
      sq_nonneg (standardKleinAttachmentNormal 2)]
  have hzero1 : standardKleinAttachmentNormal 1 = 0 := by
    unfold normalSquare dotThree at hsquare
    nlinarith [sq_nonneg (standardKleinAttachmentNormal 0),
      sq_nonneg (standardKleinAttachmentNormal 1),
      sq_nonneg (standardKleinAttachmentNormal 2)]
  have hzero2 : standardKleinAttachmentNormal 2 = 0 := by
    unfold normalSquare dotThree at hsquare
    nlinarith [sq_nonneg (standardKleinAttachmentNormal 0),
      sq_nonneg (standardKleinAttachmentNormal 1),
      sq_nonneg (standardKleinAttachmentNormal 2)]
  funext i
  fin_cases i
  · exact hzero0
  · exact hzero1
  · exact hzero2

/-- Helper for Exercise 74.4: reflection in the affine plane of attachment face 114. -/
private noncomputable def standardKleinReflection (point : Fin 3 → ℝ) : Fin 3 → ℝ :=
  reflectAcrossAffinePlane standardKleinAttachmentOrigin
    standardKleinAttachmentNormal point

/-- Helper for Exercise 74.4: attachment-plane reflection negates the signed coordinate and
fixes every point on that plane. -/
private lemma standardKleinReflection_spec (point : Fin 3 → ℝ) :
    affinePlaneCoordinate standardKleinAttachmentOrigin standardKleinAttachmentNormal
        (standardKleinReflection point) =
      -affinePlaneCoordinate standardKleinAttachmentOrigin standardKleinAttachmentNormal
        point ∧
    (affinePlaneCoordinate standardKleinAttachmentOrigin standardKleinAttachmentNormal
        point = 0 → standardKleinReflection point = point) := by
  -- Apply the generic reflection formulas using the exact nonzero attachment normal.
  constructor
  · exact affinePlaneCoordinate_reflectAcross _ _ _
      standardKleinAttachmentNormalSquare_ne_zero
  · exact reflectAcrossAffinePlane_eq_self _ _ _

/-- Helper for Exercise 74.4: the unreflected affine target on one retained simplex cell. -/
private noncomputable def standardKleinDoubleBaseTarget
    (point : StandardKleinDoubleCarrier) : Fin 3 → ℝ :=
  fun coordinate ↦ ∑ corner : Fin 3,
    point.2.1 corner * (standardKleinControl (standardKleinFace point.1.2 corner) coordinate : ℝ)

/-- Helper for Exercise 74.4: the same affine target expressed using global mesh-vertex
weights. -/
private noncomputable def standardKleinDoubleGlobalTarget
    (point : StandardKleinDoubleCarrier) : Fin 3 → ℝ :=
  fun coordinate ↦ ∑ vertex : Fin 108,
    standardKleinDoubleGlobalWeight point vertex * (standardKleinControl vertex coordinate : ℝ)

/-- Helper for Exercise 74.4: local simplex interpolation equals interpolation by global
mesh-vertex weights. -/
private lemma standardKleinDoubleBaseTarget_eq_globalTarget
    (point : StandardKleinDoubleCarrier) :
    standardKleinDoubleBaseTarget point = standardKleinDoubleGlobalTarget point := by
  -- Exchange the corner and global-vertex sums; each corner contributes at its own vertex.
  funext coordinate
  unfold standardKleinDoubleBaseTarget standardKleinDoubleGlobalTarget
  simp only [standardKleinDoubleGlobalWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul, eq_comm, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Helper for Exercise 74.4: the affine base target varies continuously on every tagged
simplex cell. -/
private lemma continuous_standardKleinDoubleBaseTarget
    (face : StandardKleinDoubleFace) :
    Continuous (fun point : stdSimplex ℝ (Fin 3) ↦
      standardKleinDoubleBaseTarget (face, point)) := by
  -- Coordinatewise, the map is a finite linear combination of simplex coordinates.
  refine continuous_pi ?_
  intro coordinate
  apply continuous_finset_sum
  intro corner _
  have hcoordinate := (continuous_apply corner).comp
    (continuous_subtype_val :
      Continuous (fun point : stdSimplex ℝ (Fin 3) ↦ point.1))
  have hconstant : Continuous (fun _ : stdSimplex ℝ (Fin 3) ↦
      (standardKleinControl (standardKleinFace face.2 corner) coordinate : ℝ)) :=
    continuous_const
  exact hcoordinate.mul hconstant

/-- Helper for Exercise 74.4: reflection in the fixed attachment plane is continuous. -/
private lemma continuous_standardKleinReflection :
    Continuous standardKleinReflection := by
  -- The reflection formula uses only fixed affine coordinates and a nonzero constant divisor.
  unfold standardKleinReflection reflectAcrossAffinePlane affinePlaneCoordinate
    normalSquare dotThree
  fun_prop

/-- Helper for Exercise 74.4: each control vertex of the attachment triangle lies in its
supporting affine plane. -/
private lemma standardKleinAttachmentControl_mem_plane (corner : Fin 3) :
    affinePlaneCoordinate standardKleinAttachmentOrigin standardKleinAttachmentNormal
        (fun coordinate ↦
          (standardKleinControl (standardKleinFace 114 corner) coordinate : ℝ)) = 0 := by
  -- A cross product is orthogonal to the two attachment edges, including their endpoints.
  have hzero :
      affinePlaneCoordinate standardKleinAttachmentOrigin standardKleinAttachmentNormal
          (fun coordinate ↦
            (standardKleinControl (standardKleinFace 114 0) coordinate : ℝ)) = 0 := by
    unfold affinePlaneCoordinate dotThree standardKleinAttachmentOrigin
    rw [standardKleinAttachmentNormal_apply 0,
      standardKleinAttachmentNormal_apply 1,
      standardKleinAttachmentNormal_apply 2]
    simp [standardKleinAttachmentFace_spec]
  have hone :
      affinePlaneCoordinate standardKleinAttachmentOrigin standardKleinAttachmentNormal
          (fun coordinate ↦
            (standardKleinControl (standardKleinFace 114 1) coordinate : ℝ)) = 0 := by
    unfold affinePlaneCoordinate dotThree standardKleinAttachmentOrigin
    rw [standardKleinAttachmentNormal_apply 0,
      standardKleinAttachmentNormal_apply 1,
      standardKleinAttachmentNormal_apply 2]
    simp [standardKleinAttachmentFace_spec]
    ring
  have htwo :
      affinePlaneCoordinate standardKleinAttachmentOrigin standardKleinAttachmentNormal
          (fun coordinate ↦
            (standardKleinControl (standardKleinFace 114 2) coordinate : ℝ)) = 0 := by
    unfold affinePlaneCoordinate dotThree standardKleinAttachmentOrigin
    rw [standardKleinAttachmentNormal_apply 0,
      standardKleinAttachmentNormal_apply 1,
      standardKleinAttachmentNormal_apply 2]
    simp [standardKleinAttachmentFace_spec]
    ring
  fin_cases corner
  · exact hzero
  · exact hone
  · exact htwo

/-- Helper for Exercise 74.4: attachment-supported barycentric data maps into the
attachment plane. -/
private lemma standardKleinDoubleBaseTarget_mem_attachmentPlane
    (point : StandardKleinDoubleCarrier)
    (hboundary : standardKleinOnAttachmentBoundary point) :
    affinePlaneCoordinate standardKleinAttachmentOrigin standardKleinAttachmentNormal
        (standardKleinDoubleBaseTarget point) = 0 := by
  -- Pass to global weights, commute the affine coordinate with their sum, and kill every
  -- summand either by attachment-plane membership or by boundary support.
  rw [standardKleinDoubleBaseTarget_eq_globalTarget]
  unfold standardKleinDoubleGlobalTarget
  rw [affinePlaneCoordinate_weighted_sum _ _
    (fun vertex ↦ standardKleinDoubleGlobalWeight point vertex)
    (fun vertex coordinate ↦ (standardKleinControl vertex coordinate : ℝ))
    (standardKleinDoubleGlobalWeight_sum point)]
  apply Finset.sum_eq_zero
  intro vertex _
  by_cases hvertex : standardKleinAttachmentVertex vertex
  · rcases hvertex with hvertex | hvertex | hvertex
    · rw [hvertex, standardKleinAttachmentControl_mem_plane, mul_zero]
    · rw [hvertex, standardKleinAttachmentControl_mem_plane, mul_zero]
    · rw [hvertex, standardKleinAttachmentControl_mem_plane, mul_zero]
  · rw [hboundary vertex hvertex, zero_mul]

/-- Helper for Exercise 74.4: coordinate function of the certified Klein target on copy zero
and its attachment-plane reflection on copy one. -/
private noncomputable def standardKleinDoubleTargetCoordinates
    (point : StandardKleinDoubleCarrier) : Fin 3 → ℝ :=
  if point.1.1 = 0 then standardKleinDoubleBaseTarget point
  else standardKleinReflection (standardKleinDoubleBaseTarget point)

/-- Helper for Exercise 74.4: the reflected target coordinates vary continuously. -/
private lemma continuous_standardKleinDoubleTargetCoordinates :
    Continuous standardKleinDoubleTargetCoordinates := by
  -- The discrete cell tag selects one of two continuous affine formulas.
  refine continuous_prod_of_discrete_left.mpr ?_
  intro face
  by_cases hcopy : face.1 = 0
  · simpa only [standardKleinDoubleTargetCoordinates, hcopy, if_true] using
      continuous_standardKleinDoubleBaseTarget face
  · simp only [standardKleinDoubleTargetCoordinates, hcopy, if_false]
    exact continuous_standardKleinReflection.comp
      (continuous_standardKleinDoubleBaseTarget face)

/-- Helper for Exercise 74.4: use the certified Klein target on copy zero and its
attachment-plane reflection on copy one. -/
private noncomputable def standardKleinDoubleTargetRaw
    (point : StandardKleinDoubleCarrier) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (standardKleinDoubleTargetCoordinates point)

/-- Helper for Exercise 74.4: the reflected cellwise Euclidean target is continuous. -/
private lemma continuous_standardKleinDoubleTargetRaw :
    Continuous standardKleinDoubleTargetRaw := by
  -- Transfer coordinatewise continuity through the finite-dimensional `PiLp` equivalence.
  exact (PiLp.continuous_toLp 2 _).comp
    continuous_standardKleinDoubleTargetCoordinates

/-- Helper for Exercise 74.4: bundle the reflected affine target as a continuous map. -/
private noncomputable def standardKleinDoubleTarget :
    C(StandardKleinDoubleCarrier, EuclideanSpace ℝ (Fin 3)) :=
  ⟨standardKleinDoubleTargetRaw, continuous_standardKleinDoubleTargetRaw⟩

/-- Helper for Exercise 74.4: equal doubled-mesh codes have equal reflected affine targets. -/
private lemma standardKleinDoubleTarget_eq_of_quotient_eq
    (x y : StandardKleinDoubleCarrier)
    (hquotient : standardKleinDoubleQuotient x = standardKleinDoubleQuotient y) :
    standardKleinDoubleTarget x = standardKleinDoubleTarget y := by
  -- Normalize code equality to global weights and the copy/attachment alternatives.
  have hnormal := (standardKleinDoubleCodePresentation.2 x y).mp hquotient
  have hbase : standardKleinDoubleBaseTarget x = standardKleinDoubleBaseTarget y := by
    rw [standardKleinDoubleBaseTarget_eq_globalTarget,
      standardKleinDoubleBaseTarget_eq_globalTarget]
    funext coordinate
    apply Finset.sum_congr rfl
    intro vertex _
    rw [congrFun hnormal.1 vertex]
  apply congrArg (WithLp.toLp 2)
  rcases hnormal.2 with htag | ⟨hxBoundary, hyBoundary⟩
  · -- Equal copy tags select the same branch, and the common base value closes it.
    by_cases hxzero : x.1.1 = 0
    · have hyzero : y.1.1 = 0 := htag.symm.trans hxzero
      simpa only [standardKleinDoubleTarget, ContinuousMap.coe_mk,
        standardKleinDoubleTargetRaw, standardKleinDoubleTargetCoordinates,
        hxzero, hyzero, if_true] using hbase
    · have hyzero : y.1.1 ≠ 0 := by
        intro hyzero
        exact hxzero (htag.trans hyzero)
      simp only [standardKleinDoubleTarget, ContinuousMap.coe_mk,
        standardKleinDoubleTargetRaw, standardKleinDoubleTargetCoordinates,
        hxzero, hyzero, if_false]
      exact congrArg standardKleinReflection hbase
  · -- On the attachment boundary reflection fixes both base values, independently of
    -- the copy tag.
    have hxPlane := standardKleinDoubleBaseTarget_mem_attachmentPlane x hxBoundary
    have hyPlane := standardKleinDoubleBaseTarget_mem_attachmentPlane y hyBoundary
    have hxFixed : standardKleinReflection (standardKleinDoubleBaseTarget x) =
        standardKleinDoubleBaseTarget x := standardKleinReflection_spec _ |>.2 hxPlane
    have hyFixed : standardKleinReflection (standardKleinDoubleBaseTarget y) =
        standardKleinDoubleBaseTarget y := standardKleinReflection_spec _ |>.2 hyPlane
    simp only [standardKleinDoubleTarget, ContinuousMap.coe_mk,
      standardKleinDoubleTargetRaw, standardKleinDoubleTargetCoordinates]
    split <;> split
    · exact hbase
    · exact hbase.trans hyFixed.symm
    · exact hxFixed.trans hbase
    · exact hxFixed.trans (hbase.trans hyFixed.symm)

/-- Helper for Exercise 74.4: the reflected affine target descends through the compact
doubled-mesh code quotient. -/
private lemma standardKleinDoubleTarget_factorsThrough :
    Function.FactorsThrough standardKleinDoubleTarget standardKleinDoubleQuotient := by
  -- Apply the target compatibility theorem to any two representatives of one code point.
  intro x y hxy
  exact standardKleinDoubleTarget_eq_of_quotient_eq x y hxy



/-- Helper for Exercise 74.4: exact Klein-mesh link cofactors cast to the real cofactors
controlling intersection of the corresponding positive cones. -/
private lemma standardKleinLinkCofactor_cast
    (face other : Fin 216) (corner otherCorner : Fin 3) :
    let vertex := standardKleinControl (standardKleinFace face corner)
    let u := fourFoldControlSub
      (standardKleinControl (standardKleinOtherFaceVertex face corner 0)) vertex
    let w := fourFoldControlSub
      (standardKleinControl (standardKleinOtherFaceVertex face corner 1)) vertex
    let x := fourFoldControlSub
      (standardKleinControl (standardKleinOtherFaceVertex other otherCorner 0)) vertex
    let y := fourFoldControlSub
      (standardKleinControl (standardKleinOtherFaceVertex other otherCorner 1)) vertex
    ∀ i, (standardKleinLinkCofactor face other corner otherCorner i : ℝ) =
      FourFoldFanPL.correctedCofactors
        (fun j ↦ u j) (fun j ↦ w j) (fun j ↦ x j) (fun j ↦ y j) i := by
  -- Evaluate each finite cofactor and use the determinant cast bridge already established.
  dsimp only
  intro i
  fin_cases i
  all_goals
    simp [standardKleinLinkCofactor, FourFoldFanPL.correctedCofactors_zero,
      FourFoldFanPL.correctedCofactors_one, FourFoldFanPL.correctedCofactors_two,
      FourFoldFanPL.correctedCofactors_three, fourFoldControlDet_cast]

/-- Helper for Exercise 74.4: an exact separated-link certificate for the Klein mesh rules
out every nonzero intersection of the associated real positive cones. -/
private lemma standardKleinLinkSeparated_noPositiveConeIntersection
    (face other : Fin 216) (corner otherCorner : Fin 3)
    (hseparated : standardKleinLinkSeparated face other corner otherCorner)
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    let vertex := standardKleinControl (standardKleinFace face corner)
    let u := fourFoldControlSub
      (standardKleinControl (standardKleinOtherFaceVertex face corner 0)) vertex
    let w := fourFoldControlSub
      (standardKleinControl (standardKleinOtherFaceVertex face corner 1)) vertex
    let x := fourFoldControlSub
      (standardKleinControl (standardKleinOtherFaceVertex other otherCorner 0)) vertex
    let y := fourFoldControlSub
      (standardKleinControl (standardKleinOtherFaceVertex other otherCorner 1)) vertex
    a • (fun j ↦ (u j : ℝ)) + b • (fun j ↦ (w j : ℝ)) =
        c • (fun j ↦ (x j : ℝ)) + d • (fun j ↦ (y j : ℝ)) →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  -- Transport the three exact sign conditions and invoke the real cofactor criterion.
  dsimp only
  intro hlinear
  dsimp only [standardKleinLinkSeparated] at hseparated
  apply FourFoldFanPL.mixedCofactors_noPositiveConeIntersection _ _ _ _
    a b c d ha hb hc hd
  · intro i
    rw [← standardKleinLinkCofactor_cast face other corner otherCorner i]
    exact_mod_cast hseparated.1 i
  · intro hallPositive
    apply hseparated.2.1
    intro i
    have hi := hallPositive i
    rw [← standardKleinLinkCofactor_cast face other corner otherCorner i] at hi
    exact_mod_cast hi
  · intro hallNegative
    apply hseparated.2.2
    intro i
    have hi := hallNegative i
    rw [← standardKleinLinkCofactor_cast face other corner otherCorner i] at hi
    exact_mod_cast hi
  · exact hlinear

/-- Helper for Exercise 74.4: vertex-only pairs of exact Klein-mesh faces have disjoint real
positive links away from their common vertex. -/
private lemma standardKleinVertexLinks_noPositiveConeIntersection
    (face other : Fin 216) (corner otherCorner : Fin 3)
    (heq : standardKleinFace face corner = standardKleinFace other otherCorner)
    (honly : standardKleinFacesMeetOnlyAt face other (standardKleinFace face corner))
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    let vertex := standardKleinControl (standardKleinFace face corner)
    let u := fourFoldControlSub
      (standardKleinControl (standardKleinOtherFaceVertex face corner 0)) vertex
    let w := fourFoldControlSub
      (standardKleinControl (standardKleinOtherFaceVertex face corner 1)) vertex
    let x := fourFoldControlSub
      (standardKleinControl (standardKleinOtherFaceVertex other otherCorner 0)) vertex
    let y := fourFoldControlSub
      (standardKleinControl (standardKleinOtherFaceVertex other otherCorner 1)) vertex
    a • (fun j ↦ (u j : ℝ)) + b • (fun j ↦ (w j : ℝ)) =
        c • (fun j ↦ (x j : ℝ)) + d • (fun j ↦ (y j : ℝ)) →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  -- Read the finite link certificate and pass it through the integer-to-real adapter.
  have hseparated : standardKleinLinkSeparated face other corner otherCorner :=
    standardKleinControlCertificate.2.2.1 face other corner otherCorner heq honly
  exact standardKleinLinkSeparated_noPositiveConeIntersection face other corner otherCorner
    hseparated a b c d ha hb hc hd

/-- Helper for Exercise 74.4: a retained doubled face is incident to a selected doubled-code
coordinate, including its copy mask away from the attachment triangle. -/
private abbrev standardKleinDoubleFaceIncident
    (index : Fin 2 × Fin 108) (face : StandardKleinDoubleFace) : Prop :=
  (index.1 = face.1 ∨ standardKleinAttachmentVertex index.2) ∧
    ∃ corner : Fin 3, standardKleinFace face.2 corner = index.2

/-- Helper for Exercise 74.4: some global vertex has positive barycentric weight at every
simplex representative. -/
private lemma standardKleinDouble_exists_positive_globalWeight
    (point : StandardKleinDoubleCarrier) :
    ∃ vertex : Fin 108, 0 < standardKleinDoubleGlobalWeight point vertex := by
  -- If every coordinate were nonpositive, nonnegativity would make the total sum zero.
  by_contra hpositive
  have hnonpositive : ∀ vertex, standardKleinDoubleGlobalWeight point vertex ≤ 0 := by
    intro vertex
    exact not_lt.mp (not_exists.mp hpositive vertex)
  have hzero : ∀ vertex, standardKleinDoubleGlobalWeight point vertex = 0 := by
    intro vertex
    exact le_antisymm (hnonpositive vertex)
      (standardKleinDoubleGlobalWeight_nonnegative point vertex)
  have hsumZero : ∑ vertex : Fin 108,
      standardKleinDoubleGlobalWeight point vertex = 0 := by
    simp only [hzero, Finset.sum_const_zero]
  rw [standardKleinDoubleGlobalWeight_sum point] at hsumZero
  exact one_ne_zero hsumZero

/-- Helper for Exercise 74.4: a positive doubled-code coordinate can only occur on a face
containing its underlying mesh vertex. -/
private lemma standardKleinDoubleFaceIncident_of_code_pos
    (point : StandardKleinDoubleCarrier) (index : Fin 2 × Fin 108)
    (hpositive : 0 < standardKleinDoubleCode point index) :
    standardKleinDoubleFaceIncident index point.1 := by
  -- Positivity first exposes the copy mask recorded by this doubled-code coordinate.
  have hmask : index.1 = point.1.1 ∨ standardKleinAttachmentVertex index.2 := by
    by_contra hmask
    simp only [standardKleinDoubleCode, hmask, if_false] at hpositive
    exact (lt_irrefl 0) hpositive
  refine ⟨hmask, ?_⟩
  -- If the vertex is absent, each term in its global barycentric coordinate is zero.
  by_contra hincident
  have habsent : ∀ corner : Fin 3,
      standardKleinFace point.1.2 corner ≠ index.2 := by
    simpa only [not_exists] using hincident
  have hweight : standardKleinDoubleGlobalWeight point index.2 = 0 := by
    unfold standardKleinDoubleGlobalWeight
    apply Finset.sum_eq_zero
    intro corner _
    simp only [habsent corner, if_false]
  -- The code coordinate is either this zero global weight or the masked value zero.
  simp only [standardKleinDoubleCode, hmask, if_true, hweight] at hpositive
  exact (lt_irrefl 0) hpositive

/-- Helper for Exercise 74.4: the compact closed star of a doubled-code coordinate in the
code model. -/
private def standardKleinDoubleClosedStar (index : Fin 2 × Fin 108) :
    Set StandardKleinDoubleModel :=
  ⋃ face : StandardKleinDoubleFace,
    if standardKleinDoubleFaceIncident index face then
      Set.range (fun point : stdSimplex ℝ (Fin 3) ↦
        standardKleinDoubleQuotient (face, point))
    else ∅

/-- Helper for Exercise 74.4: every doubled closed star is compact. -/
private lemma standardKleinDoubleClosedStar_isCompact (index : Fin 2 × Fin 108) :
    IsCompact (standardKleinDoubleClosedStar index) := by
  -- Each incident cell contributes a compact simplex image, and there are finitely many cells.
  unfold standardKleinDoubleClosedStar
  apply isCompact_iUnion
  intro face
  by_cases hincident : standardKleinDoubleFaceIncident index face
  · rw [if_pos hincident]
    apply isCompact_range
    exact continuous_standardKleinDoubleQuotient.comp
      (continuous_const.prodMk continuous_id)
  · rw [if_neg hincident]
    exact isCompact_empty

/-- Helper for Exercise 74.4: a positive coordinate puts the represented point in the
corresponding compact closed star, and that star is a neighborhood. -/
private lemma standardKleinDoubleClosedStar_mem_nhds
    (point : StandardKleinDoubleCarrier) (vertex : Fin 108)
    (hpositive : 0 < standardKleinDoubleGlobalWeight point vertex) :
    standardKleinDoubleClosedStar (point.1.1, vertex) ∈
      nhds (standardKleinDoubleQuotient point) := by
  -- The selected copy-coordinate is continuous on the code model and positive at `point`.
  let positiveSet : Set StandardKleinDoubleModel :=
    {code | 0 < code.1 (point.1.1, vertex)}
  have hcoordinate : Continuous
      (fun code : StandardKleinDoubleModel ↦ code.1 (point.1.1, vertex)) :=
    (continuous_apply (point.1.1, vertex)).comp continuous_subtype_val
  have hopen : IsOpen positiveSet := by
    exact isOpen_lt continuous_const hcoordinate
  have hpoint : standardKleinDoubleQuotient point ∈ positiveSet := by
    change 0 < standardKleinDoubleCode point (point.1.1, vertex)
    simpa only [standardKleinDoubleCode, true_or, if_true] using hpositive
  apply Filter.mem_of_superset (hopen.mem_nhds hpoint)
  intro code hcode
  -- Choose any representative of the positive code; positivity forces its cell to be incident.
  obtain ⟨representative, hrepresentative⟩ :=
    standardKleinDoubleQuotient_surjective code
  have hcodePositive :
      0 < standardKleinDoubleCode representative (point.1.1, vertex) := by
    have hrewritten := hcode
    rw [← hrepresentative] at hrewritten
    exact hrewritten
  have hincident : standardKleinDoubleFaceIncident
      (point.1.1, vertex) representative.1 :=
    standardKleinDoubleFaceIncident_of_code_pos representative
      (point.1.1, vertex) hcodePositive
  unfold standardKleinDoubleClosedStar
  apply Set.mem_iUnion.mpr
  refine ⟨representative.1, ?_⟩
  rw [if_pos hincident]
  exact ⟨representative.2, hrepresentative⟩

/-- Helper for Exercise 74.4: membership in a doubled closed star supplies an incident
simplex representative of the same code point. -/
private lemma standardKleinDouble_exists_incident_rep_of_mem_closedStar
    (index : Fin 2 × Fin 108) (code : StandardKleinDoubleModel)
    (hcode : code ∈ standardKleinDoubleClosedStar index) :
    ∃ point : StandardKleinDoubleCarrier,
      standardKleinDoubleFaceIncident index point.1 ∧
        standardKleinDoubleQuotient point = code := by
  -- Unpack the finite union and discard its empty nonincident branches.
  unfold standardKleinDoubleClosedStar at hcode
  obtain ⟨face, hface⟩ := Set.mem_iUnion.mp hcode
  by_cases hincident : standardKleinDoubleFaceIncident index face
  · rw [if_pos hincident] at hface
    obtain ⟨point, hpoint⟩ := hface
    exact ⟨(face, point), hincident, hpoint⟩
  · rw [if_neg hincident] at hface
    exact hface.elim

/-- Helper for Exercise 74.4: two original mesh faces incident to the same displayed vertex
are equal, share an edge, or meet only at that vertex. -/
private lemma standardKleinIncidentFaces_classification :
    ∀ (face other : Fin 216) (corner otherCorner : Fin 3),
      standardKleinFace face corner = standardKleinFace other otherCorner →
        face = other ∨ standardKleinFacesShareEdge face other ∨
          standardKleinFacesMeetOnlyAt face other (standardKleinFace face corner) := by
  -- Cache the exhaustive incidence calculation once, before the affine cases are considered.
  native_decide

/-- Helper for Exercise 74.4: incident faces with different copy tags must be incident through
an attachment-triangle vertex. -/
private lemma standardKleinAttachmentVertex_of_incident_of_copy_ne
    (index : Fin 2 × Fin 108) (a b : StandardKleinDoubleFace)
    (ha : standardKleinDoubleFaceIncident index a)
    (hb : standardKleinDoubleFaceIncident index b) (hab : a.1 ≠ b.1) :
    standardKleinAttachmentVertex index.2 := by
  -- Away from the attachment triangle, both incidence masks force the selected copy tag.
  rcases ha.1 with haCopy | haAttachment
  · rcases hb.1 with hbCopy | hbAttachment
    · exact False.elim (hab (haCopy.symm.trans hbCopy))
    · exact hbAttachment
  · exact haAttachment

/-- Helper for Exercise 74.4: reflection in the attachment plane is an involution. -/
private lemma standardKleinReflection_involutive :
    Function.Involutive standardKleinReflection := by
  intro point
  -- The second reflection uses the negated signed coordinate, so its correction cancels.
  funext coordinate
  simp only [standardKleinReflection, reflectAcrossAffinePlane]
  rw [affinePlaneCoordinate_reflectAcross _ _ _
    standardKleinAttachmentNormalSquare_ne_zero]
  ring

/-- Helper for Exercise 74.4: for representatives in one copy, equality of reflected targets
already implies equality of their unreflected affine targets. -/
private lemma standardKleinDoubleBaseTarget_eq_of_target_eq_of_copy_eq
    (a b : StandardKleinDoubleCarrier) (hcopy : a.1.1 = b.1.1)
    (htarget : standardKleinDoubleTarget a = standardKleinDoubleTarget b) :
    standardKleinDoubleBaseTarget a = standardKleinDoubleBaseTarget b := by
  -- Remove the Euclidean `WithLp` wrapper, then inspect the common copy branch.
  have hcoordinates : standardKleinDoubleTargetCoordinates a =
      standardKleinDoubleTargetCoordinates b := by
    exact WithLp.toLp_injective 2 htarget
  by_cases haZero : a.1.1 = 0
  · have hbZero : b.1.1 = 0 := hcopy.symm.trans haZero
    simpa only [standardKleinDoubleTargetCoordinates, haZero, hbZero, if_true] using
      hcoordinates
  · have hbZero : b.1.1 ≠ 0 := by
      intro hbZero
      exact haZero (hcopy.trans hbZero)
    have hreflected : standardKleinReflection (standardKleinDoubleBaseTarget a) =
        standardKleinReflection (standardKleinDoubleBaseTarget b) := by
      simpa only [standardKleinDoubleTargetCoordinates, haZero, hbZero, if_false] using
        hcoordinates
    exact standardKleinReflection_involutive.injective hreflected

/-- Helper for Exercise 74.4: a real triangle has a nonzero two-coordinate edge minor. -/
private abbrev realTriangleHasNonzeroMinor (point : Fin 3 → Fin 3 → ℝ) : Prop :=
  let u := fun coordinate ↦ point 1 coordinate - point 0 coordinate
  let w := fun coordinate ↦ point 2 coordinate - point 0 coordinate
  u 0 * w 1 - u 1 * w 0 ≠ 0 ∨
    u 0 * w 2 - u 2 * w 0 ≠ 0 ∨
      u 1 * w 2 - u 2 * w 1 ≠ 0

/-- Helper for Exercise 74.4: barycentric weights on a nondegenerate real triangle are
determined by their affine combination. -/
private lemma triangleWeights_eq_of_nonzeroMinor
    (point : Fin 3 → Fin 3 → ℝ) (weight otherWeight : Fin 3 → ℝ)
    (hnondegenerate : realTriangleHasNonzeroMinor point)
    (hweightSum : ∑ i, weight i = 1) (hotherWeightSum : ∑ i, otherWeight i = 1)
    (haffine :
      (fun coordinate ↦ ∑ i, weight i * point i coordinate) =
        fun coordinate ↦ ∑ i, otherWeight i * point i coordinate) :
    weight = otherWeight := by
  -- Subtracting the zeroth vertex turns affine equality into a two-vector linear relation.
  let difference : Fin 3 → ℝ := fun i ↦ weight i - otherWeight i
  let u : Fin 3 → ℝ := fun coordinate ↦ point 1 coordinate - point 0 coordinate
  let w : Fin 3 → ℝ := fun coordinate ↦ point 2 coordinate - point 0 coordinate
  have hdifferenceSum : difference 0 + difference 1 + difference 2 = 0 := by
    simp only [Fin.sum_univ_three] at hweightSum hotherWeightSum
    dsimp only [difference]
    linarith
  have hlinear (coordinate : Fin 3) :
      difference 1 * u coordinate + difference 2 * w coordinate = 0 := by
    have hcoordinate := congrFun haffine coordinate
    simp only [Fin.sum_univ_three] at hcoordinate
    dsimp only [difference] at hdifferenceSum
    dsimp only [difference, u, w]
    linear_combination hcoordinate - point 0 coordinate * hdifferenceSum
  have solveMinor (first second : Fin 3)
      (hminor : u first * w second - u second * w first ≠ 0) :
      weight = otherWeight := by
    have honeProduct : difference 1 *
        (u first * w second - u second * w first) = 0 := by
      linear_combination w second * hlinear first - w first * hlinear second
    have htwoProduct : difference 2 *
        (u first * w second - u second * w first) = 0 := by
      linear_combination u first * hlinear second - u second * hlinear first
    have hone : difference 1 = 0 := (mul_eq_zero.mp honeProduct).resolve_right hminor
    have htwo : difference 2 = 0 := (mul_eq_zero.mp htwoProduct).resolve_right hminor
    have hzero : difference 0 = 0 := by linarith
    funext i
    fin_cases i
    · exact sub_eq_zero.mp hzero
    · exact sub_eq_zero.mp hone
    · exact sub_eq_zero.mp htwo
  -- One certified coordinate minor is enough to solve the two remaining coefficients.
  rcases hnondegenerate with hminor | hminor | hminor
  · exact solveMinor 0 1 hminor
  · exact solveMinor 0 2 hminor
  · exact solveMinor 1 2 hminor

/-- Helper for Exercise 74.4: the real control triangle of every exact mesh face has a
nonzero coordinate minor. -/
private lemma standardKleinFace_realNondegenerate (face : Fin 216) :
    realTriangleHasNonzeroMinor
      (fun corner coordinate ↦ (standardKleinControl
        (standardKleinFace face corner) coordinate : ℝ)) := by
  -- Cast the exact integer minor certificate to the real control vectors.
  have hnondegenerate := standardKleinControlCertificate.1 face
  dsimp only [standardKleinFaceNondegenerate, fourFoldControlSub,
    realTriangleHasNonzeroMinor] at hnondegenerate ⊢
  rcases hnondegenerate with hminor | hminor | hminor
  · left
    exact_mod_cast hminor
  · right
    left
    exact_mod_cast hminor
  · right
    right
    exact_mod_cast hminor

/-- Helper for Exercise 74.4: the generic real nondegeneracy certificate restricts to every
retained face. -/
private lemma standardKleinRetainedFace_realNondegenerate
    (face : StandardKleinRetainedFace) :
    realTriangleHasNonzeroMinor
      (fun corner coordinate ↦ (standardKleinControl
        (standardKleinFace face corner) coordinate : ℝ)) := by
  -- Forget only the proof that this face is not the deleted attachment face.
  exact standardKleinFace_realNondegenerate face

/-- Helper for Exercise 74.4: the real origin of an exact mesh face. -/
private def standardKleinFaceOrigin (face : Fin 216) : Fin 3 → ℝ :=
  fun coordinate ↦ standardKleinControl (standardKleinFace face 0) coordinate

/-- Helper for Exercise 74.4: the real cross-product normal of an exact mesh face. -/
private def standardKleinFaceNormal (face : Fin 216) : Fin 3 → ℝ :=
  let a := standardKleinControl (standardKleinFace face 0)
  let b := standardKleinControl (standardKleinFace face 1)
  let c := standardKleinControl (standardKleinFace face 2)
  let u := fourFoldControlSub b a
  let w := fourFoldControlSub c a
  ![u 1 * w 2 - u 2 * w 1, u 2 * w 0 - u 0 * w 2,
    u 0 * w 1 - u 1 * w 0]

/-- Helper for Exercise 74.4: the real signed face coordinate of a control vertex is the
cast exact signed volume. -/
private lemma standardKleinFaceCoordinate_control
    (face : Fin 216) (vertex : Fin 108) :
    affinePlaneCoordinate (standardKleinFaceOrigin face) (standardKleinFaceNormal face)
        (fun coordinate ↦ (standardKleinControl vertex coordinate : ℝ)) =
      (standardKleinFaceVolume face vertex : ℝ) := by
  -- Expand the cross product and determinant once; integer casts preserve the formula.
  unfold affinePlaneCoordinate dotThree standardKleinFaceOrigin standardKleinFaceNormal
    standardKleinFaceVolume fourFoldControlDet fourFoldControlSub
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul]
  simp
  ring

/-- Helper for Exercise 74.4: every control vertex of a face has zero signed coordinate in
that face's plane. -/
private lemma standardKleinFaceVolume_self (face : Fin 216) (corner : Fin 3) :
    standardKleinFaceVolume face (standardKleinFace face corner) = 0 := by
  -- At each of the three corners the third determinant vector is zero or repeats an edge.
  fin_cases corner <;>
    simp [standardKleinFaceVolume, fourFoldControlDet, fourFoldControlSub] <;>
    ring

/-- Helper for Exercise 74.4: the signed coordinate of a barycentric target is the weighted
sum of its three exact face volumes. -/
private lemma standardKleinFaceCoordinate_baseTarget
    (face : Fin 216) (point : StandardKleinDoubleCarrier) :
    affinePlaneCoordinate (standardKleinFaceOrigin face) (standardKleinFaceNormal face)
        (standardKleinDoubleBaseTarget point) =
      ∑ corner : Fin 3, point.2.1 corner *
        (standardKleinFaceVolume face (standardKleinFace point.1.2 corner) : ℝ) := by
  -- Commute the affine coordinate through the simplex combination, then use the exact
  -- control-vertex bridge in each summand.
  unfold standardKleinDoubleBaseTarget
  rw [affinePlaneCoordinate_weighted_sum _ _ point.2.1
    (fun corner coordinate ↦
      (standardKleinControl (standardKleinFace point.1.2 corner) coordinate : ℝ))
    point.2.2.2]
  apply Finset.sum_congr rfl
  intro corner _
  rw [standardKleinFaceCoordinate_control]

/-- Helper for Exercise 74.4: the generic face origin at face 114 is the selected
attachment origin. -/
private lemma standardKleinFaceOrigin_attachment :
    standardKleinFaceOrigin 114 = standardKleinAttachmentOrigin := by
  -- Both definitions select the zeroth control vertex of face 114.
  rfl

/-- Helper for Exercise 74.4: the generic face normal at face 114 is the selected
attachment normal. -/
private lemma standardKleinFaceNormal_attachment :
    standardKleinFaceNormal 114 = standardKleinAttachmentNormal := by
  -- Both normals are the same exact integer cross product, cast coordinatewise to reals.
  funext coordinate
  fin_cases coordinate <;>
    simp [standardKleinFaceNormal, standardKleinAttachmentNormal,
      standardKleinAttachmentNormalInt, fourFoldControlSub]

/-- Helper for Exercise 74.4: incidence through an attachment vertex makes a retained face
meet the deleted attachment triangle. -/
private lemma standardKleinFaceMeetsAttachment_of_incident
    (index : Fin 2 × Fin 108) (point : StandardKleinDoubleCarrier)
    (hincident : standardKleinDoubleFaceIncident index point.1)
    (hattachment : standardKleinAttachmentVertex index.2) :
    standardKleinFaceMeetsAttachment point.1.2 := by
  -- Pair the incident corner with whichever of the three attachment corners names the index.
  obtain ⟨corner, hcorner⟩ := hincident.2
  rcases hattachment with hattachment | hattachment | hattachment
  · exact ⟨corner, 0, hcorner.trans hattachment⟩
  · exact ⟨corner, 1, hcorner.trans hattachment⟩
  · exact ⟨corner, 2, hcorner.trans hattachment⟩

/-- Helper for Exercise 74.4: on a face meeting the attachment triangle, every local
signed-volume summand is nonpositive. -/
private lemma standardKleinAttachmentSummand_nonpositive
    (point : StandardKleinDoubleCarrier)
    (hmeets : standardKleinFaceMeetsAttachment point.1.2) (corner : Fin 3) :
    point.2.1 corner *
      (standardKleinFaceVolume 114 (standardKleinFace point.1.2 corner) : ℝ) ≤ 0 := by
  by_cases hattachment :
      standardKleinAttachmentVertex (standardKleinFace point.1.2 corner)
  · -- Attachment vertices lie in face 114 and hence have zero signed volume.
    rcases hattachment with hattachment | hattachment | hattachment
    · rw [hattachment, standardKleinFaceVolume_self, Int.cast_zero, mul_zero]
    · rw [hattachment, standardKleinFaceVolume_self, Int.cast_zero, mul_zero]
    · rw [hattachment, standardKleinFaceVolume_self, Int.cast_zero, mul_zero]
  · -- Every other incident-star vertex lies strictly on the certified negative side.
    apply mul_nonpos_of_nonneg_of_nonpos (point.2.2.1 corner)
    have hstrict := standardKleinControlCertificate.2.2.2 point.1.2 hmeets corner
      (by
        intro attachmentCorner heq
        apply hattachment
        fin_cases attachmentCorner
        · exact Or.inl heq
        · exact Or.inr (Or.inl heq)
        · exact Or.inr (Or.inr heq))
    exact_mod_cast le_of_lt hstrict

/-- Helper for Exercise 74.4: a retained face meeting the attachment triangle lies in the
nonpositive supporting halfspace, and equality characterizes attachment-supported weights. -/
private lemma standardKleinAttachmentCoordinate_nonpositive_and_boundary
    (point : StandardKleinDoubleCarrier)
    (hmeets : standardKleinFaceMeetsAttachment point.1.2) :
    let coordinate := affinePlaneCoordinate standardKleinAttachmentOrigin
      standardKleinAttachmentNormal (standardKleinDoubleBaseTarget point)
    coordinate ≤ 0 ∧ (coordinate = 0 → standardKleinOnAttachmentBoundary point) := by
  -- Normalize the signed coordinate to the sum of the three exact signed-volume terms.
  dsimp only
  have hcoordinate :
      affinePlaneCoordinate standardKleinAttachmentOrigin standardKleinAttachmentNormal
          (standardKleinDoubleBaseTarget point) =
        ∑ corner : Fin 3, point.2.1 corner *
          (standardKleinFaceVolume 114 (standardKleinFace point.1.2 corner) : ℝ) := by
    rw [← standardKleinFaceOrigin_attachment, ← standardKleinFaceNormal_attachment]
    exact standardKleinFaceCoordinate_baseTarget 114 point
  constructor
  · rw [hcoordinate]
    exact Finset.sum_nonpos fun corner _ ↦
      standardKleinAttachmentSummand_nonpositive point hmeets corner
  · intro hzero vertex hvertex
    rw [hcoordinate] at hzero
    have hsummandZero (corner : Fin 3) :
        point.2.1 corner *
          (standardKleinFaceVolume 114 (standardKleinFace point.1.2 corner) : ℝ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos (fun i _ ↦
        standardKleinAttachmentSummand_nonpositive point hmeets i)).mp
          hzero corner (Finset.mem_univ corner)
    -- Each local coefficient contributing to a nonattachment global vertex vanishes,
    -- because its supporting signed volume is strictly negative.
    unfold standardKleinDoubleGlobalWeight
    apply Finset.sum_eq_zero
    intro corner _
    by_cases hcorner : standardKleinFace point.1.2 corner = vertex
    · rw [if_pos hcorner]
      have hstrict := standardKleinControlCertificate.2.2.2 point.1.2 hmeets corner
        (by
          intro attachmentCorner heq
          apply hvertex
          rw [← hcorner]
          fin_cases attachmentCorner
          · exact Or.inl heq
          · exact Or.inr (Or.inl heq)
          · exact Or.inr (Or.inr heq))
      have hvolume :
          (standardKleinFaceVolume 114
            (standardKleinFace point.1.2 corner) : ℝ) ≠ 0 := by
        exact_mod_cast ne_of_lt hstrict
      exact (mul_eq_zero.mp (hsummandZero corner)).resolve_right hvolume
    · rw [if_neg hcorner]

/-- Helper for Exercise 74.4: the three global weights at the attachment vertices. -/
private def standardKleinAttachmentWeight
    (point : StandardKleinDoubleCarrier) (corner : Fin 3) : ℝ :=
  standardKleinDoubleGlobalWeight point (standardKleinFace 114 corner)

/-- Helper for Exercise 74.4: attachment-supported global weights sum to one. -/
private lemma standardKleinAttachmentWeight_sum
    (point : StandardKleinDoubleCarrier)
    (hboundary : standardKleinOnAttachmentBoundary point) :
    ∑ corner : Fin 3, standardKleinAttachmentWeight point corner = 1 := by
  -- Reindex the global sum over the three injectively listed attachment vertices; every
  -- vertex outside that image has zero boundary weight.
  have himage :
      (∑ corner : Fin 3,
        standardKleinDoubleGlobalWeight point (standardKleinFace 114 corner)) =
        ∑ vertex ∈ Finset.univ.image (standardKleinFace 114),
          standardKleinDoubleGlobalWeight point vertex := by
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact standardKleinAttachmentFace_injective hij
  rw [show (∑ corner : Fin 3, standardKleinAttachmentWeight point corner) =
    ∑ corner : Fin 3,
      standardKleinDoubleGlobalWeight point (standardKleinFace 114 corner) by rfl,
    himage]
  calc
    (∑ vertex ∈ Finset.univ.image (standardKleinFace 114),
        standardKleinDoubleGlobalWeight point vertex) =
        ∑ vertex : Fin 108, standardKleinDoubleGlobalWeight point vertex := by
      apply Finset.sum_subset
      · exact Finset.subset_univ _
      · intro vertex _ hvertex
        apply hboundary vertex
        intro hattachment
        rcases hattachment with hattachment | hattachment | hattachment
        · exact hvertex (Finset.mem_image.mpr
            ⟨0, Finset.mem_univ 0, hattachment.symm⟩)
        · exact hvertex (Finset.mem_image.mpr
            ⟨1, Finset.mem_univ 1, hattachment.symm⟩)
        · exact hvertex (Finset.mem_image.mpr
            ⟨2, Finset.mem_univ 2, hattachment.symm⟩)
    _ = 1 := standardKleinDoubleGlobalWeight_sum point

/-- Helper for Exercise 74.4: an attachment-supported base target is the affine combination
of the three attachment controls with its attachment weights. -/
private lemma standardKleinAttachmentWeight_target
    (point : StandardKleinDoubleCarrier)
    (hboundary : standardKleinOnAttachmentBoundary point) :
    (fun coordinate ↦ ∑ corner : Fin 3, standardKleinAttachmentWeight point corner *
      (standardKleinControl (standardKleinFace 114 corner) coordinate : ℝ)) =
      standardKleinDoubleBaseTarget point := by
  rw [standardKleinDoubleBaseTarget_eq_globalTarget]
  funext coordinate
  unfold standardKleinDoubleGlobalTarget
  have himage :
      (∑ corner : Fin 3,
        standardKleinDoubleGlobalWeight point (standardKleinFace 114 corner) *
          (standardKleinControl (standardKleinFace 114 corner) coordinate : ℝ)) =
        ∑ vertex ∈ Finset.univ.image (standardKleinFace 114),
          standardKleinDoubleGlobalWeight point vertex *
            (standardKleinControl vertex coordinate : ℝ) := by
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact standardKleinAttachmentFace_injective hij
  rw [show (∑ corner : Fin 3, standardKleinAttachmentWeight point corner *
      (standardKleinControl (standardKleinFace 114 corner) coordinate : ℝ)) =
    ∑ corner : Fin 3,
      standardKleinDoubleGlobalWeight point (standardKleinFace 114 corner) *
        (standardKleinControl (standardKleinFace 114 corner) coordinate : ℝ) by rfl,
    himage]
  apply Finset.sum_subset
  · exact Finset.subset_univ _
  · intro vertex _ hvertex
    rw [hboundary vertex, zero_mul]
    intro hattachment
    rcases hattachment with hattachment | hattachment | hattachment
    · exact hvertex (Finset.mem_image.mpr
        ⟨0, Finset.mem_univ 0, hattachment.symm⟩)
    · exact hvertex (Finset.mem_image.mpr
        ⟨1, Finset.mem_univ 1, hattachment.symm⟩)
    · exact hvertex (Finset.mem_image.mpr
        ⟨2, Finset.mem_univ 2, hattachment.symm⟩)

/-- Helper for Exercise 74.4: attachment-supported representatives with equal base targets
have the same global mesh weights. -/
private lemma standardKleinSameGlobalWeights_of_attachmentBoundary_baseTarget_eq
    (a b : StandardKleinDoubleCarrier)
    (haBoundary : standardKleinOnAttachmentBoundary a)
    (hbBoundary : standardKleinOnAttachmentBoundary b)
    (hbase : standardKleinDoubleBaseTarget a = standardKleinDoubleBaseTarget b) :
    standardKleinSameGlobalWeights a b := by
  -- Affine uniqueness on the nondegenerate attachment triangle identifies its three weights.
  have hweights : standardKleinAttachmentWeight a = standardKleinAttachmentWeight b := by
    apply triangleWeights_eq_of_nonzeroMinor
      (fun corner coordinate ↦
        (standardKleinControl (standardKleinFace 114 corner) coordinate : ℝ))
      (standardKleinAttachmentWeight a) (standardKleinAttachmentWeight b)
      (standardKleinFace_realNondegenerate 114)
      (standardKleinAttachmentWeight_sum a haBoundary)
      (standardKleinAttachmentWeight_sum b hbBoundary)
    calc
      (fun coordinate ↦ ∑ i, standardKleinAttachmentWeight a i *
          (standardKleinControl (standardKleinFace 114 i) coordinate : ℝ)) =
          standardKleinDoubleBaseTarget a :=
        standardKleinAttachmentWeight_target a haBoundary
      _ = standardKleinDoubleBaseTarget b := hbase
      _ = (fun coordinate ↦ ∑ i, standardKleinAttachmentWeight b i *
          (standardKleinControl (standardKleinFace 114 i) coordinate : ℝ)) :=
        (standardKleinAttachmentWeight_target b hbBoundary).symm
  -- Off the attachment both sides vanish; at its three vertices use the corresponding
  -- attachment coordinate equality.
  funext vertex
  by_cases hattachment : standardKleinAttachmentVertex vertex
  · rcases hattachment with hattachment | hattachment | hattachment
    · simpa only [standardKleinAttachmentWeight, hattachment] using congrFun hweights 0
    · simpa only [standardKleinAttachmentWeight, hattachment] using congrFun hweights 1
    · simpa only [standardKleinAttachmentWeight, hattachment] using congrFun hweights 2
  · rw [haBoundary vertex hattachment, hbBoundary vertex hattachment]

/-- Helper for Exercise 74.4: every exact mesh face lists three distinct vertices. -/
private lemma standardKleinFace_injective :
    ∀ face : Fin 216, Function.Injective (standardKleinFace face) := by
  -- Check injectivity for the finite six-block face table.
  native_decide

/-- Helper for Exercise 74.4: on two distinct edge-sharing faces with equal affine targets,
the coefficient of a vertex outside the first face vanishes. -/
private lemma standardKleinWeight_eq_zero_of_sharedEdge_of_not_mem
    (a b : StandardKleinDoubleCarrier)
    (hface : (a.1.2 : Fin 216) ≠ (b.1.2 : Fin 216))
    (hshare : standardKleinFacesShareEdge a.1.2 b.1.2)
    (hbase : standardKleinDoubleBaseTarget a = standardKleinDoubleBaseTarget b)
    (corner : Fin 3)
    (hcorner : ∀ i : Fin 3,
      standardKleinFace b.1.2 corner ≠ standardKleinFace a.1.2 i) :
    b.2.1 corner = 0 := by
  -- Choose the two displayed common edge corners and show they exhaust the other corners
  -- of the second triangle.
  have hdistinctPlanes :=
    standardKleinControlCertificate.2.1 a.1.2 b.1.2 hface hshare
  obtain ⟨i, j, hij, k, l, hik, hjl⟩ := hshare
  have hkl : k ≠ l := by
    intro hkl
    apply hij
    apply standardKleinFace_injective a.1.2
    calc
      standardKleinFace a.1.2 i = standardKleinFace b.1.2 k := hik
      _ = standardKleinFace b.1.2 l := congrArg (standardKleinFace b.1.2) hkl
      _ = standardKleinFace a.1.2 j := hjl.symm
  have hcornerK : corner ≠ k := by
    intro hcornerK
    exact hcorner i (congrArg (standardKleinFace b.1.2) hcornerK |>.trans hik.symm)
  have hcornerL : corner ≠ l := by
    intro hcornerL
    exact hcorner j (congrArg (standardKleinFace b.1.2) hcornerL |>.trans hjl.symm)
  have hcorners (r : Fin 3) : r = corner ∨ r = k ∨ r = l := by
    fin_cases corner <;> fin_cases k <;> fin_cases l <;> fin_cases r <;>
      simp_all
  have hvolumeOther (r : Fin 3) (hr : r ≠ corner) :
      standardKleinFaceVolume a.1.2 (standardKleinFace b.1.2 r) = 0 := by
    rcases hcorners r with rfl | rfl | rfl
    · exact False.elim (hr rfl)
    · rw [← hik]
      exact standardKleinFaceVolume_self a.1.2 i
    · rw [← hjl]
      exact standardKleinFaceVolume_self a.1.2 j
  -- Distinct supporting planes force the remaining corner to have nonzero signed volume.
  obtain ⟨outside, houtside⟩ := hdistinctPlanes
  have houtsideCorner : outside = corner := by
    by_contra houtsideCorner
    exact houtside (hvolumeOther outside houtsideCorner)
  have hcornerVolume :
      standardKleinFaceVolume a.1.2 (standardKleinFace b.1.2 corner) ≠ 0 := by
    rwa [houtsideCorner] at houtside
  -- Apply the first face's signed coordinate to target equality. Its own triangle has
  -- coordinate zero, so only the outside coefficient survives on the second triangle.
  have haCoordinate :
      affinePlaneCoordinate (standardKleinFaceOrigin a.1.2)
          (standardKleinFaceNormal a.1.2) (standardKleinDoubleBaseTarget a) = 0 := by
    rw [standardKleinFaceCoordinate_baseTarget]
    apply Finset.sum_eq_zero
    intro r _
    rw [standardKleinFaceVolume_self, Int.cast_zero, mul_zero]
  have hbCoordinate :
      affinePlaneCoordinate (standardKleinFaceOrigin a.1.2)
          (standardKleinFaceNormal a.1.2) (standardKleinDoubleBaseTarget b) = 0 := by
    rw [← hbase]
    exact haCoordinate
  rw [standardKleinFaceCoordinate_baseTarget] at hbCoordinate
  have hsingle :
      (∑ r : Fin 3, b.2.1 r *
        (standardKleinFaceVolume a.1.2 (standardKleinFace b.1.2 r) : ℝ)) =
        b.2.1 corner *
          (standardKleinFaceVolume a.1.2 (standardKleinFace b.1.2 corner) : ℝ) := by
    apply Finset.sum_eq_single corner
    · intro r _ hr
      rw [hvolumeOther r hr, Int.cast_zero, mul_zero]
    · simp
  rw [hsingle] at hbCoordinate
  have hcornerVolumeReal :
      (standardKleinFaceVolume a.1.2
        (standardKleinFace b.1.2 corner) : ℝ) ≠ 0 := by
    exact_mod_cast hcornerVolume
  exact (mul_eq_zero.mp hbCoordinate).resolve_right hcornerVolumeReal

/-- Helper for Exercise 74.4: a local barycentric coefficient is the global weight of its
face vertex. -/
private lemma standardKleinDoubleGlobalWeight_face
    (point : StandardKleinDoubleCarrier) (corner : Fin 3) :
    standardKleinDoubleGlobalWeight point (standardKleinFace point.1.2 corner) =
      point.2.1 corner := by
  -- Face injectivity makes the selected corner the unique nonzero summand.
  unfold standardKleinDoubleGlobalWeight
  rw [Fin.sum_univ_three]
  have hzeroOne : standardKleinFace point.1.2 0 ≠ standardKleinFace point.1.2 1 := by
    intro heq
    have := standardKleinFace_injective point.1.2 heq
    omega
  have hzeroTwo : standardKleinFace point.1.2 0 ≠ standardKleinFace point.1.2 2 := by
    intro heq
    have := standardKleinFace_injective point.1.2 heq
    omega
  have honeTwo : standardKleinFace point.1.2 1 ≠ standardKleinFace point.1.2 2 := by
    intro heq
    have := standardKleinFace_injective point.1.2 heq
    omega
  fin_cases corner <;>
    simp [hzeroOne, hzeroTwo, honeTwo, Ne.symm hzeroOne,
      Ne.symm hzeroTwo, Ne.symm honeTwo]

/-- Helper for Exercise 74.4: a vertex absent from a representative's face has global
weight zero. -/
private lemma standardKleinDoubleGlobalWeight_eq_zero_of_not_mem
    (point : StandardKleinDoubleCarrier) (vertex : Fin 108)
    (hvertex : ∀ corner : Fin 3, vertex ≠ standardKleinFace point.1.2 corner) :
    standardKleinDoubleGlobalWeight point vertex = 0 := by
  -- Every conditional summand selects the absent vertex and is therefore zero.
  unfold standardKleinDoubleGlobalWeight
  apply Finset.sum_eq_zero
  intro corner _
  rw [if_neg]
  exact Ne.symm (hvertex corner)

/-- Helper for Exercise 74.4: equal affine targets have equal global weights when the
second representative is supported on the first representative's face. -/
private lemma standardKleinSameGlobalWeights_of_baseTarget_eq_of_support
    (a b : StandardKleinDoubleCarrier)
    (hbase : standardKleinDoubleBaseTarget a = standardKleinDoubleBaseTarget b)
    (hsupport : ∀ corner : Fin 3,
      (∀ i : Fin 3,
        standardKleinFace b.1.2 corner ≠ standardKleinFace a.1.2 i) →
        b.2.1 corner = 0) :
    standardKleinSameGlobalWeights a b := by
  -- Extend the second representative to global weights, then restrict those weights to
  -- the three distinct vertices of the first face.
  let transferred : Fin 3 → ℝ := fun i ↦
    standardKleinDoubleGlobalWeight b (standardKleinFace a.1.2 i)
  have hbOutside (vertex : Fin 108)
      (hvertex : ∀ i : Fin 3, vertex ≠ standardKleinFace a.1.2 i) :
      standardKleinDoubleGlobalWeight b vertex = 0 := by
    unfold standardKleinDoubleGlobalWeight
    apply Finset.sum_eq_zero
    intro corner _
    by_cases hcorner : standardKleinFace b.1.2 corner = vertex
    · rw [if_pos hcorner, hsupport corner]
      intro i heq
      exact hvertex i (hcorner.symm.trans heq)
    · rw [if_neg hcorner]
  have htransferredSum : ∑ i, transferred i = 1 := by
    have himage :
        (∑ i : Fin 3, standardKleinDoubleGlobalWeight b
          (standardKleinFace a.1.2 i)) =
          ∑ vertex ∈ Finset.univ.image (standardKleinFace a.1.2),
            standardKleinDoubleGlobalWeight b vertex := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      exact standardKleinFace_injective a.1.2 hij
    rw [show (∑ i, transferred i) =
      ∑ i : Fin 3, standardKleinDoubleGlobalWeight b
        (standardKleinFace a.1.2 i) by rfl, himage]
    calc
      (∑ vertex ∈ Finset.univ.image (standardKleinFace a.1.2),
          standardKleinDoubleGlobalWeight b vertex) =
          ∑ vertex : Fin 108, standardKleinDoubleGlobalWeight b vertex := by
        apply Finset.sum_subset
        · exact Finset.subset_univ _
        · intro vertex _ hvertex
          apply hbOutside vertex
          intro i heq
          exact hvertex (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩)
      _ = 1 := standardKleinDoubleGlobalWeight_sum b
  have htransferredTarget :
      (fun coordinate ↦ ∑ i, transferred i *
        (standardKleinControl (standardKleinFace a.1.2 i) coordinate : ℝ)) =
        standardKleinDoubleBaseTarget b := by
    rw [standardKleinDoubleBaseTarget_eq_globalTarget]
    funext coordinate
    unfold standardKleinDoubleGlobalTarget
    have himage :
        (∑ i : Fin 3, standardKleinDoubleGlobalWeight b
          (standardKleinFace a.1.2 i) *
            (standardKleinControl (standardKleinFace a.1.2 i) coordinate : ℝ)) =
          ∑ vertex ∈ Finset.univ.image (standardKleinFace a.1.2),
            standardKleinDoubleGlobalWeight b vertex *
              (standardKleinControl vertex coordinate : ℝ) := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      exact standardKleinFace_injective a.1.2 hij
    rw [show (∑ i, transferred i *
      (standardKleinControl (standardKleinFace a.1.2 i) coordinate : ℝ)) =
      ∑ i : Fin 3, standardKleinDoubleGlobalWeight b
        (standardKleinFace a.1.2 i) *
          (standardKleinControl (standardKleinFace a.1.2 i) coordinate : ℝ) by rfl,
      himage]
    apply Finset.sum_subset
    · exact Finset.subset_univ _
    · intro vertex _ hvertex
      rw [hbOutside vertex, zero_mul]
      intro i heq
      exact hvertex (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩)
  have hweights : a.2.1 = transferred := by
    apply triangleWeights_eq_of_nonzeroMinor
      (fun corner coordinate ↦
        (standardKleinControl (standardKleinFace a.1.2 corner) coordinate : ℝ))
      a.2.1 transferred (standardKleinRetainedFace_realNondegenerate a.1.2)
      a.2.2.2 htransferredSum
    calc
      (fun coordinate ↦ ∑ i, a.2.1 i *
          (standardKleinControl (standardKleinFace a.1.2 i) coordinate : ℝ)) =
          standardKleinDoubleBaseTarget a := rfl
      _ = standardKleinDoubleBaseTarget b := hbase
      _ = (fun coordinate ↦ ∑ i, transferred i *
          (standardKleinControl (standardKleinFace a.1.2 i) coordinate : ℝ)) :=
        htransferredTarget.symm
  -- Compare a vertex on the first face using its unique corner; both functions vanish
  -- at every other vertex.
  funext vertex
  by_cases hvertex : ∃ i : Fin 3, vertex = standardKleinFace a.1.2 i
  · obtain ⟨i, rfl⟩ := hvertex
    rw [standardKleinDoubleGlobalWeight_face, congrFun hweights i]
  · rw [standardKleinDoubleGlobalWeight_eq_zero_of_not_mem a vertex,
      hbOutside vertex]
    · simpa only [not_exists] using hvertex
    · simpa only [not_exists] using hvertex

/-- Helper for Exercise 74.4: equal affine targets on two edge-sharing retained faces have
the same global mesh weights. -/
private lemma standardKleinSameGlobalWeights_of_sharedEdge_baseTarget_eq
    (a b : StandardKleinDoubleCarrier)
    (hface : (a.1.2 : Fin 216) ≠ (b.1.2 : Fin 216))
    (hshare : standardKleinFacesShareEdge a.1.2 b.1.2)
    (hbase : standardKleinDoubleBaseTarget a = standardKleinDoubleBaseTarget b) :
    standardKleinSameGlobalWeights a b := by
  -- The distinct-plane coordinate kills the only coefficient outside the common edge;
  -- the support-transfer lemma then reduces to affine uniqueness on the first face.
  apply standardKleinSameGlobalWeights_of_baseTarget_eq_of_support a b hbase
  intro corner hcorner
  exact standardKleinWeight_eq_zero_of_sharedEdge_of_not_mem
    a b hface hshare hbase corner hcorner

/-- Helper for Exercise 74.4: representatives on the same retained face with the same
affine target have identical global mesh weights. -/
private lemma standardKleinSameGlobalWeights_of_face_eq
    (a b : StandardKleinDoubleCarrier) (hface : a.1.2 = b.1.2)
    (hbase : standardKleinDoubleBaseTarget a = standardKleinDoubleBaseTarget b) :
    standardKleinSameGlobalWeights a b := by
  -- First use nondegeneracy to identify the three local barycentric coordinates.
  have hweights : a.2.1 = b.2.1 := by
    apply triangleWeights_eq_of_nonzeroMinor
      (fun corner coordinate ↦
        (standardKleinControl (standardKleinFace a.1.2 corner) coordinate : ℝ))
      a.2.1 b.2.1 (standardKleinRetainedFace_realNondegenerate a.1.2)
      a.2.2.2 b.2.2.2
    funext coordinate
    have hcoordinate := congrFun hbase coordinate
    simp only [standardKleinDoubleBaseTarget] at hcoordinate ⊢
    rw [← hface] at hcoordinate
    exact hcoordinate
  -- The common face and common local weights give the same global coordinate function.
  funext vertex
  unfold standardKleinDoubleGlobalWeight
  apply Finset.sum_congr rfl
  intro corner _
  rw [hface, congrFun hweights corner]

/-- Helper for Exercise 74.4: the two barycentric weights away from a selected corner. -/
private def standardKleinOtherFaceWeight
    (point : StandardKleinDoubleCarrier) (corner : Fin 3) : Fin 2 → ℝ :=
  match corner.1 with
  | 0 => ![point.2.1 1, point.2.1 2]
  | 1 => ![point.2.1 0, point.2.1 2]
  | _ => ![point.2.1 0, point.2.1 1]

/-- Helper for Exercise 74.4: subtracting a selected control vertex from a barycentric
target leaves the positive combination of the other two edge vectors. -/
private lemma standardKleinDoubleBaseTarget_sub_corner
    (point : StandardKleinDoubleCarrier) (corner : Fin 3) :
    (fun coordinate ↦ standardKleinDoubleBaseTarget point coordinate -
      (standardKleinControl (standardKleinFace point.1.2 corner) coordinate : ℝ)) =
      standardKleinOtherFaceWeight point corner 0 •
          (fun coordinate ↦ (fourFoldControlSub
            (standardKleinControl (standardKleinOtherFaceVertex point.1.2 corner 0))
            (standardKleinControl (standardKleinFace point.1.2 corner)) coordinate : ℝ)) +
        standardKleinOtherFaceWeight point corner 1 •
          (fun coordinate ↦ (fourFoldControlSub
            (standardKleinControl (standardKleinOtherFaceVertex point.1.2 corner 1))
            (standardKleinControl (standardKleinFace point.1.2 corner)) coordinate : ℝ)) := by
  -- There are three choices of selected corner; in each, eliminate its coefficient with
  -- the simplex sum-to-one identity.
  funext coordinate
  have hsum := point.2.2.2
  simp only [Fin.sum_univ_three] at hsum
  fin_cases corner
  · simp [standardKleinDoubleBaseTarget, Fin.sum_univ_three,
      standardKleinOtherFaceWeight, standardKleinOtherFaceVertex, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, fourFoldControlSub, Int.cast_sub]
    linear_combination
      (standardKleinControl (standardKleinFace point.1.2 0) coordinate : ℝ) * hsum
  · simp [standardKleinDoubleBaseTarget, Fin.sum_univ_three,
      standardKleinOtherFaceWeight, standardKleinOtherFaceVertex, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, fourFoldControlSub, Int.cast_sub]
    linear_combination
      (standardKleinControl (standardKleinFace point.1.2 1) coordinate : ℝ) * hsum
  · simp [standardKleinDoubleBaseTarget, Fin.sum_univ_three,
      standardKleinOtherFaceWeight, standardKleinOtherFaceVertex, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, fourFoldControlSub, Int.cast_sub]
    linear_combination
      (standardKleinControl (standardKleinFace point.1.2 2) coordinate : ℝ) * hsum

/-- Helper for Exercise 74.4: if the two weights away from a selected corner vanish, the
global weight function is the unit mass at that corner's mesh vertex. -/
private lemma standardKleinGlobalWeights_eq_single_of_otherWeights_eq_zero
    (point : StandardKleinDoubleCarrier) (corner : Fin 3)
    (hzero : standardKleinOtherFaceWeight point corner 0 = 0)
    (hone : standardKleinOtherFaceWeight point corner 1 = 0) :
    (fun vertex ↦ standardKleinDoubleGlobalWeight point vertex) =
      fun vertex ↦ if standardKleinFace point.1.2 corner = vertex then 1 else 0 := by
  -- The simplex sum makes the remaining corner coefficient one; the two other summands
  -- then vanish independently of their vertex tests.
  funext vertex
  have hsum := point.2.2.2
  simp only [Fin.sum_univ_three] at hsum
  fin_cases corner
  · simp [standardKleinOtherFaceWeight] at hzero hone
    have hcorner : point.2.1 0 = 1 := by linarith
    simp [standardKleinDoubleGlobalWeight, Fin.sum_univ_three,
      hzero, hone, hcorner]
  · simp [standardKleinOtherFaceWeight] at hzero hone
    have hcorner : point.2.1 1 = 1 := by linarith
    simp [standardKleinDoubleGlobalWeight, Fin.sum_univ_three,
      hzero, hone, hcorner]
  · simp [standardKleinOtherFaceWeight] at hzero hone
    have hcorner : point.2.1 2 = 1 := by linarith
    simp [standardKleinDoubleGlobalWeight, Fin.sum_univ_three,
      hzero, hone, hcorner]

/-- Helper for Exercise 74.4: if both incident triangles meet only at their displayed common
vertex, equality of affine targets forces all weight onto that vertex. -/
private lemma standardKleinSameGlobalWeights_of_vertexOnly_baseTarget_eq
    (a b : StandardKleinDoubleCarrier) (corner otherCorner : Fin 3)
    (heq : standardKleinFace a.1.2 corner = standardKleinFace b.1.2 otherCorner)
    (honly : standardKleinFacesMeetOnlyAt a.1.2 b.1.2
      (standardKleinFace a.1.2 corner))
    (hbase : standardKleinDoubleBaseTarget a = standardKleinDoubleBaseTarget b) :
    standardKleinSameGlobalWeights a b := by
  -- Normalize both affine targets at the common control vertex and apply link separation.
  have hlinear :
      standardKleinOtherFaceWeight a corner 0 •
          (fun coordinate ↦ (fourFoldControlSub
            (standardKleinControl (standardKleinOtherFaceVertex a.1.2 corner 0))
            (standardKleinControl (standardKleinFace a.1.2 corner)) coordinate : ℝ)) +
        standardKleinOtherFaceWeight a corner 1 •
          (fun coordinate ↦ (fourFoldControlSub
            (standardKleinControl (standardKleinOtherFaceVertex a.1.2 corner 1))
            (standardKleinControl (standardKleinFace a.1.2 corner)) coordinate : ℝ)) =
      standardKleinOtherFaceWeight b otherCorner 0 •
          (fun coordinate ↦ (fourFoldControlSub
            (standardKleinControl (standardKleinOtherFaceVertex b.1.2 otherCorner 0))
            (standardKleinControl (standardKleinFace a.1.2 corner)) coordinate : ℝ)) +
        standardKleinOtherFaceWeight b otherCorner 1 •
          (fun coordinate ↦ (fourFoldControlSub
            (standardKleinControl (standardKleinOtherFaceVertex b.1.2 otherCorner 1))
            (standardKleinControl (standardKleinFace a.1.2 corner)) coordinate : ℝ)) := by
    calc
      _ = (fun coordinate ↦ standardKleinDoubleBaseTarget a coordinate -
          (standardKleinControl (standardKleinFace a.1.2 corner) coordinate : ℝ)) :=
        (standardKleinDoubleBaseTarget_sub_corner a corner).symm
      _ = (fun coordinate ↦ standardKleinDoubleBaseTarget b coordinate -
          (standardKleinControl (standardKleinFace b.1.2 otherCorner) coordinate : ℝ)) := by
        rw [hbase, heq]
      _ = _ := standardKleinDoubleBaseTarget_sub_corner b otherCorner
        |>.trans (by rw [← heq])
  have hzero := standardKleinVertexLinks_noPositiveConeIntersection
    a.1.2 b.1.2 corner otherCorner heq honly
    (standardKleinOtherFaceWeight a corner 0)
    (standardKleinOtherFaceWeight a corner 1)
    (standardKleinOtherFaceWeight b otherCorner 0)
    (standardKleinOtherFaceWeight b otherCorner 1)
    (by
      fin_cases corner <;>
        simp [standardKleinOtherFaceWeight, a.2.2.1])
    (by
      fin_cases corner <;>
        simp [standardKleinOtherFaceWeight, a.2.2.1])
    (by
      fin_cases otherCorner <;>
        simp [standardKleinOtherFaceWeight, b.2.2.1])
    (by
      fin_cases otherCorner <;>
        simp [standardKleinOtherFaceWeight, b.2.2.1]) hlinear
  -- Both global weight functions are therefore unit masses at the common mesh vertex.
  rcases hzero with ⟨haZero, haOne, hbZero, hbOne⟩
  calc
    (fun vertex ↦ standardKleinDoubleGlobalWeight a vertex) =
        (fun vertex ↦ if standardKleinFace a.1.2 corner = vertex then 1 else 0) :=
      standardKleinGlobalWeights_eq_single_of_otherWeights_eq_zero
        a corner haZero haOne
    _ = (fun vertex ↦ if standardKleinFace b.1.2 otherCorner = vertex then 1 else 0) := by
      rw [heq]
    _ = (fun vertex ↦ standardKleinDoubleGlobalWeight b vertex) :=
      (standardKleinGlobalWeights_eq_single_of_otherWeights_eq_zero
        b otherCorner hbZero hbOne).symm

/-- Helper for Exercise 74.4: on one doubled closed star, equality of unreflected affine
targets forces equality of global mesh weights. -/
private lemma standardKleinSameGlobalWeights_of_incident_baseTarget_eq
    (index : Fin 2 × Fin 108) (a b : StandardKleinDoubleCarrier)
    (ha : standardKleinDoubleFaceIncident index a.1)
    (hb : standardKleinDoubleFaceIncident index b.1)
    (hbase : standardKleinDoubleBaseTarget a = standardKleinDoubleBaseTarget b) :
    standardKleinSameGlobalWeights a b := by
  -- Select the displayed common mesh vertex, then use the certified equal-face, common-edge,
  -- or vertex-only geometry.
  obtain ⟨corner, hcorner⟩ := ha.2
  obtain ⟨otherCorner, hotherCorner⟩ := hb.2
  have heq : standardKleinFace a.1.2 corner =
      standardKleinFace b.1.2 otherCorner := hcorner.trans hotherCorner.symm
  by_cases hface : (a.1.2 : Fin 216) = (b.1.2 : Fin 216)
  · exact standardKleinSameGlobalWeights_of_face_eq a b (Subtype.ext hface) hbase
  rcases standardKleinIncidentFaces_classification a.1.2 b.1.2 corner otherCorner heq with
    hfaceEqual | hshare | honly
  · exact False.elim (hface hfaceEqual)
  · exact standardKleinSameGlobalWeights_of_sharedEdge_baseTarget_eq
      a b hface hshare hbase
  · exact standardKleinSameGlobalWeights_of_vertexOnly_baseTarget_eq
      a b corner otherCorner heq honly hbase

/-- Helper for Exercise 74.4: equal reflected targets from opposite copies are supported on
the attachment triangle and have the same global mesh weights. -/
private lemma standardKleinDoubleOppositeTarget_eq_attachment
    (index : Fin 2 × Fin 108) (a b : StandardKleinDoubleCarrier)
    (ha : standardKleinDoubleFaceIncident index a.1)
    (hb : standardKleinDoubleFaceIncident index b.1)
    (hcopy : a.1.1 ≠ b.1.1)
    (htarget : standardKleinDoubleTarget a = standardKleinDoubleTarget b) :
    standardKleinSameGlobalWeights a b ∧
      standardKleinOnAttachmentBoundary a ∧
        standardKleinOnAttachmentBoundary b := by
  -- Opposite-copy incidence can occur only through an attachment vertex, so both retained
  -- faces lie in the certified supporting halfspace.
  have hattachment :=
    standardKleinAttachmentVertex_of_incident_of_copy_ne index a.1 b.1 ha hb hcopy
  have haMeets := standardKleinFaceMeetsAttachment_of_incident index a ha hattachment
  have hbMeets := standardKleinFaceMeetsAttachment_of_incident index b hb hattachment
  have haSupport :=
    standardKleinAttachmentCoordinate_nonpositive_and_boundary a haMeets
  have hbSupport :=
    standardKleinAttachmentCoordinate_nonpositive_and_boundary b hbMeets
  have hcoordinates : standardKleinDoubleTargetCoordinates a =
      standardKleinDoubleTargetCoordinates b := by
    exact WithLp.toLp_injective 2 htarget
  -- Reflection negates the attachment-plane coordinate. Equality of targets therefore
  -- makes the two nonpositive base coordinates opposites, hence both zero.
  have hopposite :
      affinePlaneCoordinate standardKleinAttachmentOrigin standardKleinAttachmentNormal
          (standardKleinDoubleBaseTarget a) =
        -affinePlaneCoordinate standardKleinAttachmentOrigin standardKleinAttachmentNormal
          (standardKleinDoubleBaseTarget b) := by
    by_cases haZero : a.1.1 = 0
    · have hbZero : b.1.1 ≠ 0 := by
        intro hbZero
        exact hcopy (haZero.trans hbZero.symm)
      have hbaseReflected : standardKleinDoubleBaseTarget a =
          standardKleinReflection (standardKleinDoubleBaseTarget b) := by
        simpa only [standardKleinDoubleTargetCoordinates, haZero, hbZero,
          if_true, if_false] using hcoordinates
      have hcoordinate := congrArg
        (affinePlaneCoordinate standardKleinAttachmentOrigin
          standardKleinAttachmentNormal) hbaseReflected
      rw [standardKleinReflection_spec _ |>.1] at hcoordinate
      exact hcoordinate
    · have hbZero : b.1.1 = 0 := by
        omega
      have hbaseReflected :
          standardKleinReflection (standardKleinDoubleBaseTarget a) =
            standardKleinDoubleBaseTarget b := by
        simpa only [standardKleinDoubleTargetCoordinates, haZero, hbZero,
          if_true, if_false] using hcoordinates
      have hcoordinate := congrArg
        (affinePlaneCoordinate standardKleinAttachmentOrigin
          standardKleinAttachmentNormal) hbaseReflected
      rw [standardKleinReflection_spec _ |>.1] at hcoordinate
      linarith
  have haCoordinateZero :
      affinePlaneCoordinate standardKleinAttachmentOrigin standardKleinAttachmentNormal
          (standardKleinDoubleBaseTarget a) = 0 := by
    linarith [haSupport.1, hbSupport.1]
  have hbCoordinateZero :
      affinePlaneCoordinate standardKleinAttachmentOrigin standardKleinAttachmentNormal
          (standardKleinDoubleBaseTarget b) = 0 := by
    linarith [haSupport.1, hbSupport.1]
  have haBoundary := haSupport.2 haCoordinateZero
  have hbBoundary := hbSupport.2 hbCoordinateZero
  have haFixed : standardKleinReflection (standardKleinDoubleBaseTarget a) =
      standardKleinDoubleBaseTarget a :=
    standardKleinReflection_spec _ |>.2 haCoordinateZero
  have hbFixed : standardKleinReflection (standardKleinDoubleBaseTarget b) =
      standardKleinDoubleBaseTarget b :=
    standardKleinReflection_spec _ |>.2 hbCoordinateZero
  have hbase : standardKleinDoubleBaseTarget a = standardKleinDoubleBaseTarget b := by
    by_cases haZero : a.1.1 = 0
    · have hbZero : b.1.1 ≠ 0 := by
        intro hbZero
        exact hcopy (haZero.trans hbZero.symm)
      simpa only [standardKleinDoubleTargetCoordinates, haZero, hbZero,
        if_true, if_false, hbFixed] using hcoordinates
    · have hbZero : b.1.1 = 0 := by
        omega
      simpa only [standardKleinDoubleTargetCoordinates, haZero, hbZero,
        if_true, if_false, haFixed] using hcoordinates
  exact ⟨standardKleinSameGlobalWeights_of_attachmentBoundary_baseTarget_eq
    a b haBoundary hbBoundary hbase, haBoundary, hbBoundary⟩

/-- Helper for Exercise 74.4: on the closed star of one global mesh vertex, equality of
reflected affine targets forces equality of doubled codes. -/
private lemma standardKleinDoubleTarget_reflectsOnIncidentStar
    (index : Fin 2 × Fin 108) (a b : StandardKleinDoubleCarrier)
    (ha : standardKleinDoubleFaceIncident index a.1)
    (hb : standardKleinDoubleFaceIncident index b.1)
    (htarget : standardKleinDoubleTarget a = standardKleinDoubleTarget b) :
    standardKleinDoubleQuotient a = standardKleinDoubleQuotient b := by
  -- Route correction: the full code index keeps unrelated copies out of nonattachment stars.
  -- Equal copies reduce to the certified affine star geometry; opposite copies reduce to
  -- the strictly supporting attachment plane.
  apply (standardKleinDoubleCodePresentation.2 a b).mpr
  by_cases hcopy : a.1.1 = b.1.1
  · have hbase := standardKleinDoubleBaseTarget_eq_of_target_eq_of_copy_eq
      a b hcopy htarget
    exact ⟨standardKleinSameGlobalWeights_of_incident_baseTarget_eq
      index a b ha hb hbase, Or.inl hcopy⟩
  · obtain ⟨hweights, haBoundary, hbBoundary⟩ :=
      standardKleinDoubleOppositeTarget_eq_attachment
        index a b ha hb hcopy htarget
    exact ⟨hweights, Or.inr ⟨haBoundary, hbBoundary⟩⟩

/-- Helper for Exercise 74.4: two punctured standard Klein meshes, glued along their
attachment triangles, directly present the canonical four-fold projective plane. -/
private lemma standardKleinDoubleProjectiveKernel :
    ∃ p : C(StandardKleinDoubleCarrier, fourFoldProjectivePlane),
      Topology.IsQuotientMap p ∧
        ∀ x y, p x = p y ↔
          standardKleinSameGlobalWeights x y ∧
            (x.1.1 = y.1.1 ∨
              standardKleinOnAttachmentBoundary x ∧
                standardKleinOnAttachmentBoundary y) := by
  -- TODO: order the 217 boundary slots left by
  -- `standardKleinRelativeCutTree_certificate` into the four oriented outer chains, realize
  -- that certified reduction as a relative square quotient, and apply the already proved
  -- cut-flip-paste maps to its two copies. The three-edge boundary certificate supplies the
  -- gluing locus.
  -- Route correction: this direct projective kernel replaces the repeatedly blocked reverse
  -- atlas from the full canonical octagon into all 430 retained simplex cells.
  sorry

/-- Helper for Exercise 74.4: the doubled Klein code and the canonical octagon admit
quotient presentations with the same fibers. -/
private lemma standardKleinDoubleOctagonPresentation :
    ∃ p : C(StandardKleinDoubleCarrier, fourFoldProjectivePlane),
      Topology.IsQuotientMap p ∧
        ∀ x y, standardKleinDoubleQuotientMap x = standardKleinDoubleQuotientMap y ↔
          p x = p y := by
  -- The direct connected-sum presentation and the code quotient have the same normalized
  -- global-weight kernel, so no reverse polygon atlas is needed.
  obtain ⟨p, hp, hprojectiveKernel⟩ := standardKleinDoubleProjectiveKernel
  refine ⟨p, hp, ?_⟩
  intro x y
  exact (standardKleinDoubleCodePresentation.2 x y).trans
    (hprojectiveKernel x y).symm

/-- Helper for Exercise 74.4: compact closed stars reflect the fibers of the reflected
affine target over the doubled Klein code model. -/
private lemma standardKleinDoubleTargetCertificate :
    ∀ x : StandardKleinDoubleModel, ∃ U ∈ 𝓝 x, IsCompact U ∧
      ∀ a b : StandardKleinDoubleCarrier,
        standardKleinDoubleQuotientMap a ∈ U →
        standardKleinDoubleQuotientMap b ∈ U →
        standardKleinDoubleTarget a = standardKleinDoubleTarget b →
          standardKleinDoubleQuotientMap a = standardKleinDoubleQuotientMap b := by
  intro x
  -- Choose a representative and a positive barycentric coordinate of that representative.
  obtain ⟨point, hpoint⟩ := standardKleinDoubleQuotient_surjective x
  obtain ⟨vertex, hpositive⟩ :=
    standardKleinDouble_exists_positive_globalWeight point
  let index : Fin 2 × Fin 108 := (point.1.1, vertex)
  refine ⟨standardKleinDoubleClosedStar index, ?_,
    standardKleinDoubleClosedStar_isCompact index, ?_⟩
  · -- The positive-coordinate neighborhood lies inside the selected compact star.
    rw [← hpoint]
    exact standardKleinDoubleClosedStar_mem_nhds point vertex hpositive
  · intro a b ha hb htarget
    -- Replace arbitrary representatives in the star by representatives on incident cells.
    obtain ⟨a', ha'Incident, ha'Code⟩ :=
      standardKleinDouble_exists_incident_rep_of_mem_closedStar index
        (standardKleinDoubleQuotient a) ha
    obtain ⟨b', hb'Incident, hb'Code⟩ :=
      standardKleinDouble_exists_incident_rep_of_mem_closedStar index
        (standardKleinDoubleQuotient b) hb
    have ha'Target : standardKleinDoubleTarget a' = standardKleinDoubleTarget a :=
      standardKleinDoubleTarget_factorsThrough ha'Code
    have hb'Target : standardKleinDoubleTarget b' = standardKleinDoubleTarget b :=
      standardKleinDoubleTarget_factorsThrough hb'Code
    have hab' : standardKleinDoubleQuotient a' = standardKleinDoubleQuotient b' :=
      standardKleinDoubleTarget_reflectsOnIncidentStar index a' b'
        ha'Incident hb'Incident (ha'Target.trans (htarget.trans hb'Target.symm))
    exact ha'Code.symm.trans (hab'.trans hb'Code)

#eval (List.finRange 8).flatMap fun sector ↦
  (List.finRange 9).filterMap fun small ↦
    let face : FourFoldSourceMeshFace := (sector, small)
    if decide (fourFoldControlTriangleNondegenerate face) then none
    else some (sector.1, small.1)

#eval ((List.finRange 8).flatMap fun sector ↦
  (List.finRange 9).flatMap fun small ↦
  (List.finRange 8).flatMap fun otherSector ↦
  (List.finRange 9).flatMap fun otherSmall ↦
  (List.finRange 3).flatMap fun corner ↦
  (List.finRange 3).filterMap fun otherCorner ↦
    let face : FourFoldSourceMeshFace := (sector, small)
    let other : FourFoldSourceMeshFace := (otherSector, otherSmall)
    if decide (fourFoldQuotientFaceVertex face corner =
        fourFoldQuotientFaceVertex other otherCorner) &&
      decide (fourFoldFacesMeetOnlyAt face other
        (fourFoldQuotientFaceVertex face corner)) &&
      !decide (fourFoldLinkConesSeparated face other corner otherCorner) then
      some (sector.1, small.1, otherSector.1, otherSmall.1, corner.1, otherCorner.1)
    else none).take 20

/-- Helper for Exercise 74.4: local embeddings over a locally compact source admit compact
embedding neighborhoods. -/
private lemma existsCompactEmbeddingNeighborhood
    {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [TopologicalSpace Y]
    (g : C(X, Y))
    (hlocal : ∀ x : X, ∃ V ∈ 𝓝 x, Topology.IsEmbedding (V.restrict g)) (x : X) :
    ∃ K ∈ 𝓝 x, IsCompact K ∧ Topology.IsEmbedding (K.restrict g) := by
  -- Shrink the supplied embedding chart inside a compact neighborhood.
  obtain ⟨V, hV, hVembedding⟩ := hlocal x
  obtain ⟨K, hK, hKsubset, hKcompact⟩ := local_compact_nhds hV
  refine ⟨K, hK, hKcompact, ?_⟩
  -- Restricting the chart along the canonical subtype inclusion preserves embedding.
  have hcomp := hVembedding.comp (Topology.IsEmbedding.inclusion hKsubset)
  have hrestriction : V.restrict g ∘ Set.inclusion hKsubset = K.restrict g := by
    funext point
    rfl
  rw [hrestriction] at hcomp
  exact hcomp

/-- Helper for Exercise 74.4: a locally embedded realization of any homeomorphic model
produces the polygon-level compatibility and compact fiber-reflection data. -/
private lemma polygonImmersionDataOfHomeomorphicLocallyEmbeddedModel
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    (e : X ≃ₜ fourFoldProjectivePlane)
    (g : C(X, EuclideanSpace ℝ (Fin 3)))
    (hlocal : ∀ x : X, ∃ V ∈ 𝓝 x, Topology.IsEmbedding (V.restrict g)) :
    ∃ f : C((polygon 4 (Nat.one_lt_succ_succ 2)).region,
        EuclideanSpace ℝ (Fin 3)),
      (∀ a b, (pasting 4 (Nat.one_lt_succ_succ 2)).Related a b → f a = f b) ∧
        ∀ x : fourFoldProjectivePlane, ∃ U ∈ 𝓝 x, IsCompact U ∧
          ∀ a b : (polygon 4 (Nat.one_lt_succ_succ 2)).region,
            quotientMap 4 (Nat.one_lt_succ_succ 2) a ∈ U →
            quotientMap 4 (Nat.one_lt_succ_succ 2) b ∈ U → f a = f b →
              quotientMap 4 (Nat.one_lt_succ_succ 2) a =
              quotientMap 4 (Nat.one_lt_succ_succ 2) b := by
  -- Transport the model map to the canonical quotient and precompose with its polygon map.
  let transported : C(fourFoldProjectivePlane, EuclideanSpace ℝ (Fin 3)) :=
    g.comp (e.symm : C(fourFoldProjectivePlane, X))
  let q : C((polygon 4 (Nat.one_lt_succ_succ 2)).region,
      fourFoldProjectivePlane) :=
    ⟨quotientMap 4 (Nat.one_lt_succ_succ 2),
      (isQuotientMap_quotientMap 4 (Nat.one_lt_succ_succ 2)).continuous⟩
  let f : C((polygon 4 (Nat.one_lt_succ_succ 2)).region,
      EuclideanSpace ℝ (Fin 3)) := transported.comp q
  refine ⟨f, ?_, ?_⟩
  · intro a b hab
    -- A generating edge identification is already equality in the quotient.
    have hquotient : q a = q b :=
      Quotient.sound (Relation.EqvGen.rel a b hab)
    exact congrArg transported hquotient
  · intro x
    obtain ⟨K, hK, hKcompact, hKembedding⟩ :=
      existsCompactEmbeddingNeighborhood g hlocal (e.symm x)
    have hImage : e '' K ∈ 𝓝 x := by
      simpa only [e.apply_symm_apply] using e.isOpenMap.image_mem_nhds hK
    refine ⟨e '' K, hImage, hKcompact.image e.continuous_toFun, ?_⟩
    intro a b ha hb hab
    obtain ⟨a', haK, ha'⟩ := ha
    obtain ⟨b', hbK, hb'⟩ := hb
    have haModel : e.symm (q a) = a' := by
      calc
        e.symm (q a) = e.symm (e a') := congrArg e.symm ha'.symm
        _ = a' := e.symm_apply_apply a'
    have hbModel : e.symm (q b) = b' := by
      calc
        e.symm (q b) = e.symm (e b') := congrArg e.symm hb'.symm
        _ = b' := e.symm_apply_apply b'
    have haModelMem : e.symm (q a) ∈ K := haModel ▸ haK
    have hbModelMem : e.symm (q b) ∈ K := hbModel ▸ hbK
    -- On the smaller compact neighborhood, equality of target values is detected in the
    -- embedding chart on the model.
    have hmodel :
        (⟨e.symm (q a), haModelMem⟩ : K) = ⟨e.symm (q b), hbModelMem⟩ := by
      apply hKembedding.injective
      rw [Set.restrict_apply, Set.restrict_apply]
      dsimp only [f, transported, q, ContinuousMap.comp_apply] at hab
      exact hab
    exact e.symm.injective (congrArg Subtype.val hmodel)

/-- Helper for Exercise 74.4: the canonical octagon admits a continuous Euclidean
piecewise-linear realization that respects its paired edges and locally reflects the
resulting quotient fibers. -/
lemma existsFourFoldPolygonImmersionData :
    ∃ f : C((polygon 4 (Nat.one_lt_succ_succ 2)).region,
        EuclideanSpace ℝ (Fin 3)),
      (∀ a b, (pasting 4 (Nat.one_lt_succ_succ 2)).Related a b → f a = f b) ∧
        ∀ x : fourFoldProjectivePlane, ∃ U ∈ 𝓝 x, IsCompact U ∧
          ∀ a b : (polygon 4 (Nat.one_lt_succ_succ 2)).region,
            quotientMap 4 (Nat.one_lt_succ_succ 2) a ∈ U →
            quotientMap 4 (Nat.one_lt_succ_succ 2) b ∈ U → f a = f b →
              quotientMap 4 (Nat.one_lt_succ_succ 2) a =
              quotientMap 4 (Nat.one_lt_succ_succ 2) b := by
  -- Route correction: exact evaluation rejects the old 34-control realization, so the proof now
  -- transports a locally embedded connected-sum model through the adapter proved above.
  -- First compare the code quotient with the canonical octagon by their common source kernel.
  obtain ⟨p, hp, hkernel⟩ := standardKleinDoubleOctagonPresentation
  have hq : Topology.IsQuotientMap standardKleinDoubleQuotientMap := by
    exact standardKleinDoubleCodePresentation.1
  obtain ⟨e, _⟩ := CyclicPolygon.existsHomeomorphOfQuotientPresentations
    standardKleinDoubleQuotientMap p hq hp (Homeomorph.refl _)
    (fun x y ↦ hkernel x y)
  -- Descend the reflected affine target; the compact closed-star certificate makes the lift
  -- locally embedded on the code model.
  obtain ⟨g, hlocal⟩ := locallyEmbeddedLiftOfQuotientMap_of_compactFiberNeighborhoods
    standardKleinDoubleQuotientMap hq standardKleinDoubleTarget
    standardKleinDoubleTarget_factorsThrough standardKleinDoubleTargetCertificate
  -- Local instance justification (compactness): the freshly defined range subtype has proved
  -- compactness but no inferable CompactSpace instance.
  letI : CompactSpace StandardKleinDoubleModel :=
    isCompact_univ_iff.mp standardKleinDoubleModel_isCompact
  -- Transport the locally embedded code-model map to the canonical polygon presentation.
  exact polygonImmersionDataOfHomeomorphicLocallyEmbeddedModel e g hlocal

/-- Helper for Exercise 74.4: the finite octagonal fan admits a compatible Euclidean map
that reflects quotient fibers on compact neighborhoods. -/
lemma existsFourFoldFanImmersionCertificate :
    ∃ p : (polygon 4 (Nat.one_lt_succ_succ 2)).interior,
      ∃ g : C((Fin 8 × unitInterval) × unitInterval, EuclideanSpace ℝ (Fin 3)),
        Function.FactorsThrough g (fourFoldFanQuotientMap p) ∧
          ∀ x : fourFoldProjectivePlane, ∃ U ∈ 𝓝 x, IsCompact U ∧
            ∀ a b : (Fin 8 × unitInterval) × unitInterval,
              fourFoldFanQuotientMap p a ∈ U →
              fourFoldFanQuotientMap p b ∈ U → g a = g b →
                fourFoldFanQuotientMap p a = fourFoldFanQuotientMap p b := by
  -- Route correction: the final descent now uses compact fiber-reflecting neighborhoods,
  -- avoiding the impossible demand for continuous sections across pasted edges and vertices.
  obtain ⟨f, hrelated, hlocal⟩ := existsFourFoldPolygonImmersionData
  let p := fourFoldPolygonCenter
  let g : C((Fin 8 × unitInterval) × unitInterval, EuclideanSpace ℝ (Fin 3)) :=
    ⟨f ∘ (polygon 4 (Nat.one_lt_succ_succ 2)).fanParameterization p,
      f.continuous.comp
        ((polygon 4 (Nat.one_lt_succ_succ 2)).continuous_fanParameterization p)⟩
  refine ⟨p, g, ?_, ?_⟩
  · -- Edge compatibility descends the polygon map and remains valid on fan representatives.
    simpa only [g, ContinuousMap.coe_mk] using
      factorsThrough_fourFoldFanQuotientMap p f hrelated
  · intro x
    obtain ⟨U, hU, hUcompact, hreflect⟩ := hlocal x
    refine ⟨U, hU, hUcompact, ?_⟩
    intro a b ha hb hab
    -- Apply polygon-level fiber reflection to the two radial images.
    apply hreflect
    · exact ha
    · exact hb
    · simpa only [g, ContinuousMap.coe_mk, Function.comp_apply] using hab

/-- Exercise 74.4 (b): The four-fold projective plane can be pictured as an immersed surface in
`EuclideanSpace ℝ (Fin 3)`: it has a continuous realization that restricts to an embedding near
every point. -/
theorem existsLocallyEmbeddedMapFourFoldProjectivePlane :
    ∃ f : C(fourFoldProjectivePlane, EuclideanSpace ℝ (Fin 3)),
      ∀ x, ∃ U ∈ 𝓝 x, Topology.IsEmbedding (U.restrict f) := by
  -- Feed the finite fan certificate directly to compact-neighborhood descent.
  obtain ⟨p, g, hg, hlocal⟩ := existsFourFoldFanImmersionCertificate
  let q : C((Fin 8 × unitInterval) × unitInterval, fourFoldProjectivePlane) :=
    ⟨fourFoldFanQuotientMap p, (isQuotientMap_fourFoldFanQuotientMap p).continuous⟩
  exact locallyEmbeddedLiftOfQuotientMap_of_compactFiberNeighborhoods q
    (isQuotientMap_fourFoldFanQuotientMap p) g hg hlocal

end NonorientableSurfacePresentation
