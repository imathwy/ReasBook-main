module

public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Remark_18_2.Pasting
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Homotopy.Lifting

public section

open Set

universe u

namespace Theorem901

/-- Helper for Theorem 9.0.1: the normalized distance to the complements of
an open two-set cover is its transition coordinate. -/
noncomputable def openCoverDistanceRatio {X : Type u} [PseudoMetricSpace X]
    (U V : Set X) (x : X) : ℝ :=
  Metric.infDist x Uᶜ /
    (Metric.infDist x Uᶜ + Metric.infDist x Vᶜ)

/-- Helper for Theorem 9.0.1: the denominator of the open-cover transition
coordinate is everywhere positive. -/
lemma openCoverDistanceDenominator_pos {X : Type u} [PseudoMetricSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUcompl : Uᶜ.Nonempty) (hVcompl : Vᶜ.Nonempty)
    (hcover : U ∪ V = Set.univ) (x : X) :
    0 < Metric.infDist x Uᶜ + Metric.infDist x Vᶜ := by
  -- The cover places `x` in one member, hence outside that member's complement.
  have hxcover : x ∈ U ∪ V := by
    rw [hcover]
    exact Set.mem_univ x
  rcases hxcover with hxU | hxV
  · have hxNot : x ∉ Uᶜ := by
      simpa only [Set.mem_compl_iff, not_not] using hxU
    exact add_pos_of_pos_of_nonneg
      ((hU.isClosed_compl.notMem_iff_infDist_pos hUcompl).mp hxNot)
      Metric.infDist_nonneg
  · have hxNot : x ∉ Vᶜ := by
      simpa only [Set.mem_compl_iff, not_not] using hxV
    exact add_pos_of_nonneg_of_pos Metric.infDist_nonneg
      ((hV.isClosed_compl.notMem_iff_infDist_pos hVcompl).mp hxNot)

/-- Helper for Theorem 9.0.1: the normalized open-cover transition coordinate
is continuous. -/
lemma continuous_openCoverDistanceRatio {X : Type u} [PseudoMetricSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUcompl : Uᶜ.Nonempty) (hVcompl : Vᶜ.Nonempty)
    (hcover : U ∪ V = Set.univ) :
    Continuous (openCoverDistanceRatio U V) := by
  -- Continuity of both distance functions and denominator positivity permit division.
  unfold openCoverDistanceRatio
  exact (Metric.continuous_infDist_pt Uᶜ).div
    ((Metric.continuous_infDist_pt Uᶜ).add
      (Metric.continuous_infDist_pt Vᶜ))
    (fun x ↦ ne_of_gt
      (openCoverDistanceDenominator_pos hU hV hUcompl hVcompl hcover x))

/-- Helper for Theorem 9.0.1: the transition coordinate vanishes on the
complement of the first cover member. -/
lemma openCoverDistanceRatio_eq_zero_of_mem_compl_left
    {X : Type u} [PseudoMetricSpace X] (U V : Set X) {x : X} (hx : x ∈ Uᶜ) :
    openCoverDistanceRatio U V x = 0 := by
  -- Membership in `Uᶜ` makes the numerator vanish.
  simp only [openCoverDistanceRatio, Metric.infDist_zero_of_mem hx, zero_add,
    zero_div]

/-- Helper for Theorem 9.0.1: the transition coordinate is one on the
complement of the second cover member. -/
lemma openCoverDistanceRatio_eq_one_of_mem_compl_right
    {X : Type u} [PseudoMetricSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V)
    (hUcompl : Uᶜ.Nonempty) (hVcompl : Vᶜ.Nonempty)
    (hcover : U ∪ V = Set.univ) {x : X} (hx : x ∈ Vᶜ) :
    openCoverDistanceRatio U V x = 1 := by
  -- On `Vᶜ` the second distance is zero, while positivity keeps the first nonzero.
  have hden := openCoverDistanceDenominator_pos hU hV hUcompl hVcompl hcover x
  rw [Metric.infDist_zero_of_mem hx, add_zero] at hden
  simp only [openCoverDistanceRatio, Metric.infDist_zero_of_mem hx, add_zero]
  exact div_self (ne_of_gt hden)

/-- Helper for Theorem 9.0.1: the transition coordinate always lies in the
closed unit interval. -/
lemma openCoverDistanceRatio_mem_Icc {X : Type u} [PseudoMetricSpace X]
    (U V : Set X) (x : X) : openCoverDistanceRatio U V x ∈ Set.Icc (0 : ℝ) 1 := by
  -- Nonnegativity bounds the quotient below and bounds its numerator by its denominator.
  constructor
  · exact div_nonneg Metric.infDist_nonneg
      (add_nonneg Metric.infDist_nonneg Metric.infDist_nonneg)
  · exact div_le_one_of_le₀ (le_add_of_nonneg_right Metric.infDist_nonneg)
      (add_nonneg Metric.infDist_nonneg Metric.infDist_nonneg)

/-- Helper for Theorem 9.0.1: at a frontier point of one overlap piece that
still lies in the left cover member, the right cover member is absent. -/
lemma mem_compl_right_of_mem_left_frontier_overlapPiece
    {X : Type u} [TopologicalSpace X] {U V A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hoverlap : U ∩ V = A ∪ B)
    (hAB : Disjoint A B) {x : X} (hxU : x ∈ U) (hxfrontier : x ∈ frontier A) :
    x ∈ Vᶜ := by
  -- If `x` also lay in `V`, the overlap partition would put it in one open piece.
  rw [Set.mem_compl_iff]
  intro hxV
  have hxAB : x ∈ A ∪ B := by
    rw [← hoverlap]
    exact ⟨hxU, hxV⟩
  have hxNotA : x ∉ A := by
    intro hxA
    have hxInterior : x ∈ interior A := hA.interior_eq.symm ▸ hxA
    exact (mem_frontier_iff_notMem_interior hxA).mp hxfrontier hxInterior
  obtain hxA | hxB := hxAB
  · exact hxNotA hxA
  · have hxClosure : x ∈ closure A := frontier_subset_closure hxfrontier
    exact (Set.disjoint_left.mp (hAB.closure_left hB)) hxClosure hxB

/-- Helper for Theorem 9.0.1: at a frontier point of one overlap piece that
still lies in the right cover member, the left cover member is absent. -/
lemma mem_compl_left_of_mem_right_frontier_overlapPiece
    {X : Type u} [TopologicalSpace X] {U V A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hoverlap : U ∩ V = A ∪ B)
    (hAB : Disjoint A B) {x : X} (hxV : x ∈ V) (hxfrontier : x ∈ frontier A) :
    x ∈ Uᶜ := by
  -- Apply the preceding boundary argument after exchanging the cover members.
  apply mem_compl_right_of_mem_left_frontier_overlapPiece hA hB _ hAB hxV hxfrontier
  simpa only [inter_comm] using hoverlap

/-- Helper for Theorem 9.0.1: the real lift on the left cover member is
supported along the selected overlap piece. -/
noncomputable def openCoverWindingLiftLeft
    {X : Type u} [PseudoMetricSpace X] (U V A : Set X) (x : X) : ℝ :=
  A.indicator (fun y ↦ 2 * Real.pi * (1 - openCoverDistanceRatio U V y)) x

/-- Helper for Theorem 9.0.1: the real lift on the right cover member has
the complementary integer-period normalization. -/
noncomputable def openCoverWindingLiftRight
    {X : Type u} [PseudoMetricSpace X] (U V A : Set X) (x : X) : ℝ :=
  A.indicator (fun y ↦ -(2 * Real.pi * openCoverDistanceRatio U V y)) x

/-- Helper for Theorem 9.0.1: the selected left local lift is continuous on
the left member of the open cover. -/
lemma continuousOn_openCoverWindingLiftLeft
    {X : Type u} [PseudoMetricSpace X] {U V A B : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hA : IsOpen A) (hB : IsOpen B)
    (hUcompl : Uᶜ.Nonempty) (hVcompl : Vᶜ.Nonempty)
    (hcover : U ∪ V = Set.univ) (hoverlap : U ∩ V = A ∪ B)
    (hAB : Disjoint A B) :
    ContinuousOn (openCoverWindingLiftLeft U V A) U := by
  -- Both branches are continuous; on the frontier their values meet because the
  -- transition ratio is one outside `V`.
  classical
  have hratio : Continuous (openCoverDistanceRatio U V) :=
    continuous_openCoverDistanceRatio hU hV hUcompl hVcompl hcover
  unfold openCoverWindingLiftLeft Set.indicator
  apply ContinuousOn.if
  · rintro x ⟨hxU, hxfrontier⟩
    have hxVcompl := mem_compl_right_of_mem_left_frontier_overlapPiece
      hA hB hoverlap hAB hxU hxfrontier
    rw [openCoverDistanceRatio_eq_one_of_mem_compl_right
      hU hV hUcompl hVcompl hcover hxVcompl]
    ring
  · exact (continuous_const.mul (continuous_const.sub hratio)).continuousOn
  · exact continuous_const.continuousOn

/-- Helper for Theorem 9.0.1: the selected right local lift is continuous on
the right member of the open cover. -/
lemma continuousOn_openCoverWindingLiftRight
    {X : Type u} [PseudoMetricSpace X] {U V A B : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hA : IsOpen A) (hB : IsOpen B)
    (hUcompl : Uᶜ.Nonempty) (hVcompl : Vᶜ.Nonempty)
    (hcover : U ∪ V = Set.univ) (hoverlap : U ∩ V = A ∪ B)
    (hAB : Disjoint A B) :
    ContinuousOn (openCoverWindingLiftRight U V A) V := by
  -- On this frontier the point is outside `U`, where the transition ratio is zero.
  classical
  have hratio : Continuous (openCoverDistanceRatio U V) :=
    continuous_openCoverDistanceRatio hU hV hUcompl hVcompl hcover
  unfold openCoverWindingLiftRight Set.indicator
  apply ContinuousOn.if
  · rintro x ⟨hxV, hxfrontier⟩
    have hxUcompl := mem_compl_left_of_mem_right_frontier_overlapPiece
      hA hB hoverlap hAB hxV hxfrontier
    rw [openCoverDistanceRatio_eq_zero_of_mem_compl_left U V hxUcompl]
    ring
  · exact (continuous_const.mul hratio).neg.continuousOn
  · exact continuous_const.continuousOn

/-- Helper for Theorem 9.0.1: on the selected overlap piece the two local
lifts differ by one positive circle period. -/
lemma openCoverWindingLiftLeft_sub_right_of_mem
    {X : Type u} [PseudoMetricSpace X] (U V A : Set X) {x : X} (hx : x ∈ A) :
    openCoverWindingLiftLeft U V A x - openCoverWindingLiftRight U V A x =
      2 * Real.pi := by
  -- Expand the selected branches; the transition ratio cancels.
  rw [openCoverWindingLiftLeft, openCoverWindingLiftRight,
    Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  ring

/-- Helper for Theorem 9.0.1: on the other overlap piece the two local lifts
agree exactly. -/
lemma openCoverWindingLiftLeft_eq_right_of_mem_disjoint
    {X : Type u} [PseudoMetricSpace X] (U V : Set X) {A B : Set X}
    (hAB : Disjoint A B) {x : X} (hx : x ∈ B) :
    openCoverWindingLiftLeft U V A x = openCoverWindingLiftRight U V A x := by
  -- Disjointness selects the zero branch in both definitions.
  have hxNotA : x ∉ A := hAB.notMem_of_mem_right hx
  rw [openCoverWindingLiftLeft, openCoverWindingLiftRight,
    Set.indicator_of_notMem hxNotA, Set.indicator_of_notMem hxNotA]

/-- Helper for Theorem 9.0.1: exponentiating the two local lifts gives the
same circle value throughout the overlap partition. -/
lemma circleExp_openCoverWindingLifts_eq
    {X : Type u} [PseudoMetricSpace X] (U V : Set X) {A B : Set X}
    (hAB : Disjoint A B) {x : X} (hx : x ∈ A ∪ B) :
    Circle.exp (openCoverWindingLiftLeft U V A x) =
      Circle.exp (openCoverWindingLiftRight U V A x) := by
  -- The selected piece contributes one period; on the other piece the lifts agree.
  rcases hx with hxA | hxB
  · apply Circle.exp_eq_exp.mpr
    refine ⟨1, ?_⟩
    rw [Int.cast_one, one_mul]
    linarith [openCoverWindingLiftLeft_sub_right_of_mem U V A hxA]
  · rw [openCoverWindingLiftLeft_eq_right_of_mem_disjoint U V hAB hxB]

/-- Helper for Theorem 9.0.1: an open-cover winding coordinate consists of a
global circle map together with normalized real lifts on both cover members. -/
structure OpenCoverWindingCoordinate
    {X : Type u} [TopologicalSpace X] (U V A B : Set X) where
  circleMap : C(X, Circle)
  leftLift : C(U, ℝ)
  rightLift : C(V, ℝ)
  circleMap_eq_exp_leftLift : ∀ x : U, circleMap x = Circle.exp (leftLift x)
  circleMap_eq_exp_rightLift : ∀ x : V, circleMap x = Circle.exp (rightLift x)
  leftLift_sub_rightLift_of_mem_selected :
    ∀ x : (U ∩ V : Set X), x.1 ∈ A →
      leftLift ⟨x.1, x.2.1⟩ - rightLift ⟨x.1, x.2.2⟩ = 2 * Real.pi
  leftLift_eq_rightLift_of_mem_other :
    ∀ x : (U ∩ V : Set X), x.1 ∈ B →
      leftLift ⟨x.1, x.2.1⟩ = rightLift ⟨x.1, x.2.2⟩

/-- Helper for Theorem 9.0.1: every disjoint open partition of the overlap
of a nondegenerate two-set metric cover has a winding coordinate. -/
lemma exists_openCoverWindingCoordinate
    {X : Type u} [PseudoMetricSpace X] {U V A B : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hA : IsOpen A) (hB : IsOpen B)
    (hUcompl : Uᶜ.Nonempty) (hVcompl : Vᶜ.Nonempty)
    (hcover : U ∪ V = Set.univ) (hoverlap : U ∩ V = A ∪ B)
    (hAB : Disjoint A B) :
    Nonempty (OpenCoverWindingCoordinate U V A B) := by
  -- Turn the two continuous-on formulas into continuous maps on the cover subtypes.
  let leftLift : C(U, ℝ) :=
    ⟨fun x ↦ openCoverWindingLiftLeft U V A x,
      continuousOn_iff_continuous_restrict.mp
        (continuousOn_openCoverWindingLiftLeft hU hV hA hB hUcompl hVcompl
          hcover hoverlap hAB)⟩
  let rightLift : C(V, ℝ) :=
    ⟨fun x ↦ openCoverWindingLiftRight U V A x,
      continuousOn_iff_continuous_restrict.mp
        (continuousOn_openCoverWindingLiftRight hU hV hA hB hUcompl hVcompl
          hcover hoverlap hAB)⟩
  let leftCircle : C(U, Circle) := Circle.exp.comp leftLift
  let rightCircle : C(V, Circle) := Circle.exp.comp rightLift
  have hcompatible (x : (U ∩ V : Set X)) :
      leftCircle ⟨x.1, x.2.1⟩ = rightCircle ⟨x.1, x.2.2⟩ := by
    -- Exponentials agree because the overlap is partitioned by `A` and `B`.
    apply circleExp_openCoverWindingLifts_eq U V hAB
    rw [← hoverlap]
    exact x.2
  let circleMap : C(X, Circle) :=
    ContinuousMap.pasteOpen hU hV hcover leftCircle rightCircle hcompatible
  have hcircleLeft (x : U) : circleMap x = leftCircle x := by
    -- The pasted map restricts to the left exponential.
    have hrestrict := ContinuousMap.pasteOpen_restrict_left
      hU hV hcover leftCircle rightCircle hcompatible
    exact DFunLike.congr_fun hrestrict x
  have hcircleRight (x : V) : circleMap x = rightCircle x := by
    -- The pasted map restricts to the right exponential.
    have hrestrict := ContinuousMap.pasteOpen_restrict_right
      hU hV hcover leftCircle rightCircle hcompatible
    exact DFunLike.congr_fun hrestrict x
  refine ⟨⟨circleMap, leftLift, rightLift, ?_, ?_, ?_, ?_⟩⟩
  · intro x
    exact hcircleLeft x
  · intro x
    exact hcircleRight x
  · intro x hxA
    exact openCoverWindingLiftLeft_sub_right_of_mem U V A hxA
  · intro x hxB
    exact openCoverWindingLiftLeft_eq_right_of_mem_disjoint U V hAB hxB

/-- Helper for Theorem 9.0.1: an integer determines its corresponding real
period in the deck group of `Circle.exp`. -/
private noncomputable def realCirclePeriodMultiple
    (n : ℤ) : AddSubgroup.zmultiples (2 * Real.pi) :=
  ⟨n • (2 * Real.pi), AddSubgroup.zsmul_mem_zmultiples _ n⟩

/-- Helper for Theorem 9.0.1: the zero integer gives the zero real period. -/
private lemma realCirclePeriodMultiple_zero : realCirclePeriodMultiple 0 = 0 := by
  -- Equality in the period subgroup is equality of the underlying real values.
  apply Subtype.ext
  simp only [realCirclePeriodMultiple, zero_smul, AddSubgroup.coe_zero]

/-- Helper for Theorem 9.0.1: addition of integers becomes addition of real
periods. -/
private lemma realCirclePeriodMultiple_add (m n : ℤ) :
    realCirclePeriodMultiple (m + n) =
      realCirclePeriodMultiple m + realCirclePeriodMultiple n := by
  -- Integer scalar addition is the additive law in the deck subgroup.
  apply Subtype.ext
  simp only [realCirclePeriodMultiple, add_smul, AddSubgroup.coe_add]

/-- Helper for Theorem 9.0.1: integer-to-period conversion is an additive
homomorphism. -/
private noncomputable def realCirclePeriodHom : ℤ →+ AddSubgroup.zmultiples (2 * Real.pi) :=
  { toFun := realCirclePeriodMultiple
    map_zero' := realCirclePeriodMultiple_zero
    map_add' := realCirclePeriodMultiple_add }

/-- Helper for Theorem 9.0.1: distinct integers determine distinct nonzero
real-period multiples. -/
private lemma realCirclePeriodHom_injective : Function.Injective realCirclePeriodHom := by
  -- Cancel the nonzero period after comparing the underlying real values.
  intro m n hmn
  apply smul_left_injective ℤ (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
  exact congrArg Subtype.val hmn

/-- Helper for Theorem 9.0.1: every element of the deck subgroup is an
integer multiple of the standard real period. -/
private lemma realCirclePeriodHom_surjective : Function.Surjective realCirclePeriodHom := by
  -- This is exactly the defining membership property of `zmultiples`.
  intro x
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp x.property
  exact ⟨n, Subtype.ext hn⟩

/-- Helper for Theorem 9.0.1: integers are additively equivalent to the deck
group of the real exponential cover of the circle. -/
private noncomputable def realCirclePeriodAddEquiv :
    ℤ ≃+ AddSubgroup.zmultiples (2 * Real.pi) :=
  AddEquiv.ofBijective realCirclePeriodHom
    ⟨realCirclePeriodHom_injective, realCirclePeriodHom_surjective⟩

/-- Helper for Theorem 9.0.1: the explicit period equivalence has the expected
underlying real value. -/
private lemma realCirclePeriodAddEquiv_coe (n : ℤ) :
    (realCirclePeriodAddEquiv n : ℝ) = n * (2 * Real.pi) := by
  -- Unfold the homomorphism and normalize integer scalar multiplication on `ℝ`.
  change (realCirclePeriodMultiple n : ℝ) = n * (2 * Real.pi)
  simp only [realCirclePeriodMultiple, zsmul_eq_mul]

/-- Helper for Theorem 9.0.1: the real exponential sends zero to the circle
basepoint. -/
private lemma circleExp_zero_eq_one : Circle.exp 0 = 1 := by
  -- This is the zero-angle computation for the circle exponential.
  simp

/-- Helper for Theorem 9.0.1: the exponential covering and the explicit
period equivalence give a computable integer coordinate on the circle's
fundamental group. -/
noncomputable def circleExponentialFundamentalGroupEquivInt :
    FundamentalGroup Circle 1 ≃* Multiplicative ℤ :=
  (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
      (⟨0, circleExp_zero_eq_one⟩ : Circle.exp ⁻¹' ({1} : Set Circle))).trans
    (MulOpposite.opMulEquiv.symm.trans
      (AddEquiv.toMultiplicative realCirclePeriodAddEquiv).symm)

/-- Helper for Theorem 9.0.1: divide the pasted circle map by its value at
an overlap basepoint, producing a circle map based at one. -/
noncomputable def OpenCoverWindingCoordinate.normalizedCircleMap
    {X : Type u} [TopologicalSpace X] {U V A B : Set X}
    (w : OpenCoverWindingCoordinate U V A B) (a : (U ∩ V : Set X)) :
    C(X, Circle) :=
  ⟨fun x ↦ w.circleMap x * (w.circleMap a.1)⁻¹,
    w.circleMap.continuous.mul continuous_const.inv⟩

/-- Helper for Theorem 9.0.1: the normalized winding map sends its chosen
overlap basepoint to the circle identity. -/
lemma OpenCoverWindingCoordinate.normalizedCircleMap_apply_base
    {X : Type u} [TopologicalSpace X] {U V A B : Set X}
    (w : OpenCoverWindingCoordinate U V A B) (a : (U ∩ V : Set X)) :
    w.normalizedCircleMap a a.1 = 1 := by
  -- Normalization divides the basepoint value by itself.
  simp only [OpenCoverWindingCoordinate.normalizedCircleMap,
    ContinuousMap.coe_mk, mul_inv_cancel]

/-- Helper for Theorem 9.0.1: the normalized pasted map followed by the
standard exponential-cover coordinate gives an integer coordinate on loops. -/
noncomputable def OpenCoverWindingCoordinate.fundamentalGroupCoordinate
    {X : Type u} [TopologicalSpace X] {U V A B : Set X}
    (w : OpenCoverWindingCoordinate U V A B) (a : (U ∩ V : Set X)) :
    FundamentalGroup X a.1 →* Multiplicative ℤ :=
  circleExponentialFundamentalGroupEquivInt.toMonoidHom.comp
    (FundamentalGroup.mapOfEq (w.normalizedCircleMap a)
      (w.normalizedCircleMap_apply_base a))

/-- Helper for Theorem 9.0.1: on the left cover member, the normalized
circle map is the exponential of the left lift minus its basepoint value. -/
lemma OpenCoverWindingCoordinate.normalizedCircleMap_eq_exp_left
    {X : Type u} [TopologicalSpace X] {U V A B : Set X}
    (w : OpenCoverWindingCoordinate U V A B)
    (a : (U ∩ V : Set X)) (x : U) :
    w.normalizedCircleMap a x.1 =
      Circle.exp (w.leftLift x - w.leftLift ⟨a.1, a.2.1⟩) := by
  -- Substitute the local exponential formulas at `x` and at the basepoint.
  simp only [OpenCoverWindingCoordinate.normalizedCircleMap,
    ContinuousMap.coe_mk]
  rw [w.circleMap_eq_exp_leftLift x,
    w.circleMap_eq_exp_leftLift ⟨a.1, a.2.1⟩]
  simpa only [div_eq_mul_inv] using
    (Circle.exp_sub (w.leftLift x) (w.leftLift ⟨a.1, a.2.1⟩)).symm

/-- Helper for Theorem 9.0.1: on the right cover member, the normalized
circle map is the exponential of the right lift minus the left base value. -/
lemma OpenCoverWindingCoordinate.normalizedCircleMap_eq_exp_right
    {X : Type u} [TopologicalSpace X] {U V A B : Set X}
    (w : OpenCoverWindingCoordinate U V A B)
    (a : (U ∩ V : Set X)) (x : V) :
    w.normalizedCircleMap a x.1 =
      Circle.exp (w.rightLift x - w.leftLift ⟨a.1, a.2.1⟩) := by
  -- Use the right local lift at `x` and the left normalization at the basepoint.
  simp only [OpenCoverWindingCoordinate.normalizedCircleMap,
    ContinuousMap.coe_mk]
  rw [w.circleMap_eq_exp_rightLift x,
    w.circleMap_eq_exp_leftLift ⟨a.1, a.2.1⟩]
  simpa only [div_eq_mul_inv] using
    (Circle.exp_sub (w.rightLift x) (w.leftLift ⟨a.1, a.2.1⟩)).symm

/-- Helper for Theorem 9.0.1: local real lifts along a left path and a
returning right path concatenate to a normalized exponential lift whose
endpoint is the difference of the two transition indices. -/
lemma OpenCoverWindingCoordinate.exists_normalizedExpLift_pathPair
    {X : Type u} [TopologicalSpace X] {U V A B : Set X}
    (w : OpenCoverWindingCoordinate U V A B)
    (a b : (U ∩ V : Set X))
    (alpha : Path (⟨a.1, a.2.1⟩ : U) (⟨b.1, b.2.1⟩ : U))
    (beta : Path (⟨b.1, b.2.2⟩ : V) (⟨a.1, a.2.2⟩ : V))
    (m n : ℤ)
    (ha : w.leftLift ⟨a.1, a.2.1⟩ - w.rightLift ⟨a.1, a.2.2⟩ =
      m * (2 * Real.pi))
    (hb : w.leftLift ⟨b.1, b.2.1⟩ - w.rightLift ⟨b.1, b.2.2⟩ =
      n * (2 * Real.pi)) :
    ∃ lift : Path (0 : ℝ) (((n - m : ℤ) : ℝ) * (2 * Real.pi)),
      ∀ t, Circle.exp (lift t) =
        w.normalizedCircleMap a
          (((alpha.map continuous_subtype_val).trans
            (beta.map continuous_subtype_val)) t) := by
  -- Subtract the left lift at the basepoint along the outgoing path.
  let leftBase : ℝ := w.leftLift ⟨a.1, a.2.1⟩
  let leftRaw : Path
      (w.leftLift ⟨a.1, a.2.1⟩ - leftBase)
      (w.leftLift ⟨b.1, b.2.1⟩ - leftBase) :=
    (alpha.map w.leftLift.continuous).map
      ((continuous_id.sub continuous_const) :
        Continuous (fun x : ℝ ↦ x - leftBase))
  let leftPath : Path (0 : ℝ) (w.leftLift ⟨b.1, b.2.1⟩ - leftBase) :=
    leftRaw.cast (sub_self leftBase).symm rfl
  -- Shift the returning right lift by the joining-point transition index.
  let rightRaw : Path
      (w.rightLift ⟨b.1, b.2.2⟩ + n * (2 * Real.pi) - leftBase)
      (w.rightLift ⟨a.1, a.2.2⟩ + n * (2 * Real.pi) - leftBase) :=
    (beta.map w.rightLift.continuous).map
      (((continuous_id.add continuous_const).sub continuous_const) :
        Continuous (fun x : ℝ ↦ x + n * (2 * Real.pi) - leftBase))
  have hjoin : w.leftLift ⟨b.1, b.2.1⟩ - leftBase =
      w.rightLift ⟨b.1, b.2.2⟩ + n * (2 * Real.pi) - leftBase := by
    dsimp only [leftBase]
    linarith
  have hend : ((n - m : ℤ) : ℝ) * (2 * Real.pi) =
      w.rightLift ⟨a.1, a.2.2⟩ + n * (2 * Real.pi) - leftBase := by
    dsimp only [leftBase]
    rw [Int.cast_sub]
    linarith
  let rightPath : Path (w.leftLift ⟨b.1, b.2.1⟩ - leftBase)
      (((n - m : ℤ) : ℝ) * (2 * Real.pi)) := rightRaw.cast hjoin hend
  refine ⟨leftPath.trans rightPath, ?_⟩
  intro t
  -- Both concatenations use the same half-interval split; on each half the
  -- appropriate local lift formula reduces the claim to `Circle.exp_sub`.
  simp only [Path.trans_apply]
  split_ifs with ht
  · let s : unitInterval :=
      ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
    have hleftEval : leftPath s = w.leftLift (alpha s) - leftBase := rfl
    rw [hleftEval]
    exact (w.normalizedCircleMap_eq_exp_left a (alpha s)).symm
  · let s : unitInterval :=
      ⟨2 * (t : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩
    have hrightEval : rightPath s =
        w.rightLift (beta s) + n * (2 * Real.pi) - leftBase := rfl
    rw [hrightEval]
    have hperiod : Circle.exp (n * (2 * Real.pi)) = 1 :=
      Circle.exp_int_mul_two_pi n
    have hshift : Circle.exp
        (w.rightLift (beta s) + n * (2 * Real.pi) - leftBase) =
        Circle.exp (w.rightLift (beta s) - leftBase) := by
      calc
        Circle.exp (w.rightLift (beta s) + n * (2 * Real.pi) - leftBase) =
            Circle.exp
              ((w.rightLift (beta s) - leftBase) + n * (2 * Real.pi)) := by
                congr 1
                ring
        _ = Circle.exp (w.rightLift (beta s) - leftBase) *
            Circle.exp (n * (2 * Real.pi)) := Circle.exp_add _ _
        _ = Circle.exp (w.rightLift (beta s) - leftBase) := by
          rw [hperiod, mul_one]
    rw [hshift]
    exact (w.normalizedCircleMap_eq_exp_right a (beta s)).symm

/-- Helper for Theorem 9.0.1: the endpoint displacement of a real exponential
lift computes the standard integer coordinate of a based circle loop. -/
lemma circleFundamentalGroupCoordinate_of_expLift
    (n : ℤ) (gamma : Path (1 : Circle) 1)
    (lift : Path (0 : ℝ) (n * (2 * Real.pi)))
    (hprojection : ∀ t, Circle.exp (lift t) = gamma t) :
    circleExponentialFundamentalGroupEquivInt
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)) =
      Multiplicative.ofAdd n := by
  let covering := Circle.isAddQuotientCoveringMap_exp
  have hbaseFiber : Circle.exp 0 ∈ ({1} : Set Circle) := by
    simp
  let baseFiber : Circle.exp ⁻¹' ({1} : Set Circle) := ⟨0, hbaseFiber⟩
  have hendpointFiber : Circle.exp (n * (2 * Real.pi)) ∈ ({1} : Set Circle) := by
    simpa only [Set.mem_singleton_iff] using Circle.exp_int_mul_two_pi n
  let endpointFiber : Circle.exp ⁻¹' ({1} : Set Circle) :=
    ⟨n * (2 * Real.pi), hendpointFiber⟩
  have hmonodromy : covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk gamma) baseFiber = endpointFiber := by
    -- The supplied real path is the lift selected by monodromy uniqueness.
    apply covering.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk lift)
    rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact congrArg Subtype.val (hprojection t)
  have hcoveringCoordinate :
      covering.fundamentalGroupEquiv baseFiber
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)) =
        MulOpposite.op (Multiplicative.ofAdd (realCirclePeriodAddEquiv n)) := by
    -- The covering-space coordinate is the unique period translating zero to
    -- the endpoint of the lifted loop.
    change covering.fundamentalGroupToMulOpposite baseFiber
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)) = _
    rw [covering.fundamentalGroupToMulOpposite_apply_eq_Iff, hmonodromy]
    change (realCirclePeriodAddEquiv n : ℝ) + 0 = n * (2 * Real.pi)
    rw [realCirclePeriodAddEquiv_coe, add_zero]
  -- The final two equivalences remove the opposite tag and identify periods with integers.
  unfold circleExponentialFundamentalGroupEquivInt
  simp only [MulEquiv.trans_apply]
  rw [hcoveringCoordinate]
  exact (AddEquiv.toMultiplicative realCirclePeriodAddEquiv).symm_apply_apply
    (Multiplicative.ofAdd n)

/-- Helper for Theorem 9.0.1: the integer coordinate of a loop made from a
left-cover path and a returning right-cover path is the difference of its
endpoint transition indices. -/
lemma OpenCoverWindingCoordinate.pathPairCoordinate_eq_sub
    {X : Type u} [TopologicalSpace X] {U V A B : Set X}
    (w : OpenCoverWindingCoordinate U V A B)
    (a b : (U ∩ V : Set X))
    (alpha : Path (⟨a.1, a.2.1⟩ : U) (⟨b.1, b.2.1⟩ : U))
    (beta : Path (⟨b.1, b.2.2⟩ : V) (⟨a.1, a.2.2⟩ : V))
    (m n : ℤ)
    (ha : w.leftLift ⟨a.1, a.2.1⟩ - w.rightLift ⟨a.1, a.2.2⟩ =
      m * (2 * Real.pi))
    (hb : w.leftLift ⟨b.1, b.2.1⟩ - w.rightLift ⟨b.1, b.2.2⟩ =
      n * (2 * Real.pi)) :
    w.fundamentalGroupCoordinate a
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((alpha.map continuous_subtype_val).trans
            (beta.map continuous_subtype_val)))) =
      Multiplicative.ofAdd (n - m) := by
  -- The preceding lift construction computes the monodromy endpoint.
  obtain ⟨lift, hlift⟩ :=
    w.exists_normalizedExpLift_pathPair a b alpha beta m n ha hb
  let ambientLoop : Path a.1 a.1 :=
    (alpha.map continuous_subtype_val).trans (beta.map continuous_subtype_val)
  let mappedLoop : Path (w.normalizedCircleMap a a.1)
      (w.normalizedCircleMap a a.1) :=
    ambientLoop.map (w.normalizedCircleMap a).continuous
  let basedLoop : Path (1 : Circle) 1 := mappedLoop.cast
    (w.normalizedCircleMap_apply_base a).symm
    (w.normalizedCircleMap_apply_base a).symm
  have hprojection : ∀ t, Circle.exp (lift t) = basedLoop t := by
    -- Endpoint casts do not alter the underlying mapped path.
    intro t
    exact hlift t
  have hcoordinate := circleFundamentalGroupCoordinate_of_expLift
    (n - m) basedLoop lift hprojection
  -- Rewrite the induced fundamental-group map to the explicit mapped-and-cast loop.
  have hmap :
      (Path.Homotopic.Quotient.map
          (Path.Homotopic.Quotient.mk ambientLoop)
          (w.normalizedCircleMap a)).cast
            (w.normalizedCircleMap_apply_base a).symm
            (w.normalizedCircleMap_apply_base a).symm =
        Path.Homotopic.Quotient.mk basedLoop := by
    calc
      (Path.Homotopic.Quotient.map
          (Path.Homotopic.Quotient.mk ambientLoop)
          (w.normalizedCircleMap a)).cast
            (w.normalizedCircleMap_apply_base a).symm
            (w.normalizedCircleMap_apply_base a).symm =
          (Path.Homotopic.Quotient.mk mappedLoop).cast
            (w.normalizedCircleMap_apply_base a).symm
            (w.normalizedCircleMap_apply_base a).symm := by
              exact congrArg
                (fun z ↦ z.cast
                  (w.normalizedCircleMap_apply_base a).symm
                  (w.normalizedCircleMap_apply_base a).symm)
                (Path.Homotopic.Quotient.mk_map ambientLoop
                  (w.normalizedCircleMap a)).symm
      _ = Path.Homotopic.Quotient.mk basedLoop :=
        (Path.Homotopic.Quotient.mk_cast mappedLoop
          (w.normalizedCircleMap_apply_base a).symm
          (w.normalizedCircleMap_apply_base a).symm).symm
  unfold OpenCoverWindingCoordinate.fundamentalGroupCoordinate
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [FundamentalGroup.mapOfEq_apply, hmap]
  exact hcoordinate

/-- Helper for Theorem 9.0.1: a path pair going from the selected overlap
piece to the other piece has winding coordinate `-1`. -/
lemma OpenCoverWindingCoordinate.pathPairCoordinate_eq_neg_one
    {X : Type u} [TopologicalSpace X] {U V A B : Set X}
    (w : OpenCoverWindingCoordinate U V A B)
    (a b : (U ∩ V : Set X))
    (alpha : Path (⟨a.1, a.2.1⟩ : U) (⟨b.1, b.2.1⟩ : U))
    (beta : Path (⟨b.1, b.2.2⟩ : V) (⟨a.1, a.2.2⟩ : V))
    (ha : a.1 ∈ A) (hb : b.1 ∈ B) :
    w.fundamentalGroupCoordinate a
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((alpha.map continuous_subtype_val).trans
            (beta.map continuous_subtype_val)))) =
      Multiplicative.ofAdd (-1) := by
  -- The transition indices are one on `A` and zero on `B`.
  have haIndex : w.leftLift ⟨a.1, a.2.1⟩ - w.rightLift ⟨a.1, a.2.2⟩ =
      (1 : ℤ) * (2 * Real.pi) := by
    simpa only [Int.cast_one, one_mul] using
      w.leftLift_sub_rightLift_of_mem_selected a ha
  have hbIndex : w.leftLift ⟨b.1, b.2.1⟩ - w.rightLift ⟨b.1, b.2.2⟩ =
      (0 : ℤ) * (2 * Real.pi) := by
    rw [w.leftLift_eq_rightLift_of_mem_other b hb]
    norm_num
  simpa only [sub_self, zero_sub, neg_one_mul] using
    w.pathPairCoordinate_eq_sub a b alpha beta 1 0 haIndex hbIndex

/-- Helper for Theorem 9.0.1: a path pair whose two transition points both
lie in the selected overlap piece has winding coordinate zero. -/
lemma OpenCoverWindingCoordinate.pathPairCoordinate_eq_zero
    {X : Type u} [TopologicalSpace X] {U V A B : Set X}
    (w : OpenCoverWindingCoordinate U V A B)
    (a b : (U ∩ V : Set X))
    (alpha : Path (⟨a.1, a.2.1⟩ : U) (⟨b.1, b.2.1⟩ : U))
    (beta : Path (⟨b.1, b.2.2⟩ : V) (⟨a.1, a.2.2⟩ : V))
    (ha : a.1 ∈ A) (hb : b.1 ∈ A) :
    w.fundamentalGroupCoordinate a
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((alpha.map continuous_subtype_val).trans
            (beta.map continuous_subtype_val)))) =
      Multiplicative.ofAdd 0 := by
  -- Both endpoint transition indices equal one, so their difference vanishes.
  have haIndex : w.leftLift ⟨a.1, a.2.1⟩ - w.rightLift ⟨a.1, a.2.2⟩ =
      (1 : ℤ) * (2 * Real.pi) := by
    simpa only [Int.cast_one, one_mul] using
      w.leftLift_sub_rightLift_of_mem_selected a ha
  have hbIndex : w.leftLift ⟨b.1, b.2.1⟩ - w.rightLift ⟨b.1, b.2.2⟩ =
      (1 : ℤ) * (2 * Real.pi) := by
    simpa only [Int.cast_one, one_mul] using
      w.leftLift_sub_rightLift_of_mem_selected b hb
  simpa only [sub_self] using
    w.pathPairCoordinate_eq_sub a b alpha beta 1 1 haIndex hbIndex

/-- Helper for Theorem 9.0.1: any two nonidentity elements of a group
identified with the infinite cyclic group have equal nonzero integer powers. -/
lemma exists_zpow_eq_zpow_of_equiv_int
    {G : Type*} [Group G] (e : G ≃* Multiplicative ℤ) {x y : G}
    (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ m k : ℤ, m ≠ 0 ∧ k ≠ 0 ∧ x ^ m = y ^ k := by
  -- Use the other element's nonzero integer coordinate as each exponent.
  let a : ℤ := Multiplicative.toAdd (e x)
  let b : ℤ := Multiplicative.toAdd (e y)
  have ha : a ≠ 0 := by
    intro haZero
    apply hx
    apply e.injective
    rw [e.map_one]
    apply Multiplicative.toAdd.injective
    simpa only [a, toAdd_one] using haZero
  have hb : b ≠ 0 := by
    intro hbZero
    apply hy
    apply e.injective
    rw [e.map_one]
    apply Multiplicative.toAdd.injective
    simpa only [b, toAdd_one] using hbZero
  refine ⟨b, a, hb, ha, ?_⟩
  -- Both images have additive coordinate `a * b` after commuting the factors.
  apply e.injective
  apply Multiplicative.toAdd.injective
  simp only [map_zpow, toAdd_zpow, zsmul_eq_mul, a, b]
  exact Int.mul_comm _ _

/-- Helper for Theorem 9.0.1: failure of a two-component cardinal bound
provides three points in pairwise distinct connected components. -/
lemma exists_three_componentRepresentatives_of_not_le_two
    {W : Type*} [TopologicalSpace W]
    (hnot : ¬ Cardinal.mk (ConnectedComponents W) ≤ 2) :
    ∃ a a' b : W,
      (a : ConnectedComponents W) ≠ a' ∧
      (a : ConnectedComponents W) ≠ b ∧
      (a' : ConnectedComponents W) ≠ b := by
  -- Embed `Fin 3` in the component quotient and lift its values to representatives.
  have hthree : (3 : Cardinal) ≤ Cardinal.mk (ConnectedComponents W) := by
    convert Cardinal.natCast_add_one_le_iff.mpr (lt_of_not_ge hnot) using 1
    norm_num
  obtain ⟨componentEmbedding⟩ : Nonempty (Fin 3 ↪ ConnectedComponents W) := by
    apply Cardinal.lift_mk_le'.mp
    simpa using hthree
  obtain ⟨a, ha⟩ := ConnectedComponents.surjective_coe (componentEmbedding 0)
  obtain ⟨a', ha'⟩ := ConnectedComponents.surjective_coe (componentEmbedding 1)
  obtain ⟨b, hb⟩ := ConnectedComponents.surjective_coe (componentEmbedding 2)
  refine ⟨a, a', b, ?_, ?_, ?_⟩
  · rw [ha, ha']
    exact componentEmbedding.injective.ne (by decide)
  · rw [ha, hb]
    exact componentEmbedding.injective.ne (by decide)
  · rw [ha', hb]
    exact componentEmbedding.injective.ne (by decide)

end Theorem901

end
