module

public import Topology_Munkres_2000.Book.Theorem_63_6.FiniteCellPatch
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.UnitInterval

public section

open Set
open scoped Topology unitInterval

universe u

namespace Schoenflies

/-- Helper for Theorem 63.6: the real-valued piecewise affine slide carrying
`a` to `b` while preserving the endpoints of the unit interval. -/
private noncomputable def intervalSlideValue (a b x : ℝ) : ℝ :=
  if x ≤ a then b * x / a else b + (1 - b) * (x - a) / (1 - a)

/-- Helper for Theorem 63.6: the piecewise affine slide preserves the unit interval. -/
private lemma intervalSlideValue_mem
    (a b x : unitInterval)
    (ha : 0 < (a : ℝ) ∧ (a : ℝ) < 1)
    (hb : 0 < (b : ℝ) ∧ (b : ℝ) < 1) :
    intervalSlideValue a b x ∈ Set.Icc (0 : ℝ) 1 := by
  -- Each affine branch is a convex interpolation between its two endpoint values.
  unfold intervalSlideValue
  split_ifs with hx
  · have hxNonneg : 0 ≤ (x : ℝ) := x.property.1
    have hquotNonneg : 0 ≤ (x : ℝ) / a := div_nonneg hxNonneg ha.1.le
    have hquotLe : (x : ℝ) / a ≤ 1 := (div_le_one ha.1).mpr hx
    constructor
    · exact div_nonneg (mul_nonneg hb.1.le hxNonneg) ha.1.le
    · calc
        (b : ℝ) * x / a = (b : ℝ) * ((x : ℝ) / a) := by ring
        _ ≤ (b : ℝ) * 1 := mul_le_mul_of_nonneg_left hquotLe hb.1.le
        _ ≤ 1 := by simpa only [mul_one] using hb.2.le
  · have hax : (a : ℝ) ≤ x := le_of_not_ge hx
    have hdenom : 0 < (1 : ℝ) - a := sub_pos.mpr ha.2
    have hquotNonneg : 0 ≤ ((x : ℝ) - a) / (1 - a) :=
      div_nonneg (sub_nonneg.mpr hax) hdenom.le
    have hquotLe : ((x : ℝ) - a) / (1 - a) ≤ 1 := by
      rw [div_le_one hdenom]
      exact sub_le_sub_right x.property.2 a
    have honeMinusB : 0 ≤ (1 : ℝ) - b := sub_nonneg.mpr hb.2.le
    constructor
    · exact add_nonneg hb.1.le
        (div_nonneg (mul_nonneg honeMinusB (sub_nonneg.mpr hax)) hdenom.le)
    · calc
        (b : ℝ) + (1 - b) * (x - a) / (1 - a) =
            b + (1 - b) * (((x : ℝ) - a) / (1 - a)) := by ring
        _ ≤ b + (1 - b) * 1 := by
          simpa only [add_comm] using
            add_le_add_left (mul_le_mul_of_nonneg_left hquotLe honeMinusB) b
        _ = 1 := by ring

/-- Helper for Theorem 63.6: restrict the affine slide to the unit interval. -/
private noncomputable def intervalSlideMap
    (a b : unitInterval)
    (ha : 0 < (a : ℝ) ∧ (a : ℝ) < 1)
    (hb : 0 < (b : ℝ) ∧ (b : ℝ) < 1) :
    unitInterval → unitInterval :=
  fun x ↦ ⟨intervalSlideValue a b x, intervalSlideValue_mem a b x ha hb⟩

/-- Helper for Theorem 63.6: the slide sends its marked interior level to the target level. -/
private lemma intervalSlideMap_marked
    (a b : unitInterval)
    (ha : 0 < (a : ℝ) ∧ (a : ℝ) < 1)
    (hb : 0 < (b : ℝ) ∧ (b : ℝ) < 1) :
    intervalSlideMap a b ha hb a = b := by
  -- At the common breakpoint, the left affine formula evaluates to `b`.
  apply Subtype.ext
  simp only [intervalSlideMap, intervalSlideValue, if_pos le_rfl]
  field_simp [ne_of_gt ha.1]

/-- Helper for Theorem 63.6: the slide fixes the lower endpoint. -/
private lemma intervalSlideMap_bot
    (a b : unitInterval)
    (ha : 0 < (a : ℝ) ∧ (a : ℝ) < 1)
    (hb : 0 < (b : ℝ) ∧ (b : ℝ) < 1) :
    intervalSlideMap a b ha hb ⊥ = ⊥ := by
  -- The lower endpoint lies in the left branch and its affine coordinate is zero.
  apply Subtype.ext
  change intervalSlideValue a b 0 = 0
  simp only [intervalSlideValue, ha.1.le, if_true, mul_zero, zero_div]

/-- Helper for Theorem 63.6: the slide fixes the upper endpoint. -/
private lemma intervalSlideMap_top
    (a b : unitInterval)
    (ha : 0 < (a : ℝ) ∧ (a : ℝ) < 1)
    (hb : 0 < (b : ℝ) ∧ (b : ℝ) < 1) :
    intervalSlideMap a b ha hb ⊤ = ⊤ := by
  -- The upper endpoint lies in the right branch, where the normalized coordinate is one.
  apply Subtype.ext
  change intervalSlideValue a b 1 = 1
  simp only [intervalSlideValue, not_le.mpr ha.2, if_false]
  rw [mul_div_cancel_right₀ (1 - (b : ℝ))
    (sub_ne_zero.mpr (ne_of_gt ha.2))]
  ring

/-- Helper for Theorem 63.6: the slide crosses the target level exactly when
its input crosses the source level. -/
private lemma intervalSlideValue_le_marked_iff
    (a b x : unitInterval)
    (ha : 0 < (a : ℝ) ∧ (a : ℝ) < 1)
    (hb : 0 < (b : ℝ) ∧ (b : ℝ) < 1) :
    intervalSlideValue a b x ≤ b ↔ (x : ℝ) ≤ a := by
  -- Positivity of both affine slopes makes the breakpoint criterion exact.
  unfold intervalSlideValue
  by_cases hx : (x : ℝ) ≤ a
  · rw [if_pos hx]
    refine ⟨fun _ ↦ hx, fun _ ↦ ?_⟩
    rw [div_le_iff₀ ha.1]
    nlinarith [hb.1]
  · rw [if_neg hx]
    have hxa : 0 < (x : ℝ) - a := sub_pos.mpr (lt_of_not_ge hx)
    have hba : 0 < (1 : ℝ) - b := sub_pos.mpr hb.2
    have hdenom : 0 < (1 : ℝ) - a := sub_pos.mpr ha.2
    have hpositive : 0 < (1 - (b : ℝ)) * (x - a) / (1 - a) :=
      div_pos (mul_pos hba hxa) hdenom
    refine ⟨fun h ↦ False.elim (by linarith), fun h ↦ False.elim (hx h)⟩

/-- Helper for Theorem 63.6: swapping the two marked levels gives the inverse slide. -/
private lemma intervalSlideValue_inverse
    (a b x : unitInterval)
    (ha : 0 < (a : ℝ) ∧ (a : ℝ) < 1)
    (hb : 0 < (b : ℝ) ∧ (b : ℝ) < 1) :
    intervalSlideValue b a (intervalSlideMap a b ha hb x) = x := by
  -- The breakpoint criterion selects matching affine branches in the two slides.
  change intervalSlideValue b a (intervalSlideValue a b x) = x
  rw [intervalSlideValue]
  by_cases hx : (x : ℝ) ≤ a
  · rw [if_pos ((intervalSlideValue_le_marked_iff a b x ha hb).mpr hx)]
    unfold intervalSlideValue
    rw [if_pos hx]
    field_simp [ne_of_gt ha.1, ne_of_gt hb.1]
  · rw [if_neg (not_congr (intervalSlideValue_le_marked_iff a b x ha hb) |>.mpr hx)]
    unfold intervalSlideValue
    rw [if_neg hx]
    have haDenom : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt ha.2)
    have hbDenom : (1 : ℝ) - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hb.2)
    have hdifference :
        (b : ℝ) + (1 - b) * (x - a) / (1 - a) - b =
          (1 - b) * (x - a) / (1 - a) := by ring
    rw [hdifference]
    have hnumerator :
        (1 - (a : ℝ)) * ((1 - b) * (x - a) / (1 - a)) =
          (1 - b) * (x - a) := by
      calc
        (1 - (a : ℝ)) * ((1 - b) * (x - a) / (1 - a)) =
            (1 - b) * ((1 - a) * (x - a) / (1 - a)) := by ring
        _ = (1 - b) * (x - a) := by
          rw [mul_div_cancel_left₀ ((x : ℝ) - a) haDenom]
    rw [hnumerator, mul_div_cancel_left₀ ((x : ℝ) - a) hbDenom]
    ring

/-- Helper for Theorem 63.6: the restricted affine slide is strictly increasing. -/
private lemma intervalSlideMap_strictMono
    (a b : unitInterval)
    (ha : 0 < (a : ℝ) ∧ (a : ℝ) < 1)
    (hb : 0 < (b : ℝ) ∧ (b : ℝ) < 1) :
    StrictMono (intervalSlideMap a b ha hb) := by
  -- Compare inputs branchwise; crossing the breakpoint factors through `b`.
  intro x y hxy
  have hxyReal : (x : ℝ) < y := hxy
  apply Subtype.coe_lt_coe.mp
  simp only [intervalSlideMap]
  unfold intervalSlideValue
  by_cases hy : (y : ℝ) ≤ a
  · have hx : (x : ℝ) ≤ a := hxy.le.trans hy
    rw [if_pos hx, if_pos hy]
    exact (div_lt_div_iff_of_pos_right ha.1).mpr
      (mul_lt_mul_of_pos_left hxyReal hb.1)
  · by_cases hx : (x : ℝ) ≤ a
    · rw [if_pos hx, if_neg hy]
      have hleft : (b : ℝ) * x / a ≤ b := by
        rw [div_le_iff₀ ha.1]
        nlinarith [hb.1]
      have hright : (b : ℝ) < b + (1 - b) * (y - a) / (1 - a) := by
        have hya : 0 < (y : ℝ) - a := sub_pos.mpr (lt_of_not_ge hy)
        have hba : 0 < (1 : ℝ) - b := sub_pos.mpr hb.2
        have hdenom : 0 < (1 : ℝ) - a := sub_pos.mpr ha.2
        have := div_pos (mul_pos hba hya) hdenom
        linarith
      exact hleft.trans_lt hright
    · rw [if_neg hx, if_neg hy]
      have hcoef : 0 < (1 - (b : ℝ)) / (1 - a) :=
        div_pos (sub_pos.mpr hb.2) (sub_pos.mpr ha.2)
      have hsub : (x : ℝ) - a < y - a := sub_lt_sub_right hxyReal a
      calc
        (b : ℝ) + (1 - b) * (x - a) / (1 - a) =
            b + ((1 - b) / (1 - a)) * (x - a) := by ring
        _ < b + ((1 - b) / (1 - a)) * (y - a) :=
          by simpa only [add_comm] using
            add_lt_add_left (mul_lt_mul_of_pos_left hsub hcoef) b
        _ = b + (1 - b) * (y - a) / (1 - a) := by ring

/-- Helper for Theorem 63.6: the two mutually inverse affine slides form an
order isomorphism of the unit interval. -/
private noncomputable def unitIntervalSlideOrderIso
    (a b : unitInterval)
    (ha : 0 < (a : ℝ) ∧ (a : ℝ) < 1)
    (hb : 0 < (b : ℝ) ∧ (b : ℝ) < 1) :
    unitInterval ≃o unitInterval where
  toFun := intervalSlideMap a b ha hb
  invFun := intervalSlideMap b a hb ha
  left_inv := fun x ↦ Subtype.ext (intervalSlideValue_inverse a b x ha hb)
  right_inv := fun x ↦ Subtype.ext (intervalSlideValue_inverse b a x hb ha)
  map_rel_iff' := (intervalSlideMap_strictMono a b ha hb).le_iff_le

/-- Helper for Theorem 63.6: two interior levels of the unit interval are
related by an endpoint-fixing homeomorphism. -/
theorem existsUnitIntervalSlide
    (a b : unitInterval)
    (ha : 0 < (a : ℝ) ∧ (a : ℝ) < 1)
    (hb : 0 < (b : ℝ) ∧ (b : ℝ) < 1) :
    ∃ e : unitInterval ≃ₜ unitInterval,
      e a = b ∧ e ⊥ = ⊥ ∧ e ⊤ = ⊤ := by
  -- Convert the explicit order isomorphism to a homeomorphism and expose its specifications.
  let e := (unitIntervalSlideOrderIso a b ha hb).toHomeomorph
  refine ⟨e, ?_, ?_, ?_⟩
  · exact intervalSlideMap_marked a b ha hb
  · exact intervalSlideMap_bot a b ha hb
  · exact intervalSlideMap_top a b ha hb

/-- Helper for Theorem 63.6: a finite paired rectangular collar records
compatible product charts around two parameterized traces. -/
structure FinitePairedRectangularCollar
    {X : Type u} [TopologicalSpace X]
    (alpha beta : Circle → X) (n : ℕ) where
  cell : Fin n → Set X
  support : Set X
  support_eq_iUnion : support = ⋃ i, cell i
  cell_isClosed : ∀ i, IsClosed (cell i)
  chart : ∀ i, cell i ≃ₜ unitInterval × unitInterval
  sourceLevel : unitInterval
  targetLevel : unitInterval
  sourceLevel_interior : 0 < (sourceLevel : ℝ) ∧ (sourceLevel : ℝ) < 1
  targetLevel_interior : 0 < (targetLevel : ℝ) ∧ (targetLevel : ℝ) < 1
  traceCell : Circle → Fin n
  traceCoordinate : Circle → unitInterval
  source_mem : ∀ z, alpha z ∈ cell (traceCell z)
  target_mem : ∀ z, beta z ∈ cell (traceCell z)
  chart_source : ∀ z,
    chart (traceCell z) ⟨alpha z, source_mem z⟩ = (traceCoordinate z, sourceLevel)
  chart_target : ∀ z,
    chart (traceCell z) ⟨beta z, target_mem z⟩ = (traceCoordinate z, targetLevel)
  overlap_transverse : ∀ i j x (hxi : x ∈ cell i) (hxj : x ∈ cell j),
    (chart i ⟨x, hxi⟩).2 = (chart j ⟨x, hxj⟩).2
  overlap_fiber : ∀ i j x (hxi : x ∈ cell i) (hxj : x ∈ cell j) t,
    ((chart i).symm ((chart i ⟨x, hxi⟩).1, t) : X) =
      ((chart j).symm ((chart j ⟨x, hxj⟩).1, t) : X)
  frontier_transverse_endpoint : ∀ i x (hxi : x ∈ cell i),
    x ∈ frontier support →
      (chart i ⟨x, hxi⟩).2 = ⊥ ∨ (chart i ⟨x, hxi⟩).2 = ⊤

namespace FinitePairedRectangularCollar

variable {X : Type u} [TopologicalSpace X]
variable {alpha beta gamma : Circle → X} {n : ℕ}

/-- Helper for Theorem 63.6: slide the transverse coordinate in one collar cell. -/
private noncomputable def cellSlide
    (A : FinitePairedRectangularCollar alpha beta n)
    (e : unitInterval ≃ₜ unitInterval) (i : Fin n) :
    A.cell i ≃ₜ A.cell i :=
  (A.chart i).trans
    ((Homeomorph.refl unitInterval).prodCongr e |>.trans (A.chart i).symm)

/-- Helper for Theorem 63.6: applying a cell slide changes only its transverse coordinate. -/
private lemma cellSlide_apply
    (A : FinitePairedRectangularCollar alpha beta n)
    (e : unitInterval ≃ₜ unitInterval) (i : Fin n)
    {x : X} (hx : x ∈ A.cell i) :
    (cellSlide A e i ⟨x, hx⟩ : X) =
      ((A.chart i).symm
        ((A.chart i ⟨x, hx⟩).1, e (A.chart i ⟨x, hx⟩).2) : X) := by
  -- Unfold the conjugation through the product chart once.
  rfl

/-- Helper for Theorem 63.6: the inverse cell slide uses the inverse transverse slide. -/
private lemma cellSlide_symm_apply
    (A : FinitePairedRectangularCollar alpha beta n)
    (e : unitInterval ≃ₜ unitInterval) (i : Fin n)
    {x : X} (hx : x ∈ A.cell i) :
    ((cellSlide A e i).symm ⟨x, hx⟩ : X) =
      ((A.chart i).symm
        ((A.chart i ⟨x, hx⟩).1, e.symm (A.chart i ⟨x, hx⟩).2) : X) := by
  -- Reverse the same chart conjugation.
  rfl

/-- Helper for Theorem 63.6: common transverse coordinates and vertical fibers
make the forward cell slides agree on every overlap. -/
private lemma cellSlide_forward_compatible
    (A : FinitePairedRectangularCollar alpha beta n)
    (e : unitInterval ≃ₜ unitInterval)
    (i j : Fin n) (x : X) (hxi : x ∈ A.cell i) (hxj : x ∈ A.cell j) :
    (cellSlide A e i ⟨x, hxi⟩ : X) =
      (cellSlide A e j ⟨x, hxj⟩ : X) := by
  -- Normalize both local maps, then use the collar's shared-fiber law.
  rw [cellSlide_apply, cellSlide_apply, A.overlap_transverse i j x hxi hxj]
  exact A.overlap_fiber i j x hxi hxj _

/-- Helper for Theorem 63.6: the inverse cell slides also agree on overlaps. -/
private lemma cellSlide_inverse_compatible
    (A : FinitePairedRectangularCollar alpha beta n)
    (e : unitInterval ≃ₜ unitInterval)
    (i j : Fin n) (x : X) (hxi : x ∈ A.cell i) (hxj : x ∈ A.cell j) :
    ((cellSlide A e i).symm ⟨x, hxi⟩ : X) =
      ((cellSlide A e j).symm ⟨x, hxj⟩ : X) := by
  -- Apply the identical overlap normalization to the inverse interval slide.
  rw [cellSlide_symm_apply, cellSlide_symm_apply,
    A.overlap_transverse i j x hxi hxj]
  exact A.overlap_fiber i j x hxi hxj _

/-- Helper for Theorem 63.6: an endpoint-fixing slide fixes every point on
the frontier of a paired rectangular collar. -/
private lemma cellSlide_fixes_frontier
    (A : FinitePairedRectangularCollar alpha beta n)
    (e : unitInterval ≃ₜ unitInterval)
    (heBot : e ⊥ = ⊥) (heTop : e ⊤ = ⊤)
    (i : Fin n) (x : X) (hxi : x ∈ A.cell i)
    (hxfrontier : x ∈ frontier (⋃ i, A.cell i)) :
    (cellSlide A e i ⟨x, hxi⟩ : X) = x := by
  -- Rewrite the named support, then the endpoint rule makes the chart coordinate unchanged.
  have hxSupportFrontier : x ∈ frontier A.support := by
    rw [A.support_eq_iUnion]
    exact hxfrontier
  obtain hbottom | htop := A.frontier_transverse_endpoint i x hxi hxSupportFrontier
  · rw [cellSlide_apply, hbottom, heBot]
    rw [← hbottom]
    exact congrArg Subtype.val ((A.chart i).symm_apply_apply ⟨x, hxi⟩)
  · rw [cellSlide_apply, htop, heTop]
    rw [← htop]
    exact congrArg Subtype.val ((A.chart i).symm_apply_apply ⟨x, hxi⟩)

/-- Helper for Theorem 63.6: the local transverse slide carries each source
trace point to its paired target trace point. -/
private lemma cellSlide_source_to_target
    (A : FinitePairedRectangularCollar alpha beta n)
    (e : unitInterval ≃ₜ unitInterval)
    (he : e A.sourceLevel = A.targetLevel) (z : Circle) :
    (cellSlide A e (A.traceCell z) ⟨alpha z, A.source_mem z⟩ : X) = beta z := by
  -- Compute in the assigned chart and replace the target coordinates by the target trace.
  rw [cellSlide_apply, A.chart_source z, he, ← A.chart_target z]
  exact congrArg Subtype.val
    ((A.chart (A.traceCell z)).symm_apply_apply ⟨ beta z, A.target_mem z ⟩)

/-- Helper for Theorem 63.6: the inverse local slide carries each target
trace point back to its paired source trace point. -/
private lemma cellSlide_target_to_source
    (A : FinitePairedRectangularCollar alpha beta n)
    (e : unitInterval ≃ₜ unitInterval)
    (he : e.symm A.targetLevel = A.sourceLevel) (z : Circle) :
    ((cellSlide A e (A.traceCell z)).symm ⟨ beta z, A.target_mem z ⟩ : X) = alpha z := by
  -- Use the inverse chart computation and the stored source coordinates.
  rw [cellSlide_symm_apply, A.chart_target z, he, ← A.chart_source z]
  exact congrArg Subtype.val
    ((A.chart (A.traceCell z)).symm_apply_apply ⟨ alpha z, A.source_mem z ⟩)

/-- Helper for Theorem 63.6: a paired rectangular collar produces a finite
closed-cell patch that maps its source trace exactly to its target trace. -/
theorem existsPatchMappingTrace
    (A : FinitePairedRectangularCollar alpha beta n) :
    ∃ P : FiniteClosedCellPatch X n,
      P.cell = A.cell ∧
        P.support = A.support ∧
        (∀ z, P.forward (alpha z) = beta z) ∧
        ∀ z, P.inverse (beta z) = alpha z := by
  -- Use one interval slide in every product chart and glue the compatible local maps.
  obtain ⟨e, heMarked, heBot, heTop⟩ :=
    existsUnitIntervalSlide A.sourceLevel A.targetLevel
      A.sourceLevel_interior A.targetLevel_interior
  have heInverseMarked : e.symm A.targetLevel = A.sourceLevel := by
    calc
      e.symm A.targetLevel = e.symm (e A.sourceLevel) := congrArg e.symm heMarked.symm
      _ = A.sourceLevel := e.symm_apply_apply A.sourceLevel
  obtain ⟨P, hcell, hsupport, hforward, hinverse⟩ :=
    FiniteClosedCellPatch.ofLocalEquivsWithSpecs A.cell A.cell_isClosed
      (cellSlide A e)
      (cellSlide_forward_compatible A e)
      (cellSlide_inverse_compatible A e)
      (cellSlide_fixes_frontier A e heBot heTop)
  refine ⟨P, hcell, hsupport.trans A.support_eq_iUnion.symm, ?_, ?_⟩
  · intro z
    calc
      P.forward (alpha z) =
          FiniteClosedCellPatch.gluedForward A.cell (cellSlide A e) (alpha z) :=
        congrFun hforward (alpha z)
      _ = (cellSlide A e (A.traceCell z) ⟨alpha z, A.source_mem z⟩ : X) :=
        FiniteClosedCellPatch.gluedForward_eq_local A.cell (cellSlide A e)
          (cellSlide_forward_compatible A e) (A.traceCell z) (A.source_mem z)
      _ = beta z := cellSlide_source_to_target A e heMarked z
  · intro z
    calc
      P.inverse (beta z) =
          FiniteClosedCellPatch.gluedInverse A.cell (cellSlide A e) (beta z) :=
        congrFun hinverse (beta z)
      _ = ((cellSlide A e (A.traceCell z)).symm
          ⟨beta z, A.target_mem z⟩ : X) :=
        FiniteClosedCellPatch.gluedInverse_eq_local A.cell (cellSlide A e)
          (cellSlide_inverse_compatible A e) (A.traceCell z) (A.target_mem z)
      _ = alpha z := cellSlide_target_to_source A e heInverseMarked z

end FinitePairedRectangularCollar

namespace FinitePairedRectangularCollar

variable {X : Type u} [PseudoMetricSpace X]
variable {beta gamma : Circle → X} {n : ℕ}

/-- Helper for Theorem 63.6: a paired rectangular collar and two mesh bounds
produce one quantitatively controlled ambient refinement. -/
theorem refineAmbientHomeomorphAlongPairedCollar
    (h : X ≃ₜ X)
    (A : FinitePairedRectangularCollar (fun z ↦ h (gamma z)) beta n)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (htargetBounded : ∀ i, Bornology.IsBounded (A.cell i))
    (htargetDiam : ∀ i, Metric.diam (A.cell i) ≤ epsilon)
    (hsourceBounded : ∀ i, Bornology.IsBounded (h.symm '' A.cell i))
    (hsourceDiam : ∀ i, Metric.diam (h.symm '' A.cell i) ≤ epsilon) :
    ∃ h' : X ≃ₜ X,
      (∀ z, h' (gamma z) = beta z) ∧
        (∀ x, dist (h' x) (h x) ≤ epsilon) ∧
        ∀ y, dist (h'.symm y) (h.symm y) ≤ epsilon := by
  -- Convert the collar into a patch, transport its mesh hypotheses, and invoke the stage API.
  obtain ⟨P, hcell, hsupport, htrace, _⟩ := A.existsPatchMappingTrace
  have htargetBoundedP : ∀ i, Bornology.IsBounded (P.cell i) := by
    rw [hcell]
    exact htargetBounded
  have htargetDiamP : ∀ i, Metric.diam (P.cell i) ≤ epsilon := by
    rw [hcell]
    exact htargetDiam
  have hsourceBoundedP : ∀ i, Bornology.IsBounded (h.symm '' P.cell i) := by
    rw [hcell]
    exact hsourceBounded
  have hsourceDiamP : ∀ i, Metric.diam (h.symm '' P.cell i) ≤ epsilon := by
    rw [hcell]
    exact hsourceDiam
  obtain ⟨h', honSupport, _, hforwardDisplacement, hinverseDisplacement⟩ :=
    refineAmbientHomeomorphInFiniteCells h P epsilon hepsilon
      htargetBoundedP htargetDiamP hsourceBoundedP hsourceDiamP
  refine ⟨h', ?_, hforwardDisplacement, hinverseDisplacement⟩
  intro z
  have hzSupportA : h (gamma z) ∈ A.support := by
    rw [A.support_eq_iUnion]
    exact Set.mem_iUnion_of_mem (A.traceCell z) (A.source_mem z)
  have hzSupportP : h (gamma z) ∈ P.support := by
    rw [hsupport]
    exact hzSupportA
  calc
    h' (gamma z) = P.forward (h (gamma z)) := honSupport (gamma z) hzSupportP
    _ = beta z := htrace z

end FinitePairedRectangularCollar

end Schoenflies

end
