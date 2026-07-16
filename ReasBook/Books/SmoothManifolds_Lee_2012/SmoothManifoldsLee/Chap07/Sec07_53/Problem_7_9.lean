import Mathlib
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_04.Example_1_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open Projectivization
open scoped LinearAlgebra.Projectivization Manifold ContDiff

-- Domain sampling for this refine pass:
-- `Projectivization.smul_mk`
-- `Projectivization.generalLinearGroup_is_two_pretransitive`
-- `Matrix.GeneralLinearGroup.toLin`
-- `ContinuousLinearEquiv.unitsEquiv`

/- Problem 7-9 (1): the projective action formula is the canonical owner
`Projectivization.smul_mk`. -/
recall Projectivization.smul_mk

section

variable (n : ℕ)

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

local instance : CompleteSpace E := by infer_instance

local instance : CompleteSpace (E →L[ℝ] E) :=
  (SeparatingDual.completeSpace_continuousLinearMap_iff ℝ E E).2 inferInstance

local instance : ChartedSpace (E →L[ℝ] E) (E →L[ℝ] E)ˣ :=
  Units.instChartedSpace

local instance : MulAction (E →L[ℝ] E)ˣ ℝP[n] :=
  Projectivization.instMulAction

/-- Helper for Problem 7-9: each standard affine chart of `ℝPⁿ` lies in the smooth maximal
atlas. -/
lemma realProjectiveChart_memMaximalAtlas (i : Fin (n + 1)) :
    realProjectiveChart n i ∈ IsManifold.maximalAtlas (𝓡 n) ∞ (ℝP[n]) := by
  have hAtlas : realProjectiveChart n i ∈ atlas (EuclideanSpace ℝ (Fin n)) (ℝP[n]) := by
    change realProjectiveChart n i ∈ { e | ∃ j : Fin (n + 1), e = realProjectiveChart n j }
    exact ⟨i, rfl⟩
  exact IsManifold.subset_maximalAtlas hAtlas

/-- Helper for Problem 7-9: in standard affine charts, the action of a continuous-linear unit on
`ℝPⁿ` is given by the usual quotient of homogeneous coordinates. -/
theorem realProjectiveChart_smul_formula
    (A : (E →L[ℝ] E)ˣ) (i j : Fin (n + 1))
    (u : EuclideanSpace ℝ (Fin n)) :
    realProjectiveChart n j (A • (realProjectiveChart n i).symm u) =
      WithLp.toLp 2 fun k ↦
        (((A : E →L[ℝ] E) (realProjectiveChartInvVector n i u)) (j.succAbove k)) /
          (((A : E →L[ℝ] E) (realProjectiveChartInvVector n i u)) j) := by
  rw [realProjectiveChart_symm_apply, Projectivization.smul_mk, realProjectiveChart_mk]
  rfl

/-- Helper for Problem 7-9: the Euclidean local model of the projective action is smooth near any
point where the chosen denominator coordinate is nonzero. -/
theorem realProjectiveActionLocalModel_contDiffWithinAt
    (i j : Fin (n + 1))
    {p0 : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n)}
    (hj :
      ((p0.1 (realProjectiveChartInvVector n i p0.2)) j) ≠ 0) :
    ContDiffWithinAt ℝ ∞
      (fun p : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n) ↦
        WithLp.toLp 2 fun l ↦
          ((p.1 (realProjectiveChartInvVector n i p.2)) (j.succAbove l)) /
            ((p.1 (realProjectiveChartInvVector n i p.2)) j))
      (Set.range ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n))) p0 := by
  have hInv :
      ContDiff ℝ ∞
        (fun u : EuclideanSpace ℝ (Fin n) ↦ realProjectiveChartInvVector n i u) := by
    refine contDiff_piLp' (p := (2 : ENNReal)) ?_
    intro l
    exact (realProjectiveChartInvVector_coordinate_contDiff n i l).of_le (by simp)
  have hApply :
      ContDiff ℝ ∞
        (fun p : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n) ↦
          p.1 (realProjectiveChartInvVector n i p.2)) := by
    have hEval : IsBoundedBilinearMap ℝ (fun p : (E →L[ℝ] E) × E ↦ p.1 p.2) :=
      isBoundedBilinearMap_apply
    simpa using hEval.contDiff.comp₂ contDiff_fst (hInv.comp contDiff_snd)
  have hLocal :
      ContDiffAt ℝ ∞
        (fun p : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n) ↦
          WithLp.toLp 2 fun l ↦
            ((p.1 (realProjectiveChartInvVector n i p.2)) (j.succAbove l)) /
              ((p.1 (realProjectiveChartInvVector n i p.2)) j)) p0 := by
    refine contDiffAt_piLp' (p := (2 : ENNReal)) ?_
    intro l
    have hNum :
        ContDiffAt ℝ ∞
          (fun p : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n) ↦
            ((p.1 (realProjectiveChartInvVector n i p.2)) (j.succAbove l))) p0 := by
      exact (contDiffAt_piLp_apply (p := (2 : ENNReal)) (i := j.succAbove l)).comp p0
        hApply.contDiffAt
    have hDen :
        ContDiffAt ℝ ∞
          (fun p : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n) ↦
            ((p.1 (realProjectiveChartInvVector n i p.2)) j)) p0 := by
      exact (contDiffAt_piLp_apply (p := (2 : ENNReal)) (i := j)).comp p0 hApply.contDiffAt
    simpa [div_eq_mul_inv] using hNum.mul (hDen.inv hj)
  exact hLocal.contDiffWithinAt

/-- Helper for Problem 7-9: after choosing standard affine charts around `x` and `A • x`, the
projective action has the explicit quotient expression on the chart target. -/
theorem realProjectiveAction_chartExpression_eventuallyEq
    {p : (E →L[ℝ] E)ˣ × ℝP[n]}
    (i j : Fin (n + 1))
    (hi : p.2 ∈ realProjectiveChartDomain n i) :
    let eU : OpenPartialHomeomorph (E →L[ℝ] E)ˣ (E →L[ℝ] E) :=
      chartAt (E →L[ℝ] E) p.1
    let e :
        OpenPartialHomeomorph ((E →L[ℝ] E)ˣ × ℝP[n])
          ((E →L[ℝ] E) × EuclideanSpace ℝ (Fin n)) :=
      eU.prod (realProjectiveChart n i)
    let p0 : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n) :=
      ((p.1 : E →L[ℝ] E), realProjectiveChart n i p.2)
    let f : (E →L[ℝ] E)ˣ × ℝP[n] → ℝP[n] := fun q ↦ q.1 • q.2
    let localModel : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) := fun q ↦
      WithLp.toLp 2 fun l ↦
        ((q.1 (realProjectiveChartInvVector n i q.2)) (j.succAbove l)) /
          ((q.1 (realProjectiveChartInvVector n i q.2)) j)
    (((realProjectiveChart n j).extend (𝓡 n)) ∘ f ∘
        (e.extend ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n))).symm)
      =ᶠ[nhdsWithin p0 (Set.range ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n)))] localModel := by
  let eU : OpenPartialHomeomorph (E →L[ℝ] E)ˣ (E →L[ℝ] E) :=
    chartAt (E →L[ℝ] E) p.1
  let e :
      OpenPartialHomeomorph ((E →L[ℝ] E)ˣ × ℝP[n])
        ((E →L[ℝ] E) × EuclideanSpace ℝ (Fin n)) :=
    eU.prod (realProjectiveChart n i)
  let p0 : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n) :=
    ((p.1 : E →L[ℝ] E), realProjectiveChart n i p.2)
  let f : (E →L[ℝ] E)ˣ × ℝP[n] → ℝP[n] := fun q ↦ q.1 • q.2
  let localModel : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) := fun q ↦
    WithLp.toLp 2 fun l ↦
      ((q.1 (realProjectiveChartInvVector n i q.2)) (j.succAbove l)) /
        ((q.1 (realProjectiveChartInvVector n i q.2)) j)
  have hRange :
      Set.range ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n)) = Set.univ := by
    ext q
    simp
  have hp : p ∈ e.source := by
    refine ⟨?_, hi⟩
    simp [eU]
  have htarget_mem :
      (e.extend ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n))).target ∈
        nhdsWithin p0 (Set.range ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n))) := by
    simpa [hRange, e, eU, p0, Units.chartAt_apply] using
      (e.extend_target_mem_nhdsWithin
        (I := (𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n)) hp)
  refine Filter.eventuallyEq_of_mem htarget_mem ?_
  intro q hq
  have hq' : q ∈ e.target := by
    simpa [hRange, OpenPartialHomeomorph.extend_target] using hq
  have hqU : q.1 ∈ eU.target := by
    simpa [e] using hq'.1
  have hcoeeU :
      (((eU.symm q.1 : (E →L[ℝ] E)ˣ) : E →L[ℝ] E)) = q.1 := by
    have hright : eU (eU.symm q.1) = q.1 := OpenPartialHomeomorph.right_inv eU hqU
    simpa [eU, Units.chartAt_apply] using hright
  ext l
  have hformula :
      (realProjectiveChart n j
          ((eU.symm q.1 : (E →L[ℝ] E)ˣ) • (realProjectiveChart n i).symm q.2)) l =
        (WithLp.toLp 2 fun k ↦
          ((((eU.symm q.1 : (E →L[ℝ] E)ˣ) : E →L[ℝ] E)
              (realProjectiveChartInvVector n i q.2)) (j.succAbove k)) /
            ((((eU.symm q.1 : (E →L[ℝ] E)ˣ) : E →L[ℝ] E)
              (realProjectiveChartInvVector n i q.2)) j)) l := by
    exact
      congrArg (fun v : EuclideanSpace ℝ (Fin n) ↦ v l)
        (realProjectiveChart_smul_formula n (eU.symm q.1) i j q.2)
  rw [hcoeeU] at hformula
  simpa [f, localModel, e, eU, Function.comp, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm] using hformula

/-- Helper for Problem 7-9: the projective action of continuous-linear units on `ℝPⁿ` is
continuous. -/
theorem realProjectiveAction_continuous :
    Continuous (fun q : (E →L[ℝ] E)ˣ × ℝP[n] ↦ q.1 • q.2) := by
  let q : { v : E // v ≠ 0 } → ℝP[n] := Projectivization.mk' ℝ
  have hq : Topology.IsQuotientMap q := by
    simpa [q, Projectivization.mk'] using
      (isQuotientMap_quotient_mk' :
        Topology.IsQuotientMap
          (@Quotient.mk'
            { v : E // v ≠ 0 }
            (projectivizationSetoid ℝ E)))
  have hqCont : Continuous q := by
    simpa [q, Projectivization.mk'] using
      (continuous_quotient_mk' :
        Continuous
          (@Quotient.mk'
            { v : E // v ≠ 0 }
            (projectivizationSetoid ℝ E)))
  have hRep :
      Continuous fun p : (E →L[ℝ] E)ˣ × { v : E // v ≠ 0 } ↦
        (⟨((p.1 : E →L[ℝ] E) p.2 : E),
          ((smul_ne_zero_iff_ne p.1).2 p.2.2)⟩ : { v : E // v ≠ 0 }) := by
    exact Continuous.subtype_mk
      (isBoundedBilinearMap_apply.continuous.comp <|
        (Units.continuous_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd))
      (fun p ↦ (smul_ne_zero_iff_ne p.1).2 p.2.2)
  refine hq.continuous_lift_prod_right ?_
  simpa [q, Projectivization.mk'_eq_mk, Projectivization.smul_mk] using hqCont.comp hRep

/-- Helper for Problem 7-9: after choosing source and target standard charts, the chart-conjugated
projective action is smooth in the Euclidean model. -/
theorem realProjectiveAction_writtenInCharts_contDiffWithinAt
    {p : (E →L[ℝ] E)ˣ × ℝP[n]} {i j : Fin (n + 1)}
    (hi : p.2 ∈ realProjectiveChartDomain n i)
    (hj : p.1 • p.2 ∈ realProjectiveChartDomain n j) :
    let eU : OpenPartialHomeomorph (E →L[ℝ] E)ˣ (E →L[ℝ] E) :=
      chartAt (E →L[ℝ] E) p.1
    let e :
        OpenPartialHomeomorph ((E →L[ℝ] E)ˣ × ℝP[n])
          ((E →L[ℝ] E) × EuclideanSpace ℝ (Fin n)) :=
      eU.prod (realProjectiveChart n i)
    let p0 : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n) :=
      ((p.1 : E →L[ℝ] E), realProjectiveChart n i p.2)
    ContDiffWithinAt ℝ ∞
      (((realProjectiveChart n j).extend (𝓡 n)) ∘
        (fun q : (E →L[ℝ] E)ˣ × ℝP[n] ↦ q.1 • q.2) ∘
        (e.extend ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n))).symm)
      (Set.range ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n))) p0 := by
  let eU : OpenPartialHomeomorph (E →L[ℝ] E)ˣ (E →L[ℝ] E) :=
    chartAt (E →L[ℝ] E) p.1
  let e :
      OpenPartialHomeomorph ((E →L[ℝ] E)ˣ × ℝP[n])
        ((E →L[ℝ] E) × EuclideanSpace ℝ (Fin n)) :=
    eU.prod (realProjectiveChart n i)
  let p0 : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n) :=
    ((p.1 : E →L[ℝ] E), realProjectiveChart n i p.2)
  let localModel : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) := fun q ↦
    WithLp.toLp 2 fun l ↦
      ((q.1 (realProjectiveChartInvVector n i q.2)) (j.succAbove l)) /
        ((q.1 (realProjectiveChartInvVector n i q.2)) j)
  have hden :
      (((p.1 : E →L[ℝ] E) (realProjectiveChartInvVector n i (realProjectiveChart n i p.2))) j) ≠
        0 := by
    have hsmul :
        p.1 • (realProjectiveChart n i).symm (realProjectiveChart n i p.2) ∈
          realProjectiveChartDomain n j := by
      simpa [OpenPartialHomeomorph.left_inv (realProjectiveChart n i) hi] using hj
    rw [realProjectiveChart_symm_apply, Projectivization.smul_mk] at hsmul
    exact
      (realProjectiveChartDomain_mk n j
        ((p.1 : E →L[ℝ] E) (realProjectiveChartInvVector n i (realProjectiveChart n i p.2)))
        ((smul_ne_zero_iff_ne p.1).2
          (realProjectiveChartInvVector_ne_zero n i (realProjectiveChart n i p.2)))).1 hsmul
  have hmodel :
      ContDiffWithinAt ℝ ∞ localModel
        (Set.range ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n))) p0 := by
    simpa [localModel, p0] using realProjectiveActionLocalModel_contDiffWithinAt n i j hden
  have hEq :
      (((realProjectiveChart n j).extend (𝓡 n)) ∘
          (fun q : (E →L[ℝ] E)ˣ × ℝP[n] ↦ q.1 • q.2) ∘
          (e.extend ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n))).symm)
        =ᶠ[nhdsWithin p0 (Set.range ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n)))] localModel := by
    simpa [e, eU, p0, localModel] using
      realProjectiveAction_chartExpression_eventuallyEq (n := n) (p := p) i j hi
  have hp : p ∈ e.source := by
    refine ⟨?_, hi⟩
    simp [eU]
  have hp0target : p0 ∈ (e.extend ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n))).target :=
    (e.extend ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n))).map_source <| by
      simpa [e, OpenPartialHomeomorph.extend_source] using hp
  have hp0range :
      p0 ∈ Set.range ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n)) :=
    e.extend_target_subset_range hp0target
  exact hmodel.congr_of_eventuallyEq hEq (hEq.eq_of_nhdsWithin hp0range)

/-- Helper for Problem 7-9: after choosing standard affine charts around `x` and `A • x`, the
projective action is smooth at `(A, x)`. -/
theorem realProjectiveAction_contMDiffAt_of_chart_pair
    {p : (E →L[ℝ] E)ˣ × ℝP[n]} {i j : Fin (n + 1)}
    (hi : p.2 ∈ realProjectiveChartDomain n i)
    (hj : p.1 • p.2 ∈ realProjectiveChartDomain n j) :
    ContMDiffAt
      ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n))
      (𝓡 n) ∞
      (fun q : (E →L[ℝ] E)ˣ × ℝP[n] ↦ q.1 • q.2) p := by
  let eU : OpenPartialHomeomorph (E →L[ℝ] E)ˣ (E →L[ℝ] E) :=
    chartAt (E →L[ℝ] E) p.1
  let e :
      OpenPartialHomeomorph ((E →L[ℝ] E)ˣ × ℝP[n])
        ((E →L[ℝ] E) × EuclideanSpace ℝ (Fin n)) :=
    eU.prod (realProjectiveChart n i)
  let p0 : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n) :=
    ((p.1 : E →L[ℝ] E), realProjectiveChart n i p.2)
  let localModel : (E →L[ℝ] E) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) := fun q ↦
    WithLp.toLp 2 fun l ↦
      ((q.1 (realProjectiveChartInvVector n i q.2)) (j.succAbove l)) /
        ((q.1 (realProjectiveChartInvVector n i q.2)) j)
  have heU :
      eU ∈ IsManifold.maximalAtlas 𝓘(ℝ, E →L[ℝ] E) ∞ (E →L[ℝ] E)ˣ := by
    simpa [eU] using (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E →L[ℝ] E)) p.1)
  have he :
      e ∈ IsManifold.maximalAtlas ((𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n)) ∞
        ((E →L[ℝ] E)ˣ × ℝP[n]) := by
    exact IsManifold.mem_maximalAtlas_prod heU (realProjectiveChart_memMaximalAtlas n i)
  have he' :
      realProjectiveChart n j ∈ IsManifold.maximalAtlas (𝓡 n) ∞ (ℝP[n]) :=
    realProjectiveChart_memMaximalAtlas n j
  have hp : p ∈ e.source := by
    refine ⟨?_, hi⟩
    simp [eU]
  rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas
    (I := (𝓘(ℝ, E →L[ℝ] E)).prod (𝓡 n)) (I' := 𝓡 n) (e := e)
    (e' := realProjectiveChart n j) he he' hp hj,
    continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter]
  refine ⟨?_, ?_⟩
  · exact realProjectiveAction_continuous (n := n) |>.continuousAt
  · simpa [e, eU, p0] using
      realProjectiveAction_writtenInCharts_contDiffWithinAt (n := n) (p := p) hi hj

/-- Problem 7-9 (2): the canonical continuous-linear automorphism action on `ℝPⁿ` is smooth. -/
theorem real_projective_contMDiffSMul :
    ContMDiffSMul
      𝓘(ℝ, E →L[ℝ] E)
      (𝓡 n) ∞
      (E →L[ℝ] E)ˣ
      ℝP[n] := by
  refine ⟨?_⟩
  intro p
  rcases real_projective_space_has_standard_chart n p.2 with ⟨i, hi⟩
  rcases real_projective_space_has_standard_chart n (p.1 • p.2) with ⟨j, hj⟩
  exact realProjectiveAction_contMDiffAt_of_chart_pair n hi hj

/-- Problem 7-9 (3): the canonical general linear action on `ℝPⁿ` is pretransitive. -/
theorem real_projective_generalLinear_isPretransitive :
    MulAction.IsPretransitive (LinearMap.GeneralLinearGroup ℝ E) (ℙ ℝ E) := by
  let _ :
      MulAction.IsMultiplyPretransitive
        (LinearMap.GeneralLinearGroup ℝ E)
        (ℙ ℝ E)
        2 :=
    Projectivization.generalLinearGroup_is_two_pretransitive ℝ E
  exact MulAction.isPretransitive_of_is_two_pretransitive

end
