import Mathlib
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap01.Sec01_07.Problem_1_9
import SmoothManifolds_Lee_2012.Chap04.Sec04_27.Problem_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open Projectivization
open Matrix.GeneralLinearGroup LinearMap.GeneralLinearGroup
open scoped LinearAlgebra.Projectivization Manifold ContDiff

-- Domain sampling for this refine pass:
-- `Projectivization.smul_mk`
-- `Projectivization.generalLinearGroup_is_two_pretransitive`
-- `Matrix.GeneralLinearGroup.toLin`
-- `Module.End.toContinuousLinearMap`
-- `EuclideanSpace.equiv`

section

variable (n : ℕ)

local notation "E" => EuclideanSpace ℂ (Fin (n + 1))
local notation "M" => Fin (n + 1) → Fin (n + 1) → ℂ

local instance : CompleteSpace E := by infer_instance

local instance : CompleteSpace (E →L[ℂ] E) :=
  (SeparatingDual.completeSpace_continuousLinearMap_iff ℂ E E).2 inferInstance

local instance : ChartedSpace (E →L[ℂ] E) ((E →L[ℂ] E)ˣ) :=
  Units.instChartedSpace

local instance : MulAction ((E →L[ℂ] E)ˣ) (ℂP[n]) :=
  Projectivization.instMulAction

/- Problem 7-10 (1): the projective action formula is the canonical owner
`Projectivization.smul_mk`. -/
recall Projectivization.smul_mk

/-
Problem 7-10 (2): the matrix group `GL(n + 1, ℂ)` acts on `ℂPⁿ` through the canonical projective
linear-action owner `LinearMap.GeneralLinearGroup ℂ E`, with the matrix model transported to the
chapter ambient space `E = EuclideanSpace ℂ (Fin (n + 1))` by
`Matrix.GeneralLinearGroup.toLin` and `EuclideanSpace.equiv`.
-/
/-- Problem 7-10 (2), bridge/view: the concrete matrix model `GL(n + 1, ℂ)` maps to the intrinsic
continuous-linear automorphism owner `((E →L[ℂ] E)ˣ)`. This is the continuous-linear upgrade of
the canonical matrix-to-linear bridge `Matrix.GeneralLinearGroup.toLin`, transported to
`E = EuclideanSpace ℂ (Fin (n + 1))`. -/
def complex_generalLinear_toContinuousLinearUnits :
    GL (Fin (n + 1)) ℂ →* ((E →L[ℂ] E)ˣ) :=
  (Units.mapEquiv
      ((Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ)).toMulEquiv)).toMonoidHom

/-- Helper for Problem 7-10: the canonical matrix model acts on `E = ℂ^(n+1)` by a fixed real
continuous-linear map into continuous endomorphisms. -/
abbrev complexMatrixToContinuousLinearMap : M →L[ℝ] (E →L[ℂ] E) :=
  let linearPart : M →ₗ[ℝ] (E →L[ℂ] E) :=
    { toFun := fun A ↦ Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ) A
      map_add' := by
        intro A B
        simp
      map_smul' := by
        intro c A
        change
          Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ) ((c : ℂ) • A) =
            c • Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ) A
        simpa using
          (map_smul
            (Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ) : M →ₗ[ℂ] (E →L[ℂ] E))
            (c : ℂ) A) }
  linearPart.mkContinuous 1 fun A ↦ by
    -- Package the linear matrix-to-operator bridge with the operator-norm identity from mathlib.
    simpa [linearPart, one_mul] using
      le_of_eq (Matrix.l2_opNorm_toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ) A)

/-- Helper for Problem 7-10: the inserted homogeneous representative
`complexProjectiveChartInvVector n i` is smooth as a real map. -/
theorem complexProjectiveChartInvVector_contDiff (i : Fin (n + 1)) :
    ContDiff ℝ ∞ (complexProjectiveChartInvVector n i) := by
  -- Reuse the Chapter 4 smoothness theorem for the scaled inserted representative at scale `1`.
  rw [← contMDiff_iff_contDiff]
  simpa using complex_projective_scaled_inv_vector_cont_mdiff n i (1 : ℂ)

/-- Helper for Problem 7-10: in standard affine charts, the action of a continuous-linear unit on
`ℂPⁿ` is given by the usual quotient of transformed homogeneous coordinates. -/
theorem complexProjectiveChart_smul_formula
    (A : (E →L[ℂ] E)ˣ) (i j : Fin (n + 1))
    (u : EuclideanSpace ℂ (Fin n)) :
    complexProjectiveChart n j (A • (complexProjectiveChart n i).symm u) =
      WithLp.toLp 2 fun k ↦
        (((A : E →L[ℂ] E) (complexProjectiveChartInvVector n i u)) (j.succAbove k)) /
          (((A : E →L[ℂ] E) (complexProjectiveChartInvVector n i u)) j) := by
  -- Rewrite the projective action through the explicit homogeneous representative.
  rw [complexProjectiveChart_symm_apply, Projectivization.smul_mk, complexProjectiveChart_mk]
  rfl

/-- Helper for Problem 7-10: the Euclidean local model of the projective action is smooth near any
point where the chosen denominator coordinate is nonzero. -/
theorem complexProjectiveActionLocalModel_contDiffWithinAt
    (i j : Fin (n + 1))
    {p0 : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n)}
    (hj :
      ((p0.1 (complexProjectiveChartInvVector n i p0.2)) j) ≠ 0) :
    ContDiffWithinAt ℝ ∞
      (fun p : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n) ↦
        WithLp.toLp 2 fun l ↦
          ((p.1 (complexProjectiveChartInvVector n i p.2)) (j.succAbove l)) /
            ((p.1 (complexProjectiveChartInvVector n i p.2)) j))
      (Set.range ((𝓘(ℝ, E →L[ℂ] E)).prod (𝓘(ℝ, EuclideanSpace ℂ (Fin n))))) p0 := by
  let restrictScalarsCLM : (E →L[ℂ] E) →L[ℝ] E →L[ℝ] E :=
    ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
  have hInv :
      ContDiff ℝ ∞
        (fun u : EuclideanSpace ℂ (Fin n) ↦ complexProjectiveChartInvVector n i u) := by
    -- First view the inserted representative as a smooth map into homogeneous coordinates.
    simpa using complexProjectiveChartInvVector_contDiff (n := n) i
  have hfstR :
      ContDiff ℝ ∞
        (fun p : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n) ↦
          restrictScalarsCLM p.1) := by
    -- Restrict scalars on the operator so evaluation is an `ℝ`-smooth bilinear map.
    simpa [restrictScalarsCLM] using restrictScalarsCLM.contDiff.comp contDiff_fst
  have hApply :
      ContDiff ℝ ∞
        (fun p : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n) ↦
          p.1 (complexProjectiveChartInvVector n i p.2)) := by
    have hEval :
        IsBoundedBilinearMap ℝ (fun p : (E →L[ℝ] E) × E ↦ p.1 p.2) :=
      isBoundedBilinearMap_apply
    -- Evaluation is `ℝ`-smooth after restricting scalars on the operator coordinate.
    simpa [restrictScalarsCLM] using
      hEval.contDiff.comp₂ hfstR (hInv.comp contDiff_snd)
  have hLocal :
      ContDiffAt ℝ ∞
        (fun p : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n) ↦
          WithLp.toLp 2 fun l ↦
            ((p.1 (complexProjectiveChartInvVector n i p.2)) (j.succAbove l)) /
              ((p.1 (complexProjectiveChartInvVector n i p.2)) j)) p0 := by
    refine contDiffAt_piLp' (p := (2 : ENNReal)) ?_
    intro l
    have hNum :
        ContDiffAt ℝ ∞
          (fun p : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n) ↦
            ((p.1 (complexProjectiveChartInvVector n i p.2)) (j.succAbove l))) p0 := by
      -- Each numerator coordinate is a smooth projection of the evaluated vector.
      exact
        (contDiffAt_piLp_apply (p := (2 : ENNReal)) (i := j.succAbove l)).comp p0
          hApply.contDiffAt
    have hDen :
        ContDiffAt ℝ ∞
          (fun p : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n) ↦
            ((p.1 (complexProjectiveChartInvVector n i p.2)) j)) p0 := by
      -- The denominator coordinate is smooth for the same reason.
      exact (contDiffAt_piLp_apply (p := (2 : ENNReal)) (i := j)).comp p0 hApply.contDiffAt
    -- Divide the smooth numerator by the smooth nonvanishing denominator.
    simpa [div_eq_mul_inv] using hNum.mul (hDen.inv hj)
  exact hLocal.contDiffWithinAt

/-- Helper for Problem 7-10: after choosing standard affine charts around `x` and `A • x`, the
projective action has the explicit quotient expression on the chart target. -/
theorem complexProjectiveAction_chartExpression_eventuallyEq
    {p : (E →L[ℂ] E)ˣ × ℂP[n]}
    (i j : Fin (n + 1))
    (hi : p.2 ∈ complexProjectiveChartDomain n i) :
    let eU : OpenPartialHomeomorph (E →L[ℂ] E)ˣ (E →L[ℂ] E) :=
      chartAt (E →L[ℂ] E) p.1
    let e :
        OpenPartialHomeomorph ((E →L[ℂ] E)ˣ × ℂP[n])
          ((E →L[ℂ] E) × EuclideanSpace ℂ (Fin n)) :=
      eU.prod (complexProjectiveChart n i)
    let p0 : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n) :=
      ((p.1 : E →L[ℂ] E), complexProjectiveChart n i p.2)
    let f : (E →L[ℂ] E)ˣ × ℂP[n] → ℂP[n] := fun q ↦ q.1 • q.2
    let localModel : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n) →
        EuclideanSpace ℂ (Fin n) := fun q ↦
      WithLp.toLp 2 fun l ↦
        ((q.1 (complexProjectiveChartInvVector n i q.2)) (j.succAbove l)) /
          ((q.1 (complexProjectiveChartInvVector n i q.2)) j)
    (((complexProjectiveChart n j).extend (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) ∘ f ∘
        (e.extend
          ((𝓘(ℝ, E →L[ℂ] E)).prod (𝓘(ℝ, EuclideanSpace ℂ (Fin n))))).symm)
      =ᶠ[nhdsWithin p0
          (Set.range ((𝓘(ℝ, E →L[ℂ] E)).prod (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))))]
        localModel := by
  let eU : OpenPartialHomeomorph (E →L[ℂ] E)ˣ (E →L[ℂ] E) :=
    chartAt (E →L[ℂ] E) p.1
  let e :
      OpenPartialHomeomorph ((E →L[ℂ] E)ˣ × ℂP[n])
        ((E →L[ℂ] E) × EuclideanSpace ℂ (Fin n)) :=
    eU.prod (complexProjectiveChart n i)
  let p0 : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n) :=
    ((p.1 : E →L[ℂ] E), complexProjectiveChart n i p.2)
  let f : (E →L[ℂ] E)ˣ × ℂP[n] → ℂP[n] := fun q ↦ q.1 • q.2
  let localModel : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) := fun q ↦
    WithLp.toLp 2 fun l ↦
      ((q.1 (complexProjectiveChartInvVector n i q.2)) (j.succAbove l)) /
        ((q.1 (complexProjectiveChartInvVector n i q.2)) j)
  have hRange :
      Set.range ((𝓘(ℝ, E →L[ℂ] E)).prod (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) = Set.univ := by
    ext q
    simp
  have hp : p ∈ e.source := by
    refine ⟨?_, hi⟩
    simp [eU]
  have htarget_mem :
      (e.extend ((𝓘(ℝ, E →L[ℂ] E)).prod (𝓘(ℝ, EuclideanSpace ℂ (Fin n))))).target ∈
        nhdsWithin p0
          (Set.range ((𝓘(ℝ, E →L[ℂ] E)).prod (𝓘(ℝ, EuclideanSpace ℂ (Fin n))))) := by
    simpa [hRange, e, eU, p0, Units.chartAt_apply] using
      (e.extend_target_mem_nhdsWithin
        (I := (𝓘(ℝ, E →L[ℂ] E)).prod (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) hp)
  refine Filter.eventuallyEq_of_mem htarget_mem ?_
  intro q hq
  have hq' : q ∈ e.target := by
    simpa [hRange, OpenPartialHomeomorph.extend_target] using hq
  have hqU : q.1 ∈ eU.target := by
    simpa [e] using hq'.1
  have hcoeeU :
      (((eU.symm q.1 : (E →L[ℂ] E)ˣ) : E →L[ℂ] E)) = q.1 := by
    have hright : eU (eU.symm q.1) = q.1 := OpenPartialHomeomorph.right_inv eU hqU
    simpa [eU, Units.chartAt_apply] using hright
  -- Route correction: normalize the units chart inverse once here instead of reopening the same
  -- `extend`/coercion proof inside the main action theorem.
  ext l
  have hformula :
      (complexProjectiveChart n j
          ((eU.symm q.1 : (E →L[ℂ] E)ˣ) • (complexProjectiveChart n i).symm q.2)) l =
        (WithLp.toLp 2 fun k ↦
          ((((eU.symm q.1 : (E →L[ℂ] E)ˣ) : E →L[ℂ] E)
              (complexProjectiveChartInvVector n i q.2)) (j.succAbove k)) /
            ((((eU.symm q.1 : (E →L[ℂ] E)ˣ) : E →L[ℂ] E)
              (complexProjectiveChartInvVector n i q.2)) j)) l := by
    exact
      congrArg (fun v : EuclideanSpace ℂ (Fin n) ↦ v l)
        (complexProjectiveChart_smul_formula n (eU.symm q.1) i j q.2)
  rw [hcoeeU] at hformula
  simpa [f, localModel, e, eU, Function.comp, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm] using hformula

/-- Helper for Problem 7-10: the normalized chart expression agrees with the local quotient model
at the chosen chart basepoint. -/
theorem complexProjectiveAction_chartExpression_eqAtBasepoint
    {p : (E →L[ℂ] E)ˣ × ℂP[n]}
    (i j : Fin (n + 1))
    (hi : p.2 ∈ complexProjectiveChartDomain n i) :
    let eU : OpenPartialHomeomorph (E →L[ℂ] E)ˣ (E →L[ℂ] E) :=
      chartAt (E →L[ℂ] E) p.1
    let e :
        OpenPartialHomeomorph ((E →L[ℂ] E)ˣ × ℂP[n])
          ((E →L[ℂ] E) × EuclideanSpace ℂ (Fin n)) :=
      eU.prod (complexProjectiveChart n i)
    let p0 : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n) :=
      ((p.1 : E →L[ℂ] E), complexProjectiveChart n i p.2)
    let f : (E →L[ℂ] E)ˣ × ℂP[n] → ℂP[n] := fun q ↦ q.1 • q.2
    let localModel : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n) →
        EuclideanSpace ℂ (Fin n) := fun q ↦
      WithLp.toLp 2 fun l ↦
        ((q.1 (complexProjectiveChartInvVector n i q.2)) (j.succAbove l)) /
          ((q.1 (complexProjectiveChartInvVector n i q.2)) j)
    ((((complexProjectiveChart n j).extend (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) ∘ f ∘
        (e.extend
          ((𝓘(ℝ, E →L[ℂ] E)).prod (𝓘(ℝ, EuclideanSpace ℂ (Fin n))))).symm) p0)
      = localModel p0 := by
  let eU : OpenPartialHomeomorph (E →L[ℂ] E)ˣ (E →L[ℂ] E) :=
    chartAt (E →L[ℂ] E) p.1
  let e :
      OpenPartialHomeomorph ((E →L[ℂ] E)ˣ × ℂP[n])
        ((E →L[ℂ] E) × EuclideanSpace ℂ (Fin n)) :=
    eU.prod (complexProjectiveChart n i)
  let p0 : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n) :=
    ((p.1 : E →L[ℂ] E), complexProjectiveChart n i p.2)
  let f : (E →L[ℂ] E)ˣ × ℂP[n] → ℂP[n] := fun q ↦ q.1 • q.2
  let localModel : (E →L[ℂ] E) × EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) := fun q ↦
    WithLp.toLp 2 fun l ↦
      ((q.1 (complexProjectiveChartInvVector n i q.2)) (j.succAbove l)) /
        ((q.1 (complexProjectiveChartInvVector n i q.2)) j)
  have hRange :
      Set.range ((𝓘(ℝ, E →L[ℂ] E)).prod (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) = Set.univ := by
    ext q
    simp
  have hp0range :
      p0 ∈ Set.range ((𝓘(ℝ, E →L[ℂ] E)).prod (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) := by
    simpa [hRange]
  have hEq :
      (((complexProjectiveChart n j).extend (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))) ∘ f ∘
          (e.extend
            ((𝓘(ℝ, E →L[ℂ] E)).prod (𝓘(ℝ, EuclideanSpace ℂ (Fin n))))).symm)
        =ᶠ[nhdsWithin p0
            (Set.range ((𝓘(ℝ, E →L[ℂ] E)).prod (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))))]
          localModel := by
    -- Reuse the already-stable chart-expression theorem rather than reopening the same transport.
    simpa [e, eU, p0, localModel] using
      complexProjectiveAction_chartExpression_eventuallyEq (n := n) (p := p) i j hi
  exact hEq.eq_of_nhdsWithin hp0range

/-- Helper for Problem 7-10: after choosing standard affine charts around `x` and `A • x`, the
projective action is smooth at `(A, x)`. -/
theorem complexProjectiveAction_contMDiffAt_of_chart_pair
    {p : (E →L[ℂ] E)ˣ × ℂP[n]} {i j : Fin (n + 1)}
    (hi : p.2 ∈ complexProjectiveChartDomain n i)
    (hj : p.1 • p.2 ∈ complexProjectiveChartDomain n j) :
    ContMDiffAt
      ((𝓘(ℝ, E →L[ℂ] E)).prod (𝓘(ℝ, EuclideanSpace ℂ (Fin n))))
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ∞
      (fun q : (E →L[ℂ] E)ˣ × ℂP[n] ↦ q.1 • q.2) p := by
  -- TODO: the chart-level route is now reduced to one blocker. The denominator nonvanishing
  -- argument, the local-model `ContDiffWithinAt`, and the normalized chart/basepoint equality are
  -- all available from the preceding helper lemmas. The remaining missing piece is a reusable
  -- continuity bridge for the projectivized `((E →L[ℂ] E)ˣ)`-action at `(p.1, p.2)`:
  -- either a `ContinuousSMul ((E →L[ℂ] E)ˣ) (ℂP[n])` instance or a local
  -- `ContinuousWithinAt` theorem derived from the same chart data.
  sorry

/-- Problem 7-10 (2): the canonical continuous-linear automorphism action on `ℂPⁿ` is smooth. -/
theorem complex_projective_contMDiffSMul :
    ContMDiffSMul
      𝓘(ℝ, E →L[ℂ] E)
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ∞
      ((E →L[ℂ] E)ˣ)
      (ℂP[n]) := by
  refine ⟨?_⟩
  intro p
  -- Choose affine charts around both `x` and `A • x`, then invoke the chart-pair theorem.
  rcases complex_projective_space_has_standard_chart n p.2 with ⟨i, hi⟩
  rcases complex_projective_space_has_standard_chart n (p.1 • p.2) with ⟨j, hj⟩
  exact complexProjectiveAction_contMDiffAt_of_chart_pair n hi hj

/-- Helper for Problem 7-10: the repaired ambient matrix bridge evaluates to the canonical
continuous linear map `Matrix.toEuclideanCLM`. -/
theorem complexMatrixToContinuousLinearMap_apply
    (A : M) :
    complexMatrixToContinuousLinearMap n A =
      Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ) A := by
  -- Unpack the `mkContinuous` wrapper; the underlying real-linear map is exactly the owner map.
  simp [complexMatrixToContinuousLinearMap, LinearMap.mkContinuous_apply,
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]

/-- Helper for Problem 7-10: the ambient matrix-to-operator bridge is smooth because it is a fixed
real continuous-linear map. -/
theorem complexMatrixToContinuousLinearMap_contMDiff :
    ContMDiff (𝓘(ℝ, M)) 𝓘(ℝ, E →L[ℂ] E) ∞ (complexMatrixToContinuousLinearMap n) := by
  -- A continuous linear map between Euclidean models is smooth of all orders.
  simpa using (complexMatrixToContinuousLinearMap n).contMDiff

/-- Helper for Problem 7-10: coercing the units-valued matrix bridge forgets only the unit proof. -/
theorem complexGeneralLinear_toContinuousLinearUnits_val_eq
    (A : GL (Fin (n + 1)) ℂ) :
    ((complex_generalLinear_toContinuousLinearUnits n A : (E →L[ℂ] E)ˣ) : E →L[ℂ] E) =
      complexMatrixToContinuousLinearMap n A := by
  -- Forgetting the unit proof leaves the same canonical matrix action on `E`.
  rw [complexMatrixToContinuousLinearMap_apply]
  rfl

/-- Helper for Problem 7-10: after coercing to the ambient Banach algebra, the matrix-model bridge
is smooth. -/
theorem complex_generalLinear_toContinuousLinearMap_contMDiff
    [ChartedSpace M (GL (Fin (n + 1)) ℂ)]
    [LieGroup (𝓘(ℝ, M)) ∞ (GL (Fin (n + 1)) ℂ)] :
    ContMDiff
      (𝓘(ℝ, M))
      𝓘(ℝ, E →L[ℂ] E)
      ∞
      (fun A : GL (Fin (n + 1)) ℂ ↦
        ((complex_generalLinear_toContinuousLinearUnits n A : (E →L[ℂ] E)ˣ) : E →L[ℂ] E)) := by
  have hval :
      ContMDiff
        (𝓘(ℝ, M))
        (𝓘(ℝ, M))
        ∞
        (fun A : GL (Fin (n + 1)) ℂ ↦ (A : M)) := by
    -- The units chart on `GL` is modeled on the ambient matrix space by the value map.
    simpa using
      (Units.contMDiff_val :
        ContMDiff (𝓘(ℝ, M)) (𝓘(ℝ, M)) ∞
          (fun A : GL (Fin (n + 1)) ℂ ↦ (A : M)))
  have hComp :
      ContMDiff
        (𝓘(ℝ, M))
        𝓘(ℝ, E →L[ℂ] E)
        ∞
        (fun A : GL (Fin (n + 1)) ℂ ↦ complexMatrixToContinuousLinearMap n (A : M)) := by
    -- Compose the ambient linear bridge with the smooth coercion `GL -> M`.
    exact (complexMatrixToContinuousLinearMap_contMDiff n).comp hval
  simpa [complexGeneralLinear_toContinuousLinearUnits_val_eq] using hComp

/-- Helper for Problem 7-10: the matrix-model bridge into `((E →L[ℂ] E)ˣ)` is smooth. -/
theorem complex_generalLinear_toContinuousLinearUnits_contMDiff
    [ChartedSpace M (GL (Fin (n + 1)) ℂ)]
    [LieGroup (𝓘(ℝ, M)) ∞ (GL (Fin (n + 1)) ℂ)] :
    ContMDiff
      (𝓘(ℝ, M))
      𝓘(ℝ, E →L[ℂ] E)
      ∞
      (complex_generalLinear_toContinuousLinearUnits n) := by
  -- Lift the smooth ambient map through the open embedding `Units.val`.
  refine ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val ?_
  simpa using complex_generalLinear_toContinuousLinearMap_contMDiff n

/-- Problem 7-10 (2), bridge/view: the canonical matrix-to-continuous-linear bridge is a smooth
Lie group homomorphism. -/
def complex_generalLinear_toContinuousLinearUnits_lie_hom
    [ChartedSpace M (GL (Fin (n + 1)) ℂ)]
    [LieGroup (𝓘(ℝ, M)) ∞ (GL (Fin (n + 1)) ℂ)] :
    ContMDiffMonoidMorphism
      (𝓘(ℝ, M))
      𝓘(ℝ, E →L[ℂ] E)
      ∞
      (GL (Fin (n + 1)) ℂ)
      ((E →L[ℂ] E)ˣ) where
  toMonoidHom := complex_generalLinear_toContinuousLinearUnits n
  contMDiff_toFun := by
    -- The auxiliary smoothness lemma isolates the units-valued transport from the ambient map.
    simpa using complex_generalLinear_toContinuousLinearUnits_contMDiff n

/-- Problem 7-10 (2), bridge/view: any smooth homomorphism from `GL(n + 1, ℂ)` to the canonical
continuous-linear automorphism owner induces a smooth action on `ℂPⁿ` via `MulAction.compHom`. -/
theorem complex_projective_contMDiffSMul_compHom
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [ChartedSpace H (GL (Fin (n + 1)) ℂ)]
    [LieGroup (𝓘(ℝ, H)) ∞ (GL (Fin (n + 1)) ℂ)]
    (ρ : ContMDiffMonoidMorphism
      (𝓘(ℝ, H))
      𝓘(ℝ, E →L[ℂ] E)
      ∞
      (GL (Fin (n + 1)) ℂ)
      ((E →L[ℂ] E)ˣ)) :
    let _ : MulAction (GL (Fin (n + 1)) ℂ) (ℂP[n]) := MulAction.compHom (ℂP[n]) ρ.toMonoidHom
    ContMDiffSMul
      (𝓘(ℝ, H))
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ∞
      (GL (Fin (n + 1)) ℂ)
      (ℂP[n]) := by
  let _ : ContMDiffSMul
      𝓘(ℝ, E →L[ℂ] E)
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ∞
      ((E →L[ℂ] E)ˣ)
      (ℂP[n]) :=
    complex_projective_contMDiffSMul n
  let _ : MulAction (GL (Fin (n + 1)) ℂ) (ℂP[n]) := MulAction.compHom (ℂP[n]) ρ.toMonoidHom
  exact MulAction.contMDiffSMul_compHom ρ.contMDiff_toFun

/-- Problem 7-10 (2): via the canonical matrix-to-continuous-linear bridge, the standard
`GL(n + 1, ℂ)`-action on `ℂPⁿ` is smooth. -/
theorem complex_projective_generalLinear_contMDiffSMul
    [ChartedSpace M (GL (Fin (n + 1)) ℂ)]
    [LieGroup (𝓘(ℝ, M)) ∞ (GL (Fin (n + 1)) ℂ)] :
    let _ : MulAction (GL (Fin (n + 1)) ℂ) (ℂP[n]) :=
      MulAction.compHom (ℂP[n]) (complex_generalLinear_toContinuousLinearUnits n)
    ContMDiffSMul
      (𝓘(ℝ, M))
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ∞
      (GL (Fin (n + 1)) ℂ)
      (ℂP[n]) :=
  complex_projective_contMDiffSMul_compHom n
    (complex_generalLinear_toContinuousLinearUnits_lie_hom n)

/-- Problem 7-10 (3): the canonical general linear action on `ℂPⁿ` is pretransitive. -/
theorem complex_projective_generalLinear_isPretransitive :
    MulAction.IsPretransitive (LinearMap.GeneralLinearGroup ℂ E) (ℙ ℂ E) := by
  let _ :
      MulAction.IsMultiplyPretransitive
        (LinearMap.GeneralLinearGroup ℂ E)
        (ℙ ℂ E)
        2 :=
    Projectivization.generalLinearGroup_is_two_pretransitive ℂ E
  exact MulAction.isPretransitive_of_is_two_pretransitive

end
