import BauschkeLean.Chap04.Proposition_4_4
import BauschkeLean.Chap04.Remark_4_34
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.Proposition_20_10
import BauschkeLean.Chap23.Corollary_23_9
import BauschkeLean.Chap23.Proposition_23_22

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the canonical owner chain here is the Chapter 23 Yosida approximation
-- `{}^[γ] A`, together with the Chapter 4 owners `CocoerciveOn`, `FirmlyNonexpansiveOn`, and
-- `residualMap`. The proof path goes through firm nonexpansiveness of the residual map and the
-- Chapter 23 resolvent/Yosida singleton calculus, so neither completeness nor nonemptiness is
-- primitive data for this proposition.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 23.21 characterizes cocoercive maps as singleton-valued Yosida
  approximations.
- `core/canonical`: the Chapter 23 owner for that construction is `{}^[γ] A`.
- `bridge/view`: `ofFunction D T`, `Function.toSetValuedOperator`, and the Chapter 4 residual map
  `residualMap D (fun x ↦ (γ : ℝ) • T x)` bridge single-valued maps to the resolvent/Yosida
  operators. -/

private theorem maximal_isMonotone_smul
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {γ : ℝ} (hγ : 0 < γ) :
    Maximal IsMonotone (γ • A) := by
  rw [maximal_iff_mem_iff]
  intro x u
  rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ hγ.ne']
  constructor
  · intro hxu y v hv
    rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ hγ.ne'] at hv
    have hrel := (Maximal.mem_iff hA x (γ⁻¹ • u)).1 hxu hv
    rw [← smul_sub, real_inner_smul_right] at hrel
    nlinarith [inv_pos.mpr hγ]
  · intro hrel
    refine (Maximal.mem_iff hA x (γ⁻¹ • u)).2 ?_
    intro y w hw
    have hw' : γ • w ∈ (γ • A) y := by
      simpa [Pi.smul_apply] using Set.smul_mem_smul_set hw
    have hrel' := hrel hw'
    have hrewrite :
        inner ℝ (x - y) (u - γ • w) = γ * inner ℝ (x - y) (γ⁻¹ • u - w) := by
      calc
        inner ℝ (x - y) (u - γ • w)
            = inner ℝ (x - y) (γ • ((γ⁻¹ : ℝ) • u - w)) := by
                congr 2
                calc
                  u - γ • w = γ • ((γ⁻¹ : ℝ) • u) - γ • w := by
                    rw [smul_inv_smul₀ hγ.ne' u]
                  _ = γ • ((γ⁻¹ : ℝ) • u - w) := by
                    rw [smul_sub]
        _ = γ * inner ℝ (x - y) ((γ⁻¹ : ℝ) • u - w) := by
              rw [real_inner_smul_right]
    rw [hrewrite] at hrel'
    nlinarith

private theorem yosidaApproximation_eq_ofFunction_of_resolvent_eq_ofFunction_residual
    {A : SetValuedOperator H H} (hA : A.IsMonotone) (γ : PosReal)
    (D : Set H) (T : D → H)
    (hJ :
      J[((γ : ℝ) • A)] =
        ofFunction D (residualMap D (fun x : D ↦ (γ : ℝ) • T x))) :
    {}^[γ] A = ofFunction D T := by
  ext x u
  by_cases hx : x ∈ D
  · have hy_mem : x - (γ : ℝ) • T ⟨x, hx⟩ ∈ J[((γ : ℝ) • A)] x := by
      rw [hJ, ofFunction_apply_of_mem D (residualMap D (fun x : D ↦ (γ : ℝ) • T x)) hx]
      simp [residualMap]
    have hTu_mem : T ⟨x, hx⟩ ∈ ({}^[γ] A) x := by
      refine (mem_yosidaApproximation_iff_mem_graph A γ x _).2 ?_
      simpa [smul_smul, γ.2.ne'] using
        (mem_resolvent_smul_iff_mem_graph A γ x (x - (γ : ℝ) • T ⟨x, hx⟩)).1 hy_mem
    rw [yosidaApproximation_eq_singleton_of_mem hA γ hTu_mem, ofFunction_apply_of_mem D T hx]
  · have hx_empty : ({}^[γ] A) x = (∅ : Set H) := by
      rw [← Set.not_nonempty_iff_eq_empty, ← mem_dom_iff]
      rw [← dom_resolvent_smul_eq_dom_yosidaApproximation A γ, hJ]
      rw [mem_dom_iff, ofFunction_apply_of_not_mem D (residualMap D (fun x : D ↦ (γ : ℝ) • T x))
        hx]
      simp
    rw [hx_empty, ofFunction_apply_of_not_mem D T hx]

private theorem resolvent_eq_ofFunction_of_yosidaApproximation_eq_ofFunction
    {A : SetValuedOperator H H} (hA : A.IsMonotone) (γ : PosReal)
    (D : Set H) (T : D → H) (hY : {}^[γ]A = ofFunction D T) :
    J[((γ : ℝ) • A)] = ofFunction D (residualMap D (fun x : D ↦ (γ : ℝ) • T x)) := by
  ext x u
  by_cases hx : x ∈ D
  · have hTu_mem : T ⟨x, hx⟩ ∈ ({}^[γ] A) x := by
      rw [hY, ofFunction_apply_of_mem D T hx]
      simp
    have hu_mem : x - (γ : ℝ) • T ⟨x, hx⟩ ∈ J[((γ : ℝ) • A)] x := by
      refine (mem_resolvent_smul_iff_mem_graph A γ x _).2 ?_
      simpa [smul_smul, γ.2.ne'] using
        (mem_yosidaApproximation_iff_mem_graph A γ x (T ⟨x, hx⟩)).1 hTu_mem
    rw [resolvent_smul_eq_singleton_of_mem hA γ hu_mem,
      ofFunction_apply_of_mem D (residualMap D (fun x : D ↦ (γ : ℝ) • T x)) hx]
    simp [residualMap]
  · have hx_empty : J[((γ : ℝ) • A)] x = (∅ : Set H) := by
      rw [← Set.not_nonempty_iff_eq_empty, ← mem_dom_iff,
        dom_resolvent_smul_eq_dom_yosidaApproximation A γ]
      rw [hY, mem_dom_iff, ofFunction_apply_of_not_mem D T hx]
      simp
    rw [hx_empty, ofFunction_apply_of_not_mem D (residualMap D (fun x : D ↦ (γ : ℝ) • T x)) hx]

private theorem cocoerciveOn_of_yosidaApproximation_eq_ofFunction
    {A : SetValuedOperator H H} (hA : A.IsMonotone) (γ : PosReal)
    (D : Set H) (T : D → H) (hY : {}^[γ]A = ofFunction D T) :
    CocoerciveOn (γ : ℝ) D T := by
  have hJ :=
    resolvent_eq_ofFunction_of_yosidaApproximation_eq_ofFunction hA γ D T hY
  let γnn : NNReal := ⟨(γ : ℝ), γ.2.le⟩
  have hγA : ((γ : ℝ) • A).IsMonotone := by
    simpa [γnn] using SetValuedOperator.IsMonotone.smul hA γnn
  have hResidualFirm :
      FirmlyNonexpansiveOn D (residualMap D (fun x : D ↦ (γ : ℝ) • T x)) := by
    exact
      (isMonotone_iff_firmlyNonexpansiveOn_of_resolvent_eq_ofFunction
        (((γ : ℝ) • A)) D (residualMap D (fun x : D ↦ (γ : ℝ) • T x)) hJ).1 hγA
  have hScaledFirm : FirmlyNonexpansiveOn D (fun x : D ↦ (γ : ℝ) • T x) :=
    (firmlyNonexpansiveOn_residualMap_iff D (fun x : D ↦ (γ : ℝ) • T x)).1 hResidualFirm
  have hScaledAvg :
      AveragedWith (1 / 2 : ℝ) (fun x : D ↦ (γ : ℝ) • T x) :=
    (firmlyNonexpansiveOn_iff_averagedWith_half (fun x : D ↦ (γ : ℝ) • T x)).1 hScaledFirm
  exact (cocoerciveOn_iff_smul_averagedWith_half γ.2 T).2 hScaledAvg

/-- Proposition 23.21 (1): for a subset `D ⊆ H`, a map `T : D → H`, and
`γ ∈ ℝ_{++}` realized as `γ : PosReal`, the map `T` is `γ`-cocoercive on `D` if and only if it is
the Yosida approximation of index `γ` of some monotone operator `A : H → 2^H`, realized on the
singleton-valued operator surface as `{}^[γ] A = ofFunction D T`. -/
theorem cocoerciveOn_iff_exists_isMonotone_yosidaApproximation_eq_ofFunction
    (D : Set H) (T : D → H) (γ : PosReal) :
    CocoerciveOn (γ : ℝ) D T ↔
      ∃ A : SetValuedOperator H H,
        A.IsMonotone ∧ {}^[γ] A = ofFunction D T := by
  constructor
  · intro hT
    let S : D → H := fun x ↦ (γ : ℝ) • T x
    let R : D → H := residualMap D S
    let B : SetValuedOperator H H := (ofFunction D R)⁻¹ - id.toSetValuedOperator
    let γinv : NNReal := ⟨(γ : ℝ)⁻¹, inv_nonneg.mpr γ.2.le⟩
    let A : SetValuedOperator H H := (γinv : ℝ) • B
    have hScaledAvg : AveragedWith (1 / 2 : ℝ) S :=
      (cocoerciveOn_iff_smul_averagedWith_half γ.2 T).1 hT
    have hScaledFirm : FirmlyNonexpansiveOn D S :=
      (firmlyNonexpansiveOn_iff_averagedWith_half S).2 hScaledAvg
    have hResidualFirm : FirmlyNonexpansiveOn D R :=
      (firmlyNonexpansiveOn_residualMap_iff D S).2 hScaledFirm
    have hB : B.IsMonotone := by
      simpa [B] using
        (firmlyNonexpansiveOn_iff_isMonotone_sub_id_inverse_ofFunction D R).1 hResidualFirm
    have hA : A.IsMonotone := by
      simpa [A, γinv] using SetValuedOperator.IsMonotone.smul hB γinv
    have hJ : J[((γ : ℝ) • A)] = ofFunction D R := by
      simpa [A, B, γinv, smul_smul, γ.2.ne'] using
        (resolvent_sub_id_inverse_ofFunction_eq_ofFunction D R)
    exact ⟨A, hA,
      yosidaApproximation_eq_ofFunction_of_resolvent_eq_ofFunction_residual hA γ D T hJ⟩
  · rintro ⟨A, hA, hY⟩
    exact cocoerciveOn_of_yosidaApproximation_eq_ofFunction hA γ D T hY

/-- Proposition 23.21 (2): for a self-map `T : H → H` and `γ ∈ ℝ_{++}` realized as
`γ : PosReal`, `T` is `γ`-cocoercive on `H` if and only if it is the Yosida approximation of index
`γ` of some maximally monotone operator `A : H → 2^H`, realized on the singleton-valued operator
surface as `{}^[γ] A = T.toSetValuedOperator`. -/
theorem cocoerciveOn_univ_iff_exists_maximal_yosidaApproximation_eq_toSetValuedOperator
    (T : H → H) (γ : PosReal) :
    CocoerciveOn (γ : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ T x) ↔
      ∃ A : SetValuedOperator H H,
        Maximal IsMonotone A ∧ {}^[γ] A = T.toSetValuedOperator := by
  constructor
  · intro hT
    let S : H → H := fun x ↦ x - (γ : ℝ) • T x
    have hScaledAvg :
        AveragedWith (1 / 2 : ℝ) (fun x : Set.univ ↦ (γ : ℝ) • T x) :=
      (cocoerciveOn_iff_smul_averagedWith_half γ.2 (fun x : Set.univ ↦ T x)).1 hT
    have hScaledFirm :
        FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ (γ : ℝ) • T x) :=
      (firmlyNonexpansiveOn_iff_averagedWith_half (fun x : Set.univ ↦ (γ : ℝ) • T x)).2
        hScaledAvg
    have hResidualFirm :
        FirmlyNonexpansiveOn (Set.univ : Set H)
          (residualMap (Set.univ : Set H) (fun x : Set.univ ↦ (γ : ℝ) • T x)) :=
      (firmlyNonexpansiveOn_residualMap_iff (Set.univ : Set H)
        (fun x : Set.univ ↦ (γ : ℝ) • T x)).2 hScaledFirm
    have hS : FirmlyNonexpansive S := by
      simpa [S, FirmlyNonexpansive, residualMap] using hResidualFirm
    rcases (firmlyNonexpansive_iff_exists_maximal_isMonotone_resolvent S).1 hS with
      ⟨B, hB, hJB⟩
    let γinv : NNReal := ⟨(γ : ℝ)⁻¹, inv_nonneg.mpr γ.2.le⟩
    let A : SetValuedOperator H H := (γinv : ℝ) • B
    have hA : Maximal IsMonotone A := by
      simpa [A, γinv] using maximal_isMonotone_smul hB (inv_pos.mpr γ.2)
    have hJ :
        J[((γ : ℝ) • A)] =
          ofFunction (Set.univ : Set H)
            (residualMap (Set.univ : Set H) (fun x : Set.univ ↦ (γ : ℝ) • T x)) := by
      simpa [A, S, γinv, Function.toSetValuedOperator, residualMap, smul_smul, γ.2.ne'] using hJB
    refine ⟨A, hA, ?_⟩
    simpa [Function.toSetValuedOperator] using
      yosidaApproximation_eq_ofFunction_of_resolvent_eq_ofFunction_residual
        hA.1 γ (Set.univ : Set H) (fun x : Set.univ ↦ T x) hJ
  · rintro ⟨A, hA, hY⟩
    exact
      (cocoerciveOn_iff_exists_isMonotone_yosidaApproximation_eq_ofFunction
        (Set.univ : Set H) (fun x : Set.univ ↦ T x) γ).2
        ⟨A, hA.1, by simpa [Function.toSetValuedOperator] using hY⟩

end SetValuedOperator
