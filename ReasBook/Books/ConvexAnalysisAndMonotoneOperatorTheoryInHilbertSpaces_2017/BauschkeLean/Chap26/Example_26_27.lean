import BauschkeLean.Chap20.Corollary_20_50
import BauschkeLean.Chap23.Example_23_4
import BauschkeLean.Chap26.Remark_26_23
import BauschkeLean.Chap26.Theorem_26_17

open Filter
open ERealFunction
open scoped InnerProductSpace Pointwise Set SetValuedOperator Topology

universe u

namespace SetValuedOperator

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {B : SetValuedOperator H H} {Bf : H → H} {C : Set H}
variable (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "VI" =>
  variationalInequalityProblem (ι[C]) Bf.toSetValuedOperator

/- Source/core/bridge triage:
- `source-facing`: Example 26.27 specializes the projected forward-backward-forward recursion to
  the variational inequality over `C`.
- `core/canonical`: the owner abstractions are the normal cone `N[C]`, the solution set
  `C ∩ (N[C] + B).zeros`, the projection resolvent `P[C] = J[N[C]]`, and the Chapter 26 Tseng
  convergence theorems from `Theorem_26_17`.
- `bridge/view`: the only file-local bridge needed is the identification of the source solution
  set `variationalInequalityProblem (ι[C]) Bf.toSetValuedOperator` with
  `C ∩ (N[C] + B).zeros` under the single-valued-on-`C` hypothesis.

Primitive data: the normal-cone owner `N[C]`, the original operator `B`, and the representative
agreement `hB_eq` on `C`.
Derived API: the variational-inequality solution set, the projection-resolvent realization, and
the three convergence statements obtained by direct specialization of `Theorem_26_17`.

The source cone regularity hypothesis on `C - B.dom` is redundant here: maximal monotonicity of
`N[C] + B` already follows from the canonical normal-cone addition theorem using the Lipschitz,
hence continuous, single-valued representative on `C`. -/

omit hC_closed hC_convex in
omit [CompleteSpace H] in
private theorem normalCone_dom_subset :
    SetValuedOperator.dom (N[C] : SetValuedOperator H H) ⊆ C := by
  intro x hxdom
  by_contra hxC
  rcases (SetValuedOperator.mem_dom_iff (N[C]) x).1 hxdom with ⟨u, hu⟩
  rw [Set.normalCone_of_not_mem hxC] at hu
  simp at hu

omit [CompleteSpace H] in
private theorem mem_set_of_mem_zeros_normalCone_add {x : H}
    (hx : x ∈ (N[C] + B).zeros) :
    x ∈ C := by
  rw [SetValuedOperator.mem_zeros_iff] at hx
  rcases Set.mem_add.mp hx with ⟨u, hu, _, _, _⟩
  exact normalCone_dom_subset ((SetValuedOperator.mem_dom_iff (N[C]) x).2 ⟨u, hu⟩)

omit [CompleteSpace H] in
/-- The variational inequality over `C` with representative `Bf` is exactly the constrained zero
set `C ∩ zer (N[C] + B)`, where `B` is the original set-valued operator agreeing with
`Bf.toSetValuedOperatorOn C` on `C`. -/
theorem variationalInequalityProblem_indicator_eq_inter_zeros_normalCone_add
    (hC_nonempty : C.Nonempty)
    (hB_eq : ∀ x ∈ C, B x = Bf.toSetValuedOperatorOn C x) :
    VI = C ∩ (N[C] + B).zeros := by
  have hsum_eq : N[C] + B = N[C] + Bf.toSetValuedOperator := by
    funext x
    by_cases hx : x ∈ C
    · simpa [Function.toSetValuedOperator_apply, Function.toSetValuedOperatorOn, hx] using
        congrArg (fun S : Set H ↦ N[C] x + S) (hB_eq x hx)
    · simp [Set.normalCone_of_not_mem hx]
  have hVI_eq : VI = (N[C] + B).zeros := by
    calc
      VI = ((∂ ι[C]) + Bf.toSetValuedOperator).zeros := by
        simpa using variationalInequalityProblem_eq_zeros_subdifferential_add
          Bf.toSetValuedOperator
      _ = (N[C] + Bf.toSetValuedOperator).zeros := by
        rw [subdifferential_setIndicator_eq_normalCone C hC_nonempty]
      _ = (N[C] + B).zeros := by
        rw [hsum_eq]
  ext x
  constructor
  · intro hx
    have hxzero : x ∈ (N[C] + B).zeros := by
      simpa [hVI_eq] using hx
    exact ⟨mem_set_of_mem_zeros_normalCone_add hxzero, hxzero⟩
  · intro hx
    simpa [hVI_eq] using hx.2

omit [CompleteSpace H] in
private theorem representative_lipschitzOn_union_normalCone_dom
    (β : PosReal)
    (hB_lipschitz : LipschitzOnWith (Real.toNNReal (β : ℝ)) Bf C) :
    LipschitzOnWith (Real.toNNReal (β : ℝ)) Bf
      (C ∪ SetValuedOperator.dom (N[C] : SetValuedOperator H H)) := by
  simpa [Set.union_eq_left.mpr normalCone_dom_subset] using hB_lipschitz

private theorem normalCone_add_isMaximallyMonotone
    (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hB_max : Maximal IsMonotone B)
    (hB_eq : ∀ x ∈ C, B x = Bf.toSetValuedOperatorOn C x)
    (β : PosReal)
    (hB_lipschitz : LipschitzOnWith (Real.toNNReal (β : ℝ)) Bf C) :
    Maximal IsMonotone (N[C] + B) := by
  let T : C → H := fun x ↦ Bf x
  have hT_cont : Continuous T := by
    have hcont : ContinuousOn Bf C := hB_lipschitz.continuousOn
    rw [continuousOn_iff_continuous_restrict] at hcont
    simpa [T] using hcont
  have hB_singleton : ∀ x, ∀ hx : x ∈ C, B x = ({T ⟨x, hx⟩} : Set H) := by
    intro x hx
    simpa [T, Function.toSetValuedOperatorOn, hx] using hB_eq x hx
  have hsum_max : Maximal IsMonotone (B + N[C]) := by
    exact add_normalCone_isMaximallyMonotone_of_monotone_of_eq_singleton_continuous
      hC_nonempty hC_closed hC_convex B (SetValuedOperator.Maximal.isMonotone hB_max) T
      hB_singleton hT_cont
  simpa [add_comm] using hsum_max

/-- Example 26.27 (1): let `C` be a nonempty closed convex subset of a real Hilbert space, let
`β ∈ ℝ_{++}`, and let `B : H → 2^H` be maximally monotone, single-valued on `C` with
representative `Bf`, and `β`-Lipschitz on `C`. If the variational inequality
`variationalInequalityProblem (ι[C]) Bf.toSetValuedOperator` has a solution, and if the
projected forward-backward-forward recursion `(26.90)` is started at `x₀ ∈ C` with
`0 < γ < 1 / β`, then `(x_n - z_n)` converges strongly to `0`. -/
theorem projectedForwardBackwardForward_sub_tendsto_zero
    (hB_max : Maximal IsMonotone B) (hB_eq : ∀ x ∈ C, B x = Bf.toSetValuedOperatorOn C x)
    (β : PosReal) (hB_lipschitz : LipschitzOnWith (Real.toNNReal (β : ℝ)) Bf C)
    (hsol : Set.Nonempty (variationalInequalityProblem (ι[C]) Bf.toSetValuedOperator))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < (β : ℝ)⁻¹)
    (x0 : C) :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    Tendsto
      (fun n ↦
        projectedForwardBackwardForwardIteration (P[C, hC]) Bf C hC γ x0 n -
          projectedForwardBackwardForwardResolventSequence (P[C, hC]) Bf C hC γ x0 n)
      atTop (𝓝 (0 : H)) := by
  let hC : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
  let β' : PosReal := ⟨(β : ℝ)⁻¹, inv_pos.mpr β.2⟩
  have hC_nonempty : C.Nonempty := ⟨(x0 : H), x0.2⟩
  have hC_sub : C ⊆ C := fun _ hx ↦ hx
  have hNC_max : Maximal IsMonotone (N[C] : SetValuedOperator H H) :=
    Set.normalCone_isMaximallyMonotone hC_nonempty hC_closed hC_convex
  have hNB_max : Maximal IsMonotone (N[C] + B) :=
    normalCone_add_isMaximallyMonotone hC_nonempty hC_closed hC_convex hB_max hB_eq β
      hB_lipschitz
  have hzero : (C ∩ (N[C] + B).zeros).Nonempty := by
    simpa [variationalInequalityProblem_indicator_eq_inter_zeros_normalCone_add
      hC_nonempty hB_eq] using hsol
  have hB_lipschitz' :
      LipschitzOnWith (Real.toNNReal ((β' : ℝ)⁻¹)) Bf
        (C ∪ SetValuedOperator.dom (N[C] : SetValuedOperator H H)) := by
    simpa [β'] using representative_lipschitzOn_union_normalCone_dom β hB_lipschitz
  have hγ_lt' : (γ : ℝ) < (β' : ℝ) := by
    simpa [β'] using hγ_lt
  have hJγN : (P[C, hC]).toSetValuedOperator = J[((γ : ℝ) • N[C])] := by
    simpa [hC] using
      projectionPoint_toSetValuedOperator_eq_resolvent_smul_normalCone_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex γ
  simpa [hC] using
    tsengAlgorithm_sub_tendsto_zero hNC_max normalCone_dom_subset
      (SetValuedOperator.Maximal.isMonotone hB_max) hB_eq β' hNB_max hC_closed hC_convex
      hC_sub hzero hB_lipschitz' γ hγ_lt' (P[C, hC]) hJγN x0

/-- Example 26.27 (2): under the assumptions of Example 26.27, the sequences `(x_n)` and
`(z_n)` converge weakly to a common solution of the variational inequality
`variationalInequalityProblem (ι[C]) Bf.toSetValuedOperator`. -/
theorem projectedForwardBackwardForward_tendsto_weakly_to_variationalInequalitySolution
    (hB_max : Maximal IsMonotone B) (hB_eq : ∀ x ∈ C, B x = Bf.toSetValuedOperatorOn C x)
    (β : PosReal) (hB_lipschitz : LipschitzOnWith (Real.toNNReal (β : ℝ)) Bf C)
    (hsol : Set.Nonempty (variationalInequalityProblem (ι[C]) Bf.toSetValuedOperator))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < (β : ℝ)⁻¹)
    (x0 : C) :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    ∃ p ∈ VI,
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H
            (projectedForwardBackwardForwardIteration (P[C, hC]) Bf C hC γ x0 n))
        atTop (𝓝 (toWeakSpace ℝ H p)) ∧
      Tendsto
          (fun n ↦
            toWeakSpace ℝ H
              (projectedForwardBackwardForwardResolventSequence (P[C, hC]) Bf C hC γ x0 n))
          atTop (𝓝 (toWeakSpace ℝ H p)) := by
  let hC : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
  let β' : PosReal := ⟨(β : ℝ)⁻¹, inv_pos.mpr β.2⟩
  have hC_nonempty : C.Nonempty := ⟨(x0 : H), x0.2⟩
  have hC_sub : C ⊆ C := fun _ hx ↦ hx
  have hNC_max : Maximal IsMonotone (N[C] : SetValuedOperator H H) :=
    Set.normalCone_isMaximallyMonotone hC_nonempty hC_closed hC_convex
  have hNB_max : Maximal IsMonotone (N[C] + B) :=
    normalCone_add_isMaximallyMonotone hC_nonempty hC_closed hC_convex hB_max hB_eq β
      hB_lipschitz
  have hzero : (C ∩ (N[C] + B).zeros).Nonempty := by
    simpa [variationalInequalityProblem_indicator_eq_inter_zeros_normalCone_add
      hC_nonempty hB_eq] using hsol
  have hB_lipschitz' :
      LipschitzOnWith (Real.toNNReal ((β' : ℝ)⁻¹)) Bf
        (C ∪ SetValuedOperator.dom (N[C] : SetValuedOperator H H)) := by
    simpa [β'] using representative_lipschitzOn_union_normalCone_dom β hB_lipschitz
  have hγ_lt' : (γ : ℝ) < (β' : ℝ) := by
    simpa [β'] using hγ_lt
  have hJγN : (P[C, hC]).toSetValuedOperator = J[((γ : ℝ) • N[C])] := by
    simpa [hC] using
      projectionPoint_toSetValuedOperator_eq_resolvent_smul_normalCone_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex γ
  have hVI_eq :
      VI = C ∩ (N[C] + B).zeros :=
    variationalInequalityProblem_indicator_eq_inter_zeros_normalCone_add hC_nonempty hB_eq
  have htseng :
      ∃ p ∈ C ∩ (N[C] + B).zeros,
        Tendsto
          (fun n ↦
            toWeakSpace ℝ H
              (projectedForwardBackwardForwardIteration (P[C, hC]) Bf C hC γ x0 n))
          atTop (𝓝 (toWeakSpace ℝ H p)) ∧
          Tendsto
            (fun n ↦
              toWeakSpace ℝ H
                (projectedForwardBackwardForwardResolventSequence
                  (P[C, hC]) Bf C hC γ x0 n))
            atTop (𝓝 (toWeakSpace ℝ H p)) := by
    simpa [hC] using
      (show ∃ p ∈ C ∩ (N[C] + B).zeros,
          Tendsto
            (fun n ↦
              toWeakSpace ℝ H
                (projectedForwardBackwardForwardIteration (P[C, hC]) Bf C hC γ x0 n))
            atTop (𝓝 (toWeakSpace ℝ H p)) ∧
            Tendsto
              (fun n ↦
                toWeakSpace ℝ H
                  (projectedForwardBackwardForwardResolventSequence
                    (P[C, hC]) Bf C hC γ x0 n))
              atTop (𝓝 (toWeakSpace ℝ H p)) from
        tsengAlgorithm_tendsto_weakly hNC_max normalCone_dom_subset
          (SetValuedOperator.Maximal.isMonotone hB_max) hB_eq β' hNB_max hC_closed
          hC_convex hC_sub hzero hB_lipschitz' γ hγ_lt' (P[C, hC]) hJγN x0)
  rcases htseng with
    ⟨p, hp, hxp, hzp⟩
  refine ⟨p, ?_, hxp, hzp⟩
  simpa [hVI_eq] using hp

/-- Example 26.27 (3): if, in addition, `B` is uniformly monotone on every nonempty bounded
subset of `C`, then `(x_n)` and `(z_n)` converge strongly to the unique solution of
`variationalInequalityProblem (ι[C]) Bf.toSetValuedOperator`. -/
theorem
    projectedForwardBackwardForward_tendsto_to_unique_solution_of_uniformMonotonicity
    (hB_max : Maximal IsMonotone B) (hB_eq : ∀ x ∈ C, B x = Bf.toSetValuedOperatorOn C x)
    (β : PosReal) (hB_lipschitz : LipschitzOnWith (Real.toNNReal (β : ℝ)) Bf C)
    (hsol : Set.Nonempty (variationalInequalityProblem (ι[C]) Bf.toSetValuedOperator))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < (β : ℝ)⁻¹)
    (hUniform :
      ∀ S : Set H, S.Nonempty → Bornology.IsBounded S → S ⊆ C → B.IsUniformlyMonotoneOn S)
    (x0 : C) :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    ∃ p ∈ VI,
      Tendsto
        (projectedForwardBackwardForwardIteration (P[C, hC]) Bf C hC γ x0)
        atTop (𝓝 p) ∧
        Tendsto
          (projectedForwardBackwardForwardResolventSequence (P[C, hC]) Bf C hC γ x0)
          atTop (𝓝 p) ∧
        ∀ q, q ∈ VI → q = p := by
  let hC : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
  let β' : PosReal := ⟨(β : ℝ)⁻¹, inv_pos.mpr β.2⟩
  have hC_nonempty : C.Nonempty := ⟨(x0 : H), x0.2⟩
  have hC_sub : C ⊆ C := fun _ hx ↦ hx
  have hNC_max : Maximal IsMonotone (N[C] : SetValuedOperator H H) :=
    Set.normalCone_isMaximallyMonotone hC_nonempty hC_closed hC_convex
  have hNC_dom : SetValuedOperator.dom (N[C] : SetValuedOperator H H) ⊆ C :=
    normalCone_dom_subset
  have hNB_max : Maximal IsMonotone (N[C] + B) :=
    normalCone_add_isMaximallyMonotone hC_nonempty hC_closed hC_convex hB_max hB_eq β
      hB_lipschitz
  have hzero : (C ∩ (N[C] + B).zeros).Nonempty := by
    simpa [variationalInequalityProblem_indicator_eq_inter_zeros_normalCone_add
      hC_nonempty hB_eq] using hsol
  have hB_lipschitz' :
      LipschitzOnWith (Real.toNNReal ((β' : ℝ)⁻¹)) Bf
        (C ∪ SetValuedOperator.dom (N[C] : SetValuedOperator H H)) := by
    simpa [β'] using representative_lipschitzOn_union_normalCone_dom β hB_lipschitz
  have hγ_lt' : (γ : ℝ) < (β' : ℝ) := by
    simpa [β'] using hγ_lt
  have hJγN : (P[C, hC]).toSetValuedOperator = J[((γ : ℝ) • N[C])] := by
    simpa [hC] using
      projectionPoint_toSetValuedOperator_eq_resolvent_smul_normalCone_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex γ
  have hVI_eq :
      VI = C ∩ (N[C] + B).zeros :=
    variationalInequalityProblem_indicator_eq_inter_zeros_normalCone_add hC_nonempty hB_eq
  have hUniform' :
      ∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S →
          S ⊆ SetValuedOperator.dom (N[C] : SetValuedOperator H H) →
            B.IsUniformlyMonotoneOn S := by
    intro S hS_nonempty hS_bounded hS_dom
    exact hUniform S hS_nonempty hS_bounded (fun x hx ↦ hNC_dom (hS_dom hx))
  have htseng :
      ∃ p ∈ C ∩ (N[C] + B).zeros,
        Tendsto
          (projectedForwardBackwardForwardIteration (P[C, hC]) Bf C hC γ x0)
          atTop (𝓝 p) ∧
          Tendsto
            (projectedForwardBackwardForwardResolventSequence (P[C, hC]) Bf C hC γ x0)
            atTop (𝓝 p) ∧
          C ∩ (N[C] + B).zeros = ({p} : Set H) := by
    simpa [hC] using
      (show ∃ p ∈ C ∩ (N[C] + B).zeros,
          Tendsto
            (projectedForwardBackwardForwardIteration (P[C, hC]) Bf C hC γ x0)
            atTop (𝓝 p) ∧
            Tendsto
            (projectedForwardBackwardForwardResolventSequence
                (P[C, hC]) Bf C hC γ x0)
              atTop (𝓝 p) ∧
            C ∩ (N[C] + B).zeros = ({p} : Set H) from
        tsengAlgorithm_tendsto_of_uniformlyMonotoneOnEveryBoundedSubset
          hNC_max normalCone_dom_subset (SetValuedOperator.Maximal.isMonotone hB_max) hB_eq
          β' hNB_max hC_closed hC_convex hC_sub hzero hB_lipschitz' γ hγ_lt' (P[C, hC])
          hJγN x0 (Or.inr hUniform'))
  rcases htseng with
    ⟨p, hp, hxp, hzp, hsingle⟩
  refine ⟨p, ?_, hxp, hzp, ?_⟩
  · simpa [hVI_eq] using hp
  · intro q hq
    have hqsingle : q ∈ ({p} : Set H) := by
      simpa [hsingle] using (show q ∈ C ∩ (N[C] + B).zeros by simpa [hVI_eq] using hq)
    simpa using hqsingle

end

end SetValuedOperator
