import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap04.Definition_4_10
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap20.Definition_20_1
import BauschkeLean.Chap26.ForwardBackwardSplitting
import BauschkeLean.Chap29.Definition_29_24
import BauschkeLean.Chap30.Remark_30_14
import BauschkeLean.Chap30.UnitIndexing

open Filter
open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace SetValuedOperator

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The averaged forward-backward self-map
`T = (1 / 2) (Id + J_{γA} ∘ (Id - γ B))` used in the proof of Corollary 30.12. -/
abbrev haugazeauForwardBackwardOperator
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (γ : PosReal) : H → H :=
  halfIdAddOperatorFamily (fun _ : Unit ↦ forwardBackwardSplittingOperator A hA B γ) ()

/-- Applying `haugazeauForwardBackwardOperator` to `x` yields the midpoint
`(1 / 2) (x + J_{γA}(x - γ Bx))`. -/
theorem haugazeauForwardBackwardOperator_apply
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (γ : PosReal) (x : H) :
    haugazeauForwardBackwardOperator A hA B γ x =
      (1 / 2 : ℝ) • (x + resolventMap A hA γ (x - (γ : ℝ) • B x)) := by
  simp [haugazeauForwardBackwardOperator, halfIdAddOperatorFamily,
    forwardBackwardSplittingOperator_apply, smul_add]

private theorem forwardBackwardSplittingOperator_lipschitzWith_one_of_cocoercive
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (β γ : PosReal)
    (hB : CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x ↦ B x))
    (hγ : (γ : ℝ) < 2 * (β : ℝ)) :
    LipschitzWith 1 (forwardBackwardSplittingOperator A hA B γ) := by
  rcases (averaged_iff_averagedWith_univ.mp
    (forwardBackwardSplittingOperator_averaged_of_cocoercive A hA B β γ hB hγ)) with
    ⟨hα, R, hR, hT_eq⟩
  have hα_nonneg : 0 ≤
      2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ)) := hα.1.le
  have hdenom_pos : 0 < 4 * (β : ℝ) - (γ : ℝ) := by
    nlinarith [β.2, hγ]
  have h_one_sub_nonneg :
      0 ≤ 1 - 2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ)) := sub_nonneg.mpr hα.2.le
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hRxy : ‖R ⟨x, by simp⟩ - R ⟨y, by simp⟩‖ ≤ ‖x - y‖ := by
    simpa [Subtype.dist_eq, dist_eq_norm] using hR.dist_le_mul ⟨x, by simp⟩ ⟨y, by simp⟩
  have hxy :
      forwardBackwardSplittingOperator A hA B γ x -
          forwardBackwardSplittingOperator A hA B γ y =
        (1 -
            2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) • (x - y) +
          (2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) •
            (R ⟨x, by simp⟩ - R ⟨y, by simp⟩) := by
    calc
      forwardBackwardSplittingOperator A hA B γ x -
          forwardBackwardSplittingOperator A hA B γ y =
            ((1 - 2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) • x +
                (2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) • R ⟨x, by simp⟩) -
              ((1 - 2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) • y +
                (2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) • R ⟨y, by simp⟩) := by
              rw [show forwardBackwardSplittingOperator A hA B γ x =
                  ((1 - 2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) • x +
                    (2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) • R ⟨x, by simp⟩) by
                    simpa using congrArg (fun f ↦ f ⟨x, by simp⟩) hT_eq]
              rw [show forwardBackwardSplittingOperator A hA B γ y =
                  ((1 - 2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) • y +
                    (2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) • R ⟨y, by simp⟩) by
                    simpa using congrArg (fun f ↦ f ⟨y, by simp⟩) hT_eq]
      _ = (1 - 2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) • (x - y) +
            (2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) •
              (R ⟨x, by simp⟩ - R ⟨y, by simp⟩) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  simpa [dist_eq_norm, one_mul] using
    calc
      ‖forwardBackwardSplittingOperator A hA B γ x -
          forwardBackwardSplittingOperator A hA B γ y‖ =
            ‖(1 - 2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) • (x - y) +
                (2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) •
                  (R ⟨x, by simp⟩ - R ⟨y, by simp⟩)‖ := by
              rw [hxy]
      _ ≤ ‖(1 - 2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) • (x - y)‖ +
            ‖(2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) •
                (R ⟨x, by simp⟩ - R ⟨y, by simp⟩)‖ := norm_add_le _ _
      _ = (1 - 2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) * ‖x - y‖ +
            (2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) *
              ‖R ⟨x, by simp⟩ - R ⟨y, by simp⟩‖ := by
            rw [norm_smul, norm_smul]
            rw [Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h_one_sub_nonneg, abs_of_nonneg hα_nonneg]
      _ ≤ (1 - 2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) * ‖x - y‖ +
            (2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ))) * ‖x - y‖ := by
            nlinarith [hRxy, norm_nonneg (x - y)]
      _ = ‖x - y‖ := by ring

private theorem commonFixedPointSet_forwardBackwardSplittingOperator_eq_zeroSet
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (γ : PosReal) :
    commonFixedPointSet (fun _ : Unit ↦ forwardBackwardSplittingOperator A hA B γ) =
      (A + B.toSetValuedOperator).zeros := by
  rw [commonFixedPointSet_unit_eq_fixedPoints]
  simpa [primal_inclusion_solution_set] using
    (primal_inclusion_solution_set_eq_fixedPoints_forwardBackwardSplittingOperator
      A hA B γ).symm

/-- The Haugazeau orbit from Corollary 30.12, realized as the canonical Chapter 30 single-map
specialization of `haugazeauIteration`. -/
abbrev haugazeauForwardBackwardOrbit
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (γ : PosReal) (x0 : H) : ℕ → H :=
  haugazeauIteration
    (fun _ : Unit ↦ haugazeauForwardBackwardOperator A hA B γ)
    (fun _ : ℕ ↦ ()) x0

/-- The forward sequence `y_n = x_n - γ B x_n` attached to the Haugazeau forward-backward
orbit. -/
def haugazeauForwardBackwardAuxiliarySequence
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (γ : PosReal) (x0 : H) : ℕ → H :=
  fun n ↦
    haugazeauForwardBackwardOrbit A hA B γ x0 n -
      (γ : ℝ) • B (haugazeauForwardBackwardOrbit A hA B γ x0 n)

/-- The midpoint sequence `z_n = (1 / 2) (x_n + J_{γA} y_n)` attached to the Haugazeau
forward-backward orbit. -/
def haugazeauForwardBackwardMidpointSequence
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (γ : PosReal) (x0 : H) : ℕ → H :=
  fun n ↦
    haugazeauForwardBackwardOperator A hA B γ
      (haugazeauForwardBackwardOrbit A hA B γ x0 n)

/-- The Haugazeau forward-backward orbit starts at the prescribed point. -/
@[simp] theorem haugazeauForwardBackwardOrbit_zero
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (γ : PosReal) (x0 : H) :
    haugazeauForwardBackwardOrbit A hA B γ x0 0 = x0 := by
  simp [haugazeauForwardBackwardOrbit]

/-- The forward sequence is given by `y_n = x_n - γ B x_n`. -/
theorem haugazeauForwardBackwardAuxiliarySequence_eq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (γ : PosReal) (x0 : H) (n : ℕ) :
    haugazeauForwardBackwardAuxiliarySequence A hA B γ x0 n =
      haugazeauForwardBackwardOrbit A hA B γ x0 n -
        (γ : ℝ) • B (haugazeauForwardBackwardOrbit A hA B γ x0 n) := by
  rfl

/-- The midpoint sequence is given by `z_n = (1 / 2) (x_n + J_{γA} y_n)`. -/
theorem haugazeauForwardBackwardMidpointSequence_eq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (γ : PosReal) (x0 : H) (n : ℕ) :
    haugazeauForwardBackwardMidpointSequence A hA B γ x0 n =
      (1 / 2 : ℝ) •
        (haugazeauForwardBackwardOrbit A hA B γ x0 n +
          resolventMap A hA γ (haugazeauForwardBackwardAuxiliarySequence A hA B γ x0 n)) := by
  simpa
      [haugazeauForwardBackwardMidpointSequence, haugazeauForwardBackwardAuxiliarySequence_eq] using
    haugazeauForwardBackwardOperator_apply A hA B γ
      (haugazeauForwardBackwardOrbit A hA B γ x0 n)

/-- The Haugazeau forward-backward orbit satisfies the source recursion
`x_{n+1} = Q(x_0, x_n, z_n)`. -/
@[simp] theorem haugazeauForwardBackwardOrbit_succ
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (γ : PosReal) (x0 : H) (n : ℕ) :
    haugazeauForwardBackwardOrbit A hA B γ x0 (n + 1) =
      specialPolyhedronQ x0 (haugazeauForwardBackwardOrbit A hA B γ x0 n)
        (haugazeauForwardBackwardMidpointSequence A hA B γ x0 n) := by
  simp [haugazeauForwardBackwardOrbit, haugazeauForwardBackwardMidpointSequence]

/-- The Chapter 30 common fixed-point set of the constant family with value
`haugazeauForwardBackwardOperator A hA B γ` is the zero set `zer (A + B)`. -/
@[simp] theorem commonFixedPointSet_haugazeauForwardBackwardOperator_eq_zeroSet
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (γ : PosReal) :
    commonFixedPointSet (fun _ : Unit ↦ haugazeauForwardBackwardOperator A hA B γ) =
      (A + B.toSetValuedOperator).zeros := by
  calc
    commonFixedPointSet (fun _ : Unit ↦ haugazeauForwardBackwardOperator A hA B γ) =
        commonFixedPointSet (fun _ : Unit ↦ forwardBackwardSplittingOperator A hA B γ) := by
          simpa [haugazeauForwardBackwardOperator] using
            (iInter_fixedPoints_halfIdAddOperatorFamily_eq
              (fun _ : Unit ↦ forwardBackwardSplittingOperator A hA B γ))
    _ = (A + B.toSetValuedOperator).zeros :=
      commonFixedPointSet_forwardBackwardSplittingOperator_eq_zeroSet A hA B γ

/-- The fixed-point set of the averaged forward-backward operator is the zero set
`zer (A + B)`. -/
theorem haugazeauForwardBackwardOperator_fixedPoints_eq_zeroSet
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (γ : PosReal) :
    Function.fixedPoints (haugazeauForwardBackwardOperator A hA B γ) =
      (A + B.toSetValuedOperator).zeros := by
  rw [← commonFixedPointSet_unit_eq_fixedPoints]
  exact commonFixedPointSet_haugazeauForwardBackwardOperator_eq_zeroSet A hA B γ

/-- Under the cocoercivity hypotheses of Corollary 30.12, the averaged forward-backward operator
is firmly nonexpansive. -/
theorem haugazeauForwardBackwardOperator_firmlyNonexpansive
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (β γ : PosReal)
    (hB : CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x ↦ B x))
    (hγ : (γ : ℝ) < 2 * (β : ℝ)) :
    FirmlyNonexpansiveOn (Set.univ : Set H) (haugazeauForwardBackwardOperator A hA B γ) := by
  let R : Unit → H → H := fun _ ↦ forwardBackwardSplittingOperator A hA B γ
  have hR : ∀ i : Unit, LipschitzWith 1 (R i) := by
    intro i
    cases i
    simpa [R] using
      forwardBackwardSplittingOperator_lipschitzWith_one_of_cocoercive A hA B β γ hB hγ
  simpa [R, haugazeauForwardBackwardOperator] using
    (halfIdAddOperatorFamily_firmlyNonexpansive R hR ())

/-- The zero set `zer (A + B)` is Chebyshev under the hypotheses of Corollary 30.12. -/
theorem zeroSet_isChebyshev_of_haugazeauForwardBackward
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (β γ : PosReal)
    (hB : CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x ↦ B x))
    (hγ : (γ : ℝ) < 2 * (β : ℝ))
    (hzero : ((A + B.toSetValuedOperator).zeros).Nonempty) :
    IsChebyshev ((A + B.toSetValuedOperator).zeros) := by
  let R : Unit → H → H := fun _ ↦ forwardBackwardSplittingOperator A hA B γ
  have hR : ∀ i : Unit, LipschitzWith 1 (R i) := by
    intro i
    cases i
    simpa [R] using
      forwardBackwardSplittingOperator_lipschitzWith_one_of_cocoercive A hA B β γ hB hγ
  have hFix_nonempty : (commonFixedPointSet R).Nonempty := by
    rw [commonFixedPointSet_forwardBackwardSplittingOperator_eq_zeroSet A hA B γ]
    exact hzero
  have hChebyshev : IsChebyshev (commonFixedPointSet R) :=
    iInter_fixedPoints_isChebyshev_of_halfIdAddOperatorFamily R hR hFix_nonempty
  rw [commonFixedPointSet_forwardBackwardSplittingOperator_eq_zeroSet A hA B γ] at hChebyshev
  simpa using hChebyshev

/-- Corollary 30.12: let `A : H → 2^H` be maximally monotone, let `β ∈ ℝ_{++}`, let
`B : H → H` be `β`-cocoercive, let `γ ∈ ]0, 2β[`, suppose `zer (A + B) ≠ ∅`, let `x₀ ∈ H`, and
define `(x_n)`, `(y_n)`, and `(z_n)` by
`y_n = x_n - γ B x_n`, `z_n = (1 / 2) (x_n + J_{γA} y_n)`, and
`x_{n+1} = Q(x₀, x_n, z_n)`. Then `x_n` converges strongly to
`P_{zer (A + B)} x₀`. -/
theorem haugazeauForwardBackwardOrbit_tendsto_projection_zeroSet
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (B : H → H) (β γ : PosReal)
    (hB : CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x ↦ B x))
    (hγ : (γ : ℝ) < 2 * (β : ℝ))
    (hzero : ((A + B.toSetValuedOperator).zeros).Nonempty) (x0 : H) :
    Tendsto (haugazeauForwardBackwardOrbit A hA B γ x0) atTop
      (𝓝 (P[(A + B.toSetValuedOperator).zeros,
        zeroSet_isChebyshev_of_haugazeauForwardBackward A hA B β γ hB hγ hzero] x0)) := by
  let R : Unit → H → H := fun _ ↦ forwardBackwardSplittingOperator A hA B γ
  have hR : ∀ i : Unit, LipschitzWith 1 (R i) := by
    intro i
    cases i
    simpa [R] using
      forwardBackwardSplittingOperator_lipschitzWith_one_of_cocoercive A hA B β γ hB hγ
  have hFix_nonempty : (commonFixedPointSet R).Nonempty := by
    rw [commonFixedPointSet_forwardBackwardSplittingOperator_eq_zeroSet A hA B γ]
    exact hzero
  let hCommonCheb :=
    iInter_fixedPoints_isChebyshev_of_halfIdAddOperatorFamily R hR hFix_nonempty
  let hZeroCheb :=
    zeroSet_isChebyshev_of_haugazeauForwardBackward A hA B β γ hB hγ hzero
  have hbest :
      IsBestApproximation x0 ((A + B.toSetValuedOperator).zeros)
        (P[commonFixedPointSet R, hCommonCheb] x0) := by
    exact
      (commonFixedPointSet_forwardBackwardSplittingOperator_eq_zeroSet A hA B γ) ▸
        projectionPoint_isBestApproximation (commonFixedPointSet R) hCommonCheb x0
  have hproj_eq :
      P[commonFixedPointSet R, hCommonCheb] x0 =
        P[(A + B.toSetValuedOperator).zeros, hZeroCheb] x0 := by
    exact
      eq_projectionPoint_of_isBestApproximation ((A + B.toSetValuedOperator).zeros) hZeroCheb
        hbest
  have hlimit :
      Tendsto (haugazeauIteration (halfIdAddOperatorFamily R) (fun _ : ℕ ↦ ()) x0) atTop
        (𝓝 (P[commonFixedPointSet R, hCommonCheb] x0)) := by
    simpa [hCommonCheb] using
      haugazeau_iteration_tendsto_projection_iInter_fixedPoints_of_halfIdAddOperatorFamily
        R hR hFix_nonempty (fun _ : ℕ ↦ ()) visitsEveryIndexInEachBlock_unit x0
  rw [hproj_eq] at hlimit
  simpa [haugazeauForwardBackwardOrbit, haugazeauForwardBackwardOperator,
    halfIdAddOperatorFamily, R, hZeroCheb] using hlimit

end

end SetValuedOperator
