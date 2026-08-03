import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap03.Corollary_3_35
import BauschkeLean.Chap05.Theorem_5_5
import BauschkeLean.Chap04.Proposition_4_16
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.Proposition_20_37
import BauschkeLean.Chap21.Theorem_21_1
import BauschkeLean.Chap20.Proposition_20_49
import BauschkeLean.Chap23.Definition_23_1
import BauschkeLean.Chap23.Proposition_23_2
import BauschkeLean.Chap22.Remark_22_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace SetValuedOperator

/- Source/core/bridge triage:
- `source-facing`: Theorem 26.17 is the projected Tseng forward-backward-forward recursion itself
  together with its convergence properties.
- `core/canonical`: the primitive resolvent owner is `J[((γ : ℝ) • A)]`, with
  `(A + B).zeros`, `P[C, hC]`, `Function.toSetValuedOperatorOn`, and weak convergence via
  `toWeakSpace`.
- `bridge/view`: this file takes an explicit single-valued realizer `JγA : H → H` with
  `JγA.toSetValuedOperator = J[((γ : ℝ) • A)]`, and the source hypothesis that `B` is
  single-valued on `D` is represented by direct agreement of `B` with the canonical
  singleton-valued restriction `Bf.toSetValuedOperatorOn D` on `D`.
Semantic recall: `lean_leansearch` did not return a direct Tseng-splitting owner, so this file
keeps the source recursion itself as the public owner, with the auxiliary sequences derived from
the verified Chapter 3/5/20/22/23 projection, resolvent, and convergence surfaces. -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable section

section TsengAlgorithm

variable {A B : SetValuedOperator H H} {JγA Bf : H → H} {D C : Set H}

/-- The projected forward-backward-forward `x`-orbit from Theorem 26.17, started at
`x₀ ∈ C` and updated by the projected Tseng recursion `(26.90)`. -/
def projectedForwardBackwardForwardIteration
    (JγA : H → H) (Bf : H → H) (C : Set H) (hC : IsChebyshev C)
    (γ : PosReal) (x0 : C) : ℕ → H
  | 0 => x0
  | n + 1 =>
      let xn := projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n
      let yn := xn - (γ : ℝ) • Bf xn
      let zn := JγA yn
      let rn := zn - (γ : ℝ) • Bf zn
      P[C, hC] (xn - yn + rn)

/-- The first forward sequence `yₙ = xₙ - γ Bf xₙ` attached to the projected Tseng orbit. -/
def projectedForwardBackwardForwardPredictorSequence
    (JγA : H → H) (Bf : H → H) (C : Set H) (hC : IsChebyshev C)
    (γ : PosReal) (x0 : C) : ℕ → H :=
  fun n ↦
    projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n -
      (γ : ℝ) • Bf (projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n)

/-- The backward-resolvent sequence `zₙ = J_{γ A} yₙ`, realized by a chosen single-valued
realizer `JγA` of `J[((γ : ℝ) • A)]`. -/
def projectedForwardBackwardForwardResolventSequence
    (JγA : H → H) (Bf : H → H) (C : Set H) (hC : IsChebyshev C)
    (γ : PosReal) (x0 : C) : ℕ → H :=
  fun n ↦
    JγA (projectedForwardBackwardForwardPredictorSequence JγA Bf C hC γ x0 n)

/-- The second forward sequence `rₙ = zₙ - γ Bf zₙ` attached to the projected Tseng orbit. -/
def projectedForwardBackwardForwardCorrectionSequence
    (JγA : H → H) (Bf : H → H) (C : Set H) (hC : IsChebyshev C)
    (γ : PosReal) (x0 : C) : ℕ → H :=
  fun n ↦
    projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n -
      (γ : ℝ) •
        Bf (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n)

omit [CompleteSpace H] in
@[simp] theorem projectedForwardBackwardForwardIteration_zero
    (JγA : H → H) (Bf : H → H) (C : Set H) (hC : IsChebyshev C)
    (γ : PosReal) (x0 : C) :
    projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 0 = x0 := rfl

omit [CompleteSpace H] in
@[simp] theorem projectedForwardBackwardForwardIteration_succ
    (JγA : H → H) (Bf : H → H) (C : Set H) (hC : IsChebyshev C)
    (γ : PosReal) (x0 : C) (n : ℕ) :
    projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 (n + 1) =
      let xn := projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n
      let yn := xn - (γ : ℝ) • Bf xn
      let zn := JγA yn
      let rn := zn - (γ : ℝ) • Bf zn
      P[C, hC] (xn - yn + rn) := rfl

omit [CompleteSpace H] in
@[simp] theorem projectedForwardBackwardForwardPredictorSequence_apply
    (JγA : H → H) (Bf : H → H) (C : Set H) (hC : IsChebyshev C)
    (γ : PosReal) (x0 : C) (n : ℕ) :
    projectedForwardBackwardForwardPredictorSequence JγA Bf C hC γ x0 n =
      projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n -
        (γ : ℝ) • Bf (projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n) := rfl

omit [CompleteSpace H] in
@[simp] theorem projectedForwardBackwardForwardResolventSequence_apply
    (JγA : H → H) (Bf : H → H) (C : Set H) (hC : IsChebyshev C)
    (γ : PosReal) (x0 : C) (n : ℕ) :
    projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n =
      JγA (projectedForwardBackwardForwardPredictorSequence JγA Bf C hC γ x0 n) := rfl

omit [CompleteSpace H] in
@[simp] theorem projectedForwardBackwardForwardCorrectionSequence_apply
    (JγA : H → H) (Bf : H → H) (C : Set H) (hC : IsChebyshev C)
    (γ : PosReal) (x0 : C) (n : ℕ) :
    projectedForwardBackwardForwardCorrectionSequence JγA Bf C hC γ x0 n =
      projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n -
        (γ : ℝ) •
          Bf (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n) := rfl

section TsengConvergence

omit [CompleteSpace H] in
/-- Helper for Theorem 26.17: the projection argument in the Tseng update normalizes to
`zₙ + γ • (Bf xₙ - Bf zₙ)`. -/
theorem tsengProjectionArgument_eq
    (JγA : H → H) (Bf : H → H) (C : Set H) (hC : IsChebyshev C)
    (γ : PosReal) (x0 : C) (n : ℕ) :
    projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 (n + 1) =
      P[C, hC]
        (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n +
          (γ : ℝ) •
            (Bf (projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n) -
              Bf (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n))) := by
  -- Expand the source recursion once and simplify the correction term to its stable normal form.
  simp [projectedForwardBackwardForwardIteration_succ,
    projectedForwardBackwardForwardResolventSequence_apply,
    projectedForwardBackwardForwardPredictorSequence_apply, sub_eq_add_neg, add_left_comm,
    smul_add, smul_neg]

omit [CompleteSpace H] in
/-- Helper for Theorem 26.17: every Tseng iterate stays in `C`, and every resolvent iterate lies
in `A.dom ⊆ D`. -/
theorem tsengOrbitMemCAndResolventMemDom
    {A : SetValuedOperator H H} {JγA Bf : H → H} {D C : Set H}
    (hA_dom : A.dom ⊆ D) (hC_sub : C ⊆ D)
    (hC : IsChebyshev C) (γ : PosReal)
    (hJγA : JγA.toSetValuedOperator = J[((γ : ℝ) • A)]) (x0 : C) :
    ∀ n,
      projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n ∈ C ∧
        projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n ∈ A.dom ∧
        projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n ∈ D ∧
        projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n ∈ D := by
  intro n
  induction n with
  | zero =>
      have hz_mem :
          projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 0 ∈
            J[((γ : ℝ) • A)]
              (projectedForwardBackwardForwardPredictorSequence JγA Bf C hC γ x0 0) := by
        rw [← hJγA, Function.toSetValuedOperator_apply]
        simp [projectedForwardBackwardForwardResolventSequence_apply]
      have hz_dom :
          projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 0 ∈ A.dom := by
        rw [← range_resolvent_smul_eq_dom A γ, SetValuedOperator.mem_range_iff]
        let y0 := projectedForwardBackwardForwardPredictorSequence JγA Bf C hC γ x0 0
        exact ⟨y0, hz_mem⟩
      -- The base point starts in `C`, and the first resolvent point already lies in `A.dom`.
      exact ⟨x0.2, hz_dom, hC_sub x0.2, hA_dom hz_dom⟩
  | succ n ih =>
      rcases ih with ⟨hxnC, _, _, _⟩
      have hxn1C :
          projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 (n + 1) ∈ C := by
        -- Projecting onto `C` keeps the orbit inside `C`.
        rw [tsengProjectionArgument_eq]
        exact
          projectionPoint_mem C hC
            (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n +
              (γ : ℝ) •
                (Bf (projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n) -
                  Bf (projectedForwardBackwardForwardResolventSequence
                    JγA Bf C hC γ x0 n)))
      have hzn1_mem :
          projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 (n + 1) ∈
            J[((γ : ℝ) • A)]
              (projectedForwardBackwardForwardPredictorSequence JγA Bf C hC γ x0 (n + 1)) := by
        rw [← hJγA, Function.toSetValuedOperator_apply]
        simp [projectedForwardBackwardForwardResolventSequence_apply]
      have hzn1_dom :
          projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 (n + 1) ∈ A.dom := by
        rw [← range_resolvent_smul_eq_dom A γ, SetValuedOperator.mem_range_iff]
        let yn1 := projectedForwardBackwardForwardPredictorSequence JγA Bf C hC γ x0 (n + 1)
        exact ⟨yn1, hzn1_mem⟩
      -- The same domain argument works at every step because the resolvent realizer is global.
      exact ⟨hxn1C, hzn1_dom, hC_sub hxn1C, hA_dom hzn1_dom⟩

omit [CompleteSpace H] in
/-- Helper for Theorem 26.17: each resolvent point yields the canonical graph element
`(zₙ, γ⁻¹ • (yₙ - zₙ)) ∈ gra A`. -/
theorem tsengResolventSequence_mem_graph
    {A : SetValuedOperator H H} {JγA Bf : H → H} {C : Set H}
    (hC : IsChebyshev C) (γ : PosReal)
    (hJγA : JγA.toSetValuedOperator = J[((γ : ℝ) • A)]) (x0 : C) (n : ℕ) :
    (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n,
      (γ : ℝ)⁻¹ •
        (projectedForwardBackwardForwardPredictorSequence JγA Bf C hC γ x0 n -
          projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n)) ∈ gra A := by
  have hz_mem :
      projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n ∈
        J[((γ : ℝ) • A)]
          (projectedForwardBackwardForwardPredictorSequence JγA Bf C hC γ x0 n) := by
    rw [← hJγA, Function.toSetValuedOperator_apply]
    simp [projectedForwardBackwardForwardResolventSequence_apply]
  -- Convert the resolvent-membership statement into the canonical graph statement for `A`.
  simpa [mem_graph] using
    (mem_resolvent_smul_iff_mem_graph A γ
      (projectedForwardBackwardForwardPredictorSequence JγA Bf C hC γ x0 n)
      (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n)).1 hz_mem

omit [CompleteSpace H] in
/-- Helper for Theorem 26.17: the auxiliary vector
`γ⁻¹ • (xₙ - zₙ) + (Bf zₙ - Bf xₙ)` belongs to `(A + B) zₙ`. -/
theorem tsengAuxiliaryVector_mem_add
    {A B : SetValuedOperator H H} {JγA Bf : H → H} {D C : Set H}
    (hA_dom : A.dom ⊆ D) (hC_sub : C ⊆ D)
    (hB_eq : ∀ x ∈ D, B x = Bf.toSetValuedOperatorOn D x)
    (hC : IsChebyshev C) (γ : PosReal)
    (hJγA : JγA.toSetValuedOperator = J[((γ : ℝ) • A)]) (x0 : C) (n : ℕ) :
    (γ : ℝ)⁻¹ •
        (projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n -
          projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n) +
      (Bf (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n) -
        Bf (projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n)) ∈
      (A + B) (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n) := by
  let x := projectedForwardBackwardForwardIteration JγA Bf C hC γ x0
  let y := projectedForwardBackwardForwardPredictorSequence JγA Bf C hC γ x0
  let z := projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0
  have hz_graph :
      (z n, (γ : ℝ)⁻¹ • (y n - z n)) ∈ gra A := by
    simpa [x, y, z] using tsengResolventSequence_mem_graph (A := A) (Bf := Bf)
      (JγA := JγA) (C := C) hC γ hJγA x0 n
  have hAz :
      (γ : ℝ)⁻¹ • (y n - z n) ∈ A (z n) := by
    simpa [mem_graph] using hz_graph
  have hzD : z n ∈ D := by
    exact (tsengOrbitMemCAndResolventMemDom (A := A) (JγA := JγA) (Bf := Bf)
      (D := D) (C := C) hA_dom hC_sub hC γ hJγA x0 n).2.2.2
  have hBz :
      Bf (z n) ∈ B (z n) := by
    -- The single-valued representative identifies the `B`-fiber at `zₙ` with a singleton.
    have hBz' : Bf (z n) ∈ Bf.toSetValuedOperatorOn D (z n) := by
      simp [Function.toSetValuedOperatorOn, hzD]
    rw [hB_eq (z n) hzD]
    exact hBz'
  have hsum :
      (γ : ℝ)⁻¹ • (y n - z n) + Bf (z n) =
        (γ : ℝ)⁻¹ • (x n - z n) + (Bf (z n) - Bf (x n)) := by
    -- Expand `yₙ = xₙ - γ • Bf xₙ` and collect the residual terms.
    simp [x, y, z, projectedForwardBackwardForwardPredictorSequence_apply, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc, smul_add, smul_neg, smul_smul, γ.2.ne']
  -- Assemble the graph element of `A` and the singleton `B`-fiber into a point of `A + B`.
  exact Set.mem_add.2 ⟨(γ : ℝ)⁻¹ • (y n - z n), hAz, Bf (z n), hBz, hsum⟩

omit [CompleteSpace H] [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Theorem 26.17: on the single-valued region `D`, the representative `Bf x`
belongs to the `B`-fiber at `x`. -/
theorem tsengRepresentative_mem
    {B : SetValuedOperator H H} {Bf : H → H} {D : Set H}
    (hB_eq : ∀ x ∈ D, B x = Bf.toSetValuedOperatorOn D x)
    {x : H} (hx : x ∈ D) :
    Bf x ∈ B x := by
  -- Rewrite the `B`-fiber to its singleton representative on `D`.
  rw [hB_eq x hx]
  simp [Function.toSetValuedOperatorOn, hx]

omit [CompleteSpace H] [InnerProductSpace ℝ H] in
/-- Helper for Theorem 26.17: a zero of `A + B` in `D` yields the canonical `A`-fiber witness
`-Bf x`. -/
theorem tsengNegRepresentative_mem_left_of_mem_zero
    {A B : SetValuedOperator H H} {Bf : H → H} {D : Set H}
    (hB_eq : ∀ x ∈ D, B x = Bf.toSetValuedOperatorOn D x)
    {x : H} (hxD : x ∈ D) (hx_zero : x ∈ (A + B).zeros) :
    -Bf x ∈ A x := by
  have hx_zero_mem : (0 : H) ∈ (A + B) x := by
    simpa using hx_zero
  rcases Set.mem_add.1 hx_zero_mem with ⟨a, ha, b, hb, hab⟩
  have hb_eq : b = Bf x := by
    rw [hB_eq x hxD] at hb
    simpa [Function.toSetValuedOperatorOn, hxD] using hb
  have ha_eq : a = -Bf x := by
    rw [hb_eq] at hab
    exact eq_neg_of_add_eq_zero_left hab
  -- Rewriting the chosen decomposition against the singleton `B`-fiber isolates the `A` witness.
  simpa [ha_eq] using ha

omit [CompleteSpace H] in
/-- Helper for Theorem 26.17: the auxiliary vector has the stable graph-side normal form
`γ⁻¹ • (yₙ - zₙ) + Bf zₙ`. -/
theorem tsengAuxiliaryVector_eq
    {JγA Bf : H → H} {C : Set H}
    (hC : IsChebyshev C) (γ : PosReal) (x0 : C) (n : ℕ) :
    (γ : ℝ)⁻¹ •
        (projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n -
          projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n) +
      (Bf (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n) -
        Bf (projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n)) =
      (γ : ℝ)⁻¹ •
          (projectedForwardBackwardForwardPredictorSequence JγA Bf C hC γ x0 n -
            projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n) +
        Bf (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n) := by
  -- Expand `yₙ = xₙ - γ • Bf xₙ` once and collect the residual terms into the graph-side form.
  simp [projectedForwardBackwardForwardPredictorSequence_apply, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc, smul_add, smul_neg, smul_smul, γ.2.ne']

omit [CompleteSpace H] in
/-- Helper for Theorem 26.17: on a bounded orbit, a localized modulus lower bound against a
strongly null auxiliary sequence forces strong convergence to the base point. -/
theorem tendsto_of_inner_ge_modulus_of_bounded_of_tendsto_zero
    {z u : ℕ → H} {p : H} {φ : NNReal → EReal}
    (hz_bounded : Bornology.IsBounded (Set.range z))
    (hu_tendsto : Tendsto u atTop (𝓝 (0 : H)))
    (hφ_mono : Monotone φ)
    (hφ_zero : ∀ r : NNReal, φ r = 0 ↔ r = 0)
    (hineq : ∀ n, φ ‖z n - p‖₊ ≤ (⟪z n - p, u n⟫_ℝ : EReal)) :
    Tendsto z atTop (𝓝 p) := by
  rcases isBounded_iff_forall_norm_le.mp hz_bounded with ⟨R, hR⟩
  let C : ℝ := R + ‖p‖
  have hC : ∀ n, ‖z n - p‖ ≤ C := by
    intro n
    calc
      ‖z n - p‖ ≤ ‖z n‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ R + ‖p‖ := add_le_add (hR _ (Set.mem_range_self n)) le_rfl
      _ = C := rfl
  have hmul : Tendsto (fun n ↦ C * ‖u n‖) atTop (𝓝 (0 : ℝ)) := by
    simpa [C] using hu_tendsto.norm.const_mul C
  have hinner_abs :
      Tendsto (fun n ↦ |⟪z n - p, u n⟫_ℝ|) atTop (𝓝 (0 : ℝ)) := by
    refine squeeze_zero'
      (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ hmul
    exact Eventually.of_forall fun n ↦
      le_trans (abs_real_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
  have hinner_tendsto :
      Tendsto (fun n ↦ ⟪z n - p, u n⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp] using hinner_abs
  by_contra hnot
  rw [Metric.tendsto_atTop] at hnot
  push Not at hnot
  rcases hnot with ⟨ε, hε, hbad⟩
  have hfreq : ∃ᶠ n in atTop, ε ≤ dist (z n) p := by
    rw [frequently_atTop]
    intro N
    rcases hbad N with ⟨n, hnN, hndist⟩
    exact ⟨n, hnN, hndist⟩
  rcases extraction_of_frequently_atTop hfreq with ⟨ψ, hψmono, hψdist⟩
  let εNN : NNReal := ⟨ε, hε.le⟩
  have hφ_nonneg : (0 : EReal) ≤ φ εNN := by
    rw [← (hφ_zero 0).2 rfl]
    exact hφ_mono bot_le
  have hφ_ne_zero : φ εNN ≠ 0 := by
    intro hzero
    have hεNN_zero : εNN = 0 := (hφ_zero εNN).1 hzero
    exact (ne_of_gt hε) <| by
      simpa [εNN] using congrArg (fun r : NNReal ↦ (r : ℝ)) hεNN_zero
  have hφ_subseq :
      ∀ n, φ εNN ≤ (⟪z (ψ n) - p, u (ψ n)⟫_ℝ : EReal) := by
    intro n
    have hε_le : εNN ≤ ‖z (ψ n) - p‖₊ := by
      exact_mod_cast (show ε ≤ ‖z (ψ n) - p‖ by simpa [dist_eq_norm] using hψdist n)
    exact le_trans (hφ_mono hε_le) (hineq (ψ n))
  have hφ_top : φ εNN ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hφ_subseq 0)
  have hφ_bot : φ εNN ≠ ⊥ := by
    intro hbot
    rw [hbot] at hφ_nonneg
    simp at hφ_nonneg
  let c : ℝ := (φ εNN).toReal
  have hc_pos : 0 < c := by
    have hφ_pos : (0 : EReal) < φ εNN := lt_of_le_of_ne hφ_nonneg (Ne.symm hφ_ne_zero)
    simpa [c] using EReal.toReal_pos hφ_pos hφ_top
  have hinner_subseq :
      Tendsto (fun n ↦ ⟪z (ψ n) - p, u (ψ n)⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    exact hinner_tendsto.comp hψmono.tendsto_atTop
  have hlow_real : ∀ n, c ≤ ⟪z (ψ n) - p, u (ψ n)⟫_ℝ := by
    intro n
    simpa [c] using
      EReal.toReal_le_toReal (hφ_subseq n) hφ_bot (by simp)
  rcases (Metric.tendsto_atTop.1 hinner_subseq) (c / 2) (by linarith) with ⟨N, hN⟩
  have htail : dist (⟪z (ψ N) - p, u (ψ N)⟫_ℝ) 0 < c / 2 := hN N le_rfl
  have habs_lt : |⟪z (ψ N) - p, u (ψ N)⟫_ℝ| < c / 2 := by
    simpa [dist_eq_norm] using htail
  have habs_ge : c ≤ |⟪z (ψ N) - p, u (ψ N)⟫_ℝ| := by
    exact le_trans (hlow_real N) (le_abs_self _)
  linarith

omit [CompleteSpace H] [InnerProductSpace ℝ H] in
/-- Helper for Theorem 26.17: if a localized modulus at `‖p - q‖` is forced below `0`, then the
comparison points coincide. -/
theorem eq_of_modulus_le_zero
    {p q : H} {φ : NNReal → EReal}
    (hφ_mono : Monotone φ)
    (hφ_zero : ∀ r : NNReal, φ r = 0 ↔ r = 0)
    (hineq : φ ‖p - q‖₊ ≤ 0) :
    p = q := by
  have hφ_nonneg : (0 : EReal) ≤ φ ‖p - q‖₊ := by
    rw [← (hφ_zero 0).2 rfl]
    exact hφ_mono bot_le
  have hφ_eq_zero : φ ‖p - q‖₊ = 0 := le_antisymm hineq hφ_nonneg
  have hdist_zero : ‖p - q‖₊ = 0 := (hφ_zero _).1 hφ_eq_zero
  have hnorm_zero : ‖p - q‖ = 0 := by
    simpa using congrArg (fun r : NNReal ↦ (r : ℝ)) hdist_zero
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)

omit [CompleteSpace H] [InnerProductSpace ℝ H] in
/-- Helper for Theorem 26.17: every comparison point already in `C` is fixed by the metric
projection onto `C`. -/
theorem tsengProjection_eq_self_of_mem
    {C : Set H} (hC : IsChebyshev C) {p : H} (hp : p ∈ C) :
    P[C, hC] p = p := by
  -- The point `p` itself realizes distance `0` to `C`, so uniqueness forces the projection
  -- to be `p`.
  symm
  refine eq_projectionPoint_of_isBestApproximation C hC ?_
  exact ⟨hp, by simp [Metric.infDist_zero_of_mem hp]⟩

omit [CompleteSpace H] in
/-- Helper for Theorem 26.17: the monotonicity part of Tseng's proof yields the cross-term
estimate `(26.70)` against any comparison point `p ∈ C ∩ (A + B).zeros`. -/
theorem tsengCrossTerm_le_sqnormDrop
    {A B : SetValuedOperator H H} {JγA Bf : H → H} {D C : Set H}
    (hA_mono : A.IsMonotone) (hA_dom : A.dom ⊆ D) (hC_sub : C ⊆ D)
    (hB_mono : B.IsMonotone) (hB_eq : ∀ x ∈ D, B x = Bf.toSetValuedOperatorOn D x)
    (hC : IsChebyshev C) (γ : PosReal)
    (hJγA : JγA.toSetValuedOperator = J[((γ : ℝ) • A)]) (x0 : C)
    {p : H} (hp : p ∈ C ∩ (A + B).zeros) (n : ℕ) :
    2 * (γ : ℝ) *
        ⟪projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n - p,
          Bf (projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n) -
            Bf (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n)⟫_ℝ ≤
      ‖projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n - p‖ ^ 2 -
        ‖projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n - p‖ ^ 2 -
          ‖projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n -
            projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n‖ ^ 2 := by
  let x := projectedForwardBackwardForwardIteration JγA Bf C hC γ x0
  let y := projectedForwardBackwardForwardPredictorSequence JγA Bf C hC γ x0
  let z := projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0
  have hz_graph :
      (z n, (γ : ℝ)⁻¹ • (y n - z n)) ∈ gra A := by
    simpa [x, y, z] using tsengResolventSequence_mem_graph (A := A) (Bf := Bf)
      (JγA := JγA) (C := C) hC γ hJγA x0 n
  have hAz :
      (γ : ℝ)⁻¹ • (y n - z n) ∈ A (z n) := by
    simpa [mem_graph] using hz_graph
  have hzD : z n ∈ D := by
    exact (tsengOrbitMemCAndResolventMemDom (A := A) (JγA := JγA) (Bf := Bf)
      (D := D) (C := C) hA_dom hC_sub hC γ hJγA x0 n).2.2.2
  have hBz :
      Bf (z n) ∈ B (z n) := by
    -- The representative `Bf` realizes the singleton value of `B` along the Tseng orbit.
    exact tsengRepresentative_mem (B := B) (Bf := Bf) (D := D) hB_eq hzD
  have hpD : p ∈ D := hC_sub hp.1
  have hBp :
      Bf p ∈ B p := by
    -- Zero-set points also lie in the single-valued region `D`, so their `B`-fiber is the
    -- same singleton.
    exact tsengRepresentative_mem (B := B) (Bf := Bf) (D := D) hB_eq hpD
  have hAp :
      -Bf p ∈ A p := by
    have hp_zero_mem : (0 : H) ∈ (A + B) p := by
      simpa using hp.2
    rcases Set.mem_add.1 hp_zero_mem with ⟨a, ha, b, hb, hab⟩
    have hb_eq : b = Bf p := by
      have hfiber : B p = Bf.toSetValuedOperatorOn D p := hB_eq p hpD
      rw [hfiber] at hb
      simpa [Function.toSetValuedOperatorOn, hpD] using hb
    have ha_eq : a = -Bf p := by
      rw [hb_eq] at hab
      exact eq_neg_of_add_eq_zero_left hab
    simpa [ha_eq] using ha
  have hA_pairing :
      0 ≤ ⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n) - (-Bf p)⟫_ℝ := by
    exact (SetValuedOperator.isMonotone_iff A).1 hA_mono hAz hAp
  have hB_pairing :
      0 ≤ ⟪z n - p, Bf (z n) - Bf p⟫_ℝ := by
    exact (SetValuedOperator.isMonotone_iff B).1 hB_mono hBz hBp
  have hSum_pairing :
      0 ≤ ⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n) + Bf (z n)⟫_ℝ := by
    -- Adding the two monotonicity inequalities eliminates the comparison value `Bf p`.
    have hA_pairing' :
        0 ≤ ⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n) + Bf p⟫_ℝ := by
      simpa [sub_eq_add_neg] using hA_pairing
    have hsum_nonneg := add_nonneg hA_pairing' hB_pairing
    have hsum_eq :
        ⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n) + Bf p⟫_ℝ +
            ⟪z n - p, Bf (z n) - Bf p⟫_ℝ =
          ⟪z n - p, ((γ : ℝ)⁻¹ • (y n - z n) + Bf p) + (Bf (z n) - Bf p)⟫_ℝ := by
      rw [← inner_add_right]
    rw [hsum_eq] at hsum_nonneg
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum_nonneg
  have hScaled_pairing :
      0 ≤ ⟪z n - p, y n - z n + (γ : ℝ) • Bf (z n)⟫_ℝ := by
    -- Multiply by the positive stepsize to recover the source line before the predictor expansion.
    have hscaled :
        0 ≤ (γ : ℝ) * ⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n) + Bf (z n)⟫_ℝ :=
      mul_nonneg γ.2.le hSum_pairing
    have hrewrite :
        (γ : ℝ) * ⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n) + Bf (z n)⟫_ℝ =
          ⟪z n - p, y n - z n + (γ : ℝ) • Bf (z n)⟫_ℝ := by
      calc
        (γ : ℝ) * ⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n) + Bf (z n)⟫_ℝ
            = ⟪z n - p, (γ : ℝ) • ((γ : ℝ)⁻¹ • (y n - z n) + Bf (z n))⟫_ℝ := by
                rw [← real_inner_smul_right]
        _ = ⟪z n - p, y n - z n + (γ : ℝ) • Bf (z n)⟫_ℝ := by
              congr 1
              rw [smul_add, smul_smul, mul_inv_cancel₀ γ.2.ne', one_smul]
    rwa [hrewrite] at hscaled
  have hMonotoneLine :
      ⟪z n - p, z n - y n - (γ : ℝ) • Bf (z n)⟫_ℝ ≤ 0 := by
    -- This is the normalized textbook inequality `(26.69)`.
    have hneg :
        ⟪z n - p, z n - y n - (γ : ℝ) • Bf (z n)⟫_ℝ =
          -⟪z n - p, y n - z n + (γ : ℝ) • Bf (z n)⟫_ℝ := by
      rw [show z n - y n - (γ : ℝ) • Bf (z n) =
          -(y n - z n + (γ : ℝ) • Bf (z n)) by abel_nf, inner_neg_right]
    nlinarith [hScaled_pairing]
  have hCross_split :
      (γ : ℝ) * ⟪z n - p, Bf (x n) - Bf (z n)⟫_ℝ =
        ⟪z n - p, z n - y n - (γ : ℝ) • Bf (z n)⟫_ℝ +
          ⟪z n - p, x n - z n⟫_ℝ := by
    -- Route correction: expand `yₙ = xₙ - γ Bf xₙ` only after the monotonicity term is isolated.
    calc
      (γ : ℝ) * ⟪z n - p, Bf (x n) - Bf (z n)⟫_ℝ
          = ⟪z n - p, (γ : ℝ) • (Bf (x n) - Bf (z n))⟫_ℝ := by
              rw [← real_inner_smul_right]
      _ =
          ⟪z n - p,
            (z n - y n - (γ : ℝ) • Bf (z n)) + (x n - z n)⟫_ℝ := by
            congr 1
            simp [x, y, z, smul_sub]
            abel_nf
      _ =
          ⟪z n - p, z n - y n - (γ : ℝ) • Bf (z n)⟫_ℝ +
            ⟪z n - p, x n - z n⟫_ℝ := by
              rw [inner_add_right]
  have hCross_le :
      (γ : ℝ) * ⟪z n - p, Bf (x n) - Bf (z n)⟫_ℝ ≤
        ⟪z n - p, x n - z n⟫_ℝ := by
    rw [hCross_split]
    linarith
  have hSqnorm_drop :
      ‖x n - p‖ ^ 2 - ‖z n - p‖ ^ 2 - ‖x n - z n‖ ^ 2 =
        2 * ⟪z n - p, x n - z n⟫_ℝ := by
    -- Expand `‖(zₙ - p) + (xₙ - zₙ)‖²` to rewrite the norm drop into the desired inner product.
    have hnorm :
        ‖(z n - p) + (x n - z n)‖ ^ 2 =
          ‖z n - p‖ ^ 2 + 2 * ⟪z n - p, x n - z n⟫_ℝ + ‖x n - z n‖ ^ 2 := by
      simpa using norm_add_sq_real (z n - p) (x n - z n)
    have hrewrite :
        (z n - p) + (x n - z n) = x n - p := by
      abel_nf
    rw [hrewrite] at hnorm
    nlinarith
  nlinarith [hCross_le, hSqnorm_drop]

/-- Helper for Theorem 26.17: Proposition 4.16 applied to the normalized Tseng projection
argument yields the projection-side square-norm estimate needed for the Fejér step. -/
theorem tsengProjectionSqnormLe
    {JγA Bf : H → H} {C : Set H}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (γ : PosReal) (x0 : C) {p : H} (hp : p ∈ C) (n : ℕ) :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    ‖projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 (n + 1) - p‖ ^ 2 ≤
      ‖projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n - p +
          (γ : ℝ) •
            (Bf (projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n) -
              Bf (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n))‖ ^ 2 := by
  let hC : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
  let w :=
    projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n +
      (γ : ℝ) •
        (Bf (projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n) -
          Bf (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n))
  have hw_proj :
      ‖P[C, hC] w - P[C, hC] p‖ ^ 2 ≤ ⟪P[C, hC] w - P[C, hC] p, w - p⟫_ℝ := by
    -- Route correction: stop at the projection inequality before any Lipschitz normalization.
    simpa [hC] using
      norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
        ⟨(x0 : H), x0.2⟩ hC_closed hC_convex w p
  have hp_fix : P[C, hC] p = p := tsengProjection_eq_self_of_mem hC hp
  have hw_le :
      ‖P[C, hC] w - p‖ ^ 2 ≤ ‖P[C, hC] w - p‖ * ‖w - p‖ := by
    rw [hp_fix] at hw_proj
    exact le_trans hw_proj (real_inner_le_norm _ _)
  have hw_sq :
      ‖P[C, hC] w - p‖ ^ 2 ≤ ‖w - p‖ ^ 2 := by
    nlinarith [hw_le, norm_nonneg (P[C, hC] w - p), norm_nonneg (w - p)]
  -- Rewrite the Tseng iterate once into the normalized projection argument `w`.
  simpa [hC, w, tsengProjectionArgument_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using hw_sq

/-- Helper for Theorem 26.17: the relative Lipschitz assumption on `Bf` converts to the real
norm-square remainder estimate used in the Tseng Fejér step. -/
theorem tsengLipschitzSqnormLe
    {A : SetValuedOperator H H} {JγA Bf : H → H} {D C : Set H}
    (hA_dom : A.dom ⊆ D) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_sub : C ⊆ D) (β : PosReal)
    (hB_lipschitz : LipschitzOnWith (Real.toNNReal ((β : ℝ)⁻¹)) Bf (C ∪ A.dom))
    (γ : PosReal) (hJγA : JγA.toSetValuedOperator = J[((γ : ℝ) • A)]) (x0 : C) (n : ℕ) :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    ((γ : ℝ) ^ 2) *
        ‖Bf (projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n) -
            Bf (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n)‖ ^ 2 ≤
      (((γ : ℝ) ^ 2) / ((β : ℝ) ^ 2)) *
        ‖projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n -
            projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n‖ ^ 2 := by
  let hC : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
  let x := projectedForwardBackwardForwardIteration JγA Bf C hC γ x0
  let z := projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0
  have hx_mem : x n ∈ C := by
    exact (tsengOrbitMemCAndResolventMemDom (A := A) (JγA := JγA) (Bf := Bf)
      (D := D) (C := C) hA_dom hC_sub hC γ hJγA x0 n).1
  have hz_mem : z n ∈ A.dom := by
    exact (tsengOrbitMemCAndResolventMemDom (A := A) (JγA := JγA) (Bf := Bf)
      (D := D) (C := C) hA_dom hC_sub hC γ hJγA x0 n).2.1
  have hnorm :
      ‖Bf (x n) - Bf (z n)‖ ≤ (β : ℝ)⁻¹ * ‖x n - z n‖ := by
    -- Convert the `edist`-valued Lipschitz estimate once and keep the rest in real norms.
    simpa [x, z, dist_eq_norm, Real.toNNReal_of_nonneg (inv_nonneg.mpr β.2.le)] using
      hB_lipschitz.dist_le_mul (x n) (Or.inl hx_mem) (z n) (Or.inr hz_mem)
  have hdiv_eq :
      (((γ : ℝ) ^ 2) / ((β : ℝ) ^ 2)) = ((γ : ℝ) ^ 2) * ((β : ℝ)⁻¹) ^ 2 := by
    field_simp [β.2.ne']
  have hsq :
      ‖Bf (x n) - Bf (z n)‖ ^ 2 ≤ ((β : ℝ)⁻¹) ^ 2 * ‖x n - z n‖ ^ 2 := by
    have hβ_nonneg : 0 ≤ (β : ℝ)⁻¹ := inv_nonneg.mpr β.2.le
    nlinarith [hnorm, hβ_nonneg, norm_nonneg (Bf (x n) - Bf (z n)), norm_nonneg (x n - z n)]
  have hscaled :
      ((γ : ℝ) ^ 2) * ‖Bf (x n) - Bf (z n)‖ ^ 2 ≤
        ((γ : ℝ) ^ 2) * (((β : ℝ)⁻¹) ^ 2 * ‖x n - z n‖ ^ 2) := by
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg (γ : ℝ))
  rw [hdiv_eq]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Helper for Theorem 26.17: the normalized projection estimate, the monotonicity cross-term
bound, and the Lipschitz remainder combine into the one-step Fejér inequality `(26.71)`. -/
theorem tsengFejerStep
    {A B : SetValuedOperator H H} {Bf : H → H} {D C : Set H}
    (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D) (hB_mono : B.IsMonotone)
    (hB_eq : ∀ x ∈ D, B x = Bf.toSetValuedOperatorOn D x) (β : PosReal)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_sub : C ⊆ D)
    (hB_lipschitz : LipschitzOnWith (Real.toNNReal ((β : ℝ)⁻¹)) Bf (C ∪ A.dom))
    (γ : PosReal) (JγA : H → H)
    (hJγA : JγA.toSetValuedOperator = J[((γ : ℝ) • A)]) (x0 : C)
    {p : H} (hp : p ∈ C ∩ (A + B).zeros) (n : ℕ) :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    ‖projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 (n + 1) - p‖ ^ 2 ≤
      ‖projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n - p‖ ^ 2 -
        (1 - ((γ : ℝ) ^ 2 / (β : ℝ) ^ 2)) *
          ‖projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n -
            projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n‖ ^ 2 := by
  let hC : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
  let x := projectedForwardBackwardForwardIteration JγA Bf C hC γ x0
  let z := projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0
  let diff := Bf (x n) - Bf (z n)
  have hproj :
      ‖x (n + 1) - p‖ ^ 2 ≤ ‖z n - p + (γ : ℝ) • diff‖ ^ 2 := by
    simpa [hC, x, z, diff] using
      tsengProjectionSqnormLe (JγA := JγA) (Bf := Bf) (C := C)
        hC_closed hC_convex γ x0 hp.1 n
  have hcross :
      2 * (γ : ℝ) * ⟪z n - p, diff⟫_ℝ ≤
        ‖x n - p‖ ^ 2 - ‖z n - p‖ ^ 2 - ‖x n - z n‖ ^ 2 := by
    simpa [hC, x, z, diff] using
      tsengCrossTerm_le_sqnormDrop (A := A) (B := B) (JγA := JγA) (Bf := Bf)
        (D := D) (C := C) (SetValuedOperator.Maximal.isMonotone hA_max) hA_dom hC_sub
        hB_mono hB_eq hC γ hJγA x0 hp n
  have hlip :
      ((γ : ℝ) ^ 2) * ‖diff‖ ^ 2 ≤ (((γ : ℝ) ^ 2) / ((β : ℝ) ^ 2)) * ‖x n - z n‖ ^ 2 := by
    simpa [hC, x, z, diff] using
      tsengLipschitzSqnormLe (A := A) (JγA := JγA) (Bf := Bf) (D := D) (C := C)
        hA_dom hC_closed hC_convex hC_sub β hB_lipschitz γ hJγA x0 n
  have hexpand :
      ‖z n - p + (γ : ℝ) • diff‖ ^ 2 =
        ‖z n - p‖ ^ 2 + 2 * (γ : ℝ) * ⟪z n - p, diff⟫_ℝ +
          ((γ : ℝ) ^ 2) * ‖diff‖ ^ 2 := by
    -- Route correction: expand the normalized Tseng step only after the projection and Lipschitz
    -- interfaces are already in stable normal form.
    calc
      ‖z n - p + (γ : ℝ) • diff‖ ^ 2
          = ‖z n - p‖ ^ 2 + 2 * ⟪z n - p, (γ : ℝ) • diff⟫_ℝ +
              ‖(γ : ℝ) • diff‖ ^ 2 := by
                simpa using norm_add_sq_real (z n - p) ((γ : ℝ) • diff)
      _ = ‖z n - p‖ ^ 2 + 2 * (γ : ℝ) * ⟪z n - p, diff⟫_ℝ +
            ((γ : ℝ) ^ 2) * ‖diff‖ ^ 2 := by
            rw [real_inner_smul_right, norm_smul, Real.norm_of_nonneg γ.2.le]
            ring
  calc
    ‖x (n + 1) - p‖ ^ 2 ≤ ‖z n - p + (γ : ℝ) • diff‖ ^ 2 := hproj
    _ = ‖z n - p‖ ^ 2 + 2 * (γ : ℝ) * ⟪z n - p, diff⟫_ℝ +
          ((γ : ℝ) ^ 2) * ‖diff‖ ^ 2 := hexpand
    _ ≤ ‖x n - p‖ ^ 2 - ‖x n - z n‖ ^ 2 + ((γ : ℝ) ^ 2) * ‖diff‖ ^ 2 := by
          nlinarith [hcross]
    _ ≤ ‖x n - p‖ ^ 2 - ‖x n - z n‖ ^ 2 +
          (((γ : ℝ) ^ 2) / ((β : ℝ) ^ 2)) * ‖x n - z n‖ ^ 2 := by
          nlinarith [hlip]
    _ = ‖x n - p‖ ^ 2 -
          (1 - ((γ : ℝ) ^ 2 / (β : ℝ) ^ 2)) * ‖x n - z n‖ ^ 2 := by
          ring

/-- Helper for Theorem 26.17: the Tseng orbit is Fejér monotone with respect to
`C ∩ (A + B).zeros`. -/
theorem tsengFejerMonotone
    {A B : SetValuedOperator H H} {Bf : H → H} {D C : Set H}
    (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D) (hB_mono : B.IsMonotone)
    (hB_eq : ∀ x ∈ D, B x = Bf.toSetValuedOperatorOn D x) (β : PosReal)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_sub : C ⊆ D)
    (hB_lipschitz : LipschitzOnWith (Real.toNNReal ((β : ℝ)⁻¹)) Bf (C ∪ A.dom))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < (β : ℝ)) (JγA : H → H)
    (hJγA : JγA.toSetValuedOperator = J[((γ : ℝ) • A)]) (x0 : C) :
    FejerMonotone
      (C ∩ (A + B).zeros)
      (projectedForwardBackwardForwardIteration JγA Bf C
        (isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex)
        γ x0) := by
  let hC : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
  let x := projectedForwardBackwardForwardIteration JγA Bf C hC γ x0
  let z := projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0
  let coeff : ℝ := 1 - ((γ : ℝ) ^ 2 / (β : ℝ) ^ 2)
  have hcoeff_pos : 0 < coeff := by
    -- The Fejér coefficient is positive because the stepsize satisfies `γ < β`.
    have hβsq_pos : 0 < (β : ℝ) ^ 2 := sq_pos_of_pos β.2
    have hβsq_ne : (β : ℝ) ^ 2 ≠ 0 := ne_of_gt hβsq_pos
    have hγsq_lt : (γ : ℝ) ^ 2 < (β : ℝ) ^ 2 := by
      nlinarith [hγ_lt, γ.2, β.2]
    have hdiv_lt : ((γ : ℝ) ^ 2) / ((β : ℝ) ^ 2) < 1 := by
      simpa [hβsq_ne] using div_lt_div_of_pos_right hγsq_lt hβsq_pos
    dsimp [coeff]
    linarith
  change FejerMonotone (C ∩ (A + B).zeros) x
  intro p hp n
  -- Apply the one-step Fejér estimate and drop the nonnegative residual term.
  have hstep :
      ‖x (n + 1) - p‖ ^ 2 ≤ ‖x n - p‖ ^ 2 - coeff * ‖x n - z n‖ ^ 2 := by
    simpa [hC, x, z, coeff] using
      tsengFejerStep (A := A) (B := B) (Bf := Bf) (D := D) (C := C)
        hA_max hA_dom hB_mono hB_eq β hC_closed hC_convex hC_sub hB_lipschitz γ
        JγA hJγA x0 hp n
  have hsq :
      ‖x (n + 1) - p‖ ^ 2 ≤ ‖x n - p‖ ^ 2 := by
    nlinarith [hstep, hcoeff_pos, sq_nonneg (‖x n - z n‖)]
  simpa [dist_eq_norm] using
    (show ‖x (n + 1) - p‖ ≤ ‖x n - p‖ by
      nlinarith [hsq, norm_nonneg (x (n + 1) - p), norm_nonneg (x n - p)])

/-- Clause (i) of Theorem 26.17: for Tseng's algorithm under the stated
maximal-monotonicity, projection,
and relative Lipschitz hypotheses, the residual sequence `(x_n - z_n)` converges strongly to
`0`. -/
theorem tsengAlgorithm_sub_tendsto_zero
    (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D) (hB_mono : B.IsMonotone)
    (hB_eq : ∀ x ∈ D, B x = Bf.toSetValuedOperatorOn D x) (β : PosReal)
    (hAB_max : Maximal IsMonotone (A + B)) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hC_sub : C ⊆ D)
    (hC_zero : (C ∩ (A + B).zeros).Nonempty)
    (hB_lipschitz : LipschitzOnWith (Real.toNNReal ((β : ℝ)⁻¹)) Bf (C ∪ A.dom))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < (β : ℝ)) (JγA : H → H)
    (hJγA : JγA.toSetValuedOperator = J[((γ : ℝ) • A)]) (x0 : C)
    :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    Tendsto
      (fun n ↦
        projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n -
          projectedForwardBackwardForwardResolventSequence
            JγA Bf C hC γ x0 n)
      atTop (𝓝 (0 : H)) := by
  let hC : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
  let x := projectedForwardBackwardForwardIteration JγA Bf C hC γ x0
  let z := projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0
  let _ := hAB_max
  let coeff : ℝ := 1 - ((γ : ℝ) ^ 2 / (β : ℝ) ^ 2)
  have hcoeff_pos : 0 < coeff := by
    -- The textbook coefficient is positive because the stepsize satisfies `γ < β`.
    have hβsq_pos : 0 < (β : ℝ) ^ 2 := sq_pos_of_pos β.2
    have hβsq_ne : (β : ℝ) ^ 2 ≠ 0 := ne_of_gt hβsq_pos
    have hγsq_lt : (γ : ℝ) ^ 2 < (β : ℝ) ^ 2 := by
      nlinarith [hγ_lt, γ.2, β.2]
    have hdiv_lt : ((γ : ℝ) ^ 2) / ((β : ℝ) ^ 2) < 1 := by
      simpa [hβsq_ne] using div_lt_div_of_pos_right hγsq_lt hβsq_pos
    dsimp [coeff]
    linarith
  have hfejer : FejerMonotone (C ∩ (A + B).zeros) x := by
    intro p hp n
    have hstep :
        ‖x (n + 1) - p‖ ^ 2 ≤ ‖x n - p‖ ^ 2 - coeff * ‖x n - z n‖ ^ 2 := by
      simpa [hC, x, z, coeff] using
        tsengFejerStep (A := A) (B := B) (Bf := Bf) (D := D) (C := C)
          hA_max hA_dom hB_mono hB_eq β hC_closed hC_convex hC_sub hB_lipschitz γ
          JγA hJγA x0 hp n
    have hsq :
        ‖x (n + 1) - p‖ ^ 2 ≤ ‖x n - p‖ ^ 2 := by
      nlinarith [hstep, hcoeff_pos, sq_nonneg (‖x n - z n‖)]
    simpa [dist_eq_norm] using
      (show ‖x (n + 1) - p‖ ≤ ‖x n - p‖ by
        nlinarith [hsq, norm_nonneg (x (n + 1) - p), norm_nonneg (x n - p)])
  rcases hC_zero with ⟨p, hp⟩
  have hdist_tendsto : ∃ l : ℝ, Tendsto (fun n ↦ dist (x n) p) atTop (𝓝 l) := by
    simpa [x] using FejerMonotone.dist_tendsto hfejer hp
  rcases hdist_tendsto with ⟨l, hl⟩
  have hdist_sq_tendsto :
      Tendsto (fun n ↦ dist (x n) p ^ 2) atTop (𝓝 (l ^ 2)) := by
    exact hl.pow 2
  have hdist_sq_tendsto_succ :
      Tendsto (fun n ↦ dist (x (n + 1)) p ^ 2) atTop (𝓝 (l ^ 2)) := by
    simpa [Nat.succ_eq_add_one] using hdist_sq_tendsto.comp (tendsto_add_atTop_nat 1)
  have hdist_sq_diff_tendsto :
      Tendsto (fun n ↦ dist (x n) p ^ 2 - dist (x (n + 1)) p ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa [sub_eq_add_neg, Nat.succ_eq_add_one] using hdist_sq_tendsto.sub hdist_sq_tendsto_succ
  have hnorm_sq_diff_tendsto :
      Tendsto (fun n ↦ ‖x n - p‖ ^ 2 - ‖x (n + 1) - p‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa [dist_eq_norm] using hdist_sq_diff_tendsto
  have hres_sq_le :
      ∀ n, coeff * ‖x n - z n‖ ^ 2 ≤ ‖x n - p‖ ^ 2 - ‖x (n + 1) - p‖ ^ 2 := by
    intro n
    have hstep :
        ‖x (n + 1) - p‖ ^ 2 ≤ ‖x n - p‖ ^ 2 - coeff * ‖x n - z n‖ ^ 2 := by
      simpa [hC, x, z, coeff] using
        tsengFejerStep (A := A) (B := B) (Bf := Bf) (D := D) (C := C)
          hA_max hA_dom hB_mono hB_eq β hC_closed hC_convex hC_sub hB_lipschitz γ
          JγA hJγA x0 hp n
    nlinarith
  have hscaled_sq_tendsto :
      Tendsto (fun n ↦ coeff * ‖x n - z n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    -- The one-step Fejér drop traps the scaled squared residuals between `0` and a vanishing
    -- successor difference of squared comparison distances.
    refine squeeze_zero (fun n ↦ mul_nonneg hcoeff_pos.le (sq_nonneg (‖x n - z n‖)))
      hres_sq_le hnorm_sq_diff_tendsto
  have hcoeff_ne : coeff ≠ 0 := ne_of_gt hcoeff_pos
  have hres_sq_tendsto :
      Tendsto (fun n ↦ ‖x n - z n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa [coeff, hcoeff_ne, mul_assoc] using hscaled_sq_tendsto.const_mul (coeff⁻¹)
  have hres_norm_tendsto :
      Tendsto (fun n ↦ ‖x n - z n‖) atTop (𝓝 (0 : ℝ)) := by
    -- Taking square roots converts convergence of the squared norms back to convergence of norms.
    have hsqrt_tendsto :
        Tendsto (fun n ↦ Real.sqrt (‖x n - z n‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) := by
      exact Real.continuous_sqrt.continuousAt.tendsto.comp hres_sq_tendsto
    simpa [Real.sqrt_zero, Real.sqrt_sq_eq_abs] using hsqrt_tendsto
  -- Norm convergence to `0` is equivalent to strong convergence of the residuals.
  simpa [hC, x, z] using (tendsto_zero_iff_norm_tendsto_zero).mpr hres_norm_tendsto

omit [CompleteSpace H] in
/-- Helper for Theorem 26.17: subtracting a strongly null residual preserves the weak limit of a
sequence. -/
theorem tendstoWeaklyOfSubTendstoZeroSeq
    {aSeq bSeq : ℕ → H} {a : H}
    (ha :
      Tendsto (fun n ↦ toWeakSpace ℝ H (aSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H a)))
    (hsub : Tendsto (fun n ↦ aSeq n - bSeq n) atTop (𝓝 (0 : H))) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (bSeq n)) atTop
      (𝓝 (toWeakSpace ℝ H a)) := by
  -- Send the strong residual through `toWeakSpace`, then subtract in `WeakSpace`.
  have hsubWeak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (aSeq n - bSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H (0 : H))) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto (0 : H)).comp hsub
  simpa [sub_sub_cancel] using ha.sub hsubWeak

/-- Helper for Theorem 26.17: every weak sequential cluster point of the Tseng orbit belongs to
`C ∩ (A + B).zeros`. -/
theorem tsengWeakClusterPoint_mem_inter_zeros
    {A B : SetValuedOperator H H} {Bf : H → H} {D C : Set H}
    (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D) (hB_mono : B.IsMonotone)
    (hB_eq : ∀ x ∈ D, B x = Bf.toSetValuedOperatorOn D x) (β : PosReal)
    (hAB_max : Maximal IsMonotone (A + B)) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hC_sub : C ⊆ D)
    (hC_zero : (C ∩ (A + B).zeros).Nonempty)
    (hB_lipschitz : LipschitzOnWith (Real.toNNReal ((β : ℝ)⁻¹)) Bf (C ∪ A.dom))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < (β : ℝ)) (JγA : H → H)
    (hJγA : JγA.toSetValuedOperator = J[((γ : ℝ) • A)]) (x0 : C)
    {w : H}
    (hw :
      IsSequentialClusterPt
        (fun n ↦
          toWeakSpace ℝ H
            (projectedForwardBackwardForwardIteration
              JγA Bf C
                (isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩
                  hC_closed hC_convex)
                γ x0 n))
        (toWeakSpace ℝ H w)) :
    w ∈ C ∩ (A + B).zeros := by
  let hC : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
  let x := projectedForwardBackwardForwardIteration JγA Bf C hC γ x0
  let z := projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0
  let u : ℕ → H := fun n ↦
    (γ : ℝ)⁻¹ • (x n - z n) + (Bf (z n) - Bf (x n))
  have hx_mem : ∀ n, x n ∈ C := by
    intro n
    exact (tsengOrbitMemCAndResolventMemDom (A := A) (JγA := JγA) (Bf := Bf)
      (D := D) (C := C) hA_dom hC_sub hC γ hJγA x0 n).1
  have hz_mem : ∀ n, z n ∈ A.dom := by
    intro n
    exact (tsengOrbitMemCAndResolventMemDom (A := A) (JγA := JγA) (Bf := Bf)
      (D := D) (C := C) hA_dom hC_sub hC γ hJγA x0 n).2.1
  have hfejer : FejerMonotone (C ∩ (A + B).zeros) x := by
    simpa [hC, x] using
      tsengFejerMonotone (A := A) (B := B) (Bf := Bf) (D := D) (C := C)
        hA_max hA_dom hB_mono hB_eq β hC_closed hC_convex hC_sub hB_lipschitz γ
        hγ_lt JγA hJγA x0
  have hsub_tendsto :
      Tendsto (fun n ↦ x n - z n) atTop (𝓝 (0 : H)) := by
    -- Clause (i) is the strong residual estimate reused throughout the cluster argument.
    simpa [hC, x, z] using
      tsengAlgorithm_sub_tendsto_zero (A := A) (B := B) (JγA := JγA) (Bf := Bf)
        (D := D) (C := C) hA_max hA_dom hB_mono hB_eq β hAB_max hC_closed hC_convex
        hC_sub hC_zero hB_lipschitz γ hγ_lt hJγA x0
  have hBdiff_norm_le :
      ∀ n, ‖Bf (z n) - Bf (x n)‖ ≤ ‖x n - z n‖ * (β : ℝ)⁻¹ := by
    intro n
    -- Apply the relative Lipschitz estimate only once, in real-norm form.
    simpa [x, z, dist_eq_norm, norm_sub_rev, mul_comm,
      Real.toNNReal_of_nonneg (inv_nonneg.mpr β.2.le)] using
      hB_lipschitz.dist_le_mul (x n) (Or.inl (hx_mem n)) (z n) (Or.inr (hz_mem n))
  have hBdiff_norm_tendsto :
      Tendsto (fun n ↦ ‖Bf (z n) - Bf (x n)‖) atTop (𝓝 (0 : ℝ)) := by
    have hscaled :
        Tendsto (fun n ↦ ‖x n - z n‖ * (β : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa using hsub_tendsto.norm.mul_const ((β : ℝ)⁻¹)
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ hscaled
    exact Eventually.of_forall hBdiff_norm_le
  have hBdiff_tendsto :
      Tendsto (fun n ↦ Bf (z n) - Bf (x n)) atTop (𝓝 (0 : H)) := by
    exact (tendsto_zero_iff_norm_tendsto_zero).mpr hBdiff_norm_tendsto
  have hu_tendsto : Tendsto u atTop (𝓝 (0 : H)) := by
    have hscaled :
        Tendsto (fun n ↦ (γ : ℝ)⁻¹ • (x n - z n)) atTop (𝓝 (0 : H)) := by
      simpa using hsub_tendsto.const_smul ((γ : ℝ)⁻¹)
    -- Keep the auxiliary vector in its packaged graph-point normal form.
    simpa [u] using hscaled.add hBdiff_tendsto
  have hx_bounded : Bornology.IsBounded (Set.range x) :=
    FejerMonotone.isBounded hfejer hC_zero
  have hsub_bounded : Bornology.IsBounded (Set.range fun n ↦ x n - z n) :=
    Metric.isBounded_range_of_tendsto _ hsub_tendsto
  have hz_bounded : Bornology.IsBounded (Set.range z) := by
    rcases isBounded_iff_forall_norm_le.mp hx_bounded with ⟨Rx, hRx⟩
    rcases isBounded_iff_forall_norm_le.mp hsub_bounded with ⟨Rr, hRr⟩
    refine isBounded_iff_forall_norm_le.mpr ?_
    refine ⟨Rx + Rr, ?_⟩
    rintro y ⟨n, rfl⟩
    have hz_eq : x n - (x n - z n) = z n := by
      abel_nf
    calc
      ‖z n‖ = ‖x n - (x n - z n)‖ := by rw [hz_eq]
      _ ≤ ‖x n‖ + ‖x n - z n‖ := norm_sub_le _ _
      _ ≤ Rx + Rr := add_le_add (hRx _ (Set.mem_range_self n)) (hRr _ (Set.mem_range_self n))
  have hu_bounded : Bornology.IsBounded (Set.range u) :=
    Metric.isBounded_range_of_tendsto _ hu_tendsto
  rcases hw.exists_subseq_tendsto with ⟨φ, hφmono, hφtendsto⟩
  have hwC : w ∈ C := by
    -- Closed convexity keeps the weak limit of the orbit inside `C`.
    exact mem_of_tendsto_weakly_of_isClosed_convex hC_closed hC_convex
      (fun n ↦ hx_mem (φ n)) hφtendsto
  have hsubseq_tendsto :
      Tendsto (fun n ↦ x (φ n) - z (φ n)) atTop (𝓝 (0 : H)) := by
    exact hsub_tendsto.comp hφmono.tendsto_atTop
  have hz_tendsto :
      Tendsto (fun n ↦ toWeakSpace ℝ H (z (φ n))) atTop
        (𝓝 (toWeakSpace ℝ H w)) :=
    tendstoWeaklyOfSubTendstoZeroSeq hφtendsto hsubseq_tendsto
  have hu_subseq_tendsto :
      Tendsto (fun n ↦ u (φ n)) atTop (𝓝 (0 : H)) := by
    exact hu_tendsto.comp hφmono.tendsto_atTop
  have hz_subseq_bounded :
      Bornology.IsBounded (Set.range fun n ↦ z (φ n)) :=
    hz_bounded.subset fun _ hy ↦ by
      rcases hy with ⟨n, rfl⟩
      exact ⟨φ n, rfl⟩
  have hu_subseq_bounded :
      Bornology.IsBounded (Set.range fun n ↦ u (φ n)) :=
    hu_bounded.subset fun _ hy ↦ by
      rcases hy with ⟨n, rfl⟩
      exact ⟨φ n, rfl⟩
  have hgraph_bounded :
      Bornology.IsBounded (Set.range fun n ↦ (z (φ n), u (φ n))) := by
    -- Package bounded primal and dual coordinates into bounded graph pairs.
    have hfst :
        Prod.fst '' Set.range (fun n ↦ (z (φ n), u (φ n))) =
          Set.range (fun n ↦ z (φ n)) := by
      ext y
      constructor
      · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨(z (φ n), u (φ n)), ⟨n, rfl⟩, rfl⟩
    have hsnd :
        Prod.snd '' Set.range (fun n ↦ (z (φ n), u (φ n))) =
          Set.range (fun n ↦ u (φ n)) := by
      ext y
      constructor
      · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨(z (φ n), u (φ n)), ⟨n, rfl⟩, rfl⟩
    rw [← Bornology.isBounded_image_fst_and_snd]
    rw [hfst, hsnd]
    exact ⟨hz_subseq_bounded, hu_subseq_bounded⟩
  have hgraph_mem :
      ∀ n, (z (φ n), u (φ n)) ∈ gra (A + B) := by
    intro n
    -- Reuse the packaged graph element `uₙ ∈ (A + B) zₙ`.
    simpa [u, x, z] using
      tsengAuxiliaryVector_mem_add (A := A) (B := B) (JγA := JγA) (Bf := Bf)
        (D := D) (C := C) hA_dom hC_sub hB_eq hC γ hJγA x0 (φ n)
  have hw_graph :
      (w, (0 : H)) ∈ gra (A + B) :=
    SetValuedOperator.Maximal.mem_graph_of_tendsto_weakly_of_tendsto
      hAB_max hgraph_mem hgraph_bounded hz_tendsto hu_subseq_tendsto
  have hw_zero : w ∈ (A + B).zeros := by
    rw [SetValuedOperator.mem_zeros_iff]
    simpa [SetValuedOperator.mem_graph] using hw_graph
  exact ⟨hwC, hw_zero⟩

/-- Clause (ii) of Theorem 26.17: for Tseng's algorithm under the stated
maximal-monotonicity, projection,
and relative Lipschitz hypotheses, the sequences `(x_n)` and `(z_n)` converge weakly to a common
point of `C ∩ zer (A + B)`, formalized as `C ∩ (A + B).zeros`. -/
theorem tsengAlgorithm_tendsto_weakly
    (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D) (hB_mono : B.IsMonotone)
    (hB_eq : ∀ x ∈ D, B x = Bf.toSetValuedOperatorOn D x) (β : PosReal)
    (hAB_max : Maximal IsMonotone (A + B)) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hC_sub : C ⊆ D)
    (hC_zero : (C ∩ (A + B).zeros).Nonempty)
    (hB_lipschitz : LipschitzOnWith (Real.toNNReal ((β : ℝ)⁻¹)) Bf (C ∪ A.dom))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < (β : ℝ)) (JγA : H → H)
    (hJγA : JγA.toSetValuedOperator = J[((γ : ℝ) • A)]) (x0 : C)
    :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    ∃ p ∈ C ∩ (A + B).zeros,
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H
            (projectedForwardBackwardForwardIteration JγA Bf C hC γ x0 n))
        atTop (𝓝 (toWeakSpace ℝ H p)) ∧
        Tendsto
          (fun n ↦
            toWeakSpace ℝ H
              (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0 n))
          atTop (𝓝 (toWeakSpace ℝ H p)) := by
  let hC : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
  let x := projectedForwardBackwardForwardIteration JγA Bf C hC γ x0
  let z := projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0
  have hfejer : FejerMonotone (C ∩ (A + B).zeros) x := by
    -- Reuse the packaged one-step estimate as the global Fejér owner.
    simpa [hC, x] using
      tsengFejerMonotone (A := A) (B := B) (Bf := Bf) (D := D) (C := C)
        hA_max hA_dom hB_mono hB_eq β hC_closed hC_convex hC_sub hB_lipschitz γ
        hγ_lt JγA hJγA x0
  have hcluster :
      ∀ w : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H w) →
          w ∈ C ∩ (A + B).zeros := by
    intro w hw
    -- Route correction: package weak transport and graph closure once at the cluster-point level.
    simpa [hC, x] using
      tsengWeakClusterPoint_mem_inter_zeros
        (A := A) (B := B) (Bf := Bf) (D := D) (C := C)
        hA_max hA_dom hB_mono hB_eq β hAB_max hC_closed hC_convex hC_sub hC_zero
        hB_lipschitz γ hγ_lt JγA hJγA x0 hw
  rcases tendsto_weakly_of_fejerMonotone_of_weakSequentialClusterPts_mem hC_zero x hfejer hcluster
    with ⟨p, hp, hx_tendsto⟩
  have hsub_tendsto :
      Tendsto (fun n ↦ x n - z n) atTop (𝓝 (0 : H)) := by
    -- Clause (i) supplies the strong residual convergence used to transport the weak limit.
    simpa [hC, x, z] using
      tsengAlgorithm_sub_tendsto_zero (A := A) (B := B) (JγA := JγA) (Bf := Bf)
        (D := D) (C := C) hA_max hA_dom hB_mono hB_eq β hAB_max hC_closed hC_convex
        hC_sub hC_zero hB_lipschitz γ hγ_lt hJγA x0
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [hC, x] using hx_tendsto
  · -- The resolvent orbit has the same weak limit because `xₙ - zₙ → 0`.
    simpa [hC, z] using tendstoWeaklyOfSubTendstoZeroSeq hx_tendsto hsub_tendsto

/-- Theorem 26.17: if, in addition, either `A` or `B` is uniformly monotone on every
nonempty bounded subset of `dom A`, then Tseng's algorithm converges strongly to the unique point
of `C ∩ zer (A + B)`, formalized as `C ∩ (A + B).zeros`. -/
theorem tsengAlgorithm_tendsto_of_uniformlyMonotoneOnEveryBoundedSubset
    (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D) (hB_mono : B.IsMonotone)
    (hB_eq : ∀ x ∈ D, B x = Bf.toSetValuedOperatorOn D x) (β : PosReal)
    (hAB_max : Maximal IsMonotone (A + B)) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hC_sub : C ⊆ D)
    (hC_zero : (C ∩ (A + B).zeros).Nonempty)
    (hB_lipschitz : LipschitzOnWith (Real.toNNReal ((β : ℝ)⁻¹)) Bf (C ∪ A.dom))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < (β : ℝ)) (JγA : H → H)
    (hJγA : JγA.toSetValuedOperator = J[((γ : ℝ) • A)])
    (x0 : C)
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ A.dom → A.IsUniformlyMonotoneOn S) ∨
        ∀ S : Set H, S.Nonempty → Bornology.IsBounded S → S ⊆ A.dom →
          B.IsUniformlyMonotoneOn S)
    :
    let hC : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
    ∃ p ∈ C ∩ (A + B).zeros,
      Tendsto
        (projectedForwardBackwardForwardIteration JγA Bf C hC γ x0)
        atTop (𝓝 p) ∧
        Tendsto
          (projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0)
          atTop (𝓝 p) ∧
        C ∩ (A + B).zeros = ({p} : Set H) := by
  let hC : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex ⟨(x0 : H), x0.2⟩ hC_closed hC_convex
  let x := projectedForwardBackwardForwardIteration JγA Bf C hC γ x0
  let y := projectedForwardBackwardForwardPredictorSequence JγA Bf C hC γ x0
  let z := projectedForwardBackwardForwardResolventSequence JγA Bf C hC γ x0
  let u : ℕ → H := fun n ↦
    (γ : ℝ)⁻¹ • (x n - z n) + (Bf (z n) - Bf (x n))
  rcases tsengAlgorithm_tendsto_weakly
      (A := A) (B := B) (JγA := JγA) (Bf := Bf) (D := D) (C := C)
      hA_max hA_dom hB_mono hB_eq β hAB_max hC_closed hC_convex hC_sub hC_zero hB_lipschitz γ
      hγ_lt hJγA x0 with
    ⟨p, hp, _, _⟩
  have hx_mem : ∀ n, x n ∈ C := by
    intro n
    exact (tsengOrbitMemCAndResolventMemDom (A := A) (JγA := JγA) (Bf := Bf)
      (D := D) (C := C) hA_dom hC_sub hC γ hJγA x0 n).1
  have hz_memA : ∀ n, z n ∈ A.dom := by
    intro n
    exact (tsengOrbitMemCAndResolventMemDom (A := A) (JγA := JγA) (Bf := Bf)
      (D := D) (C := C) hA_dom hC_sub hC γ hJγA x0 n).2.1
  have hz_memD : ∀ n, z n ∈ D := by
    intro n
    exact (tsengOrbitMemCAndResolventMemDom (A := A) (JγA := JγA) (Bf := Bf)
      (D := D) (C := C) hA_dom hC_sub hC γ hJγA x0 n).2.2.2
  have hAz : ∀ n, (γ : ℝ)⁻¹ • (y n - z n) ∈ A (z n) := by
    intro n
    -- Keep the resolvent graph witness in its stable normal form for all later uniform estimates.
    simpa [x, y, z, mem_graph] using
      tsengResolventSequence_mem_graph (A := A) (JγA := JγA) (Bf := Bf) (C := C)
        hC γ hJγA x0 n
  have hBz : ∀ n, Bf (z n) ∈ B (z n) := by
    intro n
    exact tsengRepresentative_mem (B := B) (Bf := Bf) (D := D) hB_eq (hz_memD n)
  have hsub_tendsto :
      Tendsto (fun n ↦ x n - z n) atTop (𝓝 (0 : H)) := by
    -- Clause (i) supplies the strong residual estimate reused in the strong-convergence step.
    simpa [hC, x, z] using
      tsengAlgorithm_sub_tendsto_zero (A := A) (B := B) (JγA := JγA) (Bf := Bf)
        (D := D) (C := C) hA_max hA_dom hB_mono hB_eq β hAB_max hC_closed hC_convex hC_sub
        hC_zero hB_lipschitz γ hγ_lt hJγA x0
  have hBdiff_norm_le :
      ∀ n, ‖Bf (z n) - Bf (x n)‖ ≤ ‖x n - z n‖ * (β : ℝ)⁻¹ := by
    intro n
    -- Reuse the same real-norm Lipschitz conversion as in clause (ii).
    simpa [x, z, dist_eq_norm, norm_sub_rev, mul_comm,
      Real.toNNReal_of_nonneg (inv_nonneg.mpr β.2.le)] using
      hB_lipschitz.dist_le_mul (x n) (Or.inl (hx_mem n)) (z n) (Or.inr (hz_memA n))
  have hBdiff_norm_tendsto :
      Tendsto (fun n ↦ ‖Bf (z n) - Bf (x n)‖) atTop (𝓝 (0 : ℝ)) := by
    have hscaled :
        Tendsto (fun n ↦ ‖x n - z n‖ * (β : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa using hsub_tendsto.norm.mul_const ((β : ℝ)⁻¹)
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ hscaled
    exact Eventually.of_forall hBdiff_norm_le
  have hBdiff_tendsto :
      Tendsto (fun n ↦ Bf (z n) - Bf (x n)) atTop (𝓝 (0 : H)) := by
    exact (tendsto_zero_iff_norm_tendsto_zero).mpr hBdiff_norm_tendsto
  have hu_tendsto : Tendsto u atTop (𝓝 (0 : H)) := by
    have hscaled :
        Tendsto (fun n ↦ (γ : ℝ)⁻¹ • (x n - z n)) atTop (𝓝 (0 : H)) := by
      simpa using hsub_tendsto.const_smul ((γ : ℝ)⁻¹)
    -- Keep the auxiliary vector in the packaged graph-side form from clause (ii).
    simpa [u] using hscaled.add hBdiff_tendsto
  have hfejer : FejerMonotone (C ∩ (A + B).zeros) x := by
    simpa [hC, x] using
      tsengFejerMonotone (A := A) (B := B) (Bf := Bf) (D := D) (C := C)
        hA_max hA_dom hB_mono hB_eq β hC_closed hC_convex hC_sub hB_lipschitz γ hγ_lt JγA
        hJγA x0
  have hx_bounded : Bornology.IsBounded (Set.range x) :=
    FejerMonotone.isBounded hfejer hC_zero
  have hsub_bounded : Bornology.IsBounded (Set.range fun n ↦ x n - z n) :=
    Metric.isBounded_range_of_tendsto _ hsub_tendsto
  have hz_bounded : Bornology.IsBounded (Set.range z) := by
    rcases isBounded_iff_forall_norm_le.mp hx_bounded with ⟨Rx, hRx⟩
    rcases isBounded_iff_forall_norm_le.mp hsub_bounded with ⟨Rr, hRr⟩
    refine isBounded_iff_forall_norm_le.mpr ?_
    refine ⟨Rx + Rr, ?_⟩
    rintro w ⟨n, rfl⟩
    have hz_eq : x n - (x n - z n) = z n := by
      abel_nf
    calc
      ‖z n‖ = ‖x n - (x n - z n)‖ := by rw [hz_eq]
      _ ≤ ‖x n‖ + ‖x n - z n‖ := norm_sub_le _ _
      _ ≤ Rx + Rr :=
        add_le_add (hRx _ (Set.mem_range_self n)) (hRr _ (Set.mem_range_self n))
  have hpD : p ∈ D := hC_sub hp.1
  have hpB : Bf p ∈ B p := tsengRepresentative_mem (B := B) (Bf := Bf) (D := D) hB_eq hpD
  have hpA : -Bf p ∈ A p :=
    tsengNegRepresentative_mem_left_of_mem_zero (A := A) (B := B) (Bf := Bf) (D := D) hB_eq
      hpD hp.2
  let S : Set H := insert p (Set.range z)
  have hpS : p ∈ S := by
    simp [S]
  have hz_memS : ∀ n, z n ∈ S := by
    intro n
    exact Set.mem_insert_of_mem p (Set.mem_range_self n)
  have hS_nonempty : S.Nonempty := ⟨p, hpS⟩
  have hS_bounded : Bornology.IsBounded S := by
    -- Localize uniform monotonicity only on the bounded resolvent orbit together with its limit.
    simpa [S] using hz_bounded.insert p
  have hS_subA : S ⊆ A.dom := by
    intro q hq
    have hq' : q = p ∨ q ∈ Set.range z := by
      simpa [S, Set.mem_insert_iff] using hq
    rcases hq' with hqeq | hq'
    · cases hqeq
      exact ⟨-Bf p, hpA⟩
    · rcases hq' with ⟨n, rfl⟩
      exact hz_memA n
  have hz_tendsto : Tendsto z atTop (𝓝 p) := by
    rcases hUniform with hUniformA | hUniformB
    · rcases hUniformA S hS_nonempty hS_bounded hS_subA with ⟨φ, hφ⟩
      have hineq_seq :
          ∀ n, φ ‖z n - p‖₊ ≤ (⟪z n - p, u n⟫_ℝ : EReal) := by
        intro n
        have hAineq :
            φ ‖z n - p‖₊ ≤
              (⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n) + Bf p⟫_ℝ : EReal) := by
          -- Route correction: use the localized modulus on `A` first, then add the monotone `B`
          -- pairing only as a nonnegative correction.
          simpa [sub_eq_add_neg] using hφ.ineq (hz_memS n) hpS (hAz n) hpA
        have hBpair : 0 ≤ ⟪z n - p, Bf (z n) - Bf p⟫_ℝ := by
          exact (SetValuedOperator.isMonotone_iff B).1 hB_mono (hBz n) hpB
        have hu_split :
            u n =
              ((γ : ℝ)⁻¹ • (y n - z n) + Bf p) +
                (Bf (z n) - Bf p) := by
          calc
            u n =
                (γ : ℝ)⁻¹ • (y n - z n) + Bf (z n) := by
                  simpa [u, x, y, z] using
                    tsengAuxiliaryVector_eq (JγA := JγA) (Bf := Bf) (C := C) hC γ x0 n
            _ = ((γ : ℝ)⁻¹ • (y n - z n) + Bf p) + (Bf (z n) - Bf p) := by
                  abel_nf
        have hcore_le :
            (⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n) + Bf p⟫_ℝ : EReal) ≤
              (⟪z n - p, u n⟫_ℝ : EReal) := by
          have hcore_le_real :
              ⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n) + Bf p⟫_ℝ ≤
                ⟪z n - p, u n⟫_ℝ := by
            have hinner_split :
                ⟪z n - p, u n⟫_ℝ =
                  ⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n)⟫_ℝ +
                    ⟪z n - p, Bf p⟫_ℝ +
                      ⟪z n - p, Bf (z n) - Bf p⟫_ℝ := by
              rw [hu_split, inner_add_right, inner_add_right]
            calc
              ⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n) + Bf p⟫_ℝ
                  = ⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n)⟫_ℝ +
                      ⟪z n - p, Bf p⟫_ℝ := by
                        rw [inner_add_right]
              _ ≤ ⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n)⟫_ℝ +
                    ⟪z n - p, Bf p⟫_ℝ +
                      ⟪z n - p, Bf (z n) - Bf p⟫_ℝ := by
                        linarith
              _ = ⟪z n - p, u n⟫_ℝ := by
                    rw [hinner_split]
          exact_mod_cast hcore_le_real
        exact le_trans hAineq hcore_le
      exact tendsto_of_inner_ge_modulus_of_bounded_of_tendsto_zero
        hz_bounded hu_tendsto hφ.monotone hφ.modulus_eq_zero_iff hineq_seq
    · rcases hUniformB S hS_nonempty hS_bounded hS_subA with ⟨φ, hφ⟩
      have hineq_seq :
          ∀ n, φ ‖z n - p‖₊ ≤ (⟪z n - p, u n⟫_ℝ : EReal) := by
        intro n
        have hBineq :
            φ ‖z n - p‖₊ ≤ (⟪z n - p, Bf (z n) - Bf p⟫_ℝ : EReal) := by
          simpa using hφ.ineq (hz_memS n) hpS (hBz n) hpB
        have hApair : 0 ≤ ⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n) - (-Bf p)⟫_ℝ := by
          exact (SetValuedOperator.isMonotone_iff A).1 (SetValuedOperator.Maximal.isMonotone hA_max)
            (hAz n) hpA
        have hu_split :
            u n =
              (Bf (z n) - Bf p) +
                ((γ : ℝ)⁻¹ • (y n - z n) - (-Bf p)) := by
          calc
            u n =
                (γ : ℝ)⁻¹ • (y n - z n) + Bf (z n) := by
                  simpa [u, x, y, z] using
                    tsengAuxiliaryVector_eq (JγA := JγA) (Bf := Bf) (C := C) hC γ x0 n
            _ = (Bf (z n) - Bf p) + ((γ : ℝ)⁻¹ • (y n - z n) - (-Bf p)) := by
                  abel_nf
        have hcore_le :
            (⟪z n - p, Bf (z n) - Bf p⟫_ℝ : EReal) ≤
              (⟪z n - p, u n⟫_ℝ : EReal) := by
          have hcore_le_real :
              ⟪z n - p, Bf (z n) - Bf p⟫_ℝ ≤ ⟪z n - p, u n⟫_ℝ := by
            calc
              ⟪z n - p, Bf (z n) - Bf p⟫_ℝ
                  ≤ ⟪z n - p, Bf (z n) - Bf p⟫_ℝ +
                      ⟪z n - p, (γ : ℝ)⁻¹ • (y n - z n) - (-Bf p)⟫_ℝ := by
                        linarith
              _ = ⟪z n - p, u n⟫_ℝ := by
                    rw [hu_split, inner_add_right]
          exact_mod_cast hcore_le_real
        exact le_trans hBineq hcore_le
      exact tendsto_of_inner_ge_modulus_of_bounded_of_tendsto_zero
        hz_bounded hu_tendsto hφ.monotone hφ.modulus_eq_zero_iff hineq_seq
  have hx_tendsto : Tendsto x atTop (𝓝 p) := by
    have hsum_tendsto :
        Tendsto (fun n ↦ (x n - z n) + z n) atTop (𝓝 ((0 : H) + p)) :=
      hsub_tendsto.add hz_tendsto
    have hsplit : (fun n ↦ (x n - z n) + z n) = x := by
      funext n
      abel_nf
    simpa [hsplit] using hsum_tendsto
  have hzeros_singleton : C ∩ (A + B).zeros = ({p} : Set H) := by
    ext q
    constructor
    · intro hq
      have hqD : q ∈ D := hC_sub hq.1
      have hqB : Bf q ∈ B q :=
        tsengRepresentative_mem (B := B) (Bf := Bf) (D := D) hB_eq hqD
      have hqA : -Bf q ∈ A q :=
        tsengNegRepresentative_mem_left_of_mem_zero
          (A := A) (B := B) (Bf := Bf) (D := D) hB_eq hqD hq.2
      have hqp : q = p := by
        rcases hUniform with hUniformA | hUniformB
        · let Sq : Set H := insert p ({q} : Set H)
          have hpSq : p ∈ Sq := by simp [Sq]
          have hqSq : q ∈ Sq := by simp [Sq]
          have hSq_nonempty : Sq.Nonempty := ⟨p, hpSq⟩
          have hSq_bounded : Bornology.IsBounded Sq := by
            exact ((Set.finite_singleton q).insert p).isBounded
          have hSq_subA : Sq ⊆ A.dom := by
            intro r hr
            have hr' : r = p ∨ r = q := by
              simpa [Sq, Set.mem_insert_iff] using hr
            rcases hr' with hreq | hreq
            · cases hreq
              exact ⟨-Bf p, hpA⟩
            · cases hreq
              exact ⟨-Bf q, hqA⟩
          rcases hUniformA Sq hSq_nonempty hSq_bounded hSq_subA with ⟨φ, hφ⟩
          have hAineq :
              φ ‖q - p‖₊ ≤ (⟪q - p, (-Bf q) - (-Bf p)⟫_ℝ : EReal) := by
            simpa using hφ.ineq hqSq hpSq hqA hpA
          have hBpair : 0 ≤ ⟪q - p, Bf q - Bf p⟫_ℝ := by
            exact (SetValuedOperator.isMonotone_iff B).1 hB_mono hqB hpB
          have hupper :
              (⟪q - p, (-Bf q) - (-Bf p)⟫_ℝ : EReal) ≤ 0 := by
            have hupper_real : ⟪q - p, (-Bf q) - (-Bf p)⟫_ℝ ≤ 0 := by
              have hneg :
                  ⟪q - p, (-Bf q) - (-Bf p)⟫_ℝ =
                    -⟪q - p, Bf q - Bf p⟫_ℝ := by
                have hterm : (-Bf q) - (-Bf p) = -(Bf q - Bf p) := by
                  abel_nf
                rw [hterm, inner_neg_right]
              rw [hneg]
              exact neg_nonpos.mpr hBpair
            exact_mod_cast hupper_real
          exact eq_of_modulus_le_zero hφ.monotone hφ.modulus_eq_zero_iff (le_trans hAineq hupper)
        · let Sq : Set H := insert p ({q} : Set H)
          have hpSq : p ∈ Sq := by simp [Sq]
          have hqSq : q ∈ Sq := by simp [Sq]
          have hSq_nonempty : Sq.Nonempty := ⟨p, hpSq⟩
          have hSq_bounded : Bornology.IsBounded Sq := by
            exact ((Set.finite_singleton q).insert p).isBounded
          have hSq_subA : Sq ⊆ A.dom := by
            intro r hr
            have hr' : r = p ∨ r = q := by
              simpa [Sq, Set.mem_insert_iff] using hr
            rcases hr' with hreq | hreq
            · cases hreq
              exact ⟨-Bf p, hpA⟩
            · cases hreq
              exact ⟨-Bf q, hqA⟩
          rcases hUniformB Sq hSq_nonempty hSq_bounded hSq_subA with ⟨φ, hφ⟩
          have hBineq :
              φ ‖q - p‖₊ ≤ (⟪q - p, Bf q - Bf p⟫_ℝ : EReal) := by
            simpa using hφ.ineq hqSq hpSq hqB hpB
          have hApair : 0 ≤ ⟪q - p, (-Bf q) - (-Bf p)⟫_ℝ := by
            exact (SetValuedOperator.isMonotone_iff A).1
              (SetValuedOperator.Maximal.isMonotone hA_max) hqA hpA
          have hupper :
              (⟪q - p, Bf q - Bf p⟫_ℝ : EReal) ≤ 0 := by
            have hupper_real : ⟪q - p, Bf q - Bf p⟫_ℝ ≤ 0 := by
              have hneg :
                  ⟪q - p, (-Bf q) - (-Bf p)⟫_ℝ =
                    -⟪q - p, Bf q - Bf p⟫_ℝ := by
                have hterm : (-Bf q) - (-Bf p) = -(Bf q - Bf p) := by
                  abel_nf
                rw [hterm, inner_neg_right]
              nlinarith [hApair]
            exact_mod_cast hupper_real
          exact eq_of_modulus_le_zero hφ.monotone hφ.modulus_eq_zero_iff (le_trans hBineq hupper)
      simp [hqp]
    · intro hq
      rw [Set.mem_singleton_iff] at hq
      simpa [hq] using hp
  exact ⟨p, hp, by simpa [hC, x] using hx_tendsto, by simpa [hC, z] using hz_tendsto,
    hzeros_singleton⟩

end TsengConvergence

end TsengAlgorithm

end

end SetValuedOperator
