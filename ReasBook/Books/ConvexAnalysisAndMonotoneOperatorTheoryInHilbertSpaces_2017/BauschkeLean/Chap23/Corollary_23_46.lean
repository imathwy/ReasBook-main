import BauschkeLean.Chap23.Proposition_23_43
import BauschkeLean.Chap23.Theorem_23_44

-- Semantic recall note: `lean_leansearch` surfaced only generic logical `Xor'` lemmas, not the
-- Chapter 23 Yosida asymptotic surface, so this item follows the verified local owner
-- `yosidaApproximationMap A hA γ`, the least-norm owner `minimalNormValue`, and the
-- `γ ↓ 0` filter from Theorem 23.44.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 23.46 records the small-parameter asymptotics of the canonical
  Yosida values `{}^[γ] A x`.
- `core/canonical`: the chapter-level owners are `yosidaApproximationMap A hA γ x`,
  `atZeroRightWithinUnitInterval`, and the least-norm value `A⁰[hA, hx]`.
- `bridge/view`: the bundled source clauses in parts (2) and (3) also expose standalone monotonicity
  and limit companions for downstream reuse. -/

/-- Helper for Corollary 23.46: the translated inverse operator `(A⁻¹).addConst (-x)` is
maximally monotone whenever `A` is maximally monotone. -/
private theorem inverseAddConst_isMaximal
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x : H) :
    Maximal IsMonotone ((A⁻¹).addConst (-x)) := by
  -- Transport maximality through inverse, translation by `0`, and output translation by `-x`.
  have htranslate :
      Maximal IsMonotone (((A⁻¹).translate 0).addConst (-x)) := by
    simpa [SetValuedOperator.addConst_eq_const_toSetValuedOperator_add] using
      (Maximal.output_translation_smul_input_translation (A := A⁻¹)
        (hA := Maximal.inverse hA) (z := 0) (u := -x)
        (γ := (show Set.Ioi (0 : ℝ) from ⟨1, by norm_num⟩)))
  -- The input translation by `0` is pointwise the original inverse operator.
  convert htranslate using 1
  ext y u
  simp [SetValuedOperator.translate_apply]

/-- Helper for Corollary 23.46: the zero set of `(A⁻¹).addConst (-x)` is exactly the value set
`A x`. -/
private theorem zeros_inverseAddConst_eq_value
    {A : SetValuedOperator H H} (x : H) :
    ((A⁻¹).addConst (-x)).zeros = A x := by
  ext u
  constructor
  · intro hu
    rw [SetValuedOperator.mem_zeros_iff, SetValuedOperator.mem_addConst_iff] at hu
    rcases hu with ⟨y, hy, hy_eq⟩
    have hyx : y = x := by
      calc
        y = x + (-x + y) := by
              abel_nf
        _ = x + 0 := by
              rw [← hy_eq]
        _ = x := by
              simp
    simpa [SetValuedOperator.mem_inverse_iff, hyx] using hy
  · intro hu
    rw [SetValuedOperator.mem_zeros_iff, SetValuedOperator.mem_addConst_iff]
    refine ⟨x, ?_, by simp⟩
    simpa [SetValuedOperator.mem_inverse_iff] using hu

/-- Helper for Corollary 23.46: the canonical Yosida value at `x` is the inverse-parameter
resolvent point of the translated inverse operator `(A⁻¹).addConst (-x)` at base point `0`. -/
private theorem yosidaApproximationMap_eq_inverseParameterResolventCurve_inverseAddConst
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x : H) (γ : PosReal) :
    yosidaApproximationMap A hA γ x =
      inverseParameterResolventCurve ((A⁻¹).addConst (-x))
        (inverseAddConst_isMaximal hA x) 0 γ := by
  let B : SetValuedOperator H H := (A⁻¹).addConst (-x)
  let u := yosidaApproximationMap A hA γ x
  have hB : Maximal IsMonotone B := by
    simpa [B] using inverseAddConst_isMaximal hA x
  have hu_mem : u ∈ ({}^[γ] A) x := by
    -- The chosen Yosida realizer is the singleton point in the canonical Yosida value.
    rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal A hA γ x]
    simp [u]
  have huA : u ∈ A (x - (γ : ℝ) • u) := by
    -- Normalize the Yosida membership to the translated graph form used in Proposition 23.7.
    exact (mem_yosidaApproximation_iff_mem A γ x u).1 hu_mem
  have huInv : x - (γ : ℝ) • u ∈ A⁻¹ u := by
    simpa [SetValuedOperator.mem_inverse_iff] using huA
  have huB : -((γ : ℝ) • u) ∈ B u := by
    -- Reinsert the output translation `-x` as the source witness inside `B u`.
    change -((γ : ℝ) • u) ∈ ((A⁻¹).addConst (-x)) u
    rw [SetValuedOperator.mem_addConst_iff]
    exact ⟨x - (γ : ℝ) • u, huInv, by abel_nf⟩
  have hzeroMem : 0 ∈ B u + ({(γ : ℝ) • (u - 0)} : Set H) := by
    -- The Yosida point satisfies the inverse-parameter resolvent inclusion for `B` at `0`.
    rw [Set.mem_add]
    refine ⟨-((γ : ℝ) • u), huB, (γ : ℝ) • (u - 0), by simp, ?_⟩
    simp
  have hu_res :
      u = resolventMap B hB γ⁻¹ 0 :=
    (resolventMap_isUnique_of_zero_mem_add_singleton_smul_sub B hB 0 γ u).1 hzeroMem
  -- Rewrite the unique resolvent point back to the inverse-parameter curve owner.
  simpa [B, inverseParameterResolventCurve_apply, u] using hu_res

/-- Helper for Corollary 23.46: the projection of `0` onto
`((A⁻¹).addConst (-x)).zeros = A x` is the least-norm value `A⁰[hA, hx]`. -/
private theorem projection_zero_inverseAddConst_eq_minimalNormValue
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom)
    (hB : Maximal IsMonotone ((A⁻¹).addConst (-x)))
    (hzero : ((A⁻¹).addConst (-x)).zeros.Nonempty) :
    P[((A⁻¹).addConst (-x)).zeros, Maximal.zeros_isChebyshev hB hzero] 0 = A⁰[hA, hx] := by
  -- Identify the projection target with `A x` and use the existing least-norm characterization.
  exact
    (eq_projectionPoint_of_isBestApproximation ((A⁻¹).addConst (-x)).zeros
      (Maximal.zeros_isChebyshev hB hzero)
      (by
        simpa [zeros_inverseAddConst_eq_value] using
          (minimalNormValue_isBestApproximation_zero_of_maximal_of_mem_dom hA hx))).symm

/-- Helper for Corollary 23.46: increasing the Yosida parameter decreases the norm of the
canonical Yosida value at a fixed point `x`. -/
private theorem norm_yosidaApproximationMap_le_of_le_parameter
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x : H) {γ μ : PosReal}
    (hγμ : γ ≤ μ) :
    ‖yosidaApproximationMap A hA μ x‖ ≤ ‖yosidaApproximationMap A hA γ x‖ := by
  rcases lt_or_eq_of_le hγμ with hlt | rfl
  · let uγ := yosidaApproximationMap A hA γ x
    let uμ := yosidaApproximationMap A hA μ x
    have huγ_mem : uγ ∈ ({}^[γ] A) x := by
      -- Each chosen realizer is the singleton point in its own Yosida value.
      rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal A hA γ x]
      simp [uγ]
    have huμ_mem : uμ ∈ ({}^[μ] A) x := by
      rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal A hA μ x]
      simp [uμ]
    have hgraphγ : (x - (γ : ℝ) • uγ, uγ) ∈ gra A :=
      (mem_yosidaApproximation_iff_mem_graph A γ x uγ).1 huγ_mem
    have hgraphμ : (x - (μ : ℝ) • uμ, uμ) ∈ gra A :=
      (mem_yosidaApproximation_iff_mem_graph A μ x uμ).1 huμ_mem
    have hmono :
        0 ≤ inner ℝ ((x - (γ : ℝ) • uγ) - (x - (μ : ℝ) • uμ)) (uγ - uμ) :=
      (isMonotone_iff A).1 hA.1 hgraphγ hgraphμ
    have hrewrite :
        inner ℝ ((x - (γ : ℝ) • uγ) - (x - (μ : ℝ) • uμ)) (uγ - uμ) =
          ((μ : ℝ) - (γ : ℝ)) * inner ℝ uμ (uγ - uμ) -
            (γ : ℝ) * ‖uγ - uμ‖ ^ 2 := by
      have hsub :
          ((x - (γ : ℝ) • uγ) - (x - (μ : ℝ) • uμ)) =
            (μ : ℝ) • uμ - (γ : ℝ) • uγ := by
        abel_nf
      have hsplit :
          inner ℝ uγ (uγ - uμ) =
            inner ℝ uμ (uγ - uμ) + ‖uγ - uμ‖ ^ 2 := by
        have huγ_eq : uγ = uμ + (uγ - uμ) := by
          abel_nf
        calc
          inner ℝ uγ (uγ - uμ) = inner ℝ (uμ + (uγ - uμ)) (uγ - uμ) := by
            -- Rewrite only the first argument of the inner product to avoid changing the
            -- difference term at the same time.
            exact congrArg (fun t : H ↦ inner ℝ t (uγ - uμ)) huγ_eq
          _ = inner ℝ uμ (uγ - uμ) + inner ℝ (uγ - uμ) (uγ - uμ) := by
            rw [inner_add_left]
          _ = inner ℝ uμ (uγ - uμ) + ‖uγ - uμ‖ ^ 2 := by
            rw [real_inner_self_eq_norm_sq]
      rw [hsub, inner_sub_left, real_inner_smul_left, real_inner_smul_left, hsplit]
      ring
    have hmul_nonneg :
        0 ≤ ((μ : ℝ) - (γ : ℝ)) * inner ℝ uμ (uγ - uμ) := by
      rw [hrewrite] at hmono
      nlinarith [hmono, sq_nonneg ‖uγ - uμ‖, show 0 ≤ (γ : ℝ) by exact γ.2.le]
    have hinner_nonneg : 0 ≤ inner ℝ uμ (uγ - uμ) := by
      have hdiff_pos : 0 < (μ : ℝ) - (γ : ℝ) := sub_pos.mpr hlt
      nlinarith
    have hsq_le_inner : ‖uμ‖ ^ 2 ≤ inner ℝ uμ uγ := by
      have hsplit :
          inner ℝ uμ (uγ - uμ) = inner ℝ uμ uγ - ‖uμ‖ ^ 2 := by
        rw [inner_sub_right, real_inner_self_eq_norm_sq]
      rw [hsplit] at hinner_nonneg
      nlinarith
    have hsq_le_mul : ‖uμ‖ ^ 2 ≤ ‖uμ‖ * ‖uγ‖ := by
      exact le_trans hsq_le_inner (real_inner_le_norm _ _)
    let a := ‖uμ‖
    let b := ‖uγ‖
    change a ≤ b
    have hsq_le_mul' : a ^ 2 ≤ a * b := by
      simpa [a, b] using hsq_le_mul
    have ha_nonneg : 0 ≤ a := by
      simp [a]
    by_cases hzero : a = 0
    · simp [a, b, hzero]
    · have hpos : 0 < a :=
        lt_of_le_of_ne ha_nonneg (by simpa [eq_comm] using hzero)
      have hmul : a * a ≤ a * b := by
        simpa [pow_two] using hsq_le_mul'
      exact le_of_mul_le_mul_left hmul hpos
  · simp

/-- Corollary 23.46 (1): if `A : H → 2^H` is maximally monotone and `x ∈ dom A`, then the
canonical Yosida values `{}^[γ] A x` converge to the least-norm value `{}^0 A x` as
`γ ↓ 0` through `]0,1[`. -/
theorem tendsto_yosidaApproximationMap_atZeroRight_to_minimalNormValue_of_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom) :
    Filter.Tendsto (fun γ : PosReal ↦ yosidaApproximationMap A hA γ x)
      atZeroRightWithinUnitInterval
      (nhds (A⁰[hA, hx])) := by
  let B : SetValuedOperator H H := (A⁻¹).addConst (-x)
  let hB : Maximal IsMonotone B := inverseAddConst_isMaximal hA x
  have hzero : B.zeros.Nonempty := by
    -- The translated inverse has a zero exactly when `A x` is nonempty.
    change ((A⁻¹).addConst (-x)).zeros.Nonempty
    rw [zeros_inverseAddConst_eq_value]
    exact (SetValuedOperator.mem_dom_iff A x).1 hx
  have hcurve :
      (fun γ : PosReal ↦ yosidaApproximationMap A hA γ x) =
        inverseParameterResolventCurve B hB 0 := by
    -- Rewrite the Yosida path pointwise to the inverse-parameter resolvent curve of `B`.
    funext γ
    simpa [B, hB] using
      yosidaApproximationMap_eq_inverseParameterResolventCurve_inverseAddConst hA x γ
  have hproj :
      P[B.zeros, Maximal.zeros_isChebyshev hB hzero] 0 = A⁰[hA, hx] := by
    -- The projection returned by Theorem 23.44 is the least-norm value in `A x`.
    simpa [B] using projection_zero_inverseAddConst_eq_minimalNormValue hA hx hB hzero
  have hresolvent :
      Filter.Tendsto (inverseParameterResolventCurve B hB 0)
        atZeroRightWithinUnitInterval
        (nhds (P[B.zeros, Maximal.zeros_isChebyshev hB hzero] 0)) :=
    tendsto_resolventMap_atZeroRight_of_zeros_nonempty B hB 0 hzero
  -- Transport Theorem 23.44 back along the translated-inverse bridge and rewrite the limit point.
  rw [hcurve]
  simpa [hproj] using hresolvent

/-- Corollary 23.46 (2): if `A : H → 2^H` is maximally monotone and `x ∈ dom A`, then as
`γ ↓ 0` through `]0,1[`, the norm path `‖{}^[γ] A x‖` is monotone increasing in the textbook
sense, formalized as antitone in the parameter `γ`, and it converges to `‖{}^0 A x‖`. -/
theorem antitoneOn_norm_yosidaApproximationMap_and_tendsto_atZeroRight_of_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom) :
    AntitoneOn
      (fun γ : PosReal ↦ ‖yosidaApproximationMap A hA γ x‖)
      (Set.Iio (1 : PosReal)) ∧
      Filter.Tendsto (fun γ : PosReal ↦ ‖yosidaApproximationMap A hA γ x‖)
        atZeroRightWithinUnitInterval
        (nhds ‖A⁰[hA, hx]‖) := by
  constructor
  · intro γ _ μ _ hγμ
    -- The norm path is antitone in the parameter because larger Yosida parameters shrink norms.
    exact norm_yosidaApproximationMap_le_of_le_parameter hA x hγμ
  · have hvec :=
      tendsto_yosidaApproximationMap_atZeroRight_to_minimalNormValue_of_mem_dom hA hx
    -- Apply continuity of the norm to the vector convergence from part (1).
    simpa using continuous_norm.continuousAt.tendsto.comp hvec

/-- Corollary 23.46 (2), monotonicity companion: for `x ∈ dom A`, the norm path
`γ ↦ ‖{}^[γ] A x‖` is monotone increasing in the textbook sense, formalized as antitone in
the parameter `γ ∈ ]0,1[`. -/
theorem antitoneOn_norm_yosidaApproximationMap_of_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom) :
    AntitoneOn
      (fun γ : PosReal ↦ ‖yosidaApproximationMap A hA γ x‖)
      (Set.Iio (1 : PosReal)) :=
  (antitoneOn_norm_yosidaApproximationMap_and_tendsto_atZeroRight_of_mem_dom hA hx).1

/-- Corollary 23.46 (2), limit companion: for `x ∈ dom A`, the norm path
`γ ↦ ‖{}^[γ] A x‖` converges to `‖{}^0 A x‖` as `γ ↓ 0` through `]0,1[`. -/
theorem tendsto_norm_yosidaApproximationMap_atZeroRight_to_norm_minimalNormValue_of_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∈ A.dom) :
    Filter.Tendsto (fun γ : PosReal ↦ ‖yosidaApproximationMap A hA γ x‖)
      atZeroRightWithinUnitInterval
      (nhds ‖A⁰[hA, hx]‖) :=
  (antitoneOn_norm_yosidaApproximationMap_and_tendsto_atZeroRight_of_mem_dom hA hx).2

/-- Corollary 23.46 (3): if `A : H → 2^H` is maximally monotone and `x ∉ dom A`, then as
`γ ↓ 0` through `]0,1[`, the norm path `‖{}^[γ] A x‖` is monotone increasing in the textbook
sense, formalized as antitone in the parameter `γ`, and it diverges to `+∞`. -/
theorem norm_yosidaApproximationMap_tendsto_atTop_atZeroRight_of_not_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∉ A.dom) :
    AntitoneOn
      (fun γ : PosReal ↦ ‖yosidaApproximationMap A hA γ x‖)
      (Set.Iio (1 : PosReal)) ∧
      Filter.Tendsto (fun γ : PosReal ↦ ‖yosidaApproximationMap A hA γ x‖)
        atZeroRightWithinUnitInterval
        Filter.atTop := by
  let B : SetValuedOperator H H := (A⁻¹).addConst (-x)
  let hB : Maximal IsMonotone B := inverseAddConst_isMaximal hA x
  have hzero : B.zeros = ∅ := by
    -- Empty domain means the translated inverse has no zeros.
    ext u
    constructor
    · intro hu
      exfalso
      apply hx
      refine (SetValuedOperator.mem_dom_iff A x).2 ?_
      refine ⟨u, ?_⟩
      simpa [B, zeros_inverseAddConst_eq_value] using hu
    · intro hu
      simp at hu
  have hcurve :
      (fun γ : PosReal ↦ ‖yosidaApproximationMap A hA γ x‖) =
        fun γ : PosReal ↦ ‖inverseParameterResolventCurve B hB 0 γ‖ := by
    -- Rewrite the norm path pointwise to the translated-inverse resolvent norm path.
    funext γ
    simpa [B, hB] using congrArg norm
      (yosidaApproximationMap_eq_inverseParameterResolventCurve_inverseAddConst hA x γ)
  constructor
  · intro γ _ μ _ hγμ
    -- The parameter-antitone comparison is independent of whether `x` lies in the domain.
    exact norm_yosidaApproximationMap_le_of_le_parameter hA x hγμ
  · have hresolvent :
        Filter.Tendsto (fun γ : PosReal ↦ ‖inverseParameterResolventCurve B hB 0 γ‖)
          atZeroRightWithinUnitInterval
          Filter.atTop :=
      norm_resolventMap_tendsto_atTop_atZeroRight_of_zeros_eq_empty B hB 0 hzero
    -- Transport Theorem 23.44(3) back along the same translated-inverse bridge.
    rw [hcurve]
    exact hresolvent

/-- Corollary 23.46 (3), monotonicity companion: for `x ∉ dom A`, the norm path
`γ ↦ ‖{}^[γ] A x‖` is monotone increasing in the textbook sense, formalized as antitone in
the parameter `γ ∈ ]0,1[`. -/
theorem antitoneOn_norm_yosidaApproximationMap_of_not_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∉ A.dom) :
    AntitoneOn
      (fun γ : PosReal ↦ ‖yosidaApproximationMap A hA γ x‖)
      (Set.Iio (1 : PosReal)) :=
  (norm_yosidaApproximationMap_tendsto_atTop_atZeroRight_of_not_mem_dom hA hx).1

/-- Corollary 23.46 (3), divergence companion: for `x ∉ dom A`, the norm path
`γ ↦ ‖{}^[γ] A x‖` tends to `+∞` as `γ ↓ 0` through `]0,1[`. -/
theorem tendsto_norm_yosidaApproximationMap_atTop_atZeroRight_of_not_mem_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x : H} (hx : x ∉ A.dom) :
    Filter.Tendsto (fun γ : PosReal ↦ ‖yosidaApproximationMap A hA γ x‖)
      atZeroRightWithinUnitInterval
      Filter.atTop :=
  (norm_yosidaApproximationMap_tendsto_atTop_atZeroRight_of_not_mem_dom hA hx).2

end SetValuedOperator
