import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap23.ResolventRealizer
import BauschkeLean.Chap04.Remark_4_15_1
import BauschkeLean.Chap20.Corollary_20_28
import BauschkeLean.Chap20.Proposition_20_10
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap21.Theorem_21_1

/- Source/core/bridge triage:
- `source-facing`: Corollary 23.11 concerns the resolvent and Yosida approximation of a maximally
  monotone operator.
- `core/canonical`: the Chapter 23 owners are the set-valued operators `J[((γ : ℝ) • A)]` and
  `{}^[γ] A`.
- `bridge/view`: explicit realizers `T : H → H` satisfying
  `T.toSetValuedOperator = J[((γ : ℝ) • A)]`, together with the induced residual and scaled
  residual maps. -/

open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

section Hilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Corollary 23.11: whole-space firm nonexpansiveness is the textbook inequality
`‖T x - T y‖² ≤ ⟪T x - T y, x - y⟫`. -/
private abbrev FirmlyNonexpansive (T : H → H) : Prop :=
  ∀ x y : H, ‖T x - T y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y)

omit [CompleteSpace H] in
/-- Helper for Corollary 23.11: unfold `FirmlyNonexpansive` to its whole-space inequality. -/
private theorem firmlyNonexpansive_iff_norm_sq_le_inner {T : H → H} :
    FirmlyNonexpansive T ↔
      ∀ x y : H, ‖T x - T y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y) := by
  rfl

omit [CompleteSpace H] in
private theorem continuous_of_firmlyNonexpansive {T : H → H} (hT : FirmlyNonexpansive T) :
    Continuous T := by
  let S : Set.univ → H := fun x ↦ T x.1
  -- Firm nonexpansiveness is the `1`-cocoercive inequality on `Set.univ`.
  have hcoco : CocoerciveOn (1 : ℝ) (Set.univ : Set H) S := by
    refine ⟨by norm_num, ?_⟩
    intro x y
    have hxy := (firmlyNonexpansive_iff_norm_sq_le_inner).1 hT (x : H) (y : H)
    simpa [S, one_mul, real_inner_comm] using hxy
  -- A cocoercive map is Lipschitz on `Set.univ`, and that lifts to the ambient self-map.
  have hlipUniv : LipschitzWith 1 S := by
    simpa [S] using lipschitzWith_of_cocoercive hcoco
  have hlip : LipschitzWith 1 T := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    simpa [S, Subtype.dist_eq, dist_eq_norm, one_mul] using
      hlipUniv.dist_le_mul ⟨x, by simp⟩ ⟨y, by simp⟩
  exact hlip.continuous

omit [CompleteSpace H] in
private theorem toSetValuedOperator_isMonotone_of_firmlyNonexpansive {T : H → H}
    (hT : FirmlyNonexpansive T) :
    T.toSetValuedOperator.IsMonotone := by
  rw [SetValuedOperator.isMonotone_iff]
  intro x u y v hu hv
  rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hu hv
  subst u v
  have hxy := (firmlyNonexpansive_iff_norm_sq_le_inner).1 hT x y
  exact le_trans (sq_nonneg ‖T x - T y‖) (by simpa [real_inner_comm] using hxy)

omit [CompleteSpace H] in
private theorem toSetValuedOperator_isMaximallyMonotone_of_firmlyNonexpansive {T : H → H}
    (hT : FirmlyNonexpansive T) :
    Maximal IsMonotone T.toSetValuedOperator := by
  have hmono : T.toSetValuedOperator.IsMonotone :=
    toSetValuedOperator_isMonotone_of_firmlyNonexpansive hT
  exact Function.toSetValuedOperator_isMaximallyMonotone_of_monotone_continuous
    T hmono (continuous_of_firmlyNonexpansive hT)

omit [CompleteSpace H] in
/-- Helper for Corollary 23.11: a realizer of `J[((γ : ℝ) • A)]` yields the corresponding graph
point of `A`. -/
private theorem resolventRealizer_mem_graph_of_toSetValuedOperator_eq
    (A : SetValuedOperator H H) (γ : PosReal) (T : H → H)
    (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) (x : H) :
    (T x, (γ : ℝ)⁻¹ • (x - T x)) ∈ gra A := by
  -- Rewrite the singleton-valued realizer hypothesis into pointwise resolvent membership.
  have hx : T x ∈ J[((γ : ℝ) • A)] x := by
    rw [← hT, Function.toSetValuedOperator_apply]
    simp
  -- Proposition 23.2 turns resolvent membership into the canonical graph condition.
  simpa [mem_graph, smul_sub] using (mem_resolvent_smul_iff_mem_graph A γ x (T x)).1 hx

omit [CompleteSpace H] in
/-- Helper for Corollary 23.11: monotonicity of `A` makes the resolvent residual cross term
nonnegative. -/
private theorem resolventRealizer_residualInner_nonneg_of_toSetValuedOperator_eq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) (T : H → H)
    (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) (x y : H) :
    0 ≤
      ⟪T x - T y,
        ((γ : ℝ)⁻¹ • (x - T x)) - ((γ : ℝ)⁻¹ • (y - T y))⟫_ℝ := by
  have hx_graph := resolventRealizer_mem_graph_of_toSetValuedOperator_eq A γ T hT x
  have hy_graph := resolventRealizer_mem_graph_of_toSetValuedOperator_eq A γ T hT y
  -- Apply monotonicity to the two graph points produced by the resolvent characterization.
  exact (isMonotone_iff A).1 hA.1 hx_graph hy_graph

omit [CompleteSpace H] in
/-- Corollary 23.11 (1): if `A : H → 2^H` is maximally monotone and `γ ∈ ℝ_{++}`, then every
single-valued realization `T` of `J[((γ : ℝ) • A)]` is firmly nonexpansive. -/
theorem resolvent_smul_firmlyNonexpansive_of_toSetValuedOperator_eq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal)
    (T : H → H) (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) :
    FirmlyNonexpansive T := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  -- Route correction: prove firm nonexpansiveness directly from the resolvent graph criterion,
  -- instead of importing the stale Proposition 23.10 wrapper route.
  have hcross :
      0 ≤
        ⟪T x - T y,
          ((γ : ℝ)⁻¹ • (x - T x)) - ((γ : ℝ)⁻¹ • (y - T y))⟫_ℝ :=
    resolventRealizer_residualInner_nonneg_of_toSetValuedOperator_eq A hA γ T hT x y
  -- Remove the positive scalar `(γ : ℝ)⁻¹` from the residual term.
  have hscaledCross : 0 ≤ ⟪T x - T y, (x - T x) - (y - T y)⟫_ℝ := by
    have hγinv_pos : 0 < (γ : ℝ)⁻¹ := inv_pos.mpr γ.2
    rw [← smul_sub, real_inner_smul_right] at hcross
    exact nonneg_of_mul_nonneg_right hcross hγinv_pos
  -- Decompose `x - y` into the resolvent difference and the residual difference.
  have hdecomp : x - y = (T x - T y) + ((x - T x) - (y - T y)) := by
    abel
  -- Rewrite the target inner product as the norm square plus the nonnegative cross term.
  have hinner :
      ⟪T x - T y, x - y⟫_ℝ =
        ‖T x - T y‖ ^ 2 + ⟪T x - T y, (x - T x) - (y - T y)⟫_ℝ := by
    rw [hdecomp, inner_add_right, real_inner_self_eq_norm_sq]
  nlinarith [hscaledCross, hinner]

omit [CompleteSpace H] in
/-- Corollary 23.11 (2): if `A : H → 2^H` is maximally monotone and `γ ∈ ℝ_{++}`, then for every
single-valued realization `T` of `J[((γ : ℝ) • A)]`, the residual map `x ↦ x - T x` is firmly
nonexpansive. -/
theorem residual_resolvent_smul_firmlyNonexpansive_of_toSetValuedOperator_eq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal)
    (T : H → H) (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) :
    FirmlyNonexpansive (fun x : H ↦ x - T x) := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  -- Start from the firm inequality for the resolvent realizer itself.
  have hTxy :=
    (firmlyNonexpansive_iff_norm_sq_le_inner).1
      (resolvent_smul_firmlyNonexpansive_of_toSetValuedOperator_eq A hA γ T hT) x y
  let a : H := x - y
  let b : H := T x - T y
  have hTxy' : ‖b‖ ^ 2 ≤ inner ℝ a b := by
    simpa [a, b, real_inner_comm] using hTxy
  have hTxy'' : ‖b‖ ^ 2 ≤ inner ℝ b a := by
    simpa [real_inner_comm] using hTxy'
  have hres :
      ‖a - b‖ ^ 2 ≤ inner ℝ (a - b) a := by
    have hinner : inner ℝ (a - b) a = ‖a‖ ^ 2 - inner ℝ b a := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
    -- Rearranging the quadratic identity leaves exactly the given firm inequality for `T`.
    calc
      ‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * ⟪a, b⟫_ℝ + ‖b‖ ^ 2 := norm_sub_sq_real a b
      _ ≤ ‖a‖ ^ 2 - 2 * ⟪a, b⟫_ℝ + ⟪b, a⟫_ℝ := by
            gcongr
      _ = ‖a‖ ^ 2 - ⟪b, a⟫_ℝ := by
            rw [real_inner_comm]
            ring
      _ = inner ℝ (a - b) a := by rw [hinner]
  -- The residual difference is exactly `a - b`.
  have hdiff : x - T x - (y - T y) = a - b := by
    dsimp [a, b]
    abel_nf
  simpa [a, hdiff] using hres

omit [CompleteSpace H] in
/-- Corollary 23.11 (3): if `A : H → 2^H` is maximally monotone and `γ ∈ ℝ_{++}`, then for every
single-valued realization `T` of `J[((γ : ℝ) • A)]`, the reflected resolvent
`x ↦ (2 : ℝ) • T x - x` is nonexpansive. -/
theorem reflected_resolvent_smul_nonexpansive_of_toSetValuedOperator_eq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal)
    (T : H → H) (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) :
    LipschitzWith 1 (fun x : H ↦ (2 : ℝ) • T x - x) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  -- Rewrite the reflector in terms of the resolvent difference `b` and the ambient difference `a`.
  have hTxy :=
    (firmlyNonexpansive_iff_norm_sq_le_inner).1
      (resolvent_smul_firmlyNonexpansive_of_toSetValuedOperator_eq A hA γ T hT) x y
  let a : H := x - y
  let b : H := T x - T y
  have hTxy' : ‖b‖ ^ 2 ≤ inner ℝ a b := by
    simpa [a, b, real_inner_comm] using hTxy
  have hsq :
      ‖a - (2 : ℝ) • b‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    have hinner :
        inner ℝ a ((2 : ℝ) • b) = 2 * inner ℝ a b := by
      rw [real_inner_smul_right]
    have hnorm :
        ‖(2 : ℝ) • b‖ ^ 2 = 4 * ‖b‖ ^ 2 := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), pow_two]
      ring
    have hscaled :
        ‖(2 : ℝ) • b‖ ^ 2 ≤ 2 * inner ℝ a ((2 : ℝ) • b) := by
      rw [hnorm, hinner]
      nlinarith [hTxy']
    -- The reflected norm gap is controlled by the same firm inequality.
    nlinarith [norm_sub_sq_real a ((2 : ℝ) • b), hscaled]
  have hreflect :
      ‖(2 : ℝ) • b - a‖ ≤ ‖a‖ := by
    have hsq' : ‖(2 : ℝ) • b - a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      simpa [norm_sub_rev] using hsq
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq'
  have hreflectDiff : (2 : ℝ) • T x - x - ((2 : ℝ) • T y - y) = (2 : ℝ) • b - a := by
    calc
      (2 : ℝ) • T x - x - ((2 : ℝ) • T y - y)
          = ((2 : ℝ) • T x - (2 : ℝ) • T y) - (x - y) := by
              abel_nf
      _ = (2 : ℝ) • (T x - T y) - (x - y) := by rw [smul_sub]
      _ = (2 : ℝ) • b - a := by simp [a, b]
  simpa [dist_eq_norm, a, hreflectDiff, one_mul] using hreflect

omit [CompleteSpace H] in
/-- Corollary 23.11 (4): if `A : H → 2^H` is maximally monotone and `γ ∈ ℝ_{++}`, then for every
single-valued realization `T` of `J[((γ : ℝ) • A)]`, the induced Yosida realizer
`x ↦ (γ : ℝ)⁻¹ • (x - T x)` is `γ`-cocoercive on `H`. -/
theorem yosidaApproximation_cocoercive_of_toSetValuedOperator_eq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal)
    (T : H → H) (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) :
    CocoerciveOn (γ : ℝ) (Set.univ : Set H)
      (fun x ↦ (γ : ℝ)⁻¹ • (x - T x)) := by
  refine ⟨γ.2, ?_⟩
  intro x y
  -- The residual map is firmly nonexpansive, hence satisfies the textbook inner-product bound.
  have hResidual :=
    (firmlyNonexpansive_iff_norm_sq_le_inner).1
      (residual_resolvent_smul_firmlyNonexpansive_of_toSetValuedOperator_eq A hA γ T hT)
      (x : H) (y : H)
  let r : H := ((x : H) - T x) - (y - T y)
  have hResidual' : ‖r‖ ^ 2 ≤ inner ℝ ((x : H) - y) r := by
    simpa [r, real_inner_comm] using hResidual
  have hscaledResidual :
      (γ : ℝ) * ‖(((γ : ℝ)⁻¹ : ℝ) • r)‖ ^ 2 ≤
        inner ℝ ((x : H) - y) (((γ : ℝ)⁻¹ : ℝ) • r) := by
    calc
      (γ : ℝ) * ‖(((γ : ℝ)⁻¹ : ℝ) • r)‖ ^ 2
          = ((γ : ℝ)⁻¹ : ℝ) * ‖r‖ ^ 2 := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr γ.2.le), pow_two]
              field_simp [γ.2.ne']
      _ ≤ ((γ : ℝ)⁻¹ : ℝ) * inner ℝ ((x : H) - y) r := by
            exact mul_le_mul_of_nonneg_left hResidual' (inv_nonneg.mpr γ.2.le)
      _ = inner ℝ ((x : H) - y) (((γ : ℝ)⁻¹ : ℝ) • r) := by
            rw [real_inner_smul_right]
  -- Rewrite the Yosida difference as the scaled residual difference.
  simpa [r, smul_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hscaledResidual

/-- Corollary 23.11 (5): if `A : H → 2^H` is maximally monotone and `γ ∈ ℝ_{++}`, then the
resolvent `J[((γ : ℝ) • A)]` is maximally monotone. -/
theorem resolvent_smul_isMaximallyMonotone
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) :
    Maximal IsMonotone J[((γ : ℝ) • A)] := by
  let T : H → H := resolventMap A hA γ
  have hmax : Maximal IsMonotone T.toSetValuedOperator :=
    toSetValuedOperator_isMaximallyMonotone_of_firmlyNonexpansive
      (resolvent_smul_firmlyNonexpansive_of_toSetValuedOperator_eq
        A hA γ T (resolventMap_toSetValuedOperator_eq A hA γ))
  simpa [T, resolventMap_toSetValuedOperator_eq A hA γ] using hmax

/-- Companion bridge: every single-valued realization `T` of `J[((γ : ℝ) • A)]` induces the same
maximally monotone singleton-valued operator surface. -/
theorem resolvent_smul_isMaximallyMonotone_of_toSetValuedOperator_eq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal)
    (T : H → H) (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) :
    Maximal IsMonotone T.toSetValuedOperator := by
  simpa [hT] using resolvent_smul_isMaximallyMonotone A hA γ

/-- Corollary 23.11 (6): if `A : H → 2^H` is maximally monotone and `γ ∈ ℝ_{++}`, then the scaled
Yosida approximation `(γ : ℝ) • {}^[γ] A`, equivalently `Id - J[((γ : ℝ) • A)]`, is maximally
monotone. -/
theorem smul_yosidaApproximation_isMaximallyMonotone
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) :
    Maximal IsMonotone ((γ : ℝ) • {}^[γ] A) := by
  let T : H → H := resolventMap A hA γ
  have hmax :
      Maximal IsMonotone (fun x : H ↦ x - T x).toSetValuedOperator :=
    toSetValuedOperator_isMaximallyMonotone_of_firmlyNonexpansive
      (residual_resolvent_smul_firmlyNonexpansive_of_toSetValuedOperator_eq
        A hA γ T (resolventMap_toSetValuedOperator_eq A hA γ))
  simpa [T, residual_toSetValuedOperator_eq_smul_yosidaApproximation A γ T
    (resolventMap_toSetValuedOperator_eq A hA γ)] using hmax

/-- Companion bridge: for every single-valued realization `T` of `J[((γ : ℝ) • A)]`, the
singleton-valued operator induced by the residual map `x ↦ x - T x` is maximally monotone. -/
theorem residual_resolvent_smul_isMaximallyMonotone_of_toSetValuedOperator_eq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal)
    (T : H → H) (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) :
    Maximal IsMonotone (fun x : H ↦ x - T x).toSetValuedOperator := by
  simpa [residual_toSetValuedOperator_eq_smul_yosidaApproximation A γ T hT] using
    smul_yosidaApproximation_isMaximallyMonotone A hA γ

/-- Corollary 23.11 (7): if `A : H → 2^H` is maximally monotone and `γ ∈ ℝ_{++}`, then the
Yosida approximation `{}^[γ] A` is maximally monotone. -/
theorem yosidaApproximation_isMaximallyMonotone
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) :
    Maximal IsMonotone ({}^[γ] A) := by
  let γinv : PosReal := ⟨((γ : ℝ)⁻¹ : ℝ), inv_pos.mpr γ.2⟩
  have hmax :
      Maximal IsMonotone ((γinv : ℝ) • ((γ : ℝ) • ({}^[γ] A))) :=
    maximal_isMonotone_smul (smul_yosidaApproximation_isMaximallyMonotone A hA γ) γinv
  rw [smul_smul] at hmax
  have hscalar : ((γinv : ℝ) * (γ : ℝ)) = 1 := by
    dsimp [γinv]
    rw [inv_mul_cancel₀ γ.2.ne']
  simpa [hscalar] using hmax

/-- Companion bridge: for every single-valued realization `T` of `J[((γ : ℝ) • A)]`, the
singleton-valued operator induced by the Yosida realizer `x ↦ (γ : ℝ)⁻¹ • (x - T x)` is maximally
monotone. -/
theorem yosidaApproximation_isMaximallyMonotone_of_toSetValuedOperator_eq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal)
    (T : H → H) (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) :
    Maximal IsMonotone
      (fun x : H ↦ (((γ : ℝ)⁻¹ : ℝ) • (x - T x))).toSetValuedOperator := by
  simpa [scaledResidual_toSetValuedOperator_eq_yosidaApproximation A γ T hT] using
    yosidaApproximation_isMaximallyMonotone A hA γ

omit [CompleteSpace H] in
/-- Corollary 23.11 (8): if `A : H → 2^H` is maximally monotone and `γ ∈ ℝ_{++}`, then for every
single-valued realization `T` of `J[((γ : ℝ) • A)]`, the induced Yosida realizer
`x ↦ (γ : ℝ)⁻¹ • (x - T x)` is `γ⁻¹`-Lipschitz continuous. -/
theorem yosidaApproximation_lipschitzWith_inv_of_toSetValuedOperator_eq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal)
    (T : H → H) (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) :
    LipschitzWith (Real.toNNReal ((γ : ℝ)⁻¹)) (fun x : H ↦ (γ : ℝ)⁻¹ • (x - T x)) := by
  have hlip :
      LipschitzWith (Real.toNNReal ((γ : ℝ)⁻¹))
        (fun x : (Set.univ : Set H) ↦ (γ : ℝ)⁻¹ • ((x : H) - T (x : H))) := by
    simpa [one_div] using
      lipschitzWith_of_cocoercive
        (yosidaApproximation_cocoercive_of_toSetValuedOperator_eq A hA γ T hT)
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using
    hlip.dist_le_mul ⟨x, by simp⟩ ⟨y, by simp⟩

end Hilbert

end SetValuedOperator
