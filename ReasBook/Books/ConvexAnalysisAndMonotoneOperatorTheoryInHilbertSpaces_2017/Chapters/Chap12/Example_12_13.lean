import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap09.Example_9_36
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.Example_12_2
import BauschkeLean.Chap12.Example_12_3
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Example_13_2

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

namespace ERealFunction

/-!
### Example 12.13

Set `f = reciprocalBarrier` and `g = ERealFunction.reverse reciprocalBarrier`, the source
reflection `f^∨`. The companion theorems below keep this source-facing owner pair fixed across
clauses (i)-(iii): `f, g ∈ Γ₀(ℝ)`, `f □ g = 0` with nowhere exactness, and the epigraph-indicator
reformulation whose Minkowski sum is the open upper half-plane. For the `Γ₀` and `ExactAt`
clauses, the same source owners are related to the local `]-∞,+∞]`-valued API by the explicit
bridge theorems below.
-/

-- Semantic recall note: `lean_leansearch` was unavailable for this item (timeout/502), so this
-- file keeps the existing local API (`reverse`, `epigraph`, `□`) rather than changing owner.

/-- Helper: the canonical `]-∞,+∞]`-valued representative of the source function
`f = reciprocalBarrier` is `inversePowerIoiExtension 1`. -/
private theorem positiveReciprocalBarrier_bridge :
    (inversePowerIoiExtension 1).asEReal = reciprocalBarrier := by
  -- Compare both source owners pointwise by the three sign cases of the real variable.
  funext x
  by_cases hx : 0 < x
  · -- On `(0, ∞)`, both functions are the same reciprocal formula.
    have h := inversePowerIoiExtension_apply_of_pos 1 hx
    simp [Function.asEReal_apply, reciprocalBarrier, hx] at h ⊢
  · have hx_nonpos : x ≤ 0 := le_of_not_gt hx
    by_cases hx_zero : x = 0
    · -- At `0`, both functions take the value `+∞`.
      subst hx_zero
      have h := inversePowerIoiExtension_apply_zero 1 (show 0 < (1 : ℝ) from zero_lt_one)
      simp [Function.asEReal_apply, reciprocalBarrier] at h ⊢
    · have hx_neg : x < 0 := lt_of_le_of_ne hx_nonpos hx_zero
      -- On `(-∞, 0)`, the canonical extension and the source owner are both `+∞`.
      simpa [Function.asEReal_apply, reciprocalBarrier, hx] using
        inversePowerIoiExtension_apply_of_neg 1 hx_neg

/-- Helper: reversing the canonical `]-∞,+∞]`-valued representative of `f` recovers the source
reflection `g = f^∨`. -/
private theorem positiveReciprocalBarrierReverse_bridge :
    (Function.reverse (inversePowerIoiExtension 1)).asEReal =
      ERealFunction.reverse reciprocalBarrier := by
  -- Reflection is just precomposition by negation on both the subtype and `EReal` owners.
  funext x
  simpa [Function.asEReal_apply, Function.reverse, ERealFunction.reverse_apply] using
    congrFun positiveReciprocalBarrier_bridge (-x)

-- Proof sketch: show that the canonical `]-∞,+∞]`-valued representative of the reciprocal
-- barrier is lower semicontinuous and convex on its effective domain `(0, ∞)`, and note that
-- reversing the argument gives the canonical representative of the source reflection `f^∨`,
-- which preserves the same two properties.
/-- Helper: the canonical `Γ₀(ℝ)` representatives of the source functions
`f = reciprocalBarrier` and `g = f^∨` both belong to `Γ₀(ℝ)`. -/
private theorem positiveReciprocalBarrier_mem_gammaZero_canonical :
    inversePowerIoiExtension 1 ∈ Γ₀(ℝ) ∧
      Function.reverse (inversePowerIoiExtension 1) ∈ Γ₀(ℝ) := by
  -- First use the canonical Chapter 9 reciprocal-barrier model.
  have hcanon : inversePowerIoiExtension 1 ∈ Γ₀(ℝ) :=
    inversePowerIoiExtension_mem_gammaZero 1 (by norm_num)
  refine ⟨hcanon, ?_⟩
  -- Then transport `Γ₀` membership through the continuous linear negation equivalence.
  simpa [Function.reverse, Function.comp] using
    mem_gammaZero_comp_continuousLinearEquiv hcanon (ContinuousLinearEquiv.neg ℝ)

theorem positiveReciprocalBarrier_isProper :
    IsProper reciprocalBarrier := by
  constructor
  · -- The source owner never takes the value `-∞`; it is either a real value or `+∞`.
    intro x
    by_cases hx : 0 < x
    · simp [reciprocalBarrier, hx]
    · simp [reciprocalBarrier, hx]
  · -- The point `x = 1` lies in the effective domain and gives the finite value `1`.
    refine ⟨1, ?_⟩
    simpa [reciprocalBarrier] using (EReal.coe_lt_top (1 : ℝ))

theorem positiveReciprocalBarrierReverse_isProper :
    IsProper (ERealFunction.reverse reciprocalBarrier) := by
  constructor
  · -- Reflection preserves the pointwise dichotomy "real value or `+∞`".
    intro x
    by_cases hx : 0 < -x
    · simp [ERealFunction.reverse_apply, reciprocalBarrier, hx]
    · simp [ERealFunction.reverse_apply, reciprocalBarrier, hx]
  · -- The reflected barrier is finite at `x = -1`.
    refine ⟨-1, ?_⟩
    simpa [ERealFunction.reverse_apply, reciprocalBarrier] using (EReal.coe_lt_top (1 : ℝ))

/-- Clause (i). After the canonical `properIoi` coercion of proper `EReal`-valued functions, the
source functions `f = reciprocalBarrier` and `g = f^∨` belong to `Γ₀(ℝ)`. -/
theorem positiveReciprocalBarrier_mem_gammaZero :
    properIoi reciprocalBarrier positiveReciprocalBarrier_isProper ∈ Γ₀(ℝ) ∧
      properIoi (ERealFunction.reverse reciprocalBarrier)
        positiveReciprocalBarrierReverse_isProper ∈ Γ₀(ℝ) := by
  -- Identify each source-facing `properIoi` owner with its canonical Chapter 9 representative.
  have hsource :
      properIoi reciprocalBarrier positiveReciprocalBarrier_isProper =
        inversePowerIoiExtension 1 := by
    funext x
    apply Subtype.ext
    calc
      ((properIoi reciprocalBarrier positiveReciprocalBarrier_isProper x :
          Set.Ioi (⊥ : EReal)) : EReal) = reciprocalBarrier x :=
        congrFun (asEReal_properIoi positiveReciprocalBarrier_isProper) x
      _ = ((inversePowerIoiExtension 1 x : Set.Ioi (⊥ : EReal)) : EReal) :=
        (congrFun positiveReciprocalBarrier_bridge x).symm
  have hsourceRev :
      properIoi (ERealFunction.reverse reciprocalBarrier)
          positiveReciprocalBarrierReverse_isProper =
        Function.reverse (inversePowerIoiExtension 1) := by
    funext x
    apply Subtype.ext
    calc
      ((properIoi (ERealFunction.reverse reciprocalBarrier)
            positiveReciprocalBarrierReverse_isProper x :
          Set.Ioi (⊥ : EReal)) : EReal) =
          ERealFunction.reverse reciprocalBarrier x :=
        congrFun (asEReal_properIoi positiveReciprocalBarrierReverse_isProper) x
      _ = ((Function.reverse (inversePowerIoiExtension 1) x :
            Set.Ioi (⊥ : EReal)) : EReal) :=
        (congrFun positiveReciprocalBarrierReverse_bridge x).symm
  -- Rewrite the source-facing owners to the canonical pair proved above.
  simpa [hsource, hsourceRev] using positiveReciprocalBarrier_mem_gammaZero_canonical

/-- Helper: the canonical `Γ₀(ℝ)` representative of the reflected function `g = f^∨` is
`Function.reverse (inversePowerIoiExtension 1)`. -/
private theorem positiveReciprocalBarrierReverse_mem_gammaZero :
    Function.reverse (inversePowerIoiExtension 1) ∈ Γ₀(ℝ) := by
  -- This is the reflected half of the canonical `Γ₀` package.
  exact positiveReciprocalBarrier_mem_gammaZero_canonical.2

/-- Helper for Example 12.13: choosing `y = 2 * max x 0 + 2 / ε` makes both reciprocal summands
smaller than `ε / 2`, so their sum is smaller than `ε`. -/
private theorem exists_large_reciprocalSplit_lt
    (x ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℝ, y > max x 0 ∧ (1 / y : ℝ) + 1 / (y - x) < ε := by
  let y : ℝ := 2 * max x 0 + 4 / ε
  have htwo_div_pos : 0 < 2 / ε := by
    positivity
  have hmax_nonneg : 0 ≤ max x 0 := le_max_right x 0
  have hx_le_max : x ≤ max x 0 := le_max_left x 0
  have hy_gt_max : y > max x 0 := by
    -- The explicit witness adds the strictly positive tail `2 / ε` above `max x 0`.
    have hfour_div_pos : 0 < 4 / ε := by positivity
    dsimp [y]
    linarith [hfour_div_pos, hmax_nonneg]
  have hy_pos : 0 < y := by
    -- In particular the witness itself is positive, so the first reciprocal is finite.
    dsimp [y]
    linarith
  have hy_sub_pos : 0 < y - x := by
    -- The same witness also leaves a positive translated denominator.
    dsimp [y]
    linarith
  have htwo_div_lt_y : 2 / ε < y := by
    -- The nonnegative `2 * max x 0` term only makes the witness larger.
    dsimp [y]
    have htail : 0 < 2 / ε + 2 * max x 0 := by
      linarith [htwo_div_pos, hmax_nonneg]
    calc
      2 / ε < 2 / ε + (2 / ε + 2 * max x 0) := by linarith
      _ = y := by ring
  have htwo_div_lt_y_sub : 2 / ε < y - x := by
    -- Likewise, subtracting `x` still leaves a denominator larger than `2 / ε`.
    dsimp [y]
    have hgap_nonneg : 0 ≤ 2 * max x 0 - x := by
      linarith [hx_le_max]
    calc
      2 / ε < 2 / ε + (2 / ε + (2 * max x 0 - x)) := by linarith
      _ = y - x := by ring
  have hhalf_eq : ε / 2 = 1 / (2 / ε) := by
    field_simp [hε.ne']
  refine ⟨y, hy_gt_max, ?_⟩
  have hy_inv_lt : (1 / y : ℝ) < ε / 2 := by
    -- Compare reciprocals after rewriting `ε / 2` as the reciprocal of `2 / ε`.
    rw [hhalf_eq]
    exact (one_div_lt_one_div (α := ℝ) hy_pos (show 0 < 2 / ε by positivity)).2 htwo_div_lt_y
  have hy_sub_inv_lt : (1 / (y - x) : ℝ) < ε / 2 := by
    -- The translated denominator satisfies the same reciprocal bound.
    rw [hhalf_eq]
    exact (one_div_lt_one_div (α := ℝ) hy_sub_pos (show 0 < 2 / ε by positivity)).2
      htwo_div_lt_y_sub
  linarith

/-- Helper for Example 12.13: on the admissible region `0 < y` and `0 < y - x`, the reciprocal
barrier summands are exactly the two positive reciprocals from the source proof. -/
private theorem reciprocalBarrier_add_reverse_eq_coe_of_pos {x y : ℝ}
    (hy : 0 < y) (hxy : 0 < y - x) :
    reciprocalBarrier y + ERealFunction.reverse reciprocalBarrier (x - y) =
      (((1 / y : ℝ) + 1 / (y - x) : ℝ) : EReal) := by
  -- Both source owners are finite on the admissible split, so the sum stays on the real layer.
  simp [reciprocalBarrier, ERealFunction.reverse_apply, hy, hxy, EReal.coe_add]

/-- Helper for Example 12.13: every admissible reciprocal split has strictly positive total
height. -/
private theorem reciprocalBarrier_add_reverse_pos_of_pos {x y : ℝ}
    (hy : 0 < y) (hxy : 0 < y - x) :
    (0 : EReal) <
      reciprocalBarrier y + ERealFunction.reverse reciprocalBarrier (x - y) := by
  -- Once the split is rewritten on the real layer, positivity is the ordinary positivity of the
  -- two reciprocal terms.
  rw [reciprocalBarrier_add_reverse_eq_coe_of_pos hy hxy]
  exact_mod_cast add_pos (one_div_pos.mpr hy) (one_div_pos.mpr hxy)

/-- Helper for Example 12.13: the reciprocal barrier never attains `-∞`. -/
private theorem reciprocalBarrier_ne_bot (x : ℝ) :
    reciprocalBarrier x ≠ ⊥ := by
  by_cases hx : 0 < x <;> simp [reciprocalBarrier, hx]

-- Proof sketch: compute the defining infimum explicitly. For every `x`, the candidate
-- decomposition `x = y + (x - y)` yields the function `y ↦ 1 / y + 1 / (y - x)` on the
-- admissible region, whose infimum is `0`.
/-- Clause (ii), first half. The infimal convolution of the reciprocal barrier with its reflected
function is the zero function. -/
theorem positiveReciprocalBarrier_infimalConvolution_eq_zero :
    reciprocalBarrier □ ERealFunction.reverse reciprocalBarrier = 0 := by
  ext x
  let v : EReal := (reciprocalBarrier □ ERealFunction.reverse reciprocalBarrier) x
  change v = 0
  have hnonneg : 0 ≤ v := by
    -- Every summand in the defining infimum is nonnegative: either both terms are positive
    -- reciprocals, or one of them is `+∞`.
    dsimp [v]
    change 0 ≤ ⨅ y : ℝ, reciprocalBarrier y + reciprocalBarrier (-(x - y))
    refine le_iInf fun y ↦ ?_
    by_cases hy : 0 < y
    · by_cases hxy : 0 < y - x
      · simpa [ERealFunction.reverse_apply] using
          (show
            0 ≤ reciprocalBarrier y + ERealFunction.reverse reciprocalBarrier (x - y) by
              rw [reciprocalBarrier_add_reverse_eq_coe_of_pos hy hxy]
              exact_mod_cast (show 0 ≤ (1 / y : ℝ) + 1 / (y - x) by positivity))
      · have hxy_not : ¬ x < y := by
          intro hlt
          apply hxy
          linarith
        rw [show reciprocalBarrier (-(x - y)) = ⊤ by simp [reciprocalBarrier, hxy_not],
          EReal.add_top_of_ne_bot (reciprocalBarrier_ne_bot y)]
        simp
    · have hrev_ne_bot : reciprocalBarrier (-(x - y)) ≠ ⊥ := reciprocalBarrier_ne_bot (-(x - y))
      rw [show reciprocalBarrier y = ⊤ by simp [reciprocalBarrier, hy],
        EReal.top_add_of_ne_bot hrev_ne_bot]
      simp
  have hle : v ≤ 0 := by
    -- Route correction: instead of searching for a closed-form infimum, use the explicit
    -- large-`y` estimate to contradict any strictly positive infimal-convolution value.
    by_contra hnot_le_zero
    have hpos : 0 < v := lt_of_not_ge hnot_le_zero
    have hone : v < 1 := by
      rcases exists_large_reciprocalSplit_lt x 1 zero_lt_one with ⟨y, hy_gt, hsum_lt⟩
      have hy : 0 < y := lt_of_le_of_lt (le_max_right x 0) hy_gt
      have hxy : 0 < y - x := by
        have hx_le : x ≤ max x 0 := le_max_left x 0
        linarith
      have hupper : v ≤ (((1 / y : ℝ) + 1 / (y - x) : ℝ) : EReal) := by
        dsimp [v]
        refine le_trans
          (iInf_le (fun z : ℝ ↦ reciprocalBarrier z + reciprocalBarrier (-(x - z))) y) ?_
        simpa [ERealFunction.reverse_apply] using
          (reciprocalBarrier_add_reverse_eq_coe_of_pos (x := x) (y := y) hy hxy).le
      exact lt_of_le_of_lt hupper (by exact_mod_cast hsum_lt)
    have hv_ne_top : v ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hone le_top)
    have hv_ne_bot : v ≠ ⊥ := by
      intro hv_bot
      rw [hv_bot] at hnonneg
      simp at hnonneg
    let ε : ℝ := v.toReal / 2
    have hε_pos : 0 < ε := by
      dsimp [ε]
      exact half_pos (EReal.toReal_pos hpos hv_ne_top)
    rcases exists_large_reciprocalSplit_lt x ε hε_pos with ⟨y, hy_gt, hsum_lt⟩
    have hy : 0 < y := lt_of_le_of_lt (le_max_right x 0) hy_gt
    have hxy : 0 < y - x := by
      have hx_le : x ≤ max x 0 := le_max_left x 0
      linarith
    have hupper : v ≤ (((1 / y : ℝ) + 1 / (y - x) : ℝ) : EReal) := by
      dsimp [v]
      refine le_trans
        (iInf_le (fun z : ℝ ↦ reciprocalBarrier z + reciprocalBarrier (-(x - z))) y) ?_
      simpa [ERealFunction.reverse_apply] using
        (reciprocalBarrier_add_reverse_eq_coe_of_pos (x := x) (y := y) hy hxy).le
    have hlt_eps : v < ((ε : ℝ) : EReal) := by
      exact lt_of_le_of_lt hupper (by exact_mod_cast hsum_lt)
    have hε_lt_v : ((ε : ℝ) : EReal) < v := by
      dsimp [ε]
      rw [← EReal.coe_toReal hv_ne_top hv_ne_bot]
      exact_mod_cast (show v.toReal / 2 < v.toReal by
        nlinarith [EReal.toReal_pos hpos hv_ne_top])
    exact (not_lt_of_ge hlt_eps.le) hε_lt_v
  exact le_antisymm hle hnonneg

-- Proof sketch: unfold `infimalConvolution.ExactAt` for the canonical `]-∞,+∞]`-valued owners and
-- rewrite each occurrence of the canonical representative by the two bridge theorems above.
/-- Helper: exactness for the canonical `]-∞,+∞]`-valued representatives is exactly attainment of
the defining infimum for the source owners `f = reciprocalBarrier` and
`g = ERealFunction.reverse reciprocalBarrier`. -/
private theorem positiveReciprocalBarrier_infimalConvolution_exactAt_iff (x : ℝ) :
    infimalConvolution.ExactAt
        (inversePowerIoiExtension 1)
        (Function.reverse (inversePowerIoiExtension 1))
        x ↔
      ∃ y : ℝ,
        (reciprocalBarrier □ ERealFunction.reverse reciprocalBarrier) x =
          reciprocalBarrier y + ERealFunction.reverse reciprocalBarrier (x - y) := by
  -- Unfold exactness once, then rewrite the canonical reciprocal owner pointwise under the infimum.
  have hbridge :
      ∀ z : ℝ,
        ((inversePowerIoiExtension 1 z : Set.Ioi (⊥ : EReal)) : EReal) = reciprocalBarrier z :=
    congrFun positiveReciprocalBarrier_bridge
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simpa [infimalConvolution_apply, Function.reverse, ERealFunction.reverse_apply, hbridge] using
      hy
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simpa [infimalConvolution_apply, Function.reverse, ERealFunction.reverse_apply, hbridge] using
      hy

-- Proof sketch: if exactness held at some `x`, there would be a minimizing decomposition
-- achieving the infimum in the previous theorem. The explicit formula for the summands shows the
-- infimum `0` is only approached along a limiting family and is never attained.
/-- Clause (ii), second half. The infimal convolution of the reciprocal barrier with its reflected
function is nowhere exact, i.e. its defining infimum is never attained on the source-owner layer. -/
theorem positiveReciprocalBarrier_infimalConvolution_nowhere_exact (x : ℝ) :
    ¬ ∃ y : ℝ,
      (reciprocalBarrier □ ERealFunction.reverse reciprocalBarrier) x =
        reciprocalBarrier y + ERealFunction.reverse reciprocalBarrier (x - y) := by
  -- Clause (ii) already identifies the infimal convolution with `0`, so any exact split would
  -- have to realize the value `0`. The admissible splits are strictly positive, and the
  -- inadmissible splits jump to `+∞`.
  rintro ⟨y, hy_eq⟩
  have hzero :
      (reciprocalBarrier □ ERealFunction.reverse reciprocalBarrier) x = 0 := by
    simpa using congrFun positiveReciprocalBarrier_infimalConvolution_eq_zero x
  rw [hzero] at hy_eq
  by_cases hy : 0 < y
  · by_cases hxy : 0 < y - x
    · have hpos :
        (0 : EReal) <
          reciprocalBarrier y + ERealFunction.reverse reciprocalBarrier (x - y) :=
        reciprocalBarrier_add_reverse_pos_of_pos hy hxy
      exact (ne_of_gt hpos) hy_eq.symm
    · have htop :
        reciprocalBarrier y + ERealFunction.reverse reciprocalBarrier (x - y) = ⊤ := by
        have hxy_not : ¬ x < y := by
          intro hlt
          apply hxy
          linarith
        have hrev_top : ERealFunction.reverse reciprocalBarrier (x - y) = ⊤ := by
          simp [ERealFunction.reverse_apply, reciprocalBarrier, hxy_not]
        rw [hrev_top, EReal.add_top_of_ne_bot (reciprocalBarrier_ne_bot y)]
      rw [htop] at hy_eq
      simp at hy_eq
  · have htop :
      reciprocalBarrier y + ERealFunction.reverse reciprocalBarrier (x - y) = ⊤ := by
      have hrev_ne_bot :
          ERealFunction.reverse reciprocalBarrier (x - y) ≠ ⊥ := by
        simpa [ERealFunction.reverse_apply] using reciprocalBarrier_ne_bot (-(x - y))
      rw [show reciprocalBarrier y = ⊤ by simp [reciprocalBarrier, hy]]
      exact EReal.top_add_of_ne_bot hrev_ne_bot
    rw [htop] at hy_eq
    simp at hy_eq

/-- Helper for Example 12.13: the indicator of a nonempty closed convex set belongs to `Γ₀`. -/
private theorem indicator_mem_gammaZero_of_nonempty_isClosed_convex_local
    {H : Type*} [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ι[C] ∈ Γ₀(H) := by
  -- The indicator is lower semicontinuous exactly when the set is closed, and its convexity is
  -- just the convexity of the underlying set.
  have hindicator_lsc :
      LowerSemicontinuous (fun y ↦ ((ι[C]) y : EReal)) := by
    simpa using (lowerSemicontinuous_indicator_compl_top_iff_isClosed C).2 hC_closed
  have hindicator_dom : effectiveDomain (ι[C]) = C := by
    ext y
    by_cases hy : y ∈ C <;> simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by simpa [hindicator_dom] using hC_nonempty, fun _ hy ↦ hy, ?_⟩
  intro y hy z hz a ha0 ha1
  have hyC : y ∈ C := by
    simpa [hindicator_dom] using hy
  have hzC : z ∈ C := by
    simpa [hindicator_dom] using hz
  have hayzC : a • y + (1 - a) • z ∈ C :=
    hC_convex hyC hzC ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  -- On the effective domain, the indicator is constantly `0`, so Jensen is immediate.
  simp [ERealFunction.indicator, hyC, hzC, hayzC]

-- Proof sketch: clause (i) identifies both functions as members of `Γ₀(ℝ)`, so their epigraphs
-- are nonempty closed convex subsets of `ℝ²`. The indicator of a nonempty closed convex set then
-- lies in `Γ₀(ℝ²)`.
/-- Clause (iii), first preparation. The indicator of `epi f`, for `f = reciprocalBarrier`,
belongs to `Γ₀(ℝ²)`. -/
theorem positiveReciprocalEpigraphIndicator_mem_gammaZero :
    ι[epigraph reciprocalBarrier] ∈ Γ₀(ℝ × ℝ) := by
  have hγ : properIoi reciprocalBarrier positiveReciprocalBarrier_isProper ∈ Γ₀(ℝ) :=
    positiveReciprocalBarrier_mem_gammaZero.1
  have hlsc : LowerSemicontinuous reciprocalBarrier := by
    -- Clause (i) already packages `f` as a `Γ₀` function, so its real-height epigraph is closed.
    simpa [asEReal_properIoi] using (mem_gammaZero_iff.mp hγ).1
  have hclosed : IsClosed (epigraph reciprocalBarrier) := by
    exact (lowerSemicontinuous_iff_isClosed_epigraph reciprocalBarrier).1 hlsc
  have hconv : Convex ℝ (epigraph reciprocalBarrier) := by
    -- The canonical epigraph convexity theorem applies directly to the source owner after the
    -- `properIoi` coercion is rewritten away.
    simpa [asEReal_properIoi] using convex_epigraph_asEReal_of_mem_gammaZero hγ
  have hnonempty : (epigraph reciprocalBarrier).Nonempty := by
    refine ⟨(1, 1), ?_⟩
    rw [mem_epigraph_iff]
    norm_num [reciprocalBarrier]
  exact indicator_mem_gammaZero_of_nonempty_isClosed_convex_local hnonempty hclosed hconv

/-- Clause (iii), second preparation. The indicator of `epi g`, for
`g = ERealFunction.reverse reciprocalBarrier`, belongs to `Γ₀(ℝ²)`. -/
theorem positiveReciprocalReverseEpigraphIndicator_mem_gammaZero :
    ι[epigraph (ERealFunction.reverse reciprocalBarrier)] ∈ Γ₀(ℝ × ℝ) := by
  have hγ :
      properIoi (ERealFunction.reverse reciprocalBarrier)
        positiveReciprocalBarrierReverse_isProper ∈ Γ₀(ℝ) :=
    positiveReciprocalBarrier_mem_gammaZero.2
  have hlsc : LowerSemicontinuous (ERealFunction.reverse reciprocalBarrier) := by
    -- Clause (i) gives the reflected source owner as another `Γ₀` function.
    simpa [asEReal_properIoi] using (mem_gammaZero_iff.mp hγ).1
  have hclosed : IsClosed (epigraph (ERealFunction.reverse reciprocalBarrier)) := by
    exact (lowerSemicontinuous_iff_isClosed_epigraph (ERealFunction.reverse reciprocalBarrier)).1
      hlsc
  have hconv : Convex ℝ (epigraph (ERealFunction.reverse reciprocalBarrier)) := by
    simpa [asEReal_properIoi] using convex_epigraph_asEReal_of_mem_gammaZero hγ
  have hnonempty : (epigraph (ERealFunction.reverse reciprocalBarrier)).Nonempty := by
    refine ⟨(-1, 1), ?_⟩
    rw [mem_epigraph_iff]
    norm_num [ERealFunction.reverse_apply, reciprocalBarrier]
  exact indicator_mem_gammaZero_of_nonempty_isClosed_convex_local hnonempty hclosed hconv

-- Proof sketch: describe the Minkowski sum of the two epigraphs by writing a generic point of the
-- sum as the sum of one point on each epigraph, then eliminate the auxiliary coordinates to show
-- that the second coordinate is positive, and conversely construct such a decomposition for any
-- point with positive second coordinate.
/-- Clause (iii). The Minkowski sum of the two epigraphs is the open upper half-plane. -/
theorem positiveReciprocalEpigraph_sum_eq_openUpperHalfPlane :
    epigraph reciprocalBarrier + epigraph (ERealFunction.reverse reciprocalBarrier) =
      univ ×ˢ Ioi (0 : ℝ) := by
  ext p
  rcases p with ⟨x, ξ⟩
  constructor
  · intro hp
    rcases Set.mem_add.mp hp with ⟨p₁, hp₁, p₂, hp₂, hp_eq⟩
    rcases p₁ with ⟨y, α⟩
    rcases p₂ with ⟨z, β⟩
    have hα : reciprocalBarrier y ≤ (α : EReal) := (mem_epigraph_iff _ _ _).mp hp₁
    have hβ :
        ERealFunction.reverse reciprocalBarrier z ≤ (β : EReal) :=
      (mem_epigraph_iff _ _ _).mp hp₂
    have hξ_eq : α + β = ξ := by
      simpa using congrArg Prod.snd hp_eq
    have hy : 0 < y := by
      by_contra hy
      have htop : reciprocalBarrier y = ⊤ := by
        simp [reciprocalBarrier, hy]
      rw [htop] at hα
      exact (not_le_of_gt (EReal.coe_lt_top α)) hα
    have hz : 0 < -z := by
      by_contra hz
      have htop : ERealFunction.reverse reciprocalBarrier z = ⊤ := by
        simp [ERealFunction.reverse_apply, reciprocalBarrier, hz]
      rw [htop] at hβ
      exact (not_le_of_gt (EReal.coe_lt_top β)) hβ
    have hα_pos : 0 < α := by
      have hα_real : (1 / y : ℝ) ≤ α := by
        simpa [reciprocalBarrier, hy] using hα
      exact lt_of_lt_of_le (one_div_pos.mpr hy) hα_real
    have hβ_pos : 0 < β := by
      have hβ_realE : (((1 / (-z) : ℝ) : EReal)) ≤ (β : EReal) := by
        simpa [ERealFunction.reverse_apply, reciprocalBarrier, hz] using hβ
      have hβ_real : (1 / (-z) : ℝ) ≤ β := by
        exact_mod_cast hβ_realE
      exact lt_of_lt_of_le (one_div_pos.mpr hz) hβ_real
    refine ⟨by simp, ?_⟩
    rw [← hξ_eq]
    exact add_pos hα_pos hβ_pos
  · rintro ⟨_, hξ⟩
    rcases exists_large_reciprocalSplit_lt x ξ hξ with ⟨y, hy_gt, hsum_lt⟩
    have hy : 0 < y := lt_of_le_of_lt (le_max_right x 0) hy_gt
    have hxy : 0 < y - x := by
      have hx_le : x ≤ max x 0 := le_max_left x 0
      linarith
    let α : ℝ := 1 / y
    let β : ℝ := ξ - α
    have hy_mem : (y, α) ∈ epigraph reciprocalBarrier := by
      -- The first point sits exactly on the graph of `f`.
      rw [mem_epigraph_iff]
      simp [α, reciprocalBarrier, hy]
    have hz_mem : (x - y, β) ∈ epigraph (ERealFunction.reverse reciprocalBarrier) := by
      -- The large-`y` estimate leaves enough height for the reflected epigraph coordinate.
      rw [mem_epigraph_iff]
      have hβ_ge_real : 1 / (y - x) ≤ β := by
        dsimp [β, α]
        linarith
      have hβ_ge :
          (((1 / (y - x) : ℝ) : EReal)) ≤ (β : EReal) := by
        exact_mod_cast hβ_ge_real
      have hx_lt_y : x < y := by
        linarith
      calc
        ERealFunction.reverse reciprocalBarrier (x - y)
            = (((1 / (y - x) : ℝ) : EReal)) := by
                simp [ERealFunction.reverse_apply, reciprocalBarrier, hx_lt_y]
        _ ≤ (β : EReal) := hβ_ge
    refine Set.mem_add.2 ⟨(y, α), hy_mem, (x - y, β), hz_mem, ?_⟩
    ext <;> dsimp [α, β] <;> ring

-- Proof sketch: use the indicator-version of infimal convolution from Example 12.3 with
-- `C = epi f` and `D = epi g`, then rewrite the Minkowski sum by the previous theorem.
/-- Clause (iii), companion. The infimal convolution of the two epigraph indicators is the
indicator of the open upper half-plane. -/
theorem positiveReciprocalEpigraphIndicators_infimalConvolution_eq_openUpperHalfPlaneIndicator :
    ι[epigraph reciprocalBarrier] □ ι[epigraph (ERealFunction.reverse reciprocalBarrier)] =
      (ι[univ ×ˢ Ioi (0 : ℝ)]).asEReal := by
  -- Example 12.3 identifies indicator infimal convolution with indicator of the Minkowski sum.
  simpa [positiveReciprocalEpigraph_sum_eq_openUpperHalfPlane] using
    indicator_infimalConvolution_eq_indicator_add
      (epigraph reciprocalBarrier) (epigraph (ERealFunction.reverse reciprocalBarrier))

-- Proof sketch: rewrite the infimal convolution as the indicator of the open upper half-plane. An
-- indicator of a set is lower semicontinuous exactly when the set is closed, and the open upper
-- half-plane is not closed in `ℝ²`.
/-- Example 12.13, clause (iii), conclusion. The infimal convolution of the two epigraph
indicators is not lower semicontinuous. -/
theorem positiveReciprocalEpigraphIndicators_infimalConvolution_not_lowerSemicontinuous :
    ¬ LowerSemicontinuous
      (ι[epigraph reciprocalBarrier] □
        ι[epigraph (ERealFunction.reverse reciprocalBarrier)]) := by
  intro hlsc
  rw [
    positiveReciprocalEpigraphIndicators_infimalConvolution_eq_openUpperHalfPlaneIndicator
  ] at hlsc
  have hindicator_eq :
      (ι[(univ ×ˢ Ioi (0 : ℝ) : Set (ℝ × ℝ))]).asEReal =
        ((univ ×ˢ Ioi (0 : ℝ) : Set (ℝ × ℝ))ᶜ.indicator
          (fun _ : ℝ × ℝ ↦ (⊤ : EReal))) := by
    funext y
    have h :=
      ERealFunction.indicator_apply (C := (univ ×ˢ Ioi (0 : ℝ) : Set (ℝ × ℝ))) y
    simp [Function.asEReal_apply] at h ⊢
  have hlsc_indicator :
      LowerSemicontinuous
        ((univ ×ˢ Ioi (0 : ℝ) : Set (ℝ × ℝ))ᶜ.indicator
          (fun _ : ℝ × ℝ ↦ (⊤ : EReal))) := by
    simpa [hindicator_eq] using hlsc
  have hclosed : IsClosed (univ ×ˢ Ioi (0 : ℝ) : Set (ℝ × ℝ)) := by
    simpa using
      (lowerSemicontinuous_indicator_compl_top_iff_isClosed
        (univ ×ˢ Ioi (0 : ℝ) : Set (ℝ × ℝ))).1
        hlsc_indicator
  have hclosure :
      closure (univ ×ˢ Ioi (0 : ℝ) : Set (ℝ × ℝ)) =
        univ ×ˢ Ici (0 : ℝ) := by
    -- The closure of the open upper half-plane is the closed upper half-plane.
    rw [closure_prod_eq, closure_univ, closure_Ioi]
  have horigin_closure :
      ((0 : ℝ), (0 : ℝ)) ∈ closure (univ ×ˢ Ioi (0 : ℝ) : Set (ℝ × ℝ)) := by
    rw [hclosure]
    simp
  have horigin :
      ((0 : ℝ), (0 : ℝ)) ∈ (univ ×ˢ Ioi (0 : ℝ) : Set (ℝ × ℝ)) := by
    rw [← hclosed.closure_eq]
    exact horigin_closure
  have horigin_not :
      ((0 : ℝ), (0 : ℝ)) ∉ (univ ×ˢ Ioi (0 : ℝ) : Set (ℝ × ℝ)) := by
    simp
  exact horigin_not horigin

end ERealFunction
