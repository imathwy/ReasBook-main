import Mathlib
import BauschkeLean.Chap09.Example_9_36
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_3
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_27

-- Declarations for this item will be appended below by the statement pipeline.

open scoped EuclideanSpace InnerProductSpace Pointwise

namespace ERealFunction

noncomputable section

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The scalar branch `ξ ↦ 1 - √ξ` on `ℝ₊`, extended by `+∞` on `(-∞, 0)`. -/
def oneSubSqrtIciExtension (ξ : ℝ) : EReal :=
  if 0 ≤ ξ then ((1 - Real.sqrt ξ : ℝ) : EReal) else ⊤

/-- The extended-real-valued counterexample `(ξ₁, ξ₂) ↦ max {g(ξ₁), |ξ₂|}` from Remark 16.28. -/
def oneSubSqrtAbsMaxValue (x : ℝ²) : EReal :=
  max (oneSubSqrtIciExtension (x 0)) ((|x 1| : ℝ) : EReal)

/-- Helper for Remark 16 28: the scalar branch `ξ ↦ 1 - √ξ` extended by `+∞` never takes the
value `-∞`. -/
theorem oneSubSqrtIciExtension_gt_bot (ξ : ℝ) :
    (⊥ : EReal) < oneSubSqrtIciExtension ξ := by
  -- Split on the half-line defining the extension.
  by_cases hξ : 0 ≤ ξ
  · rw [oneSubSqrtIciExtension, if_pos hξ]
    exact EReal.bot_lt_coe _
  · rw [oneSubSqrtIciExtension, if_neg hξ]
    exact bot_lt_top

-- Proof sketch: if `x.1 < 0`, then `oneSubSqrtIciExtension x.1 = ⊤`, so the maximum is `⊤ > ⊥`.
-- If `0 ≤ x.1`, then both entries of the maximum are real casts to `EReal`, hence each lies above
-- `⊥`, and so does their maximum.
/-- The counterexample value never takes the value `-∞`. -/
theorem oneSubSqrtAbsMaxValue_gt_bot (x : ℝ²) :
    (⊥ : EReal) < oneSubSqrtAbsMaxValue x := by
  -- Compare the maximum with the first branch, whose scalar extension is already above `⊥`.
  calc
    (⊥ : EReal) < oneSubSqrtIciExtension (x 0) := oneSubSqrtIciExtension_gt_bot (x 0)
    _ ≤ oneSubSqrtAbsMaxValue x := by
      simp [oneSubSqrtAbsMaxValue]

-- Proof sketch: `oneSubSqrtAbsMaxValue_gt_bot` rules out the value `-∞`, and the origin lies in
-- the ordinary domain because the explicit maximum there is `1`.
/-- The underlying `EReal`-valued counterexample is proper. -/
theorem oneSubSqrtAbsMaxValue_isProper :
    IsProper oneSubSqrtAbsMaxValue := by
  refine ⟨?_, ⟨0, ?_⟩⟩
  · intro x
    exact ne_of_gt (oneSubSqrtAbsMaxValue_gt_bot x)
  · change oneSubSqrtAbsMaxValue 0 < ⊤
    simpa [oneSubSqrtAbsMaxValue, oneSubSqrtIciExtension] using (EReal.coe_lt_top (1 : ℝ))

/-- The `]-∞,+∞]`-valued counterexample function from Remark 16.28. -/
def oneSubSqrtAbsMaxCounterexample : ℝ² → Set.Ioi (⊥ : EReal) :=
  properIoi oneSubSqrtAbsMaxValue oneSubSqrtAbsMaxValue_isProper

/-- Helper for Remark 16 28: the scalar branch is proper as an `EReal`-valued function. -/
theorem oneSubSqrtIciExtension_isProper :
    IsProper oneSubSqrtIciExtension := by
  -- The branch never equals `-∞`, and it is finite at the boundary point `0`.
  refine ⟨?_, ⟨0, ?_⟩⟩
  · intro ξ
    exact ne_of_gt (oneSubSqrtIciExtension_gt_bot ξ)
  · change oneSubSqrtIciExtension 0 < ⊤
    simpa [oneSubSqrtIciExtension] using (EReal.coe_lt_top (1 : ℝ))

/-- Helper for Remark 16 28: the packaged scalar branch is the constant-one term plus the
half-power branch from Example 9.36. -/
theorem oneSubSqrtIci_packaged_eq_one_add_negPower_half :
    properIoi oneSubSqrtIciExtension oneSubSqrtIciExtension_isProper =
      (fun _ : ℝ ↦ (1 : ℝ)).toEReal +
        negPowerIciExtension (1 / 2) (by positivity) := by
  -- Follow the source split into the negative ray, the boundary point, and the positive ray.
  funext ξ
  apply Subtype.ext
  change oneSubSqrtIciExtension ξ =
    (((fun _ : ℝ ↦ (1 : ℝ)).toEReal ξ : EReal) +
      (negPowerIciExtension (1 / 2) (by positivity) ξ : EReal))
  rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
  · -- On `(-∞,0)`, both descriptions are `+∞`.
    rw [Function.toEReal_apply, oneSubSqrtIciExtension, if_neg (not_le_of_gt hξ),
      negPowerIciExtension_apply_of_neg (1 / 2) (by positivity) hξ]
    rw [EReal.add_top_of_ne_bot (EReal.coe_ne_bot (1 : ℝ))]
  · -- At the boundary point `0`, both formulas evaluate to `1`.
    rw [Function.toEReal_apply, oneSubSqrtIciExtension, if_pos le_rfl,
      negPowerIciExtension_apply_zero (1 / 2) (by positivity)]
    simp
  · -- On `(0,+∞)`, rewrite the half-power as `sqrt`.
    rw [Function.toEReal_apply, oneSubSqrtIciExtension, if_pos hξ.le,
      negPowerIciExtension_apply_of_pos (1 / 2) (by positivity) hξ]
    rw [Real.sqrt_eq_rpow]
    simp [sub_eq_add_neg, EReal.coe_add]

/-- Helper for Remark 16 28: the counterexample is finite exactly on the closed half-plane
`{x : ℝ² | 0 ≤ x 0}`. -/
theorem effectiveDomain_oneSubSqrtAbsMaxCounterexample :
    effectiveDomain oneSubSqrtAbsMaxCounterexample = {x : ℝ² | 0 ≤ x 0} := by
  -- Route correction: compute the effective domain directly from the sign split on `x 0`.
  ext x
  constructor
  · intro hx
    by_contra hx0
    change ¬ 0 ≤ x 0 at hx0
    have hneg : x 0 < 0 := lt_of_not_ge hx0
    have hx' : oneSubSqrtAbsMaxValue x < ⊤ := by
      simpa [oneSubSqrtAbsMaxCounterexample] using hx
    simp [oneSubSqrtAbsMaxValue, oneSubSqrtIciExtension, not_le_of_gt hneg] at hx'
  · intro hx0
    change 0 ≤ x 0 at hx0
    rw [mem_effectiveDomain_iff, oneSubSqrtAbsMaxCounterexample, properIoi_apply]
    have hfirst : oneSubSqrtIciExtension (x 0) < ⊤ := by
      -- The first branch is real-valued on the closed half-line.
      rw [oneSubSqrtIciExtension, if_pos hx0]
      exact EReal.coe_lt_top _
    have hsecond : (((|x 1| : ℝ) : EReal)) < ⊤ := EReal.coe_lt_top _
    -- Both scalar branches are finite, so their pointwise maximum is finite.
    simpa [oneSubSqrtAbsMaxValue] using (max_lt_iff.mpr ⟨hfirst, hsecond⟩)

/-- Helper for Remark 16 28: the pointwise maximum of two `Γ(H)` functions again belongs to
`Γ(H)`. -/
theorem max_mem_gamma_of_mem_gamma
    {H : Type*} [TopologicalSpace H] [SequentialSpace H] [AddCommGroup H] [Module ℝ H]
    (f g : H → EReal) (hf : f ∈ Γ(H)) (hg : g ∈ Γ(H)) :
    (fun x ↦ max (f x) (g x)) ∈ Γ(H) := by
  let h : Bool → H → EReal := fun i x ↦ if i then f x else g x
  have hh : ∀ i, h i ∈ Γ(H) := by
    intro i
    by_cases hi : i
    · -- The `true` branch is exactly `f`.
      subst hi
      simpa [h] using hf
    · -- The `false` branch is exactly `g`.
      simpa [h, hi] using hg
  have hs : (fun x ↦ ⨆ i : Bool, h i x) ∈ Γ(H) := iSup_mem_gamma h hh
  -- Rewrite the two-point supremum back to the pointwise maximum.
  convert hs using 1
  ext x
  rw [iSup_bool_eq]
  simp [h, max_def]

/-- Helper for Remark 16 28: precomposing a `Γ₀` function with a continuous linear map preserves
`Γ₀` membership when the range meets the effective domain. -/
theorem comp_continuousLinearMap_mem_gammaZero_of_range_inter_nonempty
    {E : Type*} {F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (g : F → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(F))
    (L : E →L[ℝ] F)
    (hdom : (Set.range L ∩ effectiveDomain g).Nonempty) :
    g ∘ L ∈ Γ₀(E) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · -- Lower semicontinuity is stable under precomposition with a continuous linear map.
    simpa using hg.1.comp L.continuous
  · -- The range-domain intersection gives a nonempty effective domain for the composite, and
    -- Jensen convexity transports through linearity of `L`.
    refine ⟨effectiveDomain_comp_nonempty_of_range_inter_nonempty g L hdom, subset_rfl, ?_⟩
    intro x hx y hy α hα hα_lt_one
    have hx' : L x ∈ effectiveDomain g := by
      simpa [mem_effectiveDomain_iff] using hx
    have hy' : L y ∈ effectiveDomain g := by
      simpa [mem_effectiveDomain_iff] using hy
    simpa [Function.comp, map_add, map_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hg.2.ineq hx' hy' hα hα_lt_one

-- Proof sketch: `ξ₁ ↦ oneSubSqrtIciExtension ξ₁` is the lower-semicontinuous convex extension of
-- `1 - √ξ` from `ℝ₊`, and `(ξ₁, ξ₂) ↦ (|ξ₂| : EReal)` is convex and lower semicontinuous on
-- `ℝ²`. The pointwise maximum of these two lower-semicontinuous convex functions is again a member
-- of `Γ₀(ℝ²)`.
/-- Helper for Remark 16 28: the raw `EReal`-valued maximum belongs to `Γ(ℝ²)`. -/
theorem oneSubSqrtAbsMaxValue_mem_gamma :
    oneSubSqrtAbsMaxValue ∈ Γ(ℝ²) := by
  let fstL : ℝ² →L[ℝ] ℝ := EuclideanSpace.proj 0
  let sndL : ℝ² →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hconst_one : (fun _ : ℝ ↦ (1 : ℝ)).toEReal ∈ Γ₀(ℝ) := by
    -- The constant-one branch is continuous and affine, hence belongs directly to `Γ₀(ℝ)`.
    rw [mem_gammaZero_iff]
    refine ⟨?_, ?_⟩
    · simpa [Function.toEReal_apply] using
        (continuous_coe_real_ereal.comp continuous_const).lowerSemicontinuous
    · refine ⟨by simp [Function.effectiveDomain_toEReal], subset_rfl, ?_⟩
      intro x hx y hy a ha hb
      have hsum : a + (1 - a : ℝ) = 1 := by ring
      have hsumE : ((a : EReal) + (1 - a : EReal)) = (1 : EReal) := by
        exact_mod_cast hsum
      calc
        ((1 : ℝ) : EReal) = (((a : EReal) + (1 - a : EReal)) * ((1 : ℝ) : EReal)) := by
          rw [hsumE, one_mul]
        _ = (a : EReal) * ((1 : ℝ) : EReal) + (1 - a : EReal) * ((1 : ℝ) : EReal) := by
          simp
        _ = (a : EReal) * ((fun _ : ℝ ↦ (1 : ℝ)).toEReal x : EReal) +
              (1 - a : EReal) * ((fun _ : ℝ ↦ (1 : ℝ)).toEReal y : EReal) := by
            simp [Function.toEReal_apply]
        _ ≤ (a : EReal) * ((fun _ : ℝ ↦ (1 : ℝ)).toEReal x : EReal) +
              (1 - a : EReal) * ((fun _ : ℝ ↦ (1 : ℝ)).toEReal y : EReal) := by
            exact le_rfl
  have hneg_half : negPowerIciExtension (1 / 2) (by positivity) ∈ Γ₀(ℝ) := by
    -- Example 9.36 gives the half-power extension directly.
    exact negPowerIciExtension_mem_gammaZero (1 / 2) (by positivity) (by norm_num)
  have hscalar_sum :
      (fun _ : ℝ ↦ (1 : ℝ)).toEReal + negPowerIciExtension (1 / 2) (by positivity) ∈ Γ₀(ℝ) := by
    -- The two scalar summands meet at `0`, so pointwise addition preserves `Γ₀`.
    refine pointwiseAdd_mem_gammaZero
      ((fun _ : ℝ ↦ (1 : ℝ)).toEReal)
      (negPowerIciExtension (1 / 2) (by positivity))
      hconst_one hneg_half ?_
    refine ⟨0, ?_, ?_⟩
    · simp [Function.effectiveDomain_toEReal]
    · rw [mem_effectiveDomain_iff, negPowerIciExtension_apply_zero]
      exact EReal.coe_lt_top (0 : ℝ)
  have hscalar_branch :
      properIoi oneSubSqrtIciExtension oneSubSqrtIciExtension_isProper ∈ Γ₀(ℝ) := by
    -- Route correction: package the scalar branch through the Chapter 9 decomposition
    -- `1 + negPowerIciExtension (1/2)`.
    simpa [oneSubSqrtIci_packaged_eq_one_add_negPower_half] using hscalar_sum
  have hscalar_pullback :
      (properIoi oneSubSqrtIciExtension oneSubSqrtIciExtension_isProper) ∘ fstL ∈ Γ₀(ℝ²) := by
    -- Pull the scalar first-coordinate branch back along the projection onto `x₁`.
    refine comp_continuousLinearMap_mem_gammaZero_of_range_inter_nonempty
      (properIoi oneSubSqrtIciExtension oneSubSqrtIciExtension_isProper) hscalar_branch fstL ?_
    refine ⟨0, ?_, ?_⟩
    · exact ⟨0, by simp [fstL]⟩
    · rw [mem_effectiveDomain_iff, properIoi_apply, oneSubSqrtIciExtension]
      simpa using (EReal.coe_lt_top (1 : ℝ))
  have habs_scalar_raw : (fun t : ℝ ↦ ((|t| : ℝ) : EReal)) ∈ Γ(ℝ) := by
    -- The absolute-value branch is the scalar norm, so its Jensen inequality is the triangle
    -- inequality in convex form.
    rw [mem_gamma_iff]
    constructor
    · intro x y a ha hb
      have hnorm :
          ‖a • x + (1 - a) • y‖ ≤ a * ‖x‖ + (1 - a) * ‖y‖ := by
        simpa [smul_eq_mul] using
          (convexOn_univ_norm.2 (by simp) (by simp) ha (sub_nonneg.mpr hb) (by ring) :
            ‖a • x + (1 - a) • y‖ ≤ a • ‖x‖ + (1 - a) • ‖y‖)
      change ((‖a • x + (1 - a) • y‖ : ℝ) : EReal) ≤
        ((a * ‖x‖ + (1 - a) * ‖y‖ : ℝ) : EReal)
      rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
      exact_mod_cast hnorm
    · simpa [Real.norm_eq_abs] using
        (continuous_coe_real_ereal.comp continuous_abs).lowerSemicontinuous
  have habs_scalar : (fun t : ℝ ↦ |t|).toEReal ∈ Γ₀(ℝ) := by
    -- Repackage the raw absolute-value branch as an `]-∞,+∞]`-valued function.
    exact toEReal_mem_gammaZero_of_mem_gamma habs_scalar_raw
  have habs_pullback : ((fun t : ℝ ↦ |t|).toEReal) ∘ sndL ∈ Γ₀(ℝ²) := by
    -- Pull the absolute-value branch back along the projection onto `x₂`.
    refine comp_continuousLinearMap_mem_gammaZero_of_range_inter_nonempty
      ((fun t : ℝ ↦ |t|).toEReal) habs_scalar sndL ?_
    refine ⟨0, ?_, ?_⟩
    · exact ⟨0, by simp [sndL]⟩
    · simp [Function.effectiveDomain_toEReal]
  have hscalar_raw :
      (fun x : ℝ² ↦ oneSubSqrtIciExtension (x 0)) ∈ Γ(ℝ²) := by
    -- Convert the packaged first-coordinate pullback back to its raw `EReal` owner.
    simpa [fstL, Function.comp] using
      asEReal_mem_gamma_of_mem_gammaZero (H := ℝ²) hscalar_pullback
  have habs_raw :
      (fun x : ℝ² ↦ ((|x 1| : ℝ) : EReal)) ∈ Γ(ℝ²) := by
    -- Convert the packaged second-coordinate pullback back to its raw `EReal` owner.
    simpa [sndL, Function.comp] using
      asEReal_mem_gamma_of_mem_gammaZero (H := ℝ²) habs_pullback
  -- The target is the pointwise maximum of those two coordinate branches.
  simpa [oneSubSqrtAbsMaxValue] using
    max_mem_gamma_of_mem_gamma
      (fun x : ℝ² ↦ oneSubSqrtIciExtension (x 0))
      (fun x : ℝ² ↦ ((|x 1| : ℝ) : EReal))
      hscalar_raw habs_raw

/-- The explicit counterexample from Remark 16.28 belongs to `Γ₀(ℝ²)`. -/
theorem oneSubSqrtAbsMaxCounterexample_mem_gammaZero :
    oneSubSqrtAbsMaxCounterexample ∈ Γ₀(ℝ²) := by
  -- Upgrade the raw `Γ` owner through the canonical `properIoi` packaging.
  simpa [oneSubSqrtAbsMaxCounterexample] using
    properIoi_mem_gammaZero_of_mem_gamma
      oneSubSqrtAbsMaxValue_isProper oneSubSqrtAbsMaxValue_mem_gamma

/-- Helper for Remark 16 28: every point with strictly positive first coordinate lies in the
subdifferential domain. -/
theorem mem_dom_oneSubSqrtAbsMaxCounterexample_of_pos_first_coordinate (x : ℝ²)
    (hx0 : 0 < x 0) :
    x ∈ SetValuedOperator.dom (∂ oneSubSqrtAbsMaxCounterexample) := by
  have hopen : IsOpen {y : ℝ² | 0 < y 0} :=
    isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous
  have hx_open : x ∈ {y : ℝ² | 0 < y 0} := by
    simpa using hx0
  have hsubset :
      {y : ℝ² | 0 < y 0} ⊆ effectiveDomain oneSubSqrtAbsMaxCounterexample := by
    intro y hy
    rw [effectiveDomain_oneSubSqrtAbsMaxCounterexample]
    change 0 ≤ y 0
    exact le_of_lt (by simpa using hy)
  have hx_int : x ∈ interior (effectiveDomain oneSubSqrtAbsMaxCounterexample) := by
    -- Positive first coordinate points lie in the open half-plane, hence in the domain interior.
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (hopen.mem_nhds hx_open) hsubset
  have hx_cont : ContinuousPoint oneSubSqrtAbsMaxCounterexample x :=
    -- Proposition 16.27 identifies interior-domain points with the source continuity predicate.
    continuousPoint_of_mem_interior_effectiveDomain_of_mem_gammaZero
      oneSubSqrtAbsMaxCounterexample_mem_gammaZero hx_int
  -- Continuity on the effective domain gives a nonempty subdifferential.
  exact continuitySet_subset_subdifferentialDomain_of_mem_gammaZero
    oneSubSqrtAbsMaxCounterexample_mem_gammaZero hx_cont

/-- Helper for Remark 16 28: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul (a b : ℝ) :
    ⟪a, b⟫_ℝ = a * b := by
  -- Expand the scalar inner product once so later boundary inequalities become ordinary arithmetic.
  calc
    ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
    _ = a * b := by simp

/-- Helper for Remark 16 28: a vector in `ℝ²` is determined by its two coordinates. -/
private theorem euclideanSpace_fin2_eq (x : ℝ²) :
    x = !₂[x 0, x 1] := by
  -- Coordinatewise extensionality is enough in `EuclideanSpace ℝ (Fin 2)`.
  ext i
  fin_cases i <;> simp

/-- Helper for Remark 16 28: the inner product on `ℝ²` is the usual coordinate dot product. -/
private theorem inner_fin2_eq (x u : ℝ²) :
    ⟪x, u⟫_ℝ = x 0 * u 0 + x 1 * u 1 := by
  -- Rewrite both vectors by coordinates and evaluate the two-term sum explicitly.
  rw [euclideanSpace_fin2_eq x, euclideanSpace_fin2_eq u]
  norm_num [PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_mul]

/-- Helper for Remark 16 28: boundary points with `x₂ ∉ ]-1,1[` admit the explicit subgradient
witness `!₂[0,±1]`. -/
theorem boundary_mem_dom_oneSubSqrtAbsMaxCounterexample_of_not_mem_Ioo (x : ℝ²) (hx0 : x 0 = 0)
    (hxstrip : x 1 ∉ Set.Ioo (-1 : ℝ) 1) :
    x ∈ SetValuedOperator.dom (∂ oneSubSqrtAbsMaxCounterexample) := by
  have hx_cases : x 1 ≤ -1 ∨ 1 ≤ x 1 := by
    by_cases hx_left : x 1 ≤ -1
    · exact Or.inl hx_left
    · right
      have hx_gt_left : -1 < x 1 := lt_of_not_ge hx_left
      by_contra hx_right
      exact hxstrip ⟨hx_gt_left, lt_of_not_ge hx_right⟩
  rw [SetValuedOperator.mem_dom_iff]
  rcases hx_cases with hx1 | hx1
  · refine ⟨!₂[(0 : ℝ), (-1 : ℝ)], ?_⟩
    rw [mem_subdifferential_iff]
    intro y
    by_cases hy0 : 0 ≤ y 0
    · have hx_abs_ge_one : (1 : ℝ) ≤ |x 1| := by
        have hx_abs : |x 1| = -x 1 := by
          have hx1_nonpos : x 1 ≤ 0 := by linarith
          exact abs_of_nonpos hx1_nonpos
        rw [hx_abs]
        linarith
      have hleft :
          (⟪y - x, !₂[(0 : ℝ), (-1 : ℝ)]⟫_ℝ : EReal) +
              (oneSubSqrtAbsMaxCounterexample x : EReal) =
            ((-y 1 : ℝ) : EReal) := by
        -- On the retained left boundary, the affine minorant collapses to the scalar `-y₂`.
        rw [oneSubSqrtAbsMaxCounterexample, properIoi_apply, inner_fin2_eq]
        rw [oneSubSqrtAbsMaxValue, oneSubSqrtIciExtension, hx0, if_pos le_rfl, Real.sqrt_zero]
        norm_num
        rw [max_eq_right (show (1 : EReal) ≤ ((|x 1| : ℝ) : EReal) from by
          exact_mod_cast hx_abs_ge_one)]
        have hx1_nonpos : x 1 ≤ 0 := by
          linarith
        have hx_abs : |x 1| = -x 1 := abs_of_nonpos hx1_nonpos
        have hreal : x 1 - y 1 + |x 1| = -y 1 := by
          calc
            x 1 - y 1 + |x 1| = x 1 - y 1 + (-x 1) := by rw [hx_abs]
            _ = (x 1 + -x 1) - y 1 := by ring
            _ = -y 1 := by simp
        exact_mod_cast hreal
      calc
        (⟪y - x, !₂[(0 : ℝ), (-1 : ℝ)]⟫_ℝ : EReal) +
            (oneSubSqrtAbsMaxCounterexample x : EReal) =
            ((-y 1 : ℝ) : EReal) := hleft
        _ ≤ ((|y 1| : ℝ) : EReal) := by
          exact_mod_cast (neg_le_abs (y 1))
        _ ≤ (oneSubSqrtAbsMaxCounterexample y : EReal) := by
          rw [oneSubSqrtAbsMaxCounterexample, properIoi_apply]
          simp [oneSubSqrtAbsMaxValue, oneSubSqrtIciExtension, hy0]
    · -- Outside the effective domain, the target value is `⊤`, so the inequality is automatic.
      have hy_top : (oneSubSqrtAbsMaxCounterexample y : EReal) = ⊤ := by
        rw [oneSubSqrtAbsMaxCounterexample, properIoi_apply, oneSubSqrtAbsMaxValue,
          oneSubSqrtIciExtension, if_neg hy0]
        simp
      calc
        (⟪y - x, !₂[(0 : ℝ), (-1 : ℝ)]⟫_ℝ : EReal) +
            (oneSubSqrtAbsMaxCounterexample x : EReal) ≤ (⊤ : EReal) := le_top
        _ = (oneSubSqrtAbsMaxCounterexample y : EReal) := by rw [hy_top]
  · refine ⟨!₂[(0 : ℝ), (1 : ℝ)], ?_⟩
    rw [mem_subdifferential_iff]
    intro y
    by_cases hy0 : 0 ≤ y 0
    · have hx_abs_ge_one : (1 : ℝ) ≤ |x 1| := by
        have hx1_nonneg : 0 ≤ x 1 := by linarith
        rw [abs_of_nonneg hx1_nonneg]
        exact hx1
      have hleft :
          (⟪y - x, !₂[(0 : ℝ), (1 : ℝ)]⟫_ℝ : EReal) +
              (oneSubSqrtAbsMaxCounterexample x : EReal) =
            ((y 1 : ℝ) : EReal) := by
        -- On the retained right boundary, the affine minorant collapses to the scalar `y₂`.
        rw [oneSubSqrtAbsMaxCounterexample, properIoi_apply, inner_fin2_eq]
        rw [oneSubSqrtAbsMaxValue, oneSubSqrtIciExtension, hx0, if_pos le_rfl, Real.sqrt_zero]
        norm_num
        rw [max_eq_right (show (1 : EReal) ≤ ((|x 1| : ℝ) : EReal) from by
          exact_mod_cast hx_abs_ge_one)]
        have hx1_nonneg : 0 ≤ x 1 := by
          linarith
        have hx_abs : |x 1| = x 1 := abs_of_nonneg hx1_nonneg
        have hreal : y 1 - x 1 + |x 1| = y 1 := by
          calc
            y 1 - x 1 + |x 1| = y 1 - x 1 + x 1 := by simp [hx_abs]
            _ = y 1 := by ring_nf
        exact_mod_cast hreal
      calc
        (⟪y - x, !₂[(0 : ℝ), (1 : ℝ)]⟫_ℝ : EReal) +
            (oneSubSqrtAbsMaxCounterexample x : EReal) =
            ((y 1 : ℝ) : EReal) := hleft
        _ ≤ ((|y 1| : ℝ) : EReal) := by
          exact_mod_cast (le_abs_self (y 1))
        _ ≤ (oneSubSqrtAbsMaxCounterexample y : EReal) := by
          rw [oneSubSqrtAbsMaxCounterexample, properIoi_apply]
          simp [oneSubSqrtAbsMaxValue, oneSubSqrtIciExtension, hy0]
    · -- Outside the effective domain, the target value is `⊤`, so the inequality is automatic.
      have hy_top : (oneSubSqrtAbsMaxCounterexample y : EReal) = ⊤ := by
        rw [oneSubSqrtAbsMaxCounterexample, properIoi_apply, oneSubSqrtAbsMaxValue,
          oneSubSqrtIciExtension, if_neg hy0]
        simp
      calc
        (⟪y - x, !₂[(0 : ℝ), (1 : ℝ)]⟫_ℝ : EReal) +
            (oneSubSqrtAbsMaxCounterexample x : EReal) ≤ (⊤ : EReal) := le_top
        _ = (oneSubSqrtAbsMaxCounterexample y : EReal) := by rw [hy_top]

/-- Helper for Remark 16 28: on the removed boundary strip, the counterexample value is exactly
`1`. -/
private theorem oneSubSqrtAbsMaxCounterexample_boundary_value (x : ℝ²) (hx0 : x 0 = 0)
    (hxstrip : x 1 ∈ Set.Ioo (-1 : ℝ) 1) :
    (oneSubSqrtAbsMaxCounterexample x : EReal) = (1 : ℝ) := by
  rcases hxstrip with ⟨hx1_left, hx1_right⟩
  have hx1_abs_lt : |x 1| < 1 := by
    -- The removed strip is exactly the scalar inequality `|x₂| < 1`.
    exact abs_lt.mpr ⟨by linarith, hx1_right⟩
  have hx1_abs_le : |x 1| ≤ 1 := hx1_abs_lt.le
  -- On the boundary line `x₁ = 0`, the first branch equals `1` and dominates `|x₂|`.
  rw [oneSubSqrtAbsMaxCounterexample, properIoi_apply, oneSubSqrtAbsMaxValue,
    oneSubSqrtIciExtension, hx0, if_pos le_rfl, Real.sqrt_zero]
  norm_num
  change (((|x 1| : ℝ) : EReal)) ≤ ((1 : ℝ) : EReal)
  exact EReal.coe_le_coe_iff.2 hx1_abs_le

/-- Helper for Remark 16 28: the source test point `!₂[δ², x₂]` has value `1 - δ` on the removed
boundary strip. -/
private theorem oneSubSqrtAbsMaxCounterexample_boundary_test_point_value (x : ℝ²)
    (_hx0 : x 0 = 0) (hxstrip : x 1 ∈ Set.Ioo (-1 : ℝ) 1) {δ : ℝ} (hδ : 0 < δ)
    (hδ_le : δ ≤ (1 - |x 1|) / 2) :
    (oneSubSqrtAbsMaxCounterexample !₂[δ ^ 2, x 1] : EReal) = ((1 - δ : ℝ) : EReal) := by
  rcases hxstrip with ⟨hx1_left, hx1_right⟩
  have hx1_abs_lt : |x 1| < 1 := by
    -- Reexpress the strip hypothesis as `|x₂| < 1` before comparing the two max-branches.
    exact abs_lt.mpr ⟨by linarith, hx1_right⟩
  have hδ_sq_nonneg : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hx1_le_branch : |x 1| ≤ 1 - δ := by
    -- The chosen `δ` stays below half the distance from `|x₂|` to `1`.
    linarith
  have hfirst :
      oneSubSqrtIciExtension (δ ^ 2) = ((1 - δ : ℝ) : EReal) := by
    -- The first branch evaluates to `1 - sqrt (δ²) = 1 - δ` because `δ > 0`.
    rw [oneSubSqrtIciExtension, if_pos hδ_sq_nonneg, Real.sqrt_sq_eq_abs, abs_of_nonneg hδ.le]
  have hmax :
      max (((1 - δ : ℝ) : EReal)) (((|x 1| : ℝ) : EReal)) = ((1 - δ : ℝ) : EReal) := by
    have hx1_le_branchE : (((|x 1| : ℝ) : EReal)) ≤ (((1 - δ : ℝ) : EReal)) := by
      exact EReal.coe_le_coe_iff.2 hx1_le_branch
    exact max_eq_left hx1_le_branchE
  -- At the test point, the `max` still selects the first branch.
  simpa [oneSubSqrtAbsMaxCounterexample, properIoi_apply, oneSubSqrtAbsMaxValue, hfirst] using
    hmax

/-- Helper for Remark 16 28: the source test point changes only the first coordinate, so the
inner product shift is `δ²` times the first coordinate of `u`. -/
private theorem boundary_test_point_inner_shift (x u : ℝ²) (δ : ℝ) (hx0 : x 0 = 0) :
    ⟪!₂[δ ^ 2, x 1] - x, u⟫_ℝ = δ ^ 2 * u 0 := by
  -- The second coordinate is fixed, so the dot product keeps only the first-coordinate term.
  rw [inner_fin2_eq]
  simp [hx0]

/-- Helper for Remark 16 28: the subgradient inequality at the source test point scalarizes to
`δ` times the first coordinate of `u` being at most `-1`. -/
private theorem boundary_test_point_subgradient_scalar_ineq (x u : ℝ²) (hx0 : x 0 = 0)
    (hxstrip : x 1 ∈ Set.Ioo (-1 : ℝ) 1)
    (hu : u ∈ (∂ oneSubSqrtAbsMaxCounterexample) x)
    {δ : ℝ} (hδ : 0 < δ) (hδ_le : δ ≤ (1 - |x 1|) / 2) :
    δ * u 0 ≤ -1 := by
  let y : ℝ² := !₂[δ ^ 2, x 1]
  have hx_value :
      (oneSubSqrtAbsMaxCounterexample x : EReal) = (1 : ℝ) :=
    oneSubSqrtAbsMaxCounterexample_boundary_value x hx0 hxstrip
  have hy_value :
      (oneSubSqrtAbsMaxCounterexample y : EReal) = ((1 - δ : ℝ) : EReal) := by
    -- Isolate the explicit test-point value before touching the subgradient inequality.
    simpa [y] using
      oneSubSqrtAbsMaxCounterexample_boundary_test_point_value x hx0 hxstrip hδ hδ_le
  have hy_inner : ⟪y - x, u⟫_ℝ = δ ^ 2 * u 0 := by
    -- The source test point turns the two-dimensional inner product into one scalar term.
    simpa [y] using boundary_test_point_inner_shift x u δ hx0
  have hy_ineq :
      (⟪y - x, u⟫_ℝ : EReal) + (oneSubSqrtAbsMaxCounterexample x : EReal) ≤
        (oneSubSqrtAbsMaxCounterexample y : EReal) :=
    (mem_subdifferential_iff (f := oneSubSqrtAbsMaxCounterexample) (x := x) (u := u)).1 hu y
  rw [hy_inner, hx_value, hy_value] at hy_ineq
  have hreal_cast : (((δ ^ 2 * u 0 + 1 : ℝ) : EReal)) ≤ (((1 - δ : ℝ) : EReal)) := by
    -- After the exact rewrites, the `EReal` inequality is between finite real casts.
    simpa [EReal.coe_add] using hy_ineq
  have hreal : δ ^ 2 * u 0 + 1 ≤ 1 - δ := by
    exact_mod_cast hreal_cast
  have hscaled : δ * (δ * u 0) ≤ δ * (-1 : ℝ) := by
    -- Rearrange to `δ²` times the first coordinate being at most `-δ`, then expose the common
    -- positive factor `δ`.
    have hnum : δ ^ 2 * u 0 ≤ -δ := by
      linarith
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hnum
  -- Cancel the positive factor `δ`.
  exact le_of_mul_le_mul_left hscaled hδ

/-- Helper for Remark 16 28: boundary points with `x₂ ∈ ]-1,1[` are excluded from the
subdifferential domain by the source `δ`-test-point argument. -/
theorem boundary_not_mem_dom_oneSubSqrtAbsMaxCounterexample_of_mem_Ioo (x : ℝ²) (hx0 : x 0 = 0)
    (hxstrip : x 1 ∈ Set.Ioo (-1 : ℝ) 1) :
    x ∉ SetValuedOperator.dom (∂ oneSubSqrtAbsMaxCounterexample) := by
  intro hxdom
  rw [SetValuedOperator.mem_dom_iff] at hxdom
  rcases hxdom with ⟨u, hu⟩
  have hx1_abs_lt : |x 1| < 1 := by
    -- The excluded strip is the scalar condition `|x₂| < 1`.
    rcases hxstrip with ⟨hx1_left, hx1_right⟩
    exact abs_lt.mpr ⟨by linarith, hx1_right⟩
  let δ : ℝ := min ((1 - |x 1|) / 2) (1 / (|u 0| + 1))
  have hhalf_pos : 0 < (1 - |x 1|) / 2 := by
    -- The strip leaves positive room between `|x₂|` and `1`.
    linarith
  have hden_pos : 0 < |u 0| + 1 := by
    positivity
  have hratio_pos : 0 < 1 / (|u 0| + 1) := by
    exact one_div_pos.mpr hden_pos
  have hδ_pos : 0 < δ := by
    -- Route correction: choose the source parameter `δ` as the minimum of the geometric and
    -- subgradient-control bounds.
    dsimp [δ]
    exact lt_min hhalf_pos hratio_pos
  have hδ_le_half : δ ≤ (1 - |x 1|) / 2 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_ratio : δ ≤ 1 / (|u 0| + 1) := by
    dsimp [δ]
    exact min_le_right _ _
  have hscalar : δ * u 0 ≤ -1 :=
    boundary_test_point_subgradient_scalar_ineq x u hx0 hxstrip hu hδ_pos hδ_le_half
  have hmul_le : δ * (|u 0| + 1) ≤ 1 := by
    -- The second half of the definition of `δ` bounds the scaled absolute first coordinate.
    exact (le_div_iff₀ hden_pos).mp hδ_le_ratio
  have hmul_lt : δ * |u 0| < 1 := by
    have haux : δ * |u 0| + δ ≤ 1 := by
      simpa [mul_add, add_comm, add_left_comm, add_assoc] using hmul_le
    linarith
  have hneg_abs : -(δ * |u 0|) ≤ δ * u 0 := by
    -- Convert the standard `- |δ u₀| ≤ δ u₀` estimate into the scaled first-coordinate form.
    simpa [abs_mul, abs_of_nonneg hδ_pos.le, mul_comm, mul_left_comm, mul_assoc] using
      (neg_abs_le (δ * u 0))
  have hlower : -1 < δ * u 0 := by
    -- The `δ`-bound forces `δ * |u₀| < 1`, hence `δ * u₀` stays strictly above `-1`.
    have hleft : -1 < -(δ * |u 0|) := by
      linarith
    exact lt_of_lt_of_le hleft hneg_abs
  linarith

/-- Helper for Remark 16 28: on the boundary line `x₁ = 0`, the subdifferential domain keeps
exactly the points outside the open strip `]-1,1[`. -/
theorem boundary_mem_dom_oneSubSqrtAbsMaxCounterexample_iff (x : ℝ²) (hx0 : x 0 = 0) :
    x ∈ SetValuedOperator.dom (∂ oneSubSqrtAbsMaxCounterexample) ↔
      x 1 ∉ Set.Ioo (-1 : ℝ) 1 := by
  -- Route correction: split the boundary line into the retained part and the removed strip,
  -- instead of trying to solve the whole iff in one monolithic subgradient computation.
  constructor
  · intro hx
    by_cases hxstrip : x 1 ∈ Set.Ioo (-1 : ℝ) 1
    · exact False.elim
        (boundary_not_mem_dom_oneSubSqrtAbsMaxCounterexample_of_mem_Ioo x hx0 hxstrip hx)
    · exact hxstrip
  · intro hx
    exact boundary_mem_dom_oneSubSqrtAbsMaxCounterexample_of_not_mem_Ioo x hx0 hx

-- Proof sketch: analyze the subgradient inequality separately on the open half-plane `ξ₁ > 0`,
-- on the boundary line `ξ₁ = 0`, and on the region `ξ₁ < 0` where the function takes value
-- `+∞`. For `ξ₁ > 0` the smooth branch `1 - √ξ₁` gives subgradients, while at `ξ₁ = 0` the
-- vertical strip `|ξ₂| < 1` is excluded because the singular first-coordinate branch destroys
-- subdifferentiability there. This yields exactly the stated set.
/-- Remark 16 28: for the function
`f(ξ₁, ξ₂) = max {g(ξ₁), |ξ₂|}` with `g(ξ₁) = 1 - √ξ₁` on `ℝ₊` and `g(ξ₁) = +∞` on
`(-∞, 0)`, the domain of the subdifferential is
`(ℝ₊ × ℝ) \ ({0} × ]-1,1[)`. -/
theorem subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_eq :
    SetValuedOperator.dom (∂ oneSubSqrtAbsMaxCounterexample) =
      {x : ℝ² | 0 ≤ x 0} \
        {x : ℝ² | x 0 = 0 ∧ x 1 ∈ Set.Ioo (-1 : ℝ) 1} := by
  -- Split into the negative half-plane, the open positive half-plane, and the boundary line.
  ext x
  constructor
  · intro hx
    have hx_dom_eff :
        x ∈ effectiveDomain oneSubSqrtAbsMaxCounterexample := by
      exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero
        oneSubSqrtAbsMaxCounterexample_mem_gammaZero hx
    have hx0_nonneg : 0 ≤ x 0 := by
      simpa [effectiveDomain_oneSubSqrtAbsMaxCounterexample] using hx_dom_eff
    refine ⟨hx0_nonneg, ?_⟩
    intro hxstrip
    have hx0_boundary : x 0 = 0 := hxstrip.1
    have hx1_not : x 1 ∉ Set.Ioo (-1 : ℝ) 1 := by
      exact (boundary_mem_dom_oneSubSqrtAbsMaxCounterexample_iff x hx0_boundary).1 hx
    exact hx1_not hxstrip.2
  · rintro ⟨hx0_nonneg, hx_not_strip⟩
    have hx0_nonneg' : 0 ≤ x 0 := by
      simpa using hx0_nonneg
    by_cases hx0_pos : 0 < x 0
    · exact mem_dom_oneSubSqrtAbsMaxCounterexample_of_pos_first_coordinate x hx0_pos
    · have hx0_eq : x 0 = 0 := by linarith
      have hx1_not : x 1 ∉ Set.Ioo (-1 : ℝ) 1 := by
        intro hx1_strip
        exact hx_not_strip ⟨hx0_eq, hx1_strip⟩
      exact (boundary_mem_dom_oneSubSqrtAbsMaxCounterexample_iff x hx0_eq).2 hx1_not

-- Proof sketch: use the explicit domain formula from
-- `subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_eq`. The points `(0, -1)` and `(0, 1)`
-- belong to the domain, but their midpoint `(0, 0)` lies in the removed strip `{0} × ]-1,1[`.
/-- The subdifferential domain in Remark 16.28 is not convex. -/
theorem subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_not_convex :
    ¬ Convex ℝ
      ((SetValuedOperator.dom (∂ oneSubSqrtAbsMaxCounterexample)) : Set ℝ²) := by
  intro hconv
  let xL : ℝ² := !₂[(0 : ℝ), (-1 : ℝ)]
  let xR : ℝ² := !₂[(0 : ℝ), (1 : ℝ)]
  have hxL :
      xL ∈ (SetValuedOperator.dom (∂ oneSubSqrtAbsMaxCounterexample) : Set ℝ²) := by
    -- The left endpoint lies on the retained boundary line `x₁ = 0`, `x₂ = -1`.
    rw [subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_eq]
    refine ⟨by simp [xL], ?_⟩
    intro hxL_strip
    simpa [xL] using hxL_strip.2
  have hxR :
      xR ∈ (SetValuedOperator.dom (∂ oneSubSqrtAbsMaxCounterexample) : Set ℝ²) := by
    -- The right endpoint lies on the retained boundary line `x₁ = 0`, `x₂ = 1`.
    rw [subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_eq]
    refine ⟨by simp [xR], ?_⟩
    intro hxR_strip
    simpa [xR] using hxR_strip.2
  have hmid_eq : midpoint ℝ xL xR = (0 : ℝ²) := by
    -- The midpoint of the two boundary endpoints is the origin.
    ext i
    fin_cases i <;> simp [xL, xR, midpoint_eq_smul_add]
  have hzero_mem :
      (0 : ℝ²) ∈ (SetValuedOperator.dom (∂ oneSubSqrtAbsMaxCounterexample) : Set ℝ²) := by
    simpa [hmid_eq] using hconv.midpoint_mem hxL hxR
  rw [subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_eq] at hzero_mem
  -- But the origin is removed by the open strip `{0} × ]-1,1[`.
  exact hzero_mem.2 (by simp)

end

end ERealFunction
