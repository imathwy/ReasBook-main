module

public import Topology_Munkres_2000.Book.Theorem_53_1.CircleMap

public section


namespace Circle

open Filter Topology

/-- The restriction of the one-turn circle exponential to the positive real line. -/
@[expose]
noncomputable def positiveRealExp : Set.Ioi (0 : ℝ) → Circle :=
  fun x ↦ turnExp x.1

/-- The positive-real circle exponential is the restriction of `turnExp`. -/
theorem positiveRealExp_apply (x : Set.Ioi (0 : ℝ)) :
    positiveRealExp x = turnExp x.1 := rfl

/-- The positive-real circle exponential has the usual cosine-sine coordinate formula. -/
theorem coe_positiveRealExp (x : Set.Ioi (0 : ℝ)) :
    (positiveRealExp x : ℂ) =
      Real.cos (2 * Real.pi * x.1) + Real.sin (2 * Real.pi * x.1) * Complex.I :=
  coe_turnExp x.1

/-- Helper for Example 53.2: restricting a map continuous at `0` to the positive ray
cannot evenly cover the image of the omitted endpoint. -/
private theorem not_isEvenlyCovered_restrictIoi {Y : Type*} [TopologicalSpace Y]
    (f : ℝ → Y) (hf : ContinuousAt f 0) :
    ¬ IsEvenlyCovered (fun x : Set.Ioi (0 : ℝ) ↦ f x.1) (f 0)
      ((fun x : Set.Ioi (0 : ℝ) ↦ f x.1) ⁻¹' {f 0}) := by
  -- An evenly covered neighborhood gives a product chart with a discrete sheet coordinate.
  rintro ⟨hDiscrete, U, h0U, hU, -, H, hH⟩
  letI : DiscreteTopology
      ((fun x : Set.Ioi (0 : ℝ) ↦ f x.1) ⁻¹' {f 0}) := hDiscrete
  have hEventuallyU : ∀ᶠ x in 𝓝 (0 : ℝ), f x ∈ U :=
    hf.eventually (hU.mem_nhds h0U)
  obtain ⟨l, u, h0lu, hluU⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hEventuallyU
  have hPositiveUpper : 0 < u := h0lu.2
  have hIntervalMaps : Set.MapsTo f (Set.Ioo (0 : ℝ) u) U := by
    intro x hx
    exact hluU ⟨lt_trans h0lu.1 hx.1, hx.2⟩
  have hIntervalPositive : Set.Ioo (0 : ℝ) u ⊆ Set.Ioi 0 := by
    intro x hx
    exact hx.1
  let domainMap : Set.Ioo (0 : ℝ) u →
      (fun x : Set.Ioi (0 : ℝ) ↦ f x.1) ⁻¹' U :=
    fun x ↦ ⟨Set.inclusion hIntervalPositive x, hIntervalMaps x.property⟩
  have hDomainMap : Continuous domainMap := by
    apply Continuous.subtype_mk
    exact continuous_inclusion hIntervalPositive
  let sheet : Set.Ioo (0 : ℝ) u →
      (fun x : Set.Ioi (0 : ℝ) ↦ f x.1) ⁻¹' {f 0} :=
    fun x ↦ (H (domainMap x)).2
  have hSheet : Continuous sheet := by
    exact continuous_snd.comp (H.continuous.comp hDomainMap)
  letI : PreconnectedSpace (Set.Ioo (0 : ℝ) u) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hHalf : u / 2 ∈ Set.Ioo (0 : ℝ) u := by
    constructor <;> linarith
  let anchor : Set.Ioo (0 : ℝ) u := ⟨u / 2, hHalf⟩
  have hSheetConstant (x : Set.Ioo (0 : ℝ) u) : sheet x = sheet anchor := by
    exact PreconnectedSpace.constant inferInstance hSheet
  -- Positive points tending to `0` stay in one sheet of the product chart.
  have hSequenceMem (n : ℕ) :
      u / ((n : ℝ) + 2) ∈ Set.Ioo (0 : ℝ) u := by
    have hDenominator : 0 < (n : ℝ) + 2 := by positivity
    constructor
    · positivity
    · rw [div_lt_iff₀ hDenominator]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
  let sequence : ℕ → Set.Ioo (0 : ℝ) u :=
    fun n ↦ ⟨u / ((n : ℝ) + 2), hSequenceMem n⟩
  have hSequenceTendsZero :
      Filter.Tendsto (fun n ↦ (sequence n : ℝ)) Filter.atTop (𝓝 0) := by
    have hReciprocal :
        Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) := by
      exact (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr'
        (Filter.Eventually.of_forall fun n ↦ by norm_num [Nat.cast_add]; ring)
    simpa [sequence, div_eq_mul_inv] using hReciprocal.const_mul u
  have hBaseTends :
      Filter.Tendsto (fun n ↦ (⟨f (sequence n), hIntervalMaps (sequence n).property⟩ : U))
        Filter.atTop (𝓝 ⟨f 0, h0U⟩) := by
    exact tendsto_subtype_rng.mpr (hf.tendsto.comp hSequenceTendsZero)
  have hProductTends :
      Filter.Tendsto
        (fun n ↦ ((⟨f (sequence n), hIntervalMaps (sequence n).property⟩ : U), sheet anchor))
        Filter.atTop (𝓝 ((⟨f 0, h0U⟩ : U), sheet anchor)) := by
    exact hBaseTends.prodMk_nhds tendsto_const_nhds
  have hInverseTends :
      Filter.Tendsto
        (fun n ↦ H.symm
          ((⟨f (sequence n), hIntervalMaps (sequence n).property⟩ : U), sheet anchor))
        Filter.atTop (𝓝 (H.symm ((⟨f 0, h0U⟩ : U), sheet anchor))) := by
    exact H.symm.continuous.tendsto _ |>.comp hProductTends
  have hInverseEquals (n : ℕ) :
      H.symm ((⟨f (sequence n), hIntervalMaps (sequence n).property⟩ : U), sheet anchor) =
        domainMap (sequence n) := by
    apply H.injective
    rw [H.apply_symm_apply]
    apply Prod.ext
    · apply Subtype.ext
      exact (hH (domainMap (sequence n))).symm
    · exact (hSheetConstant (sequence n)).symm
  have hDomainTends :
      Filter.Tendsto (fun n ↦ domainMap (sequence n)) Filter.atTop
        (𝓝 (H.symm ((⟨f 0, h0U⟩ : U), sheet anchor))) := by
    exact hInverseTends.congr' (Filter.Eventually.of_forall hInverseEquals)
  have hRealTendsPositive :
      Filter.Tendsto (fun n ↦ (sequence n : ℝ)) Filter.atTop
        (𝓝 ((H.symm ((⟨f 0, h0U⟩ : U), sheet anchor)).1.1 : ℝ)) := by
    have hCoercionTends :=
      (continuous_subtype_val.comp continuous_subtype_val).tendsto
        (H.symm ((⟨f 0, h0U⟩ : U), sheet anchor)) |>.comp hDomainTends
    exact hCoercionTends.congr' (Filter.Eventually.of_forall fun n ↦ rfl)
  have hLimitZero :
      ((H.symm ((⟨f 0, h0U⟩ : U), sheet anchor)).1.1 : ℝ) = 0 :=
    tendsto_nhds_unique hRealTendsPositive hSequenceTendsZero
  exact (H.symm ((⟨f 0, h0U⟩ : U), sheet anchor)).1.property.ne' hLimitZero

/-- The positive-real circle exponential is surjective. -/
theorem positiveRealExp_surjective : Function.Surjective positiveRealExp := by
  -- One full turn inside `[1, 2]` already covers the circle.
  intro y
  obtain ⟨x, hx, hxy⟩ := surjOn_Icc_int_turnExp 1 (Set.mem_univ y)
  have hxPositive : 0 < x := by
    norm_num at hx ⊢
    linarith
  exact ⟨⟨x, hxPositive⟩, hxy⟩

/-- The positive-real circle exponential is a local homeomorphism. -/
theorem positiveRealExp_isLocalHomeomorph : IsLocalHomeomorph positiveRealExp := by
  -- Restrict the covering map `turnExp` along the open positive-ray inclusion.
  unfold positiveRealExp
  simpa [Function.comp_def] using
    isCoveringMap_turnExp.isLocalHomeomorph.comp
      isOpen_Ioi.isOpenEmbedding_subtypeVal.isLocalHomeomorph

/-- The point `1 : Circle` is not evenly covered by the positive-real circle exponential. -/
theorem positiveRealExp_not_isEvenlyCovered_one :
    ¬ IsEvenlyCovered positiveRealExp (1 : Circle)
      (positiveRealExp ⁻¹' {(1 : Circle)}) := by
  -- Apply the omitted-endpoint obstruction to `turnExp` at `0`.
  unfold positiveRealExp
  rw [← turnExp_zero]
  exact not_isEvenlyCovered_restrictIoi turnExp
    isCoveringMap_turnExp.continuous.continuousAt

end Circle
