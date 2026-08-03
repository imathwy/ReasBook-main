module

public import Topology_Munkres_2000.Book.Definition_61_2
public import Topology_Munkres_2000.Book.Example_24_7.Connectedness

public section

open Set

namespace TopologistsSineCurve

/-- Helper for Exercise 63.3: the closed left core cut off at first coordinate `c`. -/
def leftCore (c : ℝ) : Set Space :=
  {z | z.1.1 ≤ c}

/-- Helper for Exercise 63.3: membership in a left core is the cutoff
inequality on the first coordinate. -/
@[simp] lemma mem_leftCore {c : ℝ} {z : Space} :
    z ∈ leftCore c ↔ z.1.1 ≤ c := by
  -- Expose the defining coordinate condition to importing modules.
  rfl

/-- Helper for Exercise 63.3: every coordinate left core is closed in the
topologist's sine-curve space. -/
lemma isClosed_leftCore (c : ℝ) : IsClosed (leftCore c) := by
  -- The core is the preimage of a closed lower interval under the first coordinate.
  rw [show leftCore c = (fun z : Space ↦ z.1.1) ⁻¹' Set.Iic c from rfl]
  exact isClosed_Iic.preimage
    (continuous_fst.comp continuous_subtype_val)

/-- Helper for Exercise 63.3: the `n`th cutoff inside a positive left core. -/
noncomputable def leftCoreCutoff (c : ℝ) (n : ℕ) : ℝ :=
  c / (n + 2 : ℕ)

/-- Helper for Exercise 63.3: each cutoff inside a positive left core is positive. -/
lemma leftCoreCutoff_pos {c : ℝ} (hc : 0 < c) (n : ℕ) :
    0 < leftCoreCutoff c n := by
  -- Both the numerator and the natural-number denominator are positive.
  unfold leftCoreCutoff
  positivity

/-- Helper for Exercise 63.3: each inner cutoff is strictly below its outer cutoff. -/
lemma leftCoreCutoff_lt {c : ℝ} (hc : 0 < c) (n : ℕ) :
    leftCoreCutoff c n < c := by
  -- Dividing by `n + 2 > 1` strictly decreases a positive number.
  have hden : (1 : ℝ) < (n + 2 : ℕ) := by
    have hnat : 1 < n + 2 := by omega
    exact_mod_cast hnat
  rw [leftCoreCutoff]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n + 2 : ℕ))).2
  nlinarith

/-- Helper for Exercise 63.3: the cutoff family is antitone in its index. -/
lemma leftCoreCutoff_anti {c : ℝ} (hc : 0 < c) {m n : ℕ} (hmn : m ≤ n) :
    leftCoreCutoff c n ≤ leftCoreCutoff c m := by
  -- Increasing a positive denominator decreases the quotient.
  have hmpos : (0 : ℝ) < (m + 2 : ℕ) := by positivity
  have hnpos : (0 : ℝ) < (n + 2 : ℕ) := by positivity
  have hden : ((m + 2 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hmn 2
  unfold leftCoreCutoff
  exact (div_le_div_iff_of_pos_left hc hnpos hmpos).2 hden

/-- Helper for Exercise 63.3: the standard vertical interval belongs to the sine carrier. -/
lemma leftCoreVerticalParam_mem (t : unitInterval) :
    ((0 : ℝ), 2 * (t : ℝ) - 1) ∈ carrier := by
  -- The first coordinate is zero and the affine second coordinate stays in `[-1,1]`.
  rw [carrier_eq_curve_union_vertical]
  right
  rw [mem_vertical_iff]
  constructor
  · rfl
  · constructor <;> linarith [t.property.1, t.property.2]

/-- Helper for Exercise 63.3: the vertical interval as a path in the sine-curve space. -/
def leftCoreVerticalParam (t : unitInterval) : Space :=
  ⟨((0 : ℝ), 2 * (t : ℝ) - 1), leftCoreVerticalParam_mem t⟩

/-- Helper for Exercise 63.3: the vertical parametrization is continuous. -/
lemma continuous_leftCoreVerticalParam : Continuous leftCoreVerticalParam := by
  -- Continuity is coordinatewise before lifting through the subtype.
  apply Continuous.subtype_mk
  fun_prop

/-- Helper for Exercise 63.3: the vertical parametrization is injective. -/
lemma injective_leftCoreVerticalParam : Function.Injective leftCoreVerticalParam := by
  -- Equality of second coordinates determines the interval parameter.
  intro s t hst
  have hsnd := congrArg (fun z : Space ↦ z.1.2) hst
  apply Subtype.ext
  dsimp [leftCoreVerticalParam] at hsnd ⊢
  linarith

/-- Helper for Exercise 63.3: the vertical parametrization has exactly the vertical-part range. -/
lemma range_leftCoreVerticalParam :
    Set.range leftCoreVerticalParam = verticalPart := by
  -- The inverse affine coordinate is `(y + 1) / 2`.
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    rw [mem_verticalPart_iff, mem_vertical_iff]
    change (0 : ℝ) = 0 ∧ 2 * (t : ℝ) - 1 ∈ Icc (-1 : ℝ) 1
    constructor
    · rfl
    · constructor <;> linarith [t.property.1, t.property.2]
  · intro hz
    rw [mem_verticalPart_iff, mem_vertical_iff] at hz
    have ht : (z.1.2 + 1) / 2 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hz.2.1, hz.2.2]
    let t : unitInterval := ⟨(z.1.2 + 1) / 2, ht⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hz.1.symm
    · dsimp [leftCoreVerticalParam, t]
      linarith

/-- Helper for Exercise 63.3: the affine first coordinate of an inner graph tail. -/
noncomputable def leftCoreTailX (c : ℝ) (n : ℕ) (t : unitInterval) : ℝ :=
  leftCoreCutoff c n + (c - leftCoreCutoff c n) * (t : ℝ)

/-- Helper for Exercise 63.3: an inner graph-tail parameter has positive first coordinate. -/
lemma leftCoreTailX_pos {c : ℝ} (hc : 0 < c) (n : ℕ) (t : unitInterval) :
    0 < leftCoreTailX c n t := by
  -- The affine coordinate starts at the positive inner cutoff.
  have hfactor : 0 ≤ c - leftCoreCutoff c n :=
    sub_nonneg.mpr (leftCoreCutoff_lt hc n).le
  unfold leftCoreTailX
  nlinarith [leftCoreCutoff_pos hc n, t.property.1]

/-- Helper for Exercise 63.3: an inner graph-tail parameter is at most the outer cutoff. -/
lemma leftCoreTailX_le {c : ℝ} (hc : 0 < c) (n : ℕ) (t : unitInterval) :
    leftCoreTailX c n t ≤ c := by
  -- The affine coordinate ends at `c` and the interval parameter is at most one.
  have hfactor : 0 ≤ c - leftCoreCutoff c n :=
    sub_nonneg.mpr (leftCoreCutoff_lt hc n).le
  unfold leftCoreTailX
  nlinarith [t.property.2]

/-- Helper for Exercise 63.3: each inner graph-tail point belongs to the sine carrier. -/
lemma leftCoreTailParam_mem {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (n : ℕ) (t : unitInterval) :
    (leftCoreTailX c n t, Real.sin (1 / leftCoreTailX c n t)) ∈ carrier := by
  -- Positivity and the outer bound put the point on the defining graph.
  rw [carrier_eq_curve_union_vertical]
  left
  exact ⟨leftCoreTailX c n t,
    ⟨leftCoreTailX_pos hc n t, (leftCoreTailX_le hc n t).trans hc1⟩, rfl⟩

/-- Helper for Exercise 63.3: the graph tail from the inner cutoff to `c`. -/
noncomputable def leftCoreTailParam (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (n : ℕ) (t : unitInterval) : Space :=
  ⟨(leftCoreTailX c n t, Real.sin (1 / leftCoreTailX c n t)),
    leftCoreTailParam_mem hc hc1 n t⟩

/-- Helper for Exercise 63.3: every inner graph-tail parametrization is continuous. -/
lemma continuous_leftCoreTailParam {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (n : ℕ) : Continuous (leftCoreTailParam c hc hc1 n) := by
  -- The reciprocal is continuous because the affine first coordinate is positive.
  apply Continuous.subtype_mk
  have hx : Continuous (leftCoreTailX c n) := by
    unfold leftCoreTailX
    fun_prop
  exact hx.prodMk (Real.continuous_sin.comp
    (continuous_const.div hx (fun t ↦ (leftCoreTailX_pos hc n t).ne')))

/-- Helper for Exercise 63.3: every inner graph-tail parametrization is injective. -/
lemma injective_leftCoreTailParam {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (n : ℕ) : Function.Injective (leftCoreTailParam c hc hc1 n) := by
  -- The strictly positive affine coefficient lets the first coordinate recover the parameter.
  intro s t hst
  have hfst := congrArg (fun z : Space ↦ z.1.1) hst
  apply Subtype.ext
  dsimp [leftCoreTailParam, leftCoreTailX] at hfst ⊢
  have hfactor : 0 < c - leftCoreCutoff c n := sub_pos.mpr (leftCoreCutoff_lt hc n)
  nlinarith

/-- Helper for Exercise 63.3: the inner tail is exactly the graph between its two cutoffs. -/
lemma range_leftCoreTailParam {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) :
    Set.range (leftCoreTailParam c hc hc1 n) =
      {z : Space | leftCoreCutoff c n ≤ z.1.1 ∧ z.1.1 ≤ c} := by
  -- Forward membership is affine monotonicity; backward membership solves for the parameter.
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    constructor
    · change leftCoreCutoff c n ≤ leftCoreTailX c n t
      have hfactor : 0 ≤ c - leftCoreCutoff c n :=
        sub_nonneg.mpr (leftCoreCutoff_lt hc n).le
      unfold leftCoreTailX
      nlinarith [t.property.1]
    · exact leftCoreTailX_le hc n t
  · intro hz
    have hzCurve : z.1 ∈ curve := by
      have hzCarrier := z.property
      change z.1 ∈ carrier at hzCarrier
      rw [carrier_eq_curve_union_vertical] at hzCarrier
      rcases hzCarrier with hzCurve | hzVertical
      · exact hzCurve
      · rw [mem_vertical_iff] at hzVertical
        linarith [hz.1, leftCoreCutoff_pos hc n]
    rcases hzCurve with ⟨u, hu, huz⟩
    have hfactor : 0 < c - leftCoreCutoff c n := sub_pos.mpr (leftCoreCutoff_lt hc n)
    have hzu : z.1.1 = u := congrArg Prod.fst huz.symm
    have ht : (z.1.1 - leftCoreCutoff c n) / (c - leftCoreCutoff c n) ∈
        Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hz.1) hfactor.le
      · exact (div_le_one hfactor).2 (by linarith [hz.2])
    let t : unitInterval :=
      ⟨(z.1.1 - leftCoreCutoff c n) / (c - leftCoreCutoff c n), ht⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · dsimp [leftCoreTailParam, leftCoreTailX, t]
      field_simp
      ring
    · have hsnd : z.1.2 = Real.sin (1 / z.1.1) := by
        rw [hzu]
        exact congrArg Prod.snd huz.symm
      dsimp [leftCoreTailParam]
      rw [hsnd]
      congr 2
      dsimp [leftCoreTailX, t]
      field_simp
      ring

/-- Helper for Exercise 63.3: the decreasing inner cores intersect in the vertical part. -/
lemma iInter_leftCore_eq_verticalPart {c : ℝ} (hc : 0 < c) :
    (⋂ n : ℕ, {z : Space | z.1.1 ≤ leftCoreCutoff c n}) = verticalPart := by
  -- A positive first coordinate eventually exceeds the cutoffs tending to zero.
  ext z
  constructor
  · intro hz
    have hznonneg : 0 ≤ z.1.1 := by
      have hzCarrier := z.property
      change z.1 ∈ carrier at hzCarrier
      rw [carrier_eq_curve_union_vertical] at hzCarrier
      rcases hzCarrier with hzCurve | hzVertical
      · rcases hzCurve with ⟨u, hu, huz⟩
        rw [← huz]
        exact hu.1.le
      · exact ((mem_vertical_iff z.1).1 hzVertical).1.symm.le
    have hzfst : z.1.1 = 0 := by
      apply le_antisymm
      · by_contra hzpos
        have hx : 0 < z.1.1 := lt_of_not_ge hzpos
        obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (c / z.1.1)
        have hden : c / z.1.1 < (n + 2 : ℕ) := by
          have hn' : (n : ℝ) < (n + 2 : ℕ) := by exact_mod_cast (show n < n + 2 by omega)
          exact hn.trans hn'
        have hdenpos : (0 : ℝ) < (n + 2 : ℕ) := by positivity
        have hcut : leftCoreCutoff c n < z.1.1 := by
          rw [leftCoreCutoff]
          apply (div_lt_iff₀ hdenpos).2
          have := (div_lt_iff₀ hx).1 hden
          nlinarith
        exact (not_lt_of_ge (Set.mem_iInter.mp hz n)) hcut
      · exact hznonneg
    rw [mem_verticalPart_iff]
    have hzCarrier := z.property
    change z.1 ∈ carrier at hzCarrier
    rw [carrier_eq_curve_union_vertical] at hzCarrier
    rcases hzCarrier with hzCurve | hzVertical
    · rcases hzCurve with ⟨u, hu, huz⟩
      have hzu : z.1.1 = u := congrArg Prod.fst huz.symm
      linarith [hu.1]
    · exact hzVertical
  · intro hz
    apply Set.mem_iInter.mpr
    intro n
    rw [mem_verticalPart_iff, mem_vertical_iff] at hz
    dsimp
    rw [hz.1]
    exact (leftCoreCutoff_pos hc n).le

/-- Helper for Exercise 63.3: a continuous injective interval image in a Hausdorff space is an arc. -/
lemma isArc_range_of_continuous_injective_leftCore
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (g : unitInterval → X) (hg : Continuous g) (hginj : Function.Injective g) :
    Topology.IsArc (Set.range g) := by
  -- Compactness of the interval upgrades the map to an embedding.
  let embedding : Topology.IsEmbedding g := hg.isClosedEmbedding hginj |>.isEmbedding
  exact ⟨⟨embedding.toHomeomorph.symm⟩⟩

/-- Helper for Exercise 63.3: every positive left cutoff has decreasing closed cores,
arc tails, and the vertical arc as their intersection. -/
theorem leftCoreTruncationData (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ (V : Set Space) (K A : ℕ → Set Space),
      Topology.IsArc V ∧ V ⊆ leftCore c ∧
      (∀ n, IsClosed (K n)) ∧
      Directed (· ⊇ ·) K ∧
      ⋂ n, K n = V ∧
      ∀ n, ∃ hAarc : Topology.IsArc (A n), leftCore c = K n ∪ A n ∧
        ∃ p : A n, @Topology.IsArc.IsEndpoint (A n) _ hAarc p ∧
          K n ∩ A n = {p.1} := by
  -- Use coordinate sublevels for the cores and affine graph intervals for their tails.
  let V : Set Space := verticalPart
  let K : ℕ → Set Space := fun n ↦ {z | z.1.1 ≤ leftCoreCutoff c n}
  let A : ℕ → Set Space := fun n ↦ Set.range (leftCoreTailParam c hc hc1 n)
  have hVarc : Topology.IsArc V := by
    change Topology.IsArc verticalPart
    rw [← range_leftCoreVerticalParam]
    exact isArc_range_of_continuous_injective_leftCore leftCoreVerticalParam
      continuous_leftCoreVerticalParam injective_leftCoreVerticalParam
  refine ⟨V, K, A, hVarc, ?_, ?_, ?_, ?_, ?_⟩
  · -- The vertical arc lies in every positive left core.
    intro z hz
    change z ∈ verticalPart at hz
    rw [mem_verticalPart_iff, mem_vertical_iff] at hz
    change z.1.1 ≤ c
    rw [hz.1]
    exact hc.le
  · -- Each coordinate sublevel is closed in the sine-curve space.
    intro n
    exact isClosed_Iic.preimage (continuous_fst.comp continuous_subtype_val)
  · -- A core at the larger index is contained in both earlier cores.
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro z hz
      exact hz.trans (leftCoreCutoff_anti hc (Nat.le_max_left i j))
    · intro z hz
      exact hz.trans (leftCoreCutoff_anti hc (Nat.le_max_right i j))
  · -- The coordinate calculation identifies the intersection with the vertical arc.
    simpa only [K, V] using iInter_leftCore_eq_verticalPart hc
  · intro n
    let g : unitInterval → Space := leftCoreTailParam c hc hc1 n
    let embedding : Topology.IsEmbedding g :=
      (continuous_leftCoreTailParam hc hc1 n).isClosedEmbedding
        (injective_leftCoreTailParam hc hc1 n) |>.isEmbedding
    let arcHomeomorph : (Set.range g) ≃ₜ unitInterval :=
      embedding.toHomeomorph.symm
    have hAarc : Topology.IsArc (A n) := by
      change Topology.IsArc (Set.range g)
      exact ⟨⟨arcHomeomorph⟩⟩
    refine ⟨hAarc, ?_, ?_⟩
    · -- Split the left core according to the inner cutoff.
      ext z
      constructor
      · intro hz
        by_cases hinner : z.1.1 ≤ leftCoreCutoff c n
        · exact Or.inl hinner
        · right
          change z ∈ Set.range (leftCoreTailParam c hc hc1 n)
          rw [range_leftCoreTailParam hc hc1 n]
          exact ⟨le_of_not_ge hinner, hz⟩
      · rintro (hz | hz)
        · exact hz.trans (leftCoreCutoff_lt hc n).le
        · change z ∈ Set.range (leftCoreTailParam c hc hc1 n) at hz
          rw [range_leftCoreTailParam hc hc1 n] at hz
          exact hz.2
    · -- The common point is the initial endpoint of the affine graph tail.
      let p : A n := ⟨leftCoreTailParam c hc hc1 n 0, Set.mem_range_self 0⟩
      refine ⟨p, ?_, ?_⟩
      · rw [@Topology.IsArc.isEndpoint_iff (A n) _ hAarc arcHomeomorph p]
        left
        apply Subtype.ext
        rfl
      · ext z
        constructor
        · intro hz
          obtain ⟨t, htz⟩ := hz.2
          have hbound : leftCoreTailX c n t ≤ leftCoreCutoff c n := by
            have hcore := hz.1
            change z.1.1 ≤ leftCoreCutoff c n at hcore
            rw [← htz] at hcore
            exact hcore
          have htZero : t = 0 := by
            apply Subtype.ext
            dsimp [leftCoreTailX] at hbound ⊢
            have hfactor : 0 < c - leftCoreCutoff c n :=
              sub_pos.mpr (leftCoreCutoff_lt hc n)
            nlinarith [t.property.1]
          rw [Set.mem_singleton_iff]
          change z = leftCoreTailParam c hc hc1 n 0
          rw [← htz, htZero]
        · intro hz
          rw [Set.mem_singleton_iff] at hz
          subst z
          constructor
          · change leftCoreTailX c n 0 ≤ leftCoreCutoff c n
            dsimp [leftCoreTailX]
            linarith
          · exact Set.mem_range_self 0

end TopologistsSineCurve
