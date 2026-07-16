import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap02.Definition_2_14
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap02.Exercise_2_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory unitInterval

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The counting process obtained from a Poisson number of marks on `[0,1]`, where `L` is the
random number of marks and `X n` is the location of the `n`th mark as an `I`-valued random
variable. The count at time `t` records how many of the first `L` marks fall in `(0,t]`. -/
def poissonizedUniformCountingProcess (L : Ω → ℕ) (X : ℕ → Ω → I) :
    I → Ω → ℕ :=
  fun t ω ↦ Finset.sum (Finset.Icc 1 (L ω))
    (fun i ↦ if (0 : I) < X i ω ∧ X i ω ≤ t then 1 else 0)

section

omit [MeasurableSpace Ω]

/-- The Poissonized counting process counts the marks among `X 1, …, X (L ω)` that lie in
`(0,t]`. -/
theorem poissonizedUniformCountingProcess_apply (L : Ω → ℕ) (X : ℕ → Ω → I)
    (t : I) (ω : Ω) :
    poissonizedUniformCountingProcess L X t ω =
      Finset.sum (Finset.Icc 1 (L ω))
        (fun i ↦ if (0 : I) < X i ω ∧ X i ω ≤ t then 1 else 0) :=
  rfl

end

-- Proof sketch: for a finite increasing grid `0 = t₀ < ⋯ < t_m ≤ 1`, identify the increment
-- `N_{t_i} - N_{t_{i-1}}` with the number of indices `l ≤ L` whose mark lies in `(t_{i-1}, t_i]`.
-- Conditional on `L = n`, these counts are multinomial with cell probabilities
-- `t_i - t_{i-1}` because the marks are i.i.d. uniform on `[0,1]`; multiplying by the Poisson law
-- of `L` shows that the increments are independent Poisson with parameters
-- `α (t_i - t_{i-1})`.
section

variable (P : Measure Ω) [IsProbabilityMeasure P] (α : NNReal) (L : Ω → ℕ) (X : ℕ → Ω → I)

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: subtracting the indicators of `(0,t]` and `(0,s]` isolates the
intermediate cell `(s,t]`. -/
theorem poissonized_uniform_indicator_sub_eq_interval_indicator {x s t : I} (hst : s ≤ t) :
    (if (0 : I) < x ∧ x ≤ t then 1 else 0) - (if (0 : I) < x ∧ x ≤ s then 1 else 0) =
      (if s < x ∧ x ≤ t then 1 else 0) := by
  -- Split on whether the point lies in `(0,t]`; this reduces the claim to the two geometric cases.
  by_cases hit : (0 : I) < x ∧ x ≤ t
  · rcases hit with ⟨h0, hxt⟩
    by_cases hs : x ≤ s
    · have hs' : (0 : I) < x ∧ x ≤ s := ⟨h0, hs⟩
      have hnot : ¬(s < x ∧ x ≤ t) := by
        intro hsx
        exact not_lt_of_ge hs hsx.1
      simp [hxt, hs']
    · have hsx : s < x := lt_of_not_ge hs
      have hs' : ¬((0 : I) < x ∧ x ≤ s) := by
        intro h
        exact hs h.2
      have hx0 : x ≠ 0 := ne_of_gt h0
      simp [hxt, hs', hsx, hx0]
  · have hs' : ¬((0 : I) < x ∧ x ≤ s) := by
      intro hs
      exact hit ⟨hs.1, hs.2.trans hst⟩
    have hnot : ¬(s < x ∧ x ≤ t) := by
      intro hsx
      exact hit ⟨lt_of_le_of_lt (show (0 : I) ≤ s from bot_le) hsx.1, hsx.2⟩
    simp [hit, hs', hnot]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: each increment of the Poissonized counting process is the number of
marks among `X 1, …, X (L ω)` that fall in the half-open interval `(s,t]`. -/
theorem poissonizedUniformCountingProcess_increment_eq_interval_count {s t : I} (hst : s ≤ t)
    (ω : Ω) :
    poissonizedUniformCountingProcess L X t ω - poissonizedUniformCountingProcess L X s ω =
      Finset.sum (Finset.Icc 1 (L ω))
        (fun i ↦ if s < X i ω ∧ X i ω ≤ t then 1 else 0) := by
  rw [poissonizedUniformCountingProcess, poissonizedUniformCountingProcess]
  -- Rewrite the increment as a sum of termwise differences.
  calc
    (∑ i ∈ Finset.Icc 1 (L ω), if (0 : I) < X i ω ∧ X i ω ≤ t then 1 else 0) -
        (∑ i ∈ Finset.Icc 1 (L ω), if (0 : I) < X i ω ∧ X i ω ≤ s then 1 else 0) =
      ∑ i ∈ Finset.Icc 1 (L ω),
        ((if (0 : I) < X i ω ∧ X i ω ≤ t then 1 else 0) -
          (if (0 : I) < X i ω ∧ X i ω ≤ s then 1 else 0)) := by
        symm
        refine Finset.sum_tsub_distrib (Finset.Icc 1 (L ω)) ?_
        intro i hi
        by_cases hit : (0 : I) < X i ω ∧ X i ω ≤ t
        · rcases hit with ⟨h0, hxt⟩
          by_cases hs : X i ω ≤ s
          · simp [hxt, h0, hs]
          · simp [hxt, h0, hs]
        · have hs' : ¬((0 : I) < X i ω ∧ X i ω ≤ s) := by
            intro hs
            exact hit ⟨hs.1, hs.2.trans hst⟩
          simp [hit, hs']
    -- Collapse each summand to the indicator of the cell `(s,t]`.
    _ = ∑ i ∈ Finset.Icc 1 (L ω), if s < X i ω ∧ X i ω ≤ t then 1 else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact poissonized_uniform_indicator_sub_eq_interval_indicator hst

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the Poissonized counting process starts at zero because `(0,0]` is
empty. -/
theorem poissonizedUniformCountingProcess_zero_eq :
    poissonizedUniformCountingProcess L X 0 = 0 := by
  ext ω
  rw [poissonizedUniformCountingProcess]
  -- Every summand vanishes because no point can satisfy `x ≤ 0` and `0 < x` simultaneously.
  refine Finset.sum_eq_zero ?_
  intro i hi
  by_cases h0 : (0 : I) < X i ω
  · have hx0 : X i ω ≠ 0 := ne_of_gt h0
    simp [h0, hx0]
  · simp [h0]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the Poissonized counting process is nondecreasing in time, since
increasing the right endpoint can only add marked points to the half-open interval `(0,t]`. -/
theorem poissonizedUniformCountingProcess_mono :
    Monotone (poissonizedUniformCountingProcess L X) := by
  intro s t hst ω
  rw [poissonizedUniformCountingProcess, poissonizedUniformCountingProcess]
  refine Finset.sum_le_sum ?_
  intro i hi
  by_cases hs : (0 : I) < X i ω ∧ X i ω ≤ s
  · have ht : (0 : I) < X i ω ∧ X i ω ≤ t := ⟨hs.1, hs.2.trans hst⟩
    simp [hs, ht]
  · by_cases ht : (0 : I) < X i ω ∧ X i ω ≤ t
    · by_cases hxs : X i ω ≤ s
      · have hs' : (0 : I) < X i ω ∧ X i ω ≤ s := ⟨ht.1, hxs⟩
        exact (hs hs').elim
      · simp [ht, hxs]
    · simp [hs, ht]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: counting the grid points strictly below `x` always produces a valid
index in the full grid because the terminal grid point is `1`. -/
theorem fullGridLabel_card_lt {m : ℕ} (u : Fin (m + 1) → I)
    (h1 : u (Fin.last m) = 1) (x : I) :
    (Finset.univ.filter fun i : Fin (m + 1) ↦ u i < x).card < m + 1 := by
  -- Proof comment: the last grid point is `1`, so it can never lie strictly below a point of `I`.
  have hlast_not_mem :
      Fin.last m ∉ Finset.univ.filter fun i : Fin (m + 1) ↦ u i < x := by
    have hx_le_one : x ≤ (1 : I) := x.2.2
    have hnot_lt : ¬u (Fin.last m) < x := by
      rw [h1]
      exact not_lt_of_ge hx_le_one
    simp [hnot_lt]
  simpa using Finset.card_lt_univ_of_notMem hlast_not_mem

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the full-grid label of a point is the number of grid points lying
strictly below it. This turns the half-open grid cells into exact successor fibers. -/
noncomputable def fullGridLabel {m : ℕ} (u : Fin (m + 1) → I)
    (h1 : u (Fin.last m) = 1) : I → Fin (m + 1) :=
  fun x ↦
    ⟨(Finset.univ.filter fun i : Fin (m + 1) ↦ u i < x).card,
      fullGridLabel_card_lt u h1 x⟩

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: any point in the half-open cell `(u i, u (i+1)]` receives the
successor label `i + 1`. -/
theorem fullGridLabel_eq_succ_of_mem_Ioc {m : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h1 : u (Fin.last m) = 1) (i : Fin m) {x : I}
    (hx : u i.castSucc < x ∧ x ≤ u i.succ) :
    fullGridLabel u h1 x = i.succ := by
  -- Proof comment: monotonicity shows that the indices below `x` are exactly `0, …, i`.
  have hfilter :
      Finset.univ.filter (fun j : Fin (m + 1) ↦ u j < x) = Finset.Iic i.castSucc := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    constructor
    · intro hj
      by_contra hji
      have hij : i.succ ≤ j := by
        exact Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hji)
      have hux : x ≤ u j := le_trans hx.2 (hu hij)
      exact (not_lt_of_ge hux) hj
    · intro hj
      exact lt_of_le_of_lt (hu hj) hx.1
  apply Fin.ext
  simp [fullGridLabel, hfilter]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: if the full-grid label is `i + 1`, then the point lies in the
corresponding half-open cell `(u i, u (i+1)]`. -/
theorem fullGridLabel_mem_Ioc_of_eq_succ {m : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h1 : u (Fin.last m) = 1) (i : Fin m) {x : I}
    (hx : fullGridLabel u h1 x = i.succ) :
    x ∈ Set.Ioc (u i.castSucc) (u i.succ) := by
  have hcard_eq :
      (Finset.univ.filter (fun j : Fin (m + 1) ↦ u j < x)).card = i.succ := by
    simpa [fullGridLabel] using congrArg Fin.val hx
  constructor
  · -- Proof comment: if `x` were at or below `u i`, then fewer than `i + 1` grid points could lie
    -- strictly below `x`, contradicting the label value.
    by_contra hx_le
    have hsubset :
        Finset.univ.filter (fun j : Fin (m + 1) ↦ u j < x) ⊆ Finset.Iio i.castSucc := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_Iio]
      by_contra hj'
      have hij : i.castSucc ≤ j := le_of_not_gt hj'
      have hxuj : x ≤ u j := le_trans (not_lt.mp hx_le) (hu hij)
      exact (not_lt_of_ge hxuj) hj
    have hcard_le :
        (Finset.univ.filter (fun j : Fin (m + 1) ↦ u j < x)).card ≤ (Finset.Iio i.castSucc).card :=
      Finset.card_le_card hsubset
    simp [hcard_eq] at hcard_le
  · -- Proof comment: if `x` were strictly above `u (i + 1)`, then the first `i + 2` grid points
    -- would all lie below `x`, again contradicting the label value.
    by_contra hx_gt
    have hsubset :
        Finset.Iic i.succ ⊆ Finset.univ.filter (fun j : Fin (m + 1) ↦ u j < x) := by
      intro j hj
      have hj_le : j ≤ i.succ := by
        simpa only [Finset.mem_Iic] using hj
      have hjx : u j < x := lt_of_le_of_lt (hu hj_le) (lt_of_not_ge hx_gt)
      simp [hjx]
    have hcard_le :
        (Finset.Iic i.succ).card ≤
          (Finset.univ.filter (fun j : Fin (m + 1) ↦ u j < x)).card :=
      Finset.card_le_card hsubset
    simp [hcard_eq] at hcard_le

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the successor fiber of `fullGridLabel` is exactly the corresponding
half-open grid cell. -/
theorem fullGridLabel_preimage_succ {m : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h1 : u (Fin.last m) = 1) (i : Fin m) :
    fullGridLabel u h1 ⁻¹' ({i.succ} : Set (Fin (m + 1))) = Set.Ioc (u i.castSucc) (u i.succ) := by
  ext x
  constructor
  · intro hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    exact fullGridLabel_mem_Ioc_of_eq_succ u hu h1 i hx
  · intro hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact fullGridLabel_eq_succ_of_mem_Ioc u hu h1 i hx

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the zero fiber of the full-grid label is exactly the singleton
`{0}`. -/
theorem fullGridLabel_preimage_zero {m : ℕ} (u : Fin (m + 1) → I)
    (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1) :
    fullGridLabel u h1 ⁻¹' ({0} : Set (Fin (m + 1))) = ({0} : Set I) := by
  ext x
  constructor
  · intro hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    by_contra hx0
    have hx_pos : (0 : I) < x := lt_of_le_of_ne x.2.1 (Ne.symm hx0)
    have hzero_mem :
        (0 : Fin (m + 1)) ∈ Finset.univ.filter fun i : Fin (m + 1) ↦ u i < x := by
      have hu0x : u 0 < x := by
        simpa [h0] using hx_pos
      simp [hu0x]
    have hcard_pos :
        0 < (Finset.univ.filter fun i : Fin (m + 1) ↦ u i < x).card :=
      Finset.card_pos.mpr ⟨0, hzero_mem⟩
    have hcard_zero :
        (Finset.univ.filter fun i : Fin (m + 1) ↦ u i < x).card = 0 := by
      simpa [fullGridLabel] using congrArg Fin.val hx
    have hnot_pos :
        ¬0 <
          (Finset.univ.filter fun i : Fin (m + 1) ↦ u i < x).card := by
      simp [hcard_zero]
    exact hnot_pos hcard_pos
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    apply Fin.ext
    have hfilter_empty :
        Finset.univ.filter (fun i : Fin (m + 1) ↦ u i < (0 : I)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact (not_lt_of_ge (u i).2.1) hi
    have hcard_zero :
        (Finset.univ.filter fun i : Fin (m + 1) ↦ u i < (0 : I)).card = 0 := by
      rw [hfilter_empty]
      simp
    simp [fullGridLabel]

/-- Helper for Theorem 5.35: a full-grid label map is measurable once the singleton fibers have
been identified by the zero and successor cell descriptions. -/
theorem measurable_fullGridLabel {m : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1) :
    Measurable (fullGridLabel u h1) := by
  -- Proof comment: the codomain is finite, so it is enough to show that every singleton fiber is
  -- measurable, and those fibers are exactly `{0}` or one of the half-open grid cells.
  refine measurable_to_countable' ?_
  intro i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · rw [fullGridLabel_preimage_zero u h0 h1]
    exact measurableSet_singleton 0
  · rw [fullGridLabel_preimage_succ u hu h1 j]
    exact measurableSet_Ioc

/-- Helper for Theorem 5.35: the common law of a full-grid label under the uniform measure on `I`
is the pushforward PMF of `volume` along the full-grid label map. -/
noncomputable def fullGridLabelPMF {m : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1) : PMF (Fin (m + 1)) :=
  letI : IsProbabilityMeasure ((volume : Measure I).map (fullGridLabel u h1)) :=
    Measure.isProbabilityMeasure_map
      (measurable_fullGridLabel u hu h0 h1).aemeasurable
  (Measure.map (fullGridLabel u h1) (volume : Measure I)).toPMF

/-- Helper for Theorem 5.35: `fullGridCount u h1 L X ω i` counts how many of the first `L ω`
marks receive the full-grid label `i`, written directly with the Chapter 2 count vector
`multinomialCount`. -/
def fullGridCount {m : ℕ} (u : Fin (m + 1) → I)
    (h1 : u (Fin.last m) = 1) (L : Ω → ℕ) (X : ℕ → Ω → I) (ω : Ω) :
    Fin (m + 1) → ℕ :=
  multinomialCount (fun j : Fin (L ω) ↦ fun ω' ↦ fullGridLabel u h1 (X (j + 1) ω')) ω

section
 
omit [IsProbabilityMeasure P] in
/-- Helper for Theorem 5.35: composing the uniform marks with the measurable full-grid label map
gives the pushforward law of the label partition. -/
theorem fullGridLabel_hasLaw {m n : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1)
    (hX_law : ∀ n, HasLaw (X (n + 1)) (volume : Measure I) P) :
    HasLaw
      (fun ω ↦ fullGridLabel u h1 (X (n + 1) ω))
      (fullGridLabelPMF u hu h0 h1).toMeasure P := by
  have h_label :
      HasLaw (fullGridLabel u h1) ((volume : Measure I).map (fullGridLabel u h1))
        (volume : Measure I) := by
    exact
      (show MeasurePreserving (fullGridLabel u h1) (volume : Measure I)
          ((volume : Measure I).map (fullGridLabel u h1)) from
        ⟨measurable_fullGridLabel u hu h0 h1, rfl⟩).hasLaw
  -- Proof comment: transport the uniform law of `X (n + 1)` through the full-grid label map.
  simpa [fullGridLabelPMF, Measure.toPMF_toMeasure] using h_label.fun_comp (hX_law n)

/-- Helper for Theorem 5.35: the zero-mass of the full-grid label distribution vanishes because
the zero fiber is the singleton `{0}`, which has zero volume in `I`. -/
theorem fullGridLabel_toPMF_apply_zero {m : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1) :
    fullGridLabelPMF u hu h0 h1 0 = 0 := by
  -- Proof comment: rewrite the singleton mass by the zero-fiber identity and collapse the
  -- resulting singleton volume.
  rw [fullGridLabelPMF]
  rw [Measure.toPMF_apply]
  rw [Measure.map_apply
    (measurable_fullGridLabel u hu h0 h1) (measurableSet_singleton 0)]
  rw [fullGridLabel_preimage_zero u h0 h1]
  simp

/-- Helper for Theorem 5.35: every successor mass of the full-grid label distribution is exactly
the volume of the corresponding half-open cell. -/
theorem fullGridLabel_toPMF_apply_succ {m : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1) (i : Fin m) :
    fullGridLabelPMF u hu h0 h1 i.succ =
      volume (Set.Ioc (u i.castSucc) (u i.succ)) := by
  -- Proof comment: the successor fiber was already identified as the corresponding half-open
  -- grid cell, so its label mass is that cell's volume.
  rw [fullGridLabelPMF]
  rw [Measure.toPMF_apply]
  rw [Measure.map_apply
    (measurable_fullGridLabel u hu h0 h1) (measurableSet_singleton i.succ)]
  rw [fullGridLabel_preimage_succ u hu h1 i]

/-- Helper for Theorem 5.35: restricting a sequence of marks to a finite prefix and then applying
the full-grid label coordinatewise is measurable. -/
theorem measurable_prefix_fullGridLabel_tuple {m n : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1) :
    Measurable (fun x : ℕ → I ↦ fun j : Fin n ↦ fullGridLabel u h1 (x j)) := by
  -- Proof comment: each coordinate is an evaluation map followed by the measurable label map.
  refine measurable_pi_lambda _ ?_
  intro j
  exact (measurable_fullGridLabel u hu h0 h1).comp (measurable_pi_apply (j : ℕ))

omit [IsProbabilityMeasure P] in
/-- Helper for Theorem 5.35: the labeled first `n` marks remain independent after composing the
uniform marks with the measurable full-grid label map and restricting to the prefix `Fin n`. -/
theorem iIndepFun_prefix_fullGridLabel {m n : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P) :
    iIndepFun
      (fun j : Fin n ↦ fun ω ↦ fullGridLabel u h1 (X (j + 1) ω)) P := by
  have hlabel_indep :
      iIndepFun (fun k : ℕ ↦ fun ω ↦ fullGridLabel u h1 (X (k + 1) ω)) P := by
    -- Proof comment: postcompose each independent coordinate with the measurable label map.
    exact hX_indep.comp (fun _ ↦ fullGridLabel u h1)
      (fun _ ↦ measurable_fullGridLabel u hu h0 h1)
  -- Proof comment: the finite prefix is obtained by precomposing with `Fin.val`.
  simpa using hlabel_indep.precomp Fin.val_injective

omit [IsProbabilityMeasure P] in
/-- Helper for Theorem 5.35: the Poisson length variable is independent of the label-count vector
of any fixed finite prefix of labeled marks. -/
theorem indep_length_multinomialCount_fullGridLabel {m n : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1)
    (hLX_indep : IndepFun L (fun ω ↦ fun n : ℕ ↦ X (n + 1) ω) P) :
    IndepFun L
      (fun ω ↦
        multinomialCount
          (fun j : Fin n ↦ fun ω' ↦ fullGridLabel u h1 (X (j + 1) ω')) ω) P := by
  let prefixTuple : (ℕ → I) → (Fin n → Fin (m + 1)) :=
    fun x j ↦ fullGridLabel u h1 (x j)
  let countMap : (Fin n → Fin (m + 1)) → (Fin (m + 1) → ℕ) :=
    fun y ↦ multinomialCount (fun j : Fin n ↦ fun y' : Fin n → Fin (m + 1) ↦ y' j) y
  have hprefix_meas : Measurable prefixTuple :=
    measurable_prefix_fullGridLabel_tuple u hu h0 h1
  have hcount_meas : Measurable countMap :=
    measurable_of_finite _
  -- Proof comment: compose the sequence-valued independent partner first with the finite prefix
  -- label tuple, then with the deterministic count map on that finite tuple.
  simpa [prefixTuple, countMap, Function.comp] using
    hLX_indep.comp measurable_id (hcount_meas.comp hprefix_meas)

end

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the entries of the random-length full-grid count vector sum to the
realized sample size `L ω`. -/
theorem sum_fullGridCount {m : ℕ} (u : Fin (m + 1) → I)
    (h1 : u (Fin.last m) = 1) (ω : Ω) :
    ∑ i, fullGridCount u h1 L X ω i = L ω := by
  -- Proof comment: `fullGridCount` is defined by applying `multinomialCount` to the finite prefix
  -- of length `L ω`, so the total count is exactly that prefix length.
  simpa [fullGridCount] using
    sum_multinomialCount
      (fun j : Fin (L ω) ↦ fun ω' ↦ fullGridLabel u h1 (X (j + 1) ω')) ω

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: on the event `L ω = n`, the random-length full-grid count vector is
exactly the fixed-length label-count vector of the first `n` marks. -/
theorem fullGridCount_eq_multinomialCount_of_length_eq {m n : ℕ}
    (u : Fin (m + 1) → I) (h1 : u (Fin.last m) = 1) {ω : Ω}
    (hLn : L ω = n) :
    fullGridCount u h1 L X ω =
      multinomialCount
        (fun j : Fin n ↦ fun ω' ↦ fullGridLabel u h1 (X (j + 1) ω')) ω := by
  -- Proof comment: after replacing `L ω` by `n`, both sides are definitionally the same count.
  subst hLn
  simp [fullGridCount]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the singleton event for the random-length full-grid count vector is
the intersection of the length event `L = ∑ i, k i` with the corresponding fixed-length sample
count event. -/
theorem fullGridCount_preimage_singleton_eq_length_inter_multinomialCount {m : ℕ}
    (u : Fin (m + 1) → I) (h1 : u (Fin.last m) = 1) (k : Fin (m + 1) → ℕ) :
    fullGridCount u h1 L X ⁻¹' {k} =
      {ω | L ω = ∑ i, k i} ∩
        {ω |
          multinomialCount
            (fun j : Fin (∑ i, k i) ↦ fun ω' ↦ fullGridLabel u h1 (X (j + 1) ω')) ω = k} := by
  ext ω
  constructor
  · intro hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
    constructor
    · -- Proof comment: summing the coordinates of the count vector forces the sample length.
      have hsum : ∑ i, fullGridCount u h1 L X ω i = ∑ i, k i := by
        exact congrArg (fun v : Fin (m + 1) → ℕ ↦ ∑ i, v i) hω
      simpa [sum_fullGridCount L X u h1 ω] using hsum
    · -- Proof comment: once the length is fixed, the random-length count reduces to the fixed
      -- finite-sample count on the first `∑ i, k i` marks.
      have hLω : L ω = ∑ i, k i := by
        have hsum : ∑ i, fullGridCount u h1 L X ω i = ∑ i, k i := by
          exact congrArg (fun v : Fin (m + 1) → ℕ ↦ ∑ i, v i) hω
        simpa [sum_fullGridCount L X u h1 ω] using hsum
      simp only [Set.mem_setOf_eq]
      rw [← fullGridCount_eq_multinomialCount_of_length_eq L X u h1 hLω]
      exact hω
  · rintro ⟨hLω, hω⟩
    -- Proof comment: the fixed-length count identity rewrites the target event back to the
    -- random-length full-grid count event.
    simp only [Set.mem_setOf_eq] at hLω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [fullGridCount_eq_multinomialCount_of_length_eq L X u h1 hLω]
    exact hω

omit [IsProbabilityMeasure P] in
private theorem iid_uniform_marks_hasLaw
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX1_law : HasLaw (X 1) (volume : Measure I) P) :
    ∀ n, HasLaw (X (n + 1)) (volume : Measure I) P := by
  intro n
  simpa using (hX_iid.identDistrib 0 n).hasLaw hX1_law

omit [IsProbabilityMeasure P] in
/-- Helper for Theorem 5.35: the full-grid count singleton event has the textbook
multinomial-times-Poisson mass obtained by conditioning on `L = ∑ i, k i`. -/
theorem fullGridCount_preimage_singleton_eq_multinomial_mul_poisson {m : ℕ}
    (u : Fin (m + 1) → I) (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1)
    (hL : HasLaw L (poissonMeasure α) P)
    (hLX_indep : IndepFun L (fun ω ↦ fun n : ℕ ↦ X (n + 1) ω) P)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX1_law : HasLaw (X 1) (volume : Measure I) P)
    (k : Fin (m + 1) → ℕ) :
    P (fullGridCount u h1 L X ⁻¹' {k}) =
      (poissonMeasure α) {∑ i, k i} *
        ((Nat.multinomial Finset.univ k : ENNReal) *
          ∏ i, (fullGridLabelPMF u hu h0 h1 i) ^ k i) := by
  haveI : IsProbabilityMeasure P := hL.isProbabilityMeasure
  have hX_indep : iIndepFun (fun n ↦ X (n + 1)) P := hX_iid.iIndepFun
  have hX_law : ∀ n, HasLaw (X (n + 1)) (volume : Measure I) P :=
    iid_uniform_marks_hasLaw P X hX_iid hX1_law
  let Y : Fin (∑ i, k i) → Ω → Fin (m + 1) :=
    fun j ↦ fun ω ↦ fullGridLabel u h1 (X (j + 1) ω)
  have h_indep_count :
      IndepFun L (fun ω ↦ multinomialCount Y ω) P := by
    -- Proof comment: the length variable is independent of the fixed-prefix label-count vector.
    simpa [Y] using
      indep_length_multinomialCount_fullGridLabel P L X u hu h0 h1 hLX_indep
  have h_length_mass :
      P (L ⁻¹' ({∑ i, k i} : Set ℕ)) = (poissonMeasure α) {∑ i, k i} := by
    -- Proof comment: read the length singleton directly from the Poisson law of `L`.
    rw [← Measure.map_apply_of_aemeasurable hL.aemeasurable (measurableSet_singleton _), hL.map_eq]
  have h_count_mass :
      P ((fun ω ↦ multinomialCount Y ω) ⁻¹' ({k} : Set (Fin (m + 1) → ℕ))) =
        (Nat.multinomial Finset.univ k : ENNReal) *
          ∏ i, (fullGridLabelPMF u hu h0 h1 i) ^ k i := by
    have hY_law : ∀ j, HasLaw (Y j) (fullGridLabelPMF u hu h0 h1).toMeasure P := by
      intro j
      simpa [Y] using fullGridLabel_hasLaw P X u hu h0 h1 hX_law
    -- Proof comment: conditional on the fixed length, the labeled marks have multinomial law.
    simpa [Y] using
      multinomialCount_preimage_singleton_eq_multinomial_of_sum_eq
        (fullGridLabelPMF u hu h0 h1) Y
        (iIndepFun_prefix_fullGridLabel P X u hu h0 h1 hX_indep)
        hY_law k rfl
  -- Proof comment: the event identity isolates the conditioning on `L = ∑ i, k i`.
  rw [fullGridCount_preimage_singleton_eq_length_inter_multinomialCount L X u h1 k]
  calc
    P ({ω | L ω = ∑ i, k i} ∩ {ω | multinomialCount Y ω = k}) =
        P (L ⁻¹' ({∑ i, k i} : Set ℕ) ∩
          (fun ω ↦ multinomialCount Y ω) ⁻¹' ({k} : Set (Fin (m + 1) → ℕ))) := by
          rfl
    _ = P (L ⁻¹' ({∑ i, k i} : Set ℕ)) *
          P ((fun ω ↦ multinomialCount Y ω) ⁻¹' ({k} : Set (Fin (m + 1) → ℕ))) := by
          exact h_indep_count.measure_inter_preimage_eq_mul
            ({∑ i, k i} : Set ℕ) ({k} : Set (Fin (m + 1) → ℕ))
            (measurableSet_singleton _) (measurableSet_singleton _)
    _ = (poissonMeasure α) {∑ i, k i} *
          ((Nat.multinomial Finset.univ k : ENNReal) *
            ∏ i, (fullGridLabelPMF u hu h0 h1 i) ^ k i) := by
          rw [h_length_mass, h_count_mass]

omit [IsProbabilityMeasure P] in
/-- Theorem 5.35: if `L` has Poisson law with parameter `α`, the marks `X₁, X₂, …` are i.i.d.
uniform on `[0,1]`, and `L` is independent of the whole mark sequence, then the counting family
`t ↦ #{l ≤ L : 0 < X_l ≤ t}` satisfies on `[0,1]` the source-facing counting-process conditions
corresponding to the chapter's canonical Poisson-process owner abstraction: it starts at `0`, is
nondecreasing, has independent increments, and its interval increments have the expected Poisson
laws. -/
theorem poissonized_uniform_counting_process_is_poisson_process_on_unit_interval
    (hL : HasLaw L (poissonMeasure α) P)
    (hLX_indep : IndepFun L (fun ω ↦ fun n : ℕ ↦ X (n + 1) ω) P)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX1_law : HasLaw (X 1) (volume : Measure I) P) :
    let N := poissonizedUniformCountingProcess L X
    N 0 = 0 ∧
      Monotone N ∧
      HasIndepIncrements N P ∧
      ∀ ⦃s t : I⦄, s ≤ t →
        HasLaw
          (fun ω ↦ N t ω - N s ω)
          (poissonMeasure (α * Real.toNNReal ((t : ℝ) - (s : ℝ)))) P := by
  haveI : IsProbabilityMeasure P := hL.isProbabilityMeasure
  have hX_indep : iIndepFun (fun n ↦ X (n + 1)) P := hX_iid.iIndepFun
  have hX_law : ∀ n, HasLaw (X (n + 1)) (volume : Measure I) P :=
    iid_uniform_marks_hasLaw P X hX_iid hX1_law
  dsimp
  refine ⟨poissonizedUniformCountingProcess_zero_eq L X,
    poissonizedUniformCountingProcess_mono L X, ?_, ?_⟩
  · -- TODO: use the new singleton-event identity for `fullGridCount` together with the imported
    -- multinomial singleton-mass theorem and the independence of `L` from the labeled mark
    -- sequence to prove the full-grid count vector has product Poisson singleton masses, then
    -- package that discrete product law into `HasIndepIncrements`.
    -- Route correction: the earlier `Fin m`-only partition missed the boundary point `0`, so the
    -- exact identity `sum of cell counts = L` failed pathwise. The new route uses the full-grid
    -- label `fullGridLabel`, with zero fiber `{0}` and successor fibers
    -- `Set.Ioc (u i.castSucc) (u i.succ)`, and that pathwise bridge is now verified in
    -- `fullGridCount_preimage_singleton_eq_length_inter_multinomialCount`.
    sorry
  · intro s t hst
    -- TODO: once the full-grid product-law theorem is established, specialize it to the grid
    -- `0, s, t, 1` and rewrite the middle cell count by
    -- `poissonizedUniformCountingProcess_increment_eq_interval_count`.
    have hincrement :=
      poissonizedUniformCountingProcess_increment_eq_interval_count L X hst
    sorry

end

end
