import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_4_23 (from Items/Chap04) -/
open MeasureTheory BoxIntegral intervalIntegral

-- Proof sketch: `Fin 1` has a unique coordinate, so the componentwise inequality needed for
-- `Box.mk` is exactly the hypothesis `a < b`.
/-- The coordinatewise strict inequality needed to build the one-dimensional box attached to the
real interval `(a, b]`. -/
private theorem realIntervalBox_lower_lt_upper (a b : ℝ) (hab : a < b) :
    ∀ i : Fin 1, (![a] : Fin 1 → ℝ) i < (![b] : Fin 1 → ℝ) i := by
  -- `Fin 1` has a single coordinate, so the componentwise inequality is exactly `hab`.
  intro i
  fin_cases i
  simpa using hab

/-- The one-dimensional `Box` whose closed hull is the interval `[a, b]`. -/
def realIntervalBox (a b : ℝ) (hab : a < b) : Box (Fin 1) :=
  Box.mk ![a] ![b] (realIntervalBox_lower_lt_upper a b hab)

/-- Riemann integrability on `[0,1]`, encoded via the chapter's canonical one-dimensional box
model. This abbreviation is the chapter's interval-facing name for the recurring box-integrability
hypothesis. -/
abbrev RiemannIntegrableOnUnitInterval (f : ℝ → ℝ) : Prop :=
  Integrable (realIntervalBox 0 1 zero_lt_one) IntegrationParams.Riemann
    (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul

-- Proof sketch: unfold `realIntervalBox` and `Box.Icc`, then use that every point of `Fin 1 → ℝ`
-- is determined by its unique coordinate.
private theorem realIntervalBox_Icc_eq (a b : ℝ) (hab : a < b) :
    Box.Icc (realIntervalBox a b hab) = Set.Icc ![a] ![b] := by
  -- The closed hull of the box is definitionally the closed interval between its endpoints.
  rfl

/-- Helper for Theorem 4.23: transport the set integral over the one-dimensional `Fin 1` box model
to the ordinary set integral over the corresponding real interval. -/
private lemma setIntegral_Icc_funUnique_eq {f : ℝ → ℝ} {a b : ℝ} :
    (∫ x in Set.Icc ![a] ![b], f (x 0) ∂volume) = ∫ x in Set.Icc a b, f x ∂volume := by
  let g : (Fin 1 → ℝ) → ℝ := fun x ↦ f (x 0)
  have h_transport : ∀ (u v : Fin 1 → ℝ) (h : (Fin 1 → ℝ) → ℝ),
      ∫ x in Set.Icc u v, h x ∂volume = ∫ x in Set.Icc (u 0) (v 0), h (fun _ ↦ x) ∂volume :=
    fun u v h ↦ by
      -- The measurable equivalence `Fin 1 → ℝ ≃ᵐ ℝ` preserves volume and sends `Icc u v` to the
      -- real interval `Icc (u 0) (v 0)`.
      convert (((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _).setIntegral_preimage_emb
        (MeasurableEquiv.measurableEmbedding _) h _).symm
      exact ((OrderIso.funUnique (Fin 1) ℝ).symm.preimage_Icc u v).symm
  simpa [g] using h_transport ![a] ![b] g

/-- Helper for Theorem 4.23: transport Lebesgue integrability between the one-dimensional `Fin 1`
box model and the ordinary real interval. -/
private lemma integrableOn_Icc_funUnique_iff {f : ℝ → ℝ} {a b : ℝ} :
    IntegrableOn (fun x : Fin 1 → ℝ ↦ f (x 0)) (Set.Icc ![a] ![b]) volume ↔
      IntegrableOn f (Set.Icc a b) volume := by
  let e : (Fin 1 → ℝ) → ℝ := fun x ↦ x 0
  have he : MeasurableEmbedding e :=
    MeasurableEquiv.measurableEmbedding (MeasurableEquiv.funUnique (Fin 1) ℝ)
  have hp : MeasurePreserving e volume volume :=
    MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ
  have himage : e '' Set.Icc ![a] ![b] = Set.Icc a b := by
    -- The unique coordinate identifies the `Fin 1` interval with the ordinary real interval.
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [Set.mem_Icc, Pi.le_def] using hx
    · intro hy
      refine ⟨fun _ ↦ y, ?_, rfl⟩
      simpa [Set.mem_Icc, Pi.le_def] using hy
  -- Apply measure-preserving transport along the unique-coordinate equivalence.
  simpa [e, himage] using
    (hp.integrableOn_image he (f := f) (s := Set.Icc ![a] ![b])).symm

/-- Helper for Theorem 4.23: retag a tagged prepartition at one chosen box while keeping the
underlying prepartition fixed. -/
private def retaggedAt {ι : Type*} [Fintype ι] [DecidableEq (Box ι)] {I : Box ι}
    (π : TaggedPrepartition I) {J : Box ι} (x : ι → ℝ) (hxI : x ∈ Box.Icc I) :
    TaggedPrepartition I :=
  { toPrepartition := π.toPrepartition
    tag := Function.update π.tag J x
    tag_mem_Icc := fun K ↦ by
      by_cases hK : K = J
      · subst hK
        simpa [Function.update_self] using hxI
      · simpa [Function.update_of_ne hK] using π.tag_mem_Icc K }

/-- Helper for Theorem 4.23: away from the retagged box, `retaggedAt` keeps the original tags. -/
private lemma retaggedAt_tag_of_ne {ι : Type*} [Fintype ι] [DecidableEq (Box ι)] {I : Box ι}
    (π : TaggedPrepartition I) {J K : Box ι} {x : ι → ℝ} {hxI : x ∈ Box.Icc I} (hK : K ≠ J) :
    (retaggedAt π (J := J) x hxI).tag K = π.tag K := by
  simp [retaggedAt, Function.update_of_ne hK]

/-- Helper for Theorem 4.23: on the chosen box, `retaggedAt` replaces the old tag by the new one. -/
private lemma retaggedAt_tag_self {ι : Type*} [Fintype ι] [DecidableEq (Box ι)] {I : Box ι}
    (π : TaggedPrepartition I) {J : Box ι} {x : ι → ℝ} {hxI : x ∈ Box.Icc I} :
    (retaggedAt π (J := J) x hxI).tag J = x := by
  simp [retaggedAt]

/-- Helper for Theorem 4.23: retagging a single box changes the integral sum exactly by that
single-box contribution. -/
private lemma integralSum_retaggedAt_sub_eq {ι : Type*} [Fintype ι] {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [DecidableEq (Box ι)] {I : Box ι} (π : TaggedPrepartition I) {J : Box ι} (hJ : J ∈ π)
    {f : (ι → ℝ) → E} {vol : ι →ᵇᵃ E →L[ℝ] F} {x : ι → ℝ} {hxI : x ∈ Box.Icc I} :
    integralSum f vol (retaggedAt π (J := J) x hxI) - integralSum f vol π =
      vol J (f x - f (π.tag J)) := by
  -- Rewrite both sums over the same underlying boxes and isolate the unique box whose tag changed.
  simp only [integralSum, retaggedAt]
  rw [← Finset.sum_sub_distrib]
  have h_single :
      ∑ K ∈ π.boxes,
        (vol K (f ((retaggedAt π (J := J) x hxI).tag K)) - vol K (f (π.tag K))) =
        vol J (f ((retaggedAt π (J := J) x hxI).tag J)) - vol J (f (π.tag J)) := by
    refine Finset.sum_eq_single_of_mem J hJ ?_
    · intro K hK hKJ
      rw [retaggedAt_tag_of_ne π (J := J) (K := K) (x := x) (hxI := hxI) hKJ]
      simp
  calc
    ∑ K ∈ π.boxes,
        (vol K (f ((retaggedAt π (J := J) x hxI).tag K)) - vol K (f (π.tag K))) =
        vol J (f ((retaggedAt π (J := J) x hxI).tag J)) - vol J (f (π.tag J)) := h_single
    _ = vol J (f x) - vol J (f (π.tag J)) := by
      rw [retaggedAt_tag_self π (J := J) (x := x) (hxI := hxI)]
    _ = vol J (f x - f (π.tag J)) := by rw [(vol J).map_sub]

/-- Helper for Theorem 4.23: if a tagged prepartition is subordinate to the constant radius
`r / 2`, then retagging one box by another point of the same box keeps it subordinate to the
constant radius `r`. -/
private lemma retaggedAt_isSubordinate_const {ι : Type*} [Fintype ι] [DecidableEq (Box ι)]
    {I : Box ι} (π : TaggedPrepartition I) {J : Box ι} (hJ : J ∈ π) {r : ℝ} (hr : 0 < r)
    (hr2 : 0 < r / 2) (hsub : π.IsSubordinate (fun _ : ι → ℝ ↦ ⟨r / 2, hr2⟩)) {x : ι → ℝ}
    (hx : x ∈ Box.Icc J) (hxI : x ∈ Box.Icc I) :
    (retaggedAt π (J := J) x hxI).IsSubordinate (fun _ : ι → ℝ ↦ ⟨r, hr⟩) := by
  -- On the modified box, use the triangle inequality inside the old `r / 2`-ball.
  intro K hK y hy
  by_cases hKJ : K = J
  · subst K
    rw [retaggedAt_tag_self π (J := J) (x := x) (hxI := hxI), Metric.mem_closedBall]
    have hy' : dist y (π.tag J) ≤ r / 2 := by
      exact Metric.mem_closedBall.1 (hsub J hJ hy)
    have hx' : dist (π.tag J) x ≤ r / 2 := by
      simpa [dist_comm] using Metric.mem_closedBall.1 (hsub J hJ hx)
    calc
      dist y x ≤ dist y (π.tag J) + dist (π.tag J) x := dist_triangle _ _ _
      _ ≤ r / 2 + r / 2 := add_le_add hy' hx'
      _ = r := by ring
  · rw [retaggedAt_tag_of_ne π (J := J) (K := K) (x := x) (hxI := hxI) hKJ]
    exact Metric.mem_closedBall.2 <|
      le_trans (Metric.mem_closedBall.1 (hsub K hK hy)) (by linarith)

/-- Helper for Theorem 4.23: for the Riemann filter, retagging one box by another point of that
box preserves membership in the base set once the common constant radius is doubled. -/
private lemma retaggedAt_memBaseSet_riemann_of_const {ι : Type*} [Fintype ι]
    [DecidableEq (Box ι)] {I : Box ι}
    {c : NNReal} (π : TaggedPrepartition I) {J : Box ι} (hJ : J ∈ π) {r : ℝ} (hr : 0 < r)
    (hr2 : 0 < r / 2)
    (hπ :
      IntegrationParams.Riemann.MemBaseSet I c (fun _ : ι → ℝ ↦ ⟨r / 2, hr2⟩) π)
    {x : ι → ℝ} (hx : x ∈ Box.Icc J) :
    IntegrationParams.Riemann.MemBaseSet I c (fun _ : ι → ℝ ↦ ⟨r, hr⟩)
      (retaggedAt π (J := J) x (Box.le_iff_Icc.1 (π.le_of_mem' J hJ) hx)) := by
  let hxI : x ∈ Box.Icc I := Box.le_iff_Icc.1 (π.le_of_mem' J hJ) hx
  refine ⟨retaggedAt_isSubordinate_const π hJ hr hr2 hπ.isSubordinate hx hxI, ?_, ?_, ?_⟩
  · intro _ K hK
    by_cases hKJ : K = J
    · subst K
      simpa [retaggedAt_tag_self π (J := J) (x := x) (hxI := hxI)] using hx
    · rw [retaggedAt_tag_of_ne π (J := J) (K := K) (x := x) (hxI := hxI) hKJ]
      exact hπ.isHenstock rfl K hK
  · intro hD
    cases hD
  · intro hD
    cases hD

/-- Helper for Theorem 4.23: a common fine Riemann partition controls the single-box variation
term obtained by retagging one box. -/
private lemma single_box_variation_le_of_riemann_partition
    {f : (Fin 1 → ℝ) → ℝ} {I : Box (Fin 1)}
    (hf :
      Integrable I IntegrationParams.Riemann f volume.toBoxAdditive.toSMul)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ π : TaggedPrepartition I,
      π.IsPartition ∧
      IntegrationParams.Riemann.MemBaseSet I I.distortion
        (hf.convergenceR (ε / 2) I.distortion) π ∧
      ∀ J ∈ π, ∀ x ∈ Box.Icc J,
        ‖volume.toBoxAdditive.toSMul J (f x - f (π.tag J))‖ ≤ ε := by
  classical
  -- Choose one partition subordinate to half of the constant Riemann radius.
  let r : ℝ := hf.convergenceR (ε / 2) I.distortion 0
  have hr : 0 < r := (hf.convergenceR (ε / 2) I.distortion 0).2
  have hr2 : 0 < r / 2 := half_pos hr
  let rhalf : (Fin 1 → ℝ) → Set.Ioi (0 : ℝ) := fun _ ↦ ⟨r / 2, hr2⟩
  obtain ⟨π, hπhalf, hπp⟩ :=
    IntegrationParams.exists_memBaseSet_isPartition IntegrationParams.Riemann I le_rfl rhalf
  have hconst :
      ∀ x : Fin 1 → ℝ,
        hf.convergenceR (ε / 2) I.distortion x = hf.convergenceR (ε / 2) I.distortion 0 := by
    intro x
    exact hf.convergenceR_cond (ε / 2) I.distortion rfl x
  have hπ :
      IntegrationParams.Riemann.MemBaseSet I I.distortion
        (hf.convergenceR (ε / 2) I.distortion) π := by
    -- The half-radius partition is automatically subordinate to the larger convergence radius.
    refine hπhalf.mono (I := I) le_rfl le_rfl ?_
    intro x hx
    rw [hconst x]
    change (r / 2 : ℝ) ≤ r
    linarith
  refine ⟨π, hπp, hπ, ?_⟩
  intro J hJ x hx
  let hxI : x ∈ Box.Icc I := Box.le_iff_Icc.1 (π.le_of_mem' J hJ) hx
  have hπret :
      IntegrationParams.Riemann.MemBaseSet I I.distortion
        (hf.convergenceR (ε / 2) I.distortion)
        (retaggedAt π (J := J) x hxI) := by
    -- Retagging one box stays within the full convergence radius.
    have hπret_half :
        IntegrationParams.Riemann.MemBaseSet I I.distortion
          (fun _ : Fin 1 → ℝ ↦ ⟨r, hr⟩)
          (retaggedAt π (J := J) x hxI) := by
      simpa [r] using
        retaggedAt_memBaseSet_riemann_of_const (π := π) (J := J) hJ hr hr2 hπhalf hx
    refine hπret_half.mono (I := I) le_rfl le_rfl ?_
    intro y hy
    rw [hconst y]
  -- Compare the original and retagged sums through the common Riemann limit.
  have hdist :
      dist (integralSum f volume.toBoxAdditive.toSMul (retaggedAt π (J := J) x hxI))
        (integralSum f volume.toBoxAdditive.toSMul π) ≤ ε := by
    have hhalf : 0 < ε / 2 := half_pos hε
    have :=
      hf.dist_integralSum_le_of_memBaseSet hhalf hhalf hπret hπ rfl
    simpa [add_halves] using this
  -- The difference of the two sums is exactly the single-box variation term.
  rw [dist_eq_norm] at hdist
  simpa [integralSum_retaggedAt_sub_eq π hJ] using hdist

/-- Helper for Theorem 4.23: the structural bridge from one-dimensional Riemann box integrability
to Lebesgue interval integrability and the matching interval-integral value. -/
private lemma riemann_box_intervalIntegrable_and_hasIntegral
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf :
      Integrable (realIntervalBox a b hab) IntegrationParams.Riemann
        (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul) :
    IntervalIntegrable f volume a b ∧
      HasIntegral (realIntervalBox a b hab) IntegrationParams.Riemann
        (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul (∫ x in a..b, f x ∂volume) := by
  -- Route correction: the failed ambient `AEContinuous` route was too strong, because the
  -- hypothesis only controls `f` on `[a, b]`. The remaining local work is to extract boundedness
  -- and `ContinuousWithinAt` almost everywhere on `Box.Icc (realIntervalBox a b hab)` from the
  -- Riemann filter by retagging a single common fine partition, then pass to the Lebesgue box
  -- integral through `integrable_of_bounded_and_ae_continuousWithinAt`.
  have h_transport :
      IntegrableOn (fun x : Fin 1 → ℝ ↦ f (x 0)) (Set.Icc ![a] ![b]) volume ↔
        IntegrableOn f (Set.Icc a b) volume :=
    integrableOn_Icc_funUnique_iff
  -- TODO: prove the planned Darboux-gap lemmas:
  -- 1. boundedness on `Set.Icc a b` from one fixed fine partition and the new
  --    `single_box_variation_le_of_riemann_partition` estimate;
  -- 2. boxwise oscillation control from two retaggings of the same partition;
  -- 3. `ContinuousWithinAt` almost everywhere on `Box.Icc (realIntervalBox a b hab)`;
  -- 4. use `IntegrableOn.hasBoxIntegral` with `l := Henstock`, then compare with
  --    `hf.hasIntegral.mono henstock_le_riemann` and rewrite using
  --    `realIntervalBox_Icc_eq`, `setIntegral_Icc_funUnique_eq`, and `h_transport`.
  clear h_transport
  sorry

-- Proof sketch: transport the Riemann-style `BoxIntegral.Integrable` hypothesis on the
-- one-dimensional box to a Lebesgue `IntervalIntegrable` statement on `a..b`, then identify the
-- resulting box integral with the interval integral.
/-- Theorem 4.23: if `f` is Riemann integrable on `[a,b]`, encoded here as Riemann box
integrability of `fun x ↦ f (x 0)` on the one-dimensional box attached to `(a,b]`, then `f` is
Lebesgue integrable on `a..b`, and the interval integral equals the Riemann integral. -/
theorem intervalIntegrable_and_intervalIntegral_eq_of_riemannIntegrable
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf :
      Integrable (realIntervalBox a b hab) IntegrationParams.Riemann
        (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul) :
    IntervalIntegrable f volume a b ∧
      ∫ x in a..b, f x ∂volume =
        integral (realIntervalBox a b hab) IntegrationParams.Riemann
          (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul := by
  -- Route correction: isolate the missing Riemann-to-Lebesgue bridge in one helper, then the main
  -- theorem closes by reading off interval integrability and the box-integral value.
  rcases riemann_box_intervalIntegrable_and_hasIntegral hab hf with ⟨hf_interval, hf_hasIntegral⟩
  refine ⟨hf_interval, ?_⟩
  -- Once the helper supplies the matching box integral, the numerical identity is immediate.
  exact hf_hasIntegral.integral_eq.symm

/-- Companion bridge for Theorem 4.23 in `Set.Icc` form. -/
theorem integrableOn_Icc_and_integral_eq_of_riemannIntegrable
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf :
      Integrable (realIntervalBox a b hab) IntegrationParams.Riemann
        (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul) :
    IntegrableOn f (Set.Icc a b) volume ∧
      ∫ x in Set.Icc a b, f x ∂volume =
        integral (realIntervalBox a b hab) IntegrationParams.Riemann
          (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul := by
  rcases intervalIntegrable_and_intervalIntegral_eq_of_riemannIntegrable hab hf with
    ⟨hf_interval, h_integral_eq⟩
  have hf_Icc : IntegrableOn f (Set.Icc a b) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact hf_interval
  refine ⟨hf_Icc, ?_⟩
  calc
    ∫ x in Set.Icc a b, f x ∂volume =
        ∫ x in Set.Ioc a b, f x ∂volume := integral_Icc_eq_integral_Ioc
    _ = ∫ x in a..b, f x ∂volume := (integral_of_le hab.le).symm
    _ = integral (realIntervalBox a b hab) IntegrationParams.Riemann
          (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul := h_integral_eq
