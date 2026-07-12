import DifferentialForms_Cartan_1970.VII.section28.«0001_Theorem_2».TranslatedComparisonFamilies

open Filter
open Set

open scoped Topology

/-- Helper for Cartan section28 0001_Theorem_2: the source-faithful local goal is joint
analyticity of the actual translated scalar slice on a small product neighborhood. -/
theorem translatedScalarSliceOwner_precompose_weightedEval
    {k j : ℕ} {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {t0 : Fin j → ℂ} (r : Fin j) {u : ℂ} {ρu : NNReal}
    (hu : ‖u‖ < ρu)
    {Qslice0 : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ)}
    (hQslice0 :
      HasFPowerSeriesAt
        (fun p : ℂ × (Fin k → ℂ) ↦
          F p.1 p.2 (Function.update t0 r (t0 r + u)))
        Qslice0
        ((0 : ℂ), (0 : Fin k → ℂ))) :
    let L := weightedParameterEvalCLM ρu u hu
    HasFPowerSeriesAt
      (fun p : ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1 ↦
        F p.1 (L p.2) (Function.update t0 r (t0 r + u)))
      (Qslice0.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L))
      ((0 : ℂ), 0) := by
  intro L
  -- Compose the frozen scalar slice owner with the weighted evaluation map in the Banach state
  -- variable; this isolates the remaining `Qtr -> QB` blocker to building one common `lp` lift of
  -- these already transported scalar owners.
  have hQslice0' :
      HasFPowerSeriesAt
        (fun p : ℂ × (Fin k → ℂ) ↦
          F p.1 p.2 (Function.update t0 r (t0 r + u)))
        Qslice0
        (((ContinuousLinearMap.id ℂ ℂ).prodMap L) ((0 : ℂ), 0)) := by
    simpa using hQslice0
  simpa [Function.comp, L] using
    (HasFPowerSeriesAt.compContinuousLinearMap
      (u := ((ContinuousLinearMap.id ℂ ℂ).prodMap L))
      (x := ((0 : ℂ), 0))
      hQslice0')

/-- Helper for Cartan section28 0001_Theorem_2: freezing the translated Taylor owner `Qtr` at a
single scalar parameter and then precomposing the state variable by weighted evaluation produces
an explicit owner on `ℂ × lp`. -/
theorem translatedLiftedSliceOwner_fromQtr
    {k j : ℕ} {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {t0 : Fin j → ℂ} (r : Fin j)
    {Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ)}
    {R : ENNReal}
    (hQtrBall :
      HasFPowerSeriesOnBall
        (fun p : ℂ × (Fin k → ℂ) × ℂ ↦
          F p.1 p.2.1 (Function.update t0 r (t0 r + p.2.2)))
        Qtr
        ((0 : ℂ), (0 : Fin k → ℂ), 0)
        R)
    {ρu : NNReal}
    (hρult : (ρu : ENNReal) < R)
    {u : ℂ}
    (hu : ‖u‖ < ρu) :
    ∃ Qslice0 : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ),
      HasFPowerSeriesAt
        (fun p : ℂ × (Fin k → ℂ) ↦
          F p.1 p.2 (Function.update t0 r (t0 r + u)))
        Qslice0
        ((0 : ℂ), (0 : Fin k → ℂ)) ∧
      let L := weightedParameterEvalCLM ρu u hu
      HasFPowerSeriesAt
        (fun p : ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1 ↦
          F p.1 (L p.2) (Function.update t0 r (t0 r + u)))
        (Qslice0.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L))
        ((0 : ℂ), 0) := by
  -- First freeze the translated Taylor model to a scalar slice owner at the chosen parameter.
  rcases translatedScalarSliceOwner_fromQtr
      (F := F) (t0 := t0) (r := r) (Qtr := Qtr) (R := R)
      hQtrBall hρult hu with
    ⟨Qslice0, hQslice0⟩
  refine ⟨Qslice0, hQslice0, ?_⟩
  -- Then precompose the frozen scalar owner with weighted parameter evaluation in the Banach
  -- state variable.
  simpa using
    translatedScalarSliceOwner_precompose_weightedEval
      (F := F) (t0 := t0) (r := r) (u := u) (ρu := ρu) hu
      (Qslice0 := Qslice0) hQslice0

/-- Helper for Cartan section28 0001_Theorem_2: freezing the last `n` slots of an
`(m + n)`-multilinear map at a fixed vector produces an `m`-multilinear map. -/
noncomputable def freezeRightSlots
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (e : E) :
    ∀ m n, ContinuousMultilinearMap ℂ (fun _ : Fin (m + n) => E) G →
      ContinuousMultilinearMap ℂ (fun _ : Fin m => E) G
  | m, 0, f => by
      simpa using f
  | m, n + 1, f =>
      freezeRightSlots e m n
        ((ContinuousLinearMap.apply ℂ G e).compContinuousMultilinearMap f.curryRight)

/-- Helper for Cartan section28 0001_Theorem_2: evaluating `freezeRightSlots` amounts to feeding
the original multilinear map with the active `m` inputs followed by `n` copies of the frozen
parameter direction. -/
theorem freezeRightSlots_apply
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (e : E) :
    ∀ {m n} (f : ContinuousMultilinearMap ℂ (fun _ : Fin (m + n) => E) G)
      (v : Fin m → E),
      freezeRightSlots e m n f v = f (Fin.append v (fun _ : Fin n => e)) := by
  intro m n
  induction n with
  | zero =>
      intro f v
      -- With no frozen slots left, the helper is just the original multilinear map.
      have happend : Fin.append v (fun _ : Fin 0 => e) = v := by
        funext i
        exact Fin.append_left v (fun _ : Fin 0 => e) i
      simp [freezeRightSlots, happend]
  | succ n ihn =>
      intro f v
      -- Freeze the last slot once, then use the induction hypothesis on the remaining `n` slots.
      rw [freezeRightSlots, ihn]
      simp only [Nat.add_eq, ContinuousLinearMap.compContinuousMultilinearMap_coe,
        Function.comp_apply, ContinuousLinearMap.apply_apply,
        ContinuousMultilinearMap.curryRight_apply, Nat.succ_eq_add_one]
      have hconst : Fin.snoc (fun _ : Fin n => e) e = (fun _ : Fin (n + 1) => e) := by
        funext i
        refine Fin.lastCases ?_ ?_ i
        · simp
        · intro j
          simp [Fin.snoc_castSucc]
      rw [← Fin.append_snoc, hconst]

/-- Helper for Cartan section28 0001_Theorem_2: the `n`th mixed Banach input contributes its
`n`th coefficient to the translated Taylor owner while the translated scalar slot stays fixed at
zero. -/
noncomputable def translatedMixedSlotCoordinateCLM
    {k : ℕ} (n : ℕ) :
    (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1) →L[ℂ] (ℂ × (Fin k → ℂ) × ℂ) := by
  let fstCLM : (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1) →L[ℂ] ℂ :=
    ContinuousLinearMap.fst ℂ ℂ (lp (fun _ : ℕ => Fin k → ℂ) 1)
  let nthCLM : (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1) →L[ℂ] (Fin k → ℂ) :=
    (lp.evalCLM ℂ (fun _ : ℕ => Fin k → ℂ) 1 n).comp
      (ContinuousLinearMap.snd ℂ ℂ (lp (fun _ : ℕ => Fin k → ℂ) 1))
  exact
    fstCLM.prod
      (nthCLM.prod (0 : (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1) →L[ℂ] ℂ))

/-- Helper for Cartan section28 0001_Theorem_2: the mixed-slot coordinate map keeps the scalar
`x`-input, reads the `n`th Banach coefficient, and leaves the translated parameter increment at
zero. -/
theorem translatedMixedSlotCoordinateCLM_apply
    {k : ℕ} (n : ℕ) (p : ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1) :
    translatedMixedSlotCoordinateCLM (k := k) n p = (p.1, p.2 n, 0) := by
  -- Expand the product map once: only the `x` and `n`th Banach coordinates survive.
  simp [translatedMixedSlotCoordinateCLM, lp.evalCLM]

/-- Helper for Cartan section28 0001_Theorem_2: the mixed-slot coordinate map never enlarges the
norm of a Banach input. -/
theorem translatedMixedSlotCoordinateCLM_norm_le
    {k : ℕ} (n : ℕ) (p : ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1) :
    ‖translatedMixedSlotCoordinateCLM (k := k) n p‖ ≤ ‖p‖ := by
  -- Read the mixed slot explicitly, then bound the extracted `lp` coordinate by the ambient
  -- `ℓ¹` norm of the Banach input.
  rw [translatedMixedSlotCoordinateCLM_apply, Prod.norm_def, Prod.norm_def]
  refine max_le_iff.mpr ⟨le_max_left _ _, ?_⟩
  refine max_le_iff.mpr ⟨?_, by simp⟩
  exact
    (lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0) p.2 n).trans
      (le_max_right _ _)

/-- Helper for Cartan section28 0001_Theorem_2: the degree-`m` mixed coefficient map of `Qtr`
keeps `m` active `ℂ × lp` slots and freezes the final `n` translated-parameter slots at the unit
parameter direction. -/
noncomputable def translatedQtrMixedCoeffMap
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    (m n : ℕ) :
    ContinuousMultilinearMap
      ℂ
      (fun _ : Fin m => (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1))
      (Fin k → ℂ) :=
  (freezeRightSlots ((0 : ℂ), (0 : Fin k → ℂ), (1 : ℂ)) m n (Qtr (m + n))).compContinuousLinearMap
    (fun _ : Fin m => translatedMixedSlotCoordinateCLM (k := k) n)

/-- Helper for Cartan section28 0001_Theorem_2: evaluating the mixed coefficient map is the same
as feeding `Qtr` with the `m` active mixed slots followed by `n` copies of the pure translated
parameter direction. -/
theorem translatedQtrMixedCoeffMap_apply
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    (m n : ℕ)
    (v : Fin m → (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)) :
    translatedQtrMixedCoeffMap Qtr m n v =
      Qtr (m + n)
        (Fin.append
          (fun i ↦ translatedMixedSlotCoordinateCLM (k := k) n (v i))
          (fun _ : Fin n ↦ ((0 : ℂ), (0 : Fin k → ℂ), (1 : ℂ)))) := by
  -- First expand the frozen-slot recursion, then rewrite the active slots through the explicit
  -- coordinate map from `ℂ × lp` into the translated Taylor owner.
  simp [translatedQtrMixedCoeffMap, freezeRightSlots_apply]

/-- Helper for Cartan section28 0001_Theorem_2: for fixed mixed inputs in the first `m` slots,
the remaining translated-parameter coefficients of `Qtr` form a one-variable formal series. -/
noncomputable def translatedQtrMixedCoeffSeries
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    (m : ℕ) (v : Fin m → (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)) :
    FormalMultilinearSeries ℂ ℂ (Fin k → ℂ) :=
  oneVariableSeriesOfCoefficients fun n ↦ translatedQtrMixedCoeffMap Qtr m n v

/-- Helper for Cartan section28 0001_Theorem_2: the diagonal coefficients of the mixed
one-variable series are exactly the frozen mixed coefficients of `Qtr`. -/
theorem translatedQtrMixedCoeffSeries_coeff
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    (m : ℕ) (v : Fin m → (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)) (n : ℕ) :
    (translatedQtrMixedCoeffSeries Qtr m v).coeff n = translatedQtrMixedCoeffMap Qtr m n v := by
  -- The mixed series was defined by storing these coefficients directly.
  rw [translatedQtrMixedCoeffSeries, oneVariableSeriesOfCoefficients_coeff]

/-- Helper for Cartan section28 0001_Theorem_2: each weighted mixed coefficient of `Qtr` is
pointwise dominated by the shifted radius budget of `Qtr` times the product of the active input
norms. -/
theorem translatedQtrMixedCoeffMap_weightedNorm_le
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    {ρ : NNReal} (hρ : 0 < ρ) (m n : ℕ)
    (v : Fin m → (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)) :
    ‖((ρ : ℂ) ^ n) • translatedQtrMixedCoeffMap Qtr m n v‖ ≤
      (((ρ : ℝ) ^ m)⁻¹ * ∏ i : Fin m, ‖v i‖) * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n)) := by
  let C : ℝ := ∏ i : Fin m, ‖v i‖
  have hρRnonneg : 0 ≤ (ρ : ℝ) := by exact_mod_cast hρ.le
  have hρRne : (ρ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ)
  have hactive :
      ∏ i : Fin m, ‖translatedMixedSlotCoordinateCLM (k := k) n (v i)‖ ≤ C := by
    -- Each active mixed slot is controlled by the norm of its original `ℂ × lp` input.
    calc
      ∏ i : Fin m, ‖translatedMixedSlotCoordinateCLM (k := k) n (v i)‖
          ≤ ∏ i : Fin m, ‖v i‖ := by
              exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) fun i _ ↦
                translatedMixedSlotCoordinateCLM_norm_le (k := k) n (v i)
      _ = C := rfl
  have happend :
      ∏ i : Fin (m + n),
          ‖Fin.append
              (fun i ↦ translatedMixedSlotCoordinateCLM (k := k) n (v i))
              (fun _ : Fin n ↦ ((0 : ℂ), (0 : Fin k → ℂ), (1 : ℂ))) i‖
        ≤ C := by
    -- The frozen parameter slots have norm `1`, so only the active mixed slots matter.
    calc
      ∏ i : Fin (m + n),
          ‖Fin.append
              (fun i ↦ translatedMixedSlotCoordinateCLM (k := k) n (v i))
              (fun _ : Fin n ↦ ((0 : ℂ), (0 : Fin k → ℂ), (1 : ℂ))) i‖
          =
            (∏ i : Fin m, ‖translatedMixedSlotCoordinateCLM (k := k) n (v i)‖) *
              ∏ _ : Fin n, ‖((0 : ℂ), (0 : Fin k → ℂ), (1 : ℂ))‖ := by
                rw [Fin.prod_univ_add]
                simp [Fin.append_left, Fin.append_right]
      _ ≤ C * ∏ _ : Fin n, ‖((0 : ℂ), (0 : Fin k → ℂ), (1 : ℂ))‖ := by
            exact mul_le_mul hactive le_rfl (by positivity) (by positivity)
      _ = C := by
            simp [C, Prod.norm_def]
  have hcoeff :
      ‖translatedQtrMixedCoeffMap Qtr m n v‖ ≤ ‖Qtr (m + n)‖ * C := by
    -- Evaluate `Qtr` on the appended active/frozen tuple and bound it by the operator norm of the
    -- degree-`m + n` multilinear term.
    calc
      ‖translatedQtrMixedCoeffMap Qtr m n v‖
          =
            ‖Qtr (m + n)
              (Fin.append
                (fun i ↦ translatedMixedSlotCoordinateCLM (k := k) n (v i))
                (fun _ : Fin n ↦ ((0 : ℂ), (0 : Fin k → ℂ), (1 : ℂ))))‖ := by
                  rw [translatedQtrMixedCoeffMap_apply]
      _ ≤ ‖Qtr (m + n)‖ *
            ∏ i : Fin (m + n),
              ‖Fin.append
                  (fun i ↦ translatedMixedSlotCoordinateCLM (k := k) n (v i))
                  (fun _ : Fin n ↦ ((0 : ℂ), (0 : Fin k → ℂ), (1 : ℂ))) i‖ :=
            (Qtr (m + n)).le_opNorm _
      _ ≤ ‖Qtr (m + n)‖ * C := by
            exact mul_le_mul_of_nonneg_left happend (norm_nonneg _)
  have hpow :
      (ρ : ℝ) ^ n = ((ρ : ℝ) ^ m)⁻¹ * (ρ : ℝ) ^ (m + n) := by
    calc
      (ρ : ℝ) ^ n = (((ρ : ℝ) ^ m)⁻¹ * (ρ : ℝ) ^ m) * (ρ : ℝ) ^ n := by
        simp [pow_ne_zero _ hρRne]
      _ = ((ρ : ℝ) ^ m)⁻¹ * ((ρ : ℝ) ^ m * (ρ : ℝ) ^ n) := by ring
      _ = ((ρ : ℝ) ^ m)⁻¹ * (ρ : ℝ) ^ (m + n) := by rw [pow_add]
  -- Rewrite the scaled mixed coefficient row against the shifted `Qtr` budget.
  calc
    ‖((ρ : ℂ) ^ n) • translatedQtrMixedCoeffMap Qtr m n v‖
        = (ρ : ℝ) ^ n * ‖translatedQtrMixedCoeffMap Qtr m n v‖ := by
            rw [norm_smul, norm_pow]
            simp
    _ ≤ (ρ : ℝ) ^ n * (‖Qtr (m + n)‖ * C) := by
          exact mul_le_mul_of_nonneg_left hcoeff (pow_nonneg hρRnonneg _)
    _ = (((ρ : ℝ) ^ m)⁻¹ * C) * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n)) := by
          rw [hpow]
          ring

/-- Helper for Cartan section28 0001_Theorem_2: after freezing the first `m` mixed slots, the
remaining translated-parameter coefficient row is summable at every smaller radius. -/
theorem translatedQtrMixedCoeffMap_summableNormRow
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    {ρ : NNReal} (hρ : 0 < ρ) (hρlt : (ρ : ENNReal) < Qtr.radius)
    (m : ℕ) (v : Fin m → (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)) :
    Summable (fun n : ℕ ↦ ‖((ρ : ℂ) ^ n) • translatedQtrMixedCoeffMap Qtr m n v‖) := by
  let C : ℝ := ∏ i : Fin m, ‖v i‖
  have hshift :
      Summable (fun n : ℕ ↦ ‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n)) := by
    -- Shift the radius-controlled coefficient budget of `Qtr` to the tail starting at degree `m`.
    refine ((_root_.summable_nat_add_iff m).2 (Qtr.summable_norm_mul_pow hρlt)).congr ?_
    intro n
    rw [Nat.add_comm n m]
  have hmajor :
      Summable
        (fun n : ℕ ↦ (((ρ : ℝ) ^ m)⁻¹ * C) * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n))) := by
    -- The frozen active slots contribute only a constant multiplicative factor in front of the
    -- shifted `Qtr` coefficient budget.
    simpa [C] using hshift.mul_left (((ρ : ℝ) ^ m)⁻¹ * C)
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_ hmajor
  intro n
  simpa [C] using translatedQtrMixedCoeffMap_weightedNorm_le (Qtr := Qtr) hρ m n v

/-- Helper for Cartan section28 0001_Theorem_2: the `lp` packaging of the weighted mixed
coefficient row is bounded by the shifted radius budget of `Qtr`. -/
theorem translatedQtrMixedCoeffToLp_norm_le
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    {ρ : NNReal} (hρ : 0 < ρ) (hρlt : (ρ : ENNReal) < Qtr.radius)
    (m : ℕ) (v : Fin m → (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)) :
    ‖summableNormRowToLp
        (f := fun n ↦ ((ρ : ℂ) ^ n) • translatedQtrMixedCoeffMap Qtr m n v)
        (translatedQtrMixedCoeffMap_summableNormRow (Qtr := Qtr) hρ hρlt m v)‖
      ≤
        (∑' n : ℕ,
          (((ρ : ℝ) ^ m)⁻¹ * ∏ i : Fin m, ‖v i‖) *
            (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n))) := by
  have hp : 0 < (1 : ENNReal).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow hp]
  simp [summableNormRowToLp_apply, Real.rpow_one]
  refine Summable.tsum_le_tsum ?_
    (translatedQtrMixedCoeffMap_summableNormRow (Qtr := Qtr) hρ hρlt m v) ?_
  · intro n
    exact translatedQtrMixedCoeffMap_weightedNorm_le (Qtr := Qtr) hρ m n v
  · let C : ℝ := ((ρ : ℝ) ^ m)⁻¹ * ∏ i : Fin m, ‖v i‖
    have hshift :
        Summable (fun n : ℕ ↦ ‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n)) := by
      refine ((_root_.summable_nat_add_iff m).2 (Qtr.summable_norm_mul_pow hρlt)).congr ?_
      intro n
      rw [Nat.add_comm n m]
    simpa [C] using hshift.mul_left C

/-- Helper for Cartan section28 0001_Theorem_2: after freezing the first `m` mixed slots, any
smaller radius for `Qtr` remains a valid lower bound for the resulting one-variable mixed
coefficient series. -/
theorem le_radius_translatedQtrMixedCoeffSeries
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    {ρ : NNReal} (hρ : 0 < ρ) (hρlt : (ρ : ENNReal) < Qtr.radius)
    (m : ℕ) (v : Fin m → (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)) :
    (ρ : ENNReal) ≤ (translatedQtrMixedCoeffSeries Qtr m v).radius := by
  have howner :
      Summable
        (fun n : ℕ ↦ ‖(translatedQtrMixedCoeffSeries Qtr m v) n‖ * (ρ : ℝ) ^ n) := by
    -- Rewrite the frozen mixed row as the one-variable coefficient budget of the packaged
    -- series, then reuse the shifted `Qtr` summability estimate proved above.
    refine (translatedQtrMixedCoeffMap_summableNormRow (Qtr := Qtr) hρ hρlt m v).congr ?_
    intro n
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef
      (p := translatedQtrMixedCoeffSeries Qtr m v) (n := n)]
    rw [translatedQtrMixedCoeffSeries_coeff, norm_smul, norm_pow]
    have hρnorm : ‖(ρ : ℂ)‖ = (ρ : ℝ) := by
      simp
    rw [hρnorm]
    ring
  -- Apply the standard one-variable radius criterion to the frozen mixed coefficient series.
  exact FormalMultilinearSeries.le_radius_of_summable_norm
    (p := translatedQtrMixedCoeffSeries Qtr m v) (r := ρ) howner

/-- Helper for Cartan section28 0001_Theorem_2: every frozen mixed one-variable coefficient series
obtained from `Qtr` has positive radius whenever `Qtr` itself has a positive smaller radius. -/
theorem translatedQtrMixedCoeffSeries_radius_pos
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    {ρ : NNReal} (hρ : 0 < ρ) (hρlt : (ρ : ENNReal) < Qtr.radius)
    (m : ℕ) (v : Fin m → (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)) :
    0 < (translatedQtrMixedCoeffSeries Qtr m v).radius := by
  -- Any positive lower bound in `ENNReal` gives the required positivity of the frozen series
  -- radius.
  exact lt_of_lt_of_le
    (by simpa [ENNReal.coe_pos] using hρ)
    (le_radius_translatedQtrMixedCoeffSeries (Qtr := Qtr) hρ hρlt m v)

/-- Helper for Cartan section28 0001_Theorem_2: weighted evaluation of the packaged mixed
coefficient row recovers the one-variable mixed series obtained from `Qtr`. -/
theorem weightedParameterEvalCLM_translatedQtrMixedCoeffRow_eq_sum
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    {ρ : NNReal} (hρ : 0 < ρ) (hρlt : (ρ : ENNReal) < Qtr.radius)
    {u : ℂ} (hu : ‖u‖ < ρ)
    (m : ℕ) (v : Fin m → (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)) :
    weightedParameterEvalCLM ρ u hu
      (summableNormRowToLp
        (f := fun n ↦ ((ρ : ℂ) ^ n) • translatedQtrMixedCoeffMap Qtr m n v)
        (translatedQtrMixedCoeffMap_summableNormRow (Qtr := Qtr) hρ hρlt m v)) =
      (translatedQtrMixedCoeffSeries Qtr m v).sum u := by
  have hsumCoeff :
      Summable (fun n : ℕ ↦ ‖translatedQtrMixedCoeffMap Qtr m n v‖ * (ρ : ℝ) ^ n) := by
    -- Forget the explicit scaling by `ρ^n` and record the corresponding coefficient budget.
    refine (translatedQtrMixedCoeffMap_summableNormRow (Qtr := Qtr) hρ hρlt m v).congr ?_
    intro n
    rw [norm_smul, norm_pow]
    simp
    ring
  -- The packaged mixed row is exactly the one-variable coefficient series associated to the
  -- frozen first `m` slots of `Qtr`.
  simpa [translatedQtrMixedCoeffSeries] using
    (weightedParameterEvalCLM_scaledCoeffRow_eq_oneVariableSeriesSum
      (k := k) (ρ := ρ) (u := u) hρ hu
      (a := fun n ↦ translatedQtrMixedCoeffMap Qtr m n v) hsumCoeff)

/-- Helper for Cartan section28 0001_Theorem_2: package the scaled mixed coefficient row of
`Qtr` into the Banach carrier `lp (fun _ : ℕ => Fin k → ℂ) 1` as one multilinear coefficient. -/
noncomputable def translatedQtrMixedCoeffToLp
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    {ρ : NNReal} (hρ : 0 < ρ) (hρlt : (ρ : ENNReal) < Qtr.radius)
    (m : ℕ) :
    ContinuousMultilinearMap
      ℂ
      (fun _ : Fin m => (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1))
      (lp (fun _ : ℕ => Fin k → ℂ) 1) := by
  let f :
      MultilinearMap
        ℂ
        (fun _ : Fin m => (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1))
        (lp (fun _ : ℕ => Fin k → ℂ) 1) :=
    { toFun := fun v ↦
        summableNormRowToLp
          (f := fun n ↦ ((ρ : ℂ) ^ n) • translatedQtrMixedCoeffMap Qtr m n v)
          (translatedQtrMixedCoeffMap_summableNormRow (Qtr := Qtr) hρ hρlt m v)
      map_update_add' := fun v i x y ↦ by
        -- The packaged `lp` row is multilinear because every coordinate row is multilinear.
        apply Subtype.ext
        funext n
        change
          ((ρ : ℂ) ^ n) • translatedQtrMixedCoeffMap Qtr m n (Function.update v i (x + y)) =
            (summableNormRowToLp
                (f := fun j ↦
                  ((ρ : ℂ) ^ j) • translatedQtrMixedCoeffMap Qtr m j (Function.update v i x))
                (translatedQtrMixedCoeffMap_summableNormRow (Qtr := Qtr) hρ hρlt m
                  (Function.update v i x)) : lp (fun _ : ℕ => Fin k → ℂ) 1) n
              +
            (summableNormRowToLp
                (f := fun j ↦
                  ((ρ : ℂ) ^ j) • translatedQtrMixedCoeffMap Qtr m j (Function.update v i y))
                (translatedQtrMixedCoeffMap_summableNormRow (Qtr := Qtr) hρ hρlt m
                  (Function.update v i y)) : lp (fun _ : ℕ => Fin k → ℂ) 1) n
        rw [summableNormRowToLp_apply, summableNormRowToLp_apply]
        calc
          ((ρ : ℂ) ^ n) • translatedQtrMixedCoeffMap Qtr m n (Function.update v i (x + y))
              = ((ρ : ℂ) ^ n) •
                  ((translatedQtrMixedCoeffMap Qtr m n) (Function.update v i x) +
                    (translatedQtrMixedCoeffMap Qtr m n) (Function.update v i y)) := by
                      exact
                        congrArg
                          (fun z : Fin k → ℂ ↦ ((ρ : ℂ) ^ n) • z)
                          ((translatedQtrMixedCoeffMap Qtr m n).map_update_add v i x y)
          _ = ((ρ : ℂ) ^ n) • translatedQtrMixedCoeffMap Qtr m n (Function.update v i x) +
                ((ρ : ℂ) ^ n) • translatedQtrMixedCoeffMap Qtr m n (Function.update v i y) := by
                  simp [smul_add]
      map_update_smul' := fun v i c x ↦ by
        -- Scalar multiplication propagates coordinatewise through the packaged mixed row.
        apply Subtype.ext
        funext n
        change
          ((ρ : ℂ) ^ n) • translatedQtrMixedCoeffMap Qtr m n (Function.update v i (c • x)) =
            c •
              (summableNormRowToLp
                (f := fun j ↦
                  ((ρ : ℂ) ^ j) • translatedQtrMixedCoeffMap Qtr m j (Function.update v i x))
                (translatedQtrMixedCoeffMap_summableNormRow (Qtr := Qtr) hρ hρlt m
                  (Function.update v i x)) : lp (fun _ : ℕ => Fin k → ℂ) 1) n
        rw [summableNormRowToLp_apply]
        simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
          congrArg
            (fun z : Fin k → ℂ ↦ ((ρ : ℂ) ^ n) • z)
            ((translatedQtrMixedCoeffMap Qtr m n).map_update_smul v i c x) }
  let C : ℝ :=
    ∑' n : ℕ, ((ρ : ℝ) ^ m)⁻¹ * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n))
  refine f.mkContinuous C ?_
  intro v
  let A : ℝ := ∏ i : Fin m, ‖v i‖
  have hshift :
      Summable (fun n : ℕ ↦ ‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n)) := by
    -- The shifted radius budget of `Qtr` stays summable.
    refine ((_root_.summable_nat_add_iff m).2 (Qtr.summable_norm_mul_pow hρlt)).congr ?_
    intro n
    rw [Nat.add_comm n m]
  have hscaled :
      Summable (fun n : ℕ ↦ ((ρ : ℝ) ^ m)⁻¹ * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n))) := by
    -- Only a constant factor is introduced in front of the shifted coefficient budget.
    simpa using hshift.mul_left (((ρ : ℝ) ^ m)⁻¹)
  -- Factor the active-input norm product out of the explicit pointwise estimate.
  calc
    ‖f v‖
        ≤ ∑' n : ℕ, (((ρ : ℝ) ^ m)⁻¹ * A) * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n)) := by
          simpa [f, A] using translatedQtrMixedCoeffToLp_norm_le (Qtr := Qtr) hρ hρlt m v
    _ = (∑' n : ℕ, ((ρ : ℝ) ^ m)⁻¹ * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n))) * A := by
          have hrew :
              (fun n : ℕ ↦ (((ρ : ℝ) ^ m)⁻¹ * A) * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n))) =
                (fun n : ℕ ↦ (((ρ : ℝ) ^ m)⁻¹ * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n))) * A) := by
            funext n
            ring
          rw [hrew, tsum_mul_right]
    _ = C * ∏ i : Fin m, ‖v i‖ := by
          simp [C, A]

/-- Helper for Cartan section28 0001_Theorem_2: evaluating the packaged multilinear coefficient
recovers the canonical `lp` row built from the scaled mixed coefficients of `Qtr`. -/
theorem translatedQtrMixedCoeffToLp_apply
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    {ρ : NNReal} (hρ : 0 < ρ) (hρlt : (ρ : ENNReal) < Qtr.radius)
    (m : ℕ) (v : Fin m → (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)) :
    translatedQtrMixedCoeffToLp Qtr hρ hρlt m v =
      summableNormRowToLp
        (f := fun n ↦ ((ρ : ℂ) ^ n) • translatedQtrMixedCoeffMap Qtr m n v)
        (translatedQtrMixedCoeffMap_summableNormRow (Qtr := Qtr) hρ hρlt m v) := by
  -- The bundled multilinear map evaluates by the same direct `lp` row used in its definition.
  simp [translatedQtrMixedCoeffToLp, MultilinearMap.coe_mkContinuous]

/-- Helper for Cartan section28 0001_Theorem_2: the direct `lp` packaging of the mixed
coefficient row satisfies the expected multilinear norm bound with the shifted `Qtr` budget. -/
theorem translatedQtrMixedCoeffToLp_le
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    {ρ : NNReal} (hρ : 0 < ρ) (hρlt : (ρ : ENNReal) < Qtr.radius)
    (m : ℕ) (v : Fin m → (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)) :
    ‖translatedQtrMixedCoeffToLp Qtr hρ hρlt m v‖ ≤
      (∑' n : ℕ, ((ρ : ℝ) ^ m)⁻¹ * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n))) *
        ∏ i : Fin m, ‖v i‖ := by
  let A : ℝ := ∏ i : Fin m, ‖v i‖
  have hshift :
      Summable (fun n : ℕ ↦ ‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n)) := by
    -- The shifted radius budget of `Qtr` stays summable.
    refine ((_root_.summable_nat_add_iff m).2 (Qtr.summable_norm_mul_pow hρlt)).congr ?_
    intro n
    rw [Nat.add_comm n m]
  have hscaled :
      Summable (fun n : ℕ ↦ ((ρ : ℝ) ^ m)⁻¹ * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n))) := by
    -- Only a constant factor is introduced in front of the shifted coefficient budget.
    simpa using hshift.mul_left (((ρ : ℝ) ^ m)⁻¹)
  -- Reuse the packaged row estimate and factor the active-input norm product out of the `tsum`.
  calc
    ‖translatedQtrMixedCoeffToLp Qtr hρ hρlt m v‖
        ≤ ∑' n : ℕ, (((ρ : ℝ) ^ m)⁻¹ * A) * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n)) := by
          simpa [translatedQtrMixedCoeffToLp_apply, A] using
            translatedQtrMixedCoeffToLp_norm_le (Qtr := Qtr) hρ hρlt m v
    _ = (∑' n : ℕ, ((ρ : ℝ) ^ m)⁻¹ * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n))) * A := by
          have hrew :
              (fun n : ℕ ↦ (((ρ : ℝ) ^ m)⁻¹ * A) * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n))) =
                (fun n : ℕ ↦ (((ρ : ℝ) ^ m)⁻¹ * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n))) * A) := by
            funext n
            ring
          rw [hrew, tsum_mul_right]
    _ = (∑' n : ℕ, ((ρ : ℝ) ^ m)⁻¹ * (‖Qtr (m + n)‖ * (ρ : ℝ) ^ (m + n))) *
          ∏ i : Fin m, ‖v i‖ := by
          simp [A]

/-- Helper for Cartan section28 0001_Theorem_2: weighted evaluation of the packaged multilinear
mixed coefficient agrees with the corresponding one-variable mixed series sum. -/
theorem weightedParameterEvalCLM_translatedQtrMixedCoeffToLp_eq_sum
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    {ρ : NNReal} (hρ : 0 < ρ) (hρlt : (ρ : ENNReal) < Qtr.radius)
    {u : ℂ} (hu : ‖u‖ < ρ)
    (m : ℕ) (v : Fin m → (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)) :
    weightedParameterEvalCLM ρ u hu (translatedQtrMixedCoeffToLp Qtr hρ hρlt m v) =
      (translatedQtrMixedCoeffSeries Qtr m v).sum u := by
  -- Expand the packaged multilinear coefficient back to the explicit `lp` row and invoke the
  -- already-proved row evaluation formula.
  rw [translatedQtrMixedCoeffToLp_apply (Qtr := Qtr) hρ hρlt m v]
  exact weightedParameterEvalCLM_translatedQtrMixedCoeffRow_eq_sum
    (Qtr := Qtr) hρ hρlt hu m v

/-- Helper for Cartan section28 0001_Theorem_2: the direct `lp`-packaged common Banach owner has
positive radius as soon as the translated Taylor owner is evaluated strictly inside its radius. -/
theorem translatedCommonBanachOwner_radiusPos
    {k : ℕ}
    (Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ))
    {ρu : NNReal} (hρupos : 0 < ρu) (hρult : (ρu : ENNReal) < Qtr.radius) :
    let QB :
      FormalMultilinearSeries
        ℂ
        (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)
        (lp (fun _ : ℕ => Fin k → ℂ) 1) :=
      fun m ↦ translatedQtrMixedCoeffToLp Qtr hρupos hρult m
    0 < QB.radius := by
  dsimp
  let QB :
      FormalMultilinearSeries
        ℂ
        (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)
        (lp (fun _ : ℕ => Fin k → ℂ) 1) :=
    fun m ↦ translatedQtrMixedCoeffToLp Qtr hρupos hρult m
  change 0 < QB.radius
  let r : NNReal := ρu / 2
  have hrpos : 0 < r := by
    -- Any strict inner radius keeps half of the original positive radius.
    dsimp [r]
    positivity
  have hρune : (ρu : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hρupos)
  let a : ℕ → ℝ := fun n ↦ ‖Qtr n‖ * (ρu : ℝ) ^ n
  let S : ℝ := ∑' n : ℕ, a n
  have hbudget : Summable a := by
    -- The original translated Taylor owner is summable at every strict inner radius.
    simpa [a] using Qtr.summable_norm_mul_pow hρult
  have htail_le : ∀ m : ℕ, (∑' n : ℕ, a (n + m)) ≤ S := by
    intro m
    have hprefix_nonneg : 0 ≤ Finset.sum (Finset.range m) a := by
      refine Finset.sum_nonneg ?_
      intro i hi
      dsimp [a]
      positivity
    have hsplit := hbudget.sum_add_tsum_nat_add m
    calc
      ∑' n : ℕ, a (n + m)
          ≤ Finset.sum (Finset.range m) a + ∑' n : ℕ, a (n + m) := by linarith
      _ = S := by
            have hsplit' : Finset.sum (Finset.range m) a + ∑' n : ℕ, a (n + m) = S := by
              simpa [S, a, Nat.add_comm] using hsplit
            exact hsplit'
  have hgeom :
      Summable (fun m : ℕ ↦ ((1 / 2 : ℝ) ^ m) * S) := by
    -- The geometric factor from halving the radius dominates the remaining tail uniformly in `m`.
    simpa using
      (summable_geometric_of_lt_one (by positivity) (by norm_num : (1 / 2 : ℝ) < 1)).mul_right S
  have hnormSumm :
      Summable (fun m : ℕ ↦ ‖QB m‖ * (r : ℝ) ^ m) := by
    refine Summable.of_nonneg_of_le (fun m ↦ by positivity) ?_ hgeom
    intro m
    have hop :
        ‖QB m‖ ≤
          ∑' n : ℕ, ((ρu : ℝ) ^ m)⁻¹ * (‖Qtr (m + n)‖ * (ρu : ℝ) ^ (m + n)) := by
      -- The operator norm is controlled by the explicit multilinear bound already proved for the
      -- packaged mixed coefficient row.
      refine ContinuousMultilinearMap.opNorm_le_bound ?_ ?_
      · exact tsum_nonneg (fun n ↦ by positivity)
      · intro v
        simpa [QB] using translatedQtrMixedCoeffToLp_le (Qtr := Qtr) hρupos hρult m v
    have htailSumm : Summable (fun n : ℕ ↦ a (n + m)) := by
      exact ((_root_.summable_nat_add_iff m).2 hbudget)
    have hratio :
        ((ρu : ℝ) ^ m)⁻¹ * (r : ℝ) ^ m = (1 / 2 : ℝ) ^ m := by
      -- Halving the working radius contributes the geometric factor `(1/2)^m`.
      change ((ρu : ℝ) ^ m)⁻¹ * (((ρu : ℝ) / 2) ^ m) = (1 / 2 : ℝ) ^ m
      rw [div_eq_mul_inv, mul_pow]
      calc
        ((ρu : ℝ) ^ m)⁻¹ * ((ρu : ℝ) ^ m * ((2 : ℝ)⁻¹) ^ m) =
            (((ρu : ℝ) ^ m)⁻¹ * (ρu : ℝ) ^ m) * ((2 : ℝ)⁻¹) ^ m := by ring
        _ = ((2 : ℝ)⁻¹) ^ m := by
              simp [pow_ne_zero _ hρune]
        _ = (1 / 2 : ℝ) ^ m := by norm_num
    calc
      ‖QB m‖ * (r : ℝ) ^ m
          ≤
            (∑' n : ℕ, ((ρu : ℝ) ^ m)⁻¹ *
              (‖Qtr (m + n)‖ * (ρu : ℝ) ^ (m + n))) *
              (r : ℝ) ^ m := by
                gcongr
      _ =
          ((1 / 2 : ℝ) ^ m) * (∑' n : ℕ, a (n + m)) := by
            have htsum :
                (∑' n : ℕ, ((ρu : ℝ) ^ m)⁻¹ * (‖Qtr (m + n)‖ * (ρu : ℝ) ^ (m + n))) =
                  ((ρu : ℝ) ^ m)⁻¹ *
                    (∑' n : ℕ, ‖Qtr (m + n)‖ * (ρu : ℝ) ^ (m + n)) := by
              rw [tsum_mul_left]
            have htailComm :
                (∑' n : ℕ, ‖Qtr (m + n)‖ * (ρu : ℝ) ^ (m + n)) =
                  ∑' n : ℕ, (ρu : ℝ) ^ (m + n) * ‖Qtr (m + n)‖ := by
              refine tsum_congr ?_
              intro n
              ring
            rw [htsum, htailComm]
            calc
              ((((ρu : ℝ) ^ m)⁻¹ * ∑' n : ℕ, (ρu : ℝ) ^ (m + n) * ‖Qtr (m + n)‖)) *
                    (r : ℝ) ^ m
                  = (((ρu : ℝ) ^ m)⁻¹ * (r : ℝ) ^ m) *
                      (∑' n : ℕ, (ρu : ℝ) ^ (m + n) * ‖Qtr (m + n)‖) := by ring
              _ = ((1 / 2 : ℝ) ^ m) *
                    (∑' n : ℕ, (ρu : ℝ) ^ (m + n) * ‖Qtr (m + n)‖) := by
                      rw [hratio]
              _ = ((1 / 2 : ℝ) ^ m) * (∑' n : ℕ, a (n + m)) := by
                    simp [a, Nat.add_comm, mul_comm]
      _ ≤ ((1 / 2 : ℝ) ^ m) * S := by
            gcongr
            exact htail_le m
  have hrle : (r : ENNReal) ≤ QB.radius := by
    -- Summability at the halved radius gives a concrete lower bound on the radius of `QB`.
    exact FormalMultilinearSeries.le_radius_of_summable_norm (p := QB) (r := r) hnormSumm
  exact lt_of_lt_of_le (by simpa [ENNReal.coe_pos] using hrpos) hrle

/-- Helper for Cartan section28 0001_Theorem_2: after packaging the translated Taylor owner into a
common Banach-valued owner, freezing the parameter and evaluating in the Banach direction should
recover the lifted scalar slice owner coming from `translatedLiftedSliceOwner_fromQtr`. -/
theorem translatedLiftedSliceOwner_changeOrigin_fromQtr
    {k j : ℕ} {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {t0 : Fin j → ℂ} (r : Fin j)
    {Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ)}
    {R : ENNReal}
    (hQtrBall :
      HasFPowerSeriesOnBall
        (fun p : ℂ × (Fin k → ℂ) × ℂ ↦
          F p.1 p.2.1 (Function.update t0 r (t0 r + p.2.2)))
        Qtr
        ((0 : ℂ), (0 : Fin k → ℂ), 0)
        R)
    {ρu : NNReal}
    (hρult : (ρu : ENNReal) < R)
    {u : ℂ}
    (hu : ‖u‖ < ρu) :
    let L := weightedParameterEvalCLM ρu u hu
    let y : ℂ × (Fin k → ℂ) × ℂ := ((0 : ℂ), (0 : Fin k → ℂ), u)
    let M :
      (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1) →L[ℂ]
        (ℂ × (Fin k → ℂ) × ℂ) :=
      (ContinuousLinearMap.fst ℂ ℂ (lp (fun _ : ℕ => Fin k → ℂ) 1)).prod
        (((L.comp (ContinuousLinearMap.snd ℂ ℂ (lp (fun _ : ℕ => Fin k → ℂ) 1))).prod
          (0 : (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1) →L[ℂ] ℂ)))
    HasFPowerSeriesAt
      (fun p : ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1 ↦
        F p.1 (L p.2) (Function.update t0 r (t0 r + u)))
      ((Qtr.changeOrigin y).compContinuousLinearMap M)
      ((0 : ℂ), 0) := by
  intro L y M
  have hylt : (‖y‖₊ : ENNReal) < R := by
    have hnorm : ‖u‖₊ < ρu := by
      simpa using hu
    have hlt : (‖u‖₊ : ENNReal) < R := lt_trans (by exact_mod_cast hnorm) hρult
    simpa [y] using hlt
  have hchange :
      HasFPowerSeriesOnBall
        (fun q : ℂ × (Fin k → ℂ) × ℂ ↦
          F q.1 q.2.1 (Function.update t0 r (t0 r + q.2.2)))
        (Qtr.changeOrigin y)
        y
        (R - ‖y‖₊) := by
    simpa [y] using hQtrBall.changeOrigin hylt
  have hshift :
      HasFPowerSeriesAt
        (fun q : ℂ × (Fin k → ℂ) × ℂ ↦
          F (q + y).1 (q + y).2.1 (Function.update t0 r (t0 r + (q + y).2.2)))
        (Qtr.changeOrigin y)
        (0 : ℂ × (Fin k → ℂ) × ℂ) := by
    -- Translate the scalar parameter center back to the origin once before freezing the `lp`
    -- state variable by a linear map.
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (hchange.comp_sub (-y)).hasFPowerSeriesAt
  -- Now freeze the last coordinate and evaluate the Banach state variable through the weighted
  -- parameter map.
  have hshiftAtM0 :
      HasFPowerSeriesAt
        (fun q : ℂ × (Fin k → ℂ) × ℂ ↦
          F (q + y).1 (q + y).2.1 (Function.update t0 r (t0 r + (q + y).2.2)))
        (Qtr.changeOrigin y)
        (M ((0 : ℂ), 0)) := by
    simpa [M] using hshift
  have hcomp :
      HasFPowerSeriesAt
        (fun p : ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1 ↦
          F ((M p + y).1) ((M p + y).2.1)
            (Function.update t0 r (t0 r + (M p + y).2.2)))
        ((Qtr.changeOrigin y).compContinuousLinearMap M)
        ((0 : ℂ), 0) := by
    simpa [Function.comp] using
      hshiftAtM0.compContinuousLinearMap (u := M) (x := ((0 : ℂ), 0))
  convert hcomp using 1
  -- Expand the fixed affine embedding once: it keeps the `x` coordinate, evaluates the Banach
  -- state variable through `L`, and sets the translated parameter increment to `u`.
  funext p
  simp [M, y, add_comm]
